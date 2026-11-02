import EthInapproximability.CurrentPaper.SourceClauseAllSlots
import EthInapproximability.CurrentPaper.SourceClauseCircuitClock

/-! Clocking the *same* selected-slot and ascending all-slot circuits. -/

namespace EthInapproximability.CurrentPaper.SourceClauseCallback.AllSlotsClock

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical
open SourceClauseCallback

theorem lift_bounded {q : ℕ}
    (A : Circuit (SourceClauseRowWriterOperands.Stack q))
    (S T : SourceClauseRowWriterOperands.Stack q → List Bool)
    (F : SourceClauseRowWriterTruthFrame.Stack q → List Bool)
    (bound : ℕ)
    (h : Circuit.BoundedRun A bound S T)
    (hbank : bank SourceClauseRowWriterTruthFrame.writerEmbedding F S = F) :
    Circuit.BoundedRun (FalseDispatch.liftCircuit A) bound F
      (bank SourceClauseRowWriterTruthFrame.writerEmbedding F T) := by
  obtain ⟨t, ht, hr⟩ := h
  have he := BitMachineStackRun.run
    (SourceClauseRowWriterTruthFrame.writerEmbedding (q := q)) F
    A.program (⟨some A.start, A.initial, S⟩) t
  have hall (d : DecidableEq (SourceClauseRowWriterOperands.Stack q)) :
      ((@advance _ _ _ d A.program)^[t])
        (⟨some A.start, A.initial, S⟩) =
        ⟨none, A.initial, T⟩ := by
    have hd : d = Classical.decEq _ := Subsingleton.elim _ _
    subst d
    exact hr
  rw [hall] at he
  apply SourceClauseCircuitClock.bounded_irrel _ _ _ _ _ _
  exact ⟨t, ht, by simpa only [FalseDispatch.liftCircuit, stackCfg,
    hbank] using he⟩

theorem false_framed_bounded {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count remaining : List Bool) (b : Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.BoundedRun (DualDispatch.falseCircuit k)
      (SourceClauseCircuitClock.falseBlockCost row n r k saved output count)
      (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
        saved output count b remaining)
      (bank SourceClauseRowWriterTruthFrame.writerEmbedding
        (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
          saved output count b remaining)
        (SourceClauseRowWriterBlank.bank row n r
          ((EncodedCNF.clauseFields
            (SourceClauseEncoding.chain (SourceClauseCallback.base n r k)
              (SourceClauseRowSchedule.tupleClause hq k
                (SourceClauseCallback.rowQuery row) false))).reverse ++ saved)
          output (List.replicate (3 * q + 2) true ++ count))) := by
  apply lift_bounded
  · exact SourceClauseCircuitClock.false_block_source_bounded
      hq row n r k saved output count hquery
  · exact FalseDispatch.flagged_writer_bank row n r
      saved output count remaining b

theorem true_framed_bounded {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count remaining : List Bool) (b : Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.BoundedRun (DualDispatch.trueCircuit hq k)
      (SourceClauseCircuitClock.trueBlockCost hq row n r k
        saved output count)
      (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
        saved output count b remaining)
      (bank SourceClauseRowWriterTruthFrame.writerEmbedding
        (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
          saved output count b remaining)
        (SourceClauseRowWriterBlank.bank row n r
          ((EncodedCNF.clauseFields
            (SourceClauseEncoding.chain (SourceClauseCallback.base n r k)
              (SourceClauseRowSchedule.tupleClause hq k
                (SourceClauseCallback.rowQuery row) true))).reverse ++ saved)
          output (List.replicate (3 * q + 5) true ++ count))) := by
  apply lift_bounded
  · exact SourceClauseCircuitClock.true_block_source_bounded
      hq row n r k saved output count hquery
  · exact FalseDispatch.flagged_writer_bank row n r
      saved output count remaining b

noncomputable def blockCost {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool) (b : Bool) : ℕ :=
  if b then
    SourceClauseCircuitClock.trueBlockCost hq row n r k saved output count
  else
    SourceClauseCircuitClock.falseBlockCost row n r k saved output count

noncomputable def selectedCost {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool) (b : Bool) : ℕ :=
  k.val + 4 + blockCost hq row n r k saved output count b

theorem false_selected_bounded {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool)
    (table : Fin (2 ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (hfalse : table k = false)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    ∃ t ≤ selectedCost hq row n r k saved output count false,
      ((advance (DualDispatch.program hq k))^[t])
        (⟨some (DualDispatch.flagLabel hq k .marker),
          (((none : Option Bool), (DualDispatch.falseCircuit k).initial),
            (DualDispatch.trueCircuit hq k).initial),
          SourceClauseRowWriterTruthFrame.afterCopy row n r
            saved output count (true :: List.ofFn table)⟩) =
        ⟨none,
          (((none : Option Bool), (DualDispatch.falseCircuit k).initial),
            (DualDispatch.trueCircuit hq k).initial),
          DualDispatch.finalBank hq row n r k saved output count
            ((List.ofFn table).drop (k.val + 1)) false⟩ := by
  let Bf := DualDispatch.falseCircuit k
  let Bt := DualDispatch.trueCircuit hq k
  let F := SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
    saved output count false ((List.ofFn table).drop (k.val + 1))
  let U := DualDispatch.finalBank hq row n r k saved output count
    ((List.ofFn table).drop (k.val + 1)) false
  obtain ⟨tf, htfle, htf⟩ := DualDispatch.flag_phase hq row n r k
    saved output count table hrow
  rw [hfalse] at htf
  obtain ⟨tb, htble, hb⟩ := false_framed_bounded hq row n r k
    saved output count ((List.ofFn table).drop (k.val + 1)) false hquery
  have hh :
      ((advance Bf.program)^[tb])
        (⟨some Bf.start, Bf.initial, F⟩) =
        ⟨none, Bf.initial, U⟩ := by
    simpa [Bf, F, U, DualDispatch.finalBank,
      DualDispatch.clauseCount] using hb
  have hbo := BitMachineInline.outputs
    (DualDispatch.falseLabel hq k)
    (fun w : Bf.Control => (((none : Option Bool), w), Bt.initial))
    (fun v => v.1.2) (fun _ => rfl)
    none Bf.program (DualDispatch.program hq k) (fun l => rfl)
    (⟨some Bf.start, Bf.initial, F⟩) tb (by rw [hh])
  obtain ⟨te, htele, hte⟩ := hbo
  have hbAll (d : DecidableEq (DualDispatch.Stack q)) :
      ((@advance _ _ _ d Bf.program)^[tb])
        (⟨some Bf.start, Bf.initial, F⟩) =
        ⟨none, Bf.initial, U⟩ := by
    have hd : d = Classical.decEq _ := Subsingleton.elim _ _
    subst d
    exact hh
  have hte' :
      ((advance (DualDispatch.program hq k))^[te])
        (⟨some (DualDispatch.falseLabel hq k Bf.start),
          (((none : Option Bool), Bf.initial), Bt.initial), F⟩) =
        ⟨none, (((none : Option Bool), Bf.initial), Bt.initial), U⟩ := by
    simpa only [BitMachineInline.cfg, hbAll] using hte
  refine ⟨tf + 1 + te, ?_, ?_⟩
  · dsimp [selectedCost, blockCost]
    omega
  · rw [show tf + 1 + te = te + (1 + tf) by omega,
      Function.iterate_add_apply,
      show 1 + tf = tf + 1 by omega,
      Function.iterate_succ_apply', htf]
    rw [DualDispatch.check_false]
    exact hte'

theorem true_selected_bounded {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool)
    (table : Fin (2 ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (htrue : table k = true)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    ∃ t ≤ selectedCost hq row n r k saved output count true,
      ((advance (DualDispatch.program hq k))^[t])
        (⟨some (DualDispatch.flagLabel hq k .marker),
          (((none : Option Bool), (DualDispatch.falseCircuit k).initial),
            (DualDispatch.trueCircuit hq k).initial),
          SourceClauseRowWriterTruthFrame.afterCopy row n r
            saved output count (true :: List.ofFn table)⟩) =
        ⟨none,
          (((none : Option Bool), (DualDispatch.falseCircuit k).initial),
            (DualDispatch.trueCircuit hq k).initial),
          DualDispatch.finalBank hq row n r k saved output count
            ((List.ofFn table).drop (k.val + 1)) true⟩ := by
  let Bf := DualDispatch.falseCircuit k
  let Bt := DualDispatch.trueCircuit hq k
  let F := SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
    saved output count true ((List.ofFn table).drop (k.val + 1))
  let U := DualDispatch.finalBank hq row n r k saved output count
    ((List.ofFn table).drop (k.val + 1)) true
  obtain ⟨tf, htfle, htf⟩ := DualDispatch.flag_phase hq row n r k
    saved output count table hrow
  rw [htrue] at htf
  obtain ⟨tb, htble, hb⟩ := true_framed_bounded hq row n r k
    saved output count ((List.ofFn table).drop (k.val + 1)) true hquery
  have hh :
      ((advance Bt.program)^[tb])
        (⟨some Bt.start, Bt.initial, F⟩) =
        ⟨none, Bt.initial, U⟩ := by
    simpa [Bt, F, U, DualDispatch.finalBank,
      DualDispatch.clauseCount] using hb
  have hbo := BitMachineInline.outputs
    (DualDispatch.trueLabel hq k)
    (fun w : Bt.Control => (((none : Option Bool), Bf.initial), w))
    (fun v => v.2) (fun _ => rfl)
    none Bt.program (DualDispatch.program hq k) (fun l => rfl)
    (⟨some Bt.start, Bt.initial, F⟩) tb (by rw [hh])
  obtain ⟨te, htele, hte⟩ := hbo
  have hbAll (d : DecidableEq (DualDispatch.Stack q)) :
      ((@advance _ _ _ d Bt.program)^[tb])
        (⟨some Bt.start, Bt.initial, F⟩) =
        ⟨none, Bt.initial, U⟩ := by
    have hd : d = Classical.decEq _ := Subsingleton.elim _ _
    subst d
    exact hh
  have hte' :
      ((advance (DualDispatch.program hq k))^[te])
        (⟨some (DualDispatch.trueLabel hq k Bt.start),
          (((none : Option Bool), Bf.initial), Bt.initial), F⟩) =
        ⟨none, (((none : Option Bool), Bf.initial), Bt.initial), U⟩ := by
    simpa only [BitMachineInline.cfg, hbAll] using hte
  refine ⟨tf + 1 + te, ?_, ?_⟩
  · dsimp [selectedCost, blockCost]
    omega
  · rw [show tf + 1 + te = te + (1 + tf) by omega,
      Function.iterate_add_apply,
      show 1 + tf = tf + 1 by omega,
      Function.iterate_succ_apply', htf]
    rw [DualDispatch.check_true]
    exact hte'

theorem selected_bounded {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool)
    (table : Fin (2 ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    ∃ t ≤ selectedCost hq row n r k saved output count (table k),
      ((advance (DualDispatch.program hq k))^[t])
        (⟨some (DualDispatch.flagLabel hq k .marker),
          (((none : Option Bool), (DualDispatch.falseCircuit k).initial),
            (DualDispatch.trueCircuit hq k).initial),
          SourceClauseRowWriterTruthFrame.afterCopy row n r
            saved output count (true :: List.ofFn table)⟩) =
        ⟨none,
          (((none : Option Bool), (DualDispatch.falseCircuit k).initial),
            (DualDispatch.trueCircuit hq k).initial),
          DualDispatch.finalBank hq row n r k saved output count
            ((List.ofFn table).drop (k.val + 1)) (table k)⟩ := by
  cases h : table k with
  | false =>
      simpa only [h] using false_selected_bounded hq row n r k
        saved output count table hrow h hquery
  | true =>
      simpa only [h] using true_selected_bounded hq row n r k
        saved output count table hrow h hquery

noncomputable def fullCost {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool) (b : Bool) : ℕ :=
  2 * (true :: List.ofFn (fun _ : Fin (2 ^ q) => false)).length + 2 +
    selectedCost hq row n r k saved output count b + 1

theorem full_bounded {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool)
    (table : Fin (2 ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.BoundedRun (AllSlots.fullCircuit hq k)
      (fullCost hq row n r k saved output count (table k))
      (SourceClauseRowWriterTruthFrame.initial row n r saved output count)
      (DualDispatch.finalBank hq row n r k saved output count
        ((List.ofFn table).drop (k.val + 1)) (table k)) := by
  have hc := SourceClauseRowWriterTruthFrame.copy_run row n r
    saved output count (true :: List.ofFn table) hrow
  obtain ⟨td, hdle, hd⟩ := selected_bounded hq row n r k
    saved output count table hrow hquery
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (SourceClauseRowWriterTruthFrame.copyProgram (q := q))
    (DualDispatch.program hq k)
    BitMachineCopy.Label.scan (DualDispatch.flagLabel hq k .marker)
    (none : Option Bool) (none : Option Bool)
    ((((none : Option Bool), (DualDispatch.falseCircuit k).initial),
      (DualDispatch.trueCircuit hq k).initial))
    ((((none : Option Bool), (DualDispatch.falseCircuit k).initial),
      (DualDispatch.trueCircuit hq k).initial))
    (SourceClauseRowWriterTruthFrame.initial row n r saved output count)
    (SourceClauseRowWriterTruthFrame.afterCopy row n r saved output count
      (true :: List.ofFn table))
    (DualDispatch.finalBank hq row n r k saved output count
      ((List.ofFn table).drop (k.val + 1)) (table k))
    (2 * (true :: List.ofFn table).length + 2) td hc hd
  refine ⟨t, ?_, ?_⟩
  · dsimp [fullCost]
    simp only [List.length_cons, List.length_ofFn] at *
    omega
  · simpa only [AllSlots.fullCircuit, Circuit.of,
      DualDispatch.fullProgram] using hr

def resetCost {q : ℕ}
    (S : SourceClauseRowWriterTruthFrame.Stack q → List Bool) : ℕ :=
  (S (.inr 0)).length + (S (.inr 1)).length + 4

theorem reset_bounded {q : ℕ}
    (S : SourceClauseRowWriterTruthFrame.Stack q → List Bool) :
    Circuit.BoundedRun (AllSlots.resetCircuit (q := q))
      (resetCost S) S (TruthReset.cleared S) := by
  exact ⟨resetCost S, le_rfl, by
    simpa only [AllSlots.resetCircuit, Circuit.of, resetCost] using
      TruthReset.run S⟩

noncomputable def slotCost {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool)
    (table : Fin (2 ^ q) → Bool) : ℕ :=
  fullCost hq row n r k saved output count (table k) +
    resetCost (DualDispatch.finalBank hq row n r k saved output count
      ((List.ofFn table).drop (k.val + 1)) (table k)) + 1

theorem slot_bounded {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool)
    (table : Fin (2 ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.BoundedRun (AllSlots.slotCircuit hq k)
      (slotCost hq row n r k saved output count table)
      (SourceClauseRowWriterTruthFrame.initial row n r saved output count)
      (SourceClauseRowWriterTruthFrame.initial row n r
        (AllSlots.slotSaved hq row n r k (table k) saved)
        output (AllSlots.slotCount (q := q) (table k) count)) := by
  have hfull := full_bounded hq row n r k
    saved output count table hrow hquery
  have hreset := reset_bounded
    (DualDispatch.finalBank hq row n r k saved output count
      ((List.ofFn table).drop (k.val + 1)) (table k))
  have h := Circuit.seq_bounded_run
    (AllSlots.fullCircuit hq k) (AllSlots.resetCircuit (q := q))
    (SourceClauseRowWriterTruthFrame.initial row n r saved output count)
    (DualDispatch.finalBank hq row n r k saved output count
      ((List.ofFn table).drop (k.val + 1)) (table k))
    (TruthReset.cleared (DualDispatch.finalBank hq row n r k
      saved output count ((List.ofFn table).drop (k.val + 1)) (table k)))
    (fullCost hq row n r k saved output count (table k))
    (resetCost (DualDispatch.finalBank hq row n r k saved output count
      ((List.ofFn table).drop (k.val + 1)) (table k)))
    hfull hreset
  simpa only [AllSlots.slotCircuit, slotCost,
    TruthReset.cleared_finalBank, AllSlots.slotSaved,
    AllSlots.slotClauses, AllSlots.slotCount] using h

noncomputable def listCost {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (table : Fin (2 ^ q) → Bool) :
    List (Fin (2 ^ q)) → List Bool → List Bool → List Bool → ℕ
  | [], _, _, _ => 1
  | k :: ks, saved, output, count =>
      slotCost hq row n r k saved output count table +
        listCost hq row n r table ks
          (AllSlots.slotSaved hq row n r k (table k) saved)
          output (AllSlots.slotCount (q := q) (table k) count) + 1

theorem list_bounded {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (table : Fin (2 ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true)
    (ks : List (Fin (2 ^ q))) (saved output count : List Bool) :
    Circuit.BoundedRun (AllSlots.listCircuit hq ks)
      (listCost hq row n r table ks saved output count)
      (SourceClauseRowWriterTruthFrame.initial row n r saved output count)
      (SourceClauseRowWriterTruthFrame.initial row n r
        (AllSlots.listSaved hq row n r table ks saved) output
        (AllSlots.listCount table ks count)) := by
  induction ks generalizing saved count with
  | nil =>
      simpa only [AllSlots.listCircuit, listCost,
        AllSlots.listSaved, AllSlots.listCount] using
        Circuit.halt_bounded_run
          (SourceClauseRowWriterTruthFrame.initial row n r
            saved output count)
  | cons k ks ih =>
      have hhead := slot_bounded hq row n r k saved output count table
        hrow hquery
      have htail := ih
        (AllSlots.slotSaved hq row n r k (table k) saved)
        (AllSlots.slotCount (q := q) (table k) count)
      have hseq := Circuit.seq_bounded_run
        (AllSlots.slotCircuit hq k) (AllSlots.listCircuit hq ks)
        (SourceClauseRowWriterTruthFrame.initial row n r
          saved output count)
        (SourceClauseRowWriterTruthFrame.initial row n r
          (AllSlots.slotSaved hq row n r k (table k) saved)
          output (AllSlots.slotCount (q := q) (table k) count))
        (SourceClauseRowWriterTruthFrame.initial row n r
          (AllSlots.listSaved hq row n r table ks
            (AllSlots.slotSaved hq row n r k (table k) saved))
          output
          (AllSlots.listCount table ks
            (AllSlots.slotCount (q := q) (table k) count)))
        (slotCost hq row n r k saved output count table)
        (listCost hq row n r table ks
          (AllSlots.slotSaved hq row n r k (table k) saved)
          output (AllSlots.slotCount (q := q) (table k) count))
        hhead htail
      simpa only [AllSlots.listCircuit, listCost,
        AllSlots.listSaved, AllSlots.listCount] using hseq

noncomputable def allCost {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (table : Fin (2 ^ q) → Bool)
    (saved output count : List Bool) : ℕ :=
  listCost hq row n r table
    (List.ofFn (fun k : Fin (2 ^ q) => k)) saved output count

theorem all_bounded_actual {n m q : ℕ}
    (P : SourceBooleanEncoding.CSP n m 2 q) (hq : 0 < q)
    (r : Fin m) (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (table : Fin (2 ^ q) → Bool)
    (hrow : row (.inr 2) = true :: List.ofFn table)
    (hunary : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true)
    (hquery : ∀ j : Fin q,
      SourceClauseCallback.rowQuery row j = (P.query r j).val)
    (haccept : ∀ k : Fin (2 ^ q),
      table k = P.accept r (SourceClauseRowSchedule.tuple 2 q k))
    (saved output count : List Bool) :
    Circuit.BoundedRun (AllSlots.allCircuit hq)
      (allCost hq row n r.val table saved output count)
      (SourceClauseRowWriterTruthFrame.initial row n r.val saved output count)
      (SourceClauseRowWriterTruthFrame.initial row n r.val
        ((EncodedCNF.clauseFields
          (AllSlots.actualListClauses P hq r
            (List.ofFn (fun k : Fin (2 ^ q) => k)))).reverse ++ saved)
        output
        (AllSlots.listCount table
          (List.ofFn (fun k : Fin (2 ^ q) => k)) count)) := by
  have h := list_bounded hq row n r.val table hrow hunary
    (List.ofFn (fun k : Fin (2 ^ q) => k)) saved output count
  simpa only [allCost, AllSlots.allCircuit,
    AllSlots.listSaved_ordered,
    AllSlots.listClauses_actual P hq r row table _ hquery haccept] using h

end EthInapproximability.CurrentPaper.SourceClauseCallback.AllSlotsClock
