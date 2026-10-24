import EthInapproximability.CurrentPaper.SourceTrueClauseCallback

/-!
Explicit clocks for the physical clause-writer circuit combinator.  This
module does not alter either frozen tuple-slot callback.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseCallback.Circuit

open Turing BitMachineEncoding
open scoped Classical
open SourceClauseRowSchedule SourceClauseEncoding EncodedCNF

def BoundedRun {K : Type} (A : Circuit K) (bound : ℕ)
    (S T : K → List Bool) : Prop :=
  ∃ t ≤ bound, ((advance A.program)^[t])
    (⟨some A.start, A.initial, S⟩ :
      Turing.TM2.Cfg (fun _ : K => Bool) A.Label A.Control) =
      ⟨none, A.initial, T⟩

theorem bounded_run {K : Type} (A : Circuit K) (bound : ℕ)
    (S T : K → List Bool) (h : BoundedRun A bound S T) :
    Run A S T := by
  obtain ⟨t, _, ht⟩ := h
  exact ⟨t, ht⟩

theorem seq_bounded_run {K : Type} (A B : Circuit K)
    (S T U : K → List Bool) (a b : ℕ)
    (hA : BoundedRun A a S T) (hB : BoundedRun B b T U) :
    BoundedRun (seq A B) (a + b + 1) S U := by
  obtain ⟨ta, hta, ha⟩ := hA
  obtain ⟨tb, htb, hb⟩ := hB
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    A.program B.program A.start B.start A.initial A.initial
    B.initial B.initial S T U ta tb ha hb
  exact ⟨t, by omega, hr⟩

theorem halt_bounded_run {K : Type} (S : K → List Bool) :
    BoundedRun (halt (K := K)) 1 S S := by
  exact ⟨1, le_rfl, rfl⟩

end EthInapproximability.CurrentPaper.SourceClauseCallback.Circuit

namespace EthInapproximability.CurrentPaper.SourceClauseCircuitClock

open Turing BitMachineEncoding
open scoped Classical
open SourceClauseRowSchedule SourceClauseEncoding EncodedCNF
open SourceClauseCallback

theorem bounded_irrel {K L V : Type}
    (P : L → Turing.TM2.Stmt (fun _ : K => Bool) L V)
    (c u : Turing.TM2.Cfg (fun _ : K => Bool) L V)
    (d e : DecidableEq K) (B : ℕ)
    (h : ∃ t ≤ B, ((@advance K L V d P)^[t]) c = u) :
    ∃ t ≤ B, ((@advance K L V e P)^[t]) c = u := by
  cases SourceClauseCallback.decidable_eq_irrel d e
  exact h

noncomputable def unitCost {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q)) (ell : ℕ) (sign : Bool)
    (saved output count : List Bool) : ℕ :=
  SourceClauseRowWriterUnitReady.stageCost q n r 2 k.val (width q) ell +
  SourceClauseRowUnitMachine.cost n r 2 q k.val (width q) ell + 1 +
  SourceClauseRowWriterUnitClean.clearCost
    (SourceClauseRowWriterUnitReady.unitFinalBank row n r 2 k.val
      (width q) ell sign saved output count) + 1

noncomputable def gateCost {q : ℕ}
    (j : Fin q) (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q)) (s t : ℕ) (sign : Bool)
    (saved output count : List Bool) : ℕ :=
  SourceClauseRowWriterGateRun.stageCost j row n r 2 k.val s t (width q) +
  SourceClauseRowIndexedGate.cost q n r 2 k.val
    (row (.inl (j, 1))).length s t (width q) sign + 1 +
  SourceClauseRowWriterGateClean.clearCost
    (SourceClauseRowWriterGateRun.result j row n r 2 k.val
      s t (width q) sign saved output count) + 1

theorem opening_bounded {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool) :
    Circuit.BoundedRun (openingCircuit k)
      (unitCost row n r k 0 false saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((encodeClause (unit (negative (base n r k)))).reverse ++ saved)
        output (true :: count)) := by
  classical
  obtain ⟨t, ht, hr⟩ := opening_run row n r k saved output count
  exact bounded_irrel _ _ _ _ _ _ ⟨t, ht, hr⟩

theorem false_gate_bounded {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool)
    (hquery : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.BoundedRun (SourceClauseCallback.gateCircuit k j)
      (gateCost j row n r k (tuple 2 q k j).val j.val false
        saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((SourceClauseCallback.gatePayload row n r k j).reverse ++ saved)
        output (true :: true :: true :: count)) := by
  classical
  obtain ⟨t, ht, hr⟩ := gate_run j row n r k saved output count hquery
  exact bounded_irrel _ _ _ _ _ _ ⟨t, ht, hr⟩

theorem false_closing_bounded {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool) :
    Circuit.BoundedRun (SourceClauseCallback.closingCircuit k)
      (unitCost row n r k q true saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((encodeClause (unit (positive (base n r k + q)))).reverse ++ saved)
        output (true :: count)) := by
  classical
  obtain ⟨t, ht, hr⟩ := closing_run row n r k saved output count
  exact bounded_irrel _ _ _ _ _ _ ⟨t, ht, hr⟩

theorem true_gate_bounded {q : ℕ} (hq : 0 < q) (p : Fin (q + 1))
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool)
    (hquery : row (.inl ((SourceTrueClauseCallback.instruction hq k p).1, 1)) =
      List.replicate
        (row (.inl ((SourceTrueClauseCallback.instruction hq k p).1, 1))).length true) :
    Circuit.BoundedRun (SourceTrueClauseCallback.gateCircuit hq k p)
      (gateCost (SourceTrueClauseCallback.instruction hq k p).1
        row n r k (SourceTrueClauseCallback.instruction hq k p).2.1.val
        p.val (SourceTrueClauseCallback.instruction hq k p).2.2
        saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((SourceTrueClauseCallback.gatePayload hq row n r k p).reverse ++ saved)
        output (true :: true :: true :: count)) := by
  classical
  obtain ⟨t, ht, hr⟩ := SourceClauseRowWriterGateClean.run
    (SourceTrueClauseCallback.instruction hq k p).1 row n r 2 k.val
    (SourceTrueClauseCallback.instruction hq k p).2.1.val p.val (width q)
    (SourceTrueClauseCallback.instruction hq k p).2.2
    saved output count hquery
  rw [SourceClauseRowWriterNormalize.gate_blank (h := hquery),
    SourceTrueClauseCallback.gate_saved] at hr
  exact bounded_irrel _ _ _ _ _ _ ⟨t, ht, hr⟩

theorem true_closing_bounded {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool) :
    Circuit.BoundedRun (SourceTrueClauseCallback.closingCircuit k)
      (unitCost row n r k (q + 1) true saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((encodeClause (unit (positive (base n r k + (q + 1))))).reverse ++ saved)
        output (true :: count)) := by
  classical
  obtain ⟨t, ht, hr⟩ := SourceClauseRowWriterUnitClean.run
    row n r 2 k.val (width q) (q + 1) true saved output count
  rw [SourceClauseRowWriterUnitClean.unit_blank,
    SourceTrueClauseCallback.closing_saved] at hr
  exact bounded_irrel _ _ _ _ _ _ ⟨t, ht, hr⟩

noncomputable def listCircuit {K α : Type} (C : α → Circuit K) :
    List α → Circuit K
  | [] => Circuit.halt
  | a :: as => Circuit.seq (C a) (listCircuit C as)

def foldSaved {α : Type} (payload : α → List Bool)
    (as : List α) (saved : List Bool) : List Bool :=
  as.foldl (fun acc a => payload a ++ acc) saved

noncomputable def listCost {α : Type}
    (stepCost : α → List Bool → List Bool → List Bool → ℕ)
    (payload : α → List Bool) (as : List α)
    (saved output count : List Bool) : ℕ :=
  match as with
  | [] => 1
  | a :: as =>
      stepCost a saved output count +
      listCost stepCost payload as (payload a ++ saved)
        output (true :: true :: true :: count) + 1

theorem list_bounded_run {α : Type} {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (C : α → Circuit (SourceClauseRowWriterOperands.Stack q))
    (stepCost : α → List Bool → List Bool → List Bool → ℕ)
    (payload : α → List Bool) (as : List α)
    (saved output count : List Bool)
    (hstep : ∀ a saved output count,
      Circuit.BoundedRun (C a) (stepCost a saved output count)
        (SourceClauseRowWriterBlank.bank row n r saved output count)
        (SourceClauseRowWriterBlank.bank row n r
          (payload a ++ saved) output
          (true :: true :: true :: count))) :
    Circuit.BoundedRun (listCircuit C as)
      (listCost stepCost payload as saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        (foldSaved payload as saved) output
        (List.replicate (3 * as.length) true ++ count)) := by
  induction as generalizing saved count with
  | nil =>
      simpa [listCircuit, listCost, foldSaved] using
        Circuit.halt_bounded_run
          (SourceClauseRowWriterBlank.bank row n r saved output count)
  | cons a as ih =>
      have hhead := hstep a saved output count
      have htail := ih (payload a ++ saved)
        (true :: true :: true :: count)
      have hseq := Circuit.seq_bounded_run (C a) (listCircuit C as)
        (SourceClauseRowWriterBlank.bank row n r saved output count)
        (SourceClauseRowWriterBlank.bank row n r
          (payload a ++ saved) output (true :: true :: true :: count))
        (SourceClauseRowWriterBlank.bank row n r
          (foldSaved payload as (payload a ++ saved)) output
          (List.replicate (3 * as.length) true ++
            (true :: true :: true :: count)))
        (stepCost a saved output count)
        (listCost stepCost payload as (payload a ++ saved)
          output (true :: true :: true :: count))
        hhead htail
      have hnum :
          List.replicate (3 * (a :: as).length) true ++ count =
            List.replicate (3 * as.length) true ++
              (true :: true :: true :: count) := by
        rw [List.length_cons, Nat.mul_add, Nat.mul_one,
          List.replicate_add, List.append_assoc]
        rfl
      simpa only [listCircuit, listCost, foldSaved, List.foldl_cons,
        hnum] using hseq

theorem false_listCircuit_eq {q : ℕ} (k : Fin (2 ^ q))
    (js : List (Fin q)) :
    listCircuit (SourceClauseCallback.gateCircuit k) js =
      SourceClauseCallback.gateListCircuit k js := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [listCircuit, SourceClauseCallback.gateListCircuit, ih]

theorem true_listCircuit_eq {q : ℕ} (hq : 0 < q)
    (k : Fin (2 ^ q)) (ps : List (Fin (q + 1))) :
    listCircuit (SourceTrueClauseCallback.gateCircuit hq k) ps =
      SourceTrueClauseCallback.gateListCircuit hq k ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [listCircuit, SourceTrueClauseCallback.gateListCircuit, ih]

def falseGateBytes {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q)) (j : Fin q) : List Bool :=
  (SourceClauseCallback.gatePayload row n r k j).reverse

noncomputable def falseGateCost {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q)) (j : Fin q)
    (saved output count : List Bool) : ℕ :=
  gateCost j row n r k (tuple 2 q k j).val j.val false
    saved output count

def trueGateBytes {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q)) (p : Fin (q + 1)) : List Bool :=
  (SourceTrueClauseCallback.gatePayload hq row n r k p).reverse

noncomputable def trueGateCost {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q)) (p : Fin (q + 1))
    (saved output count : List Bool) : ℕ :=
  gateCost (SourceTrueClauseCallback.instruction hq k p).1 row n r k
    (SourceTrueClauseCallback.instruction hq k p).2.1.val p.val
    (SourceTrueClauseCallback.instruction hq k p).2.2
    saved output count

theorem false_gates_bounded {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (js : List (Fin q)) (saved output count : List Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.BoundedRun (SourceClauseCallback.gateListCircuit k js)
      (listCost (falseGateCost row n r k) (falseGateBytes row n r k)
        js saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        (foldSaved (falseGateBytes row n r k) js saved) output
        (List.replicate (3 * js.length) true ++ count)) := by
  rw [← false_listCircuit_eq]
  apply list_bounded_run
  intro j saved output count
  simpa [falseGateCost, falseGateBytes] using
    false_gate_bounded j row n r k saved output count (hquery j)

theorem true_gates_bounded {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (ps : List (Fin (q + 1))) (saved output count : List Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.BoundedRun (SourceTrueClauseCallback.gateListCircuit hq k ps)
      (listCost (trueGateCost hq row n r k)
        (trueGateBytes hq row n r k) ps saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        (foldSaved (trueGateBytes hq row n r k) ps saved) output
        (List.replicate (3 * ps.length) true ++ count)) := by
  rw [← true_listCircuit_eq]
  apply list_bounded_run
  intro p saved output count
  simpa [trueGateCost, trueGateBytes] using
    true_gate_bounded hq p row n r k saved output count
      (hquery (SourceTrueClauseCallback.instruction hq k p).1)

theorem false_fold_eq {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (js : List (Fin q)) (saved : List Bool) :
    foldSaved (falseGateBytes row n r k) js saved =
      SourceClauseCallback.gateFold row n r k js saved := rfl

theorem true_fold_eq {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (ps : List (Fin (q + 1))) (saved : List Bool) :
    foldSaved (trueGateBytes hq row n r k) ps saved =
      SourceTrueClauseCallback.gateFold hq row n r k ps saved := rfl

noncomputable def falseBlockCost {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool) : ℕ :=
  let s₀ := (encodeClause (unit (negative (base n r k)))).reverse ++ saved
  let c₀ := true :: count
  let js := List.ofFn (fun j : Fin q => j)
  let s₁ := foldSaved (falseGateBytes row n r k) js s₀
  let c₁ := List.replicate (3 * q) true ++ c₀
  unitCost row n r k 0 false saved output count +
    (listCost (falseGateCost row n r k) (falseGateBytes row n r k)
      js s₀ output c₀ +
      unitCost row n r k q true s₁ output c₁ + 1) + 1

theorem false_block_source_bounded {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.BoundedRun (SourceClauseCallback.blockCircuit k)
      (falseBlockCost row n r k saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((clauseFields (chain (base n r k)
          (tupleClause hq k (rowQuery row) false))).reverse ++ saved)
        output (List.replicate (3 * q + 2) true ++ count)) := by
  let s₀ := (encodeClause (unit (negative (base n r k)))).reverse ++ saved
  let c₀ := true :: count
  let js := List.ofFn (fun j : Fin q => j)
  let s₁ := foldSaved (falseGateBytes row n r k) js s₀
  let c₁ := List.replicate (3 * q) true ++ c₀
  have h₀ := opening_bounded row n r k saved output count
  have h₁ := false_gates_bounded row n r k js s₀ output c₀ hquery
  have h₂ := false_closing_bounded row n r k s₁ output c₁
  have h₁₂ := Circuit.seq_bounded_run
    (SourceClauseCallback.gateListCircuit k js)
    (SourceClauseCallback.closingCircuit k)
    (SourceClauseRowWriterBlank.bank row n r s₀ output c₀)
    (SourceClauseRowWriterBlank.bank row n r s₁ output c₁)
    (SourceClauseRowWriterBlank.bank row n r
      ((encodeClause (unit (positive (base n r k + q)))).reverse ++ s₁)
      output (true :: c₁))
    (listCost (falseGateCost row n r k) (falseGateBytes row n r k)
      js s₀ output c₀)
    (unitCost row n r k q true s₁ output c₁)
    (by simpa [js, c₁, s₁] using h₁) h₂
  have h := Circuit.seq_bounded_run
    (openingCircuit k)
    (Circuit.seq (SourceClauseCallback.gateListCircuit k js)
      (SourceClauseCallback.closingCircuit k))
    (SourceClauseRowWriterBlank.bank row n r saved output count)
    (SourceClauseRowWriterBlank.bank row n r s₀ output c₀)
    (SourceClauseRowWriterBlank.bank row n r
      ((encodeClause (unit (positive (base n r k + q)))).reverse ++ s₁)
      output (true :: c₁))
    (unitCost row n r k 0 false saved output count)
    (listCost (falseGateCost row n r k) (falseGateBytes row n r k)
      js s₀ output c₀ +
      unitCost row n r k q true s₁ output c₁ + 1)
    h₀ h₁₂
  have hp := SourceClauseCallback.source_payload hq row n r k saved
  rw [← false_fold_eq] at hp
  have hc : true :: c₁ =
      List.replicate (3 * q + 2) true ++ count := by
    dsimp [c₁, c₀]
    rw [show 3 * q + 2 = 1 + (3 * q + 1) by omega,
      List.replicate_add]
    simp [List.replicate_add, List.append_assoc]
  simpa only [SourceClauseCallback.blockCircuit,
    falseBlockCost, js, s₀, c₀, s₁, c₁, hp, hc] using h

noncomputable def trueBlockCost {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool) : ℕ :=
  let s₀ := (encodeClause (unit (negative (base n r k)))).reverse ++ saved
  let c₀ := true :: count
  let ps := List.ofFn (fun p : Fin (q + 1) => p)
  let s₁ := foldSaved (trueGateBytes hq row n r k) ps s₀
  let c₁ := List.replicate (3 * (q + 1)) true ++ c₀
  unitCost row n r k 0 false saved output count +
    (listCost (trueGateCost hq row n r k) (trueGateBytes hq row n r k)
      ps s₀ output c₀ +
      unitCost row n r k (q + 1) true s₁ output c₁ + 1) + 1

theorem true_block_source_bounded {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.BoundedRun (SourceTrueClauseCallback.blockCircuit hq k)
      (trueBlockCost hq row n r k saved output count)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((clauseFields (chain (base n r k)
          (tupleClause hq k (rowQuery row) true))).reverse ++ saved)
        output (List.replicate (3 * q + 5) true ++ count)) := by
  let s₀ := (encodeClause (unit (negative (base n r k)))).reverse ++ saved
  let c₀ := true :: count
  let ps := List.ofFn (fun p : Fin (q + 1) => p)
  let s₁ := foldSaved (trueGateBytes hq row n r k) ps s₀
  let c₁ := List.replicate (3 * (q + 1)) true ++ c₀
  have h₀ := opening_bounded row n r k saved output count
  have h₁ := true_gates_bounded hq row n r k ps s₀ output c₀ hquery
  have h₂ := true_closing_bounded row n r k s₁ output c₁
  have h₁₂ := Circuit.seq_bounded_run
    (SourceTrueClauseCallback.gateListCircuit hq k ps)
    (SourceTrueClauseCallback.closingCircuit k)
    (SourceClauseRowWriterBlank.bank row n r s₀ output c₀)
    (SourceClauseRowWriterBlank.bank row n r s₁ output c₁)
    (SourceClauseRowWriterBlank.bank row n r
      ((encodeClause (unit (positive (base n r k + (q + 1))))).reverse ++ s₁)
      output (true :: c₁))
    (listCost (trueGateCost hq row n r k) (trueGateBytes hq row n r k)
      ps s₀ output c₀)
    (unitCost row n r k (q + 1) true s₁ output c₁)
    (by simpa [ps, c₁, s₁] using h₁) h₂
  have h := Circuit.seq_bounded_run
    (openingCircuit k)
    (Circuit.seq (SourceTrueClauseCallback.gateListCircuit hq k ps)
      (SourceTrueClauseCallback.closingCircuit k))
    (SourceClauseRowWriterBlank.bank row n r saved output count)
    (SourceClauseRowWriterBlank.bank row n r s₀ output c₀)
    (SourceClauseRowWriterBlank.bank row n r
      ((encodeClause (unit (positive (base n r k + (q + 1))))).reverse ++ s₁)
      output (true :: c₁))
    (unitCost row n r k 0 false saved output count)
    (listCost (trueGateCost hq row n r k) (trueGateBytes hq row n r k)
      ps s₀ output c₀ +
      unitCost row n r k (q + 1) true s₁ output c₁ + 1)
    h₀ h₁₂
  have hp := SourceTrueClauseCallback.source_payload hq row n r k saved
  rw [← true_fold_eq] at hp
  have hc : true :: c₁ =
      List.replicate (3 * q + 5) true ++ count := by
    dsimp [c₁, c₀]
    rw [show 3 * q + 5 = 1 + (3 * (q + 1) + 1) by omega,
      List.replicate_add]
    simp [List.replicate_add, List.append_assoc]
  simpa only [SourceTrueClauseCallback.blockCircuit,
    trueBlockCost, ps, s₀, c₀, s₁, c₁, hp, hc] using h

end EthInapproximability.CurrentPaper.SourceClauseCircuitClock
