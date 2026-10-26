import EthInapproximability.CurrentPaper.SourceClauseGenericCallback

/-!
The accepting fixed-alphabet CSP tuple slot is retained in the indexed clause list.
Its first literal is a positive copy of query zero; its remaining `q` literals
are negative.  This file implements that exact `q+1`-gate chain with the
physical shared writer bank, for positive arity `q`.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseGenericTrue

open Turing BitMachineEncoding
open scoped Classical
open SourceClauseRowSchedule SourceClauseEncoding EncodedCNF
open SourceClauseCallback (Circuit exists_run_irrel rowQuery)
open SourceClauseGenericCallback (base width openingCircuit opening_circuit_run)

def instruction {a q : ℕ} (hq : 0 < q) (k : Fin (a ^ q))
    (p : Fin (q + 1)) : Fin q × Fin a × Bool :=
  SourceClauseRowInstruction.accepted hq k p

def gatePayload {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q)) (p : Fin (q + 1)) : List Bool :=
  clauseFields (orGate (base n r k + p.val)
    (SourceClauseRowInstruction.literal (rowQuery row) (instruction hq k p)))

def gateFold {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (ps : List (Fin (q + 1))) (saved : List Bool) : List Bool :=
  ps.foldl (fun acc p => (gatePayload hq row n r k p).reverse ++ acc) saved

theorem gateFold_eq_reverse {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (ps : List (Fin (q + 1))) (saved : List Bool) :
    gateFold hq row n r k ps saved =
      (ps.flatMap (gatePayload hq row n r k)).reverse ++ saved := by
  induction ps generalizing saved with
  | nil => simp [gateFold]
  | cons p ps ih =>
      rw [gateFold, List.foldl_cons]
      change gateFold hq row n r k ps
        ((gatePayload hq row n r k p).reverse ++ saved) = _
      rw [ih]
      simp [List.flatMap_cons, List.reverse_append, List.append_assoc]

private theorem zipIdx_ofFn {α : Type*} (xs : List α) :
    xs.zipIdx = List.ofFn (fun j : Fin xs.length => (xs.get j, j.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_zipIdx, List.getElem_ofFn,
      Nat.zero_add, List.get_eq_getElem]

private theorem clauseFields_append (xs ys : List Clause) :
    clauseFields (xs ++ ys) = clauseFields xs ++ clauseFields ys := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.cons_append, clauseFields, ih, List.append_assoc]

private theorem clauseFields_flatMap {α : Type*} (ds : List α)
    (f : α → List Clause) :
    clauseFields (ds.flatMap f) =
      ds.flatMap (fun d => clauseFields (f d)) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      simp only [List.flatMap_cons, clauseFields_append, ih]

theorem source_payload {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q)) (saved : List Bool) :
    ((encodeClause (unit (positive (base n r k + (q + 1))))).reverse ++
      gateFold hq row n r k
        (List.ofFn (fun p : Fin (q + 1) => p))
        ((encodeClause (unit (negative (base n r k)))).reverse ++ saved)) =
    (clauseFields (chain (base n r k)
      (tupleClause hq k (rowQuery row) true))).reverse ++ saved := by
  rw [gateFold_eq_reverse]
  rw [← SourceClauseRowInstruction.accepted_exact hq k (rowQuery row)]
  unfold chain
  simp only [clauseFields_append, clauseFields_flatMap,
    List.reverse_append, List.append_assoc]
  have hz := zipIdx_ofFn
    (List.ofFn (fun p : Fin (q + 1) =>
      SourceClauseRowInstruction.literal (rowQuery row)
        (instruction hq k p)))
  simp only [instruction] at hz
  simp only [List.length_ofFn] at hz
  rw [hz]
  simp [List.flatMap, List.map_ofFn, Function.comp_def,
    gatePayload, clauseFields, instruction]

theorem gate_address {a q : ℕ} (n r : ℕ) (k : Fin (a ^ q))
    (p : Fin (q + 1)) :
    SourceClauseRowSlotAddress.slot n r a q k.val * width a q +
      (n * a + p.val) = base n r k + p.val := by
  simp [SourceClauseRowSlotAddress.slot, base, width, slot]
  ring

theorem closing_address {a q : ℕ} (n r : ℕ) (k : Fin (a ^ q)) :
    SourceClauseRowUnitMachine.p n r a q k.val (width a q) (q + 1) =
      base n r k + (q + 1) := by
  simp [SourceClauseRowUnitMachine.p, SourceClauseRowUnitAddress.address,
    SourceClauseRowUnitAddress.slotValue, SourceClauseRowUnitAddress.offsetValue,
    SourceClauseRowSlotAddress.slot, base, width, slot]
  ring

theorem gate_saved {a q : ℕ} (hq : 0 < q)
    (p : Fin (q + 1))
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q)) (saved : List Bool) :
    SourceClauseRowWriterNormalize.gateSaved (instruction hq k p).1
      row n r a k.val (instruction hq k p).2.1.val p.val (width a q)
      (instruction hq k p).2.2 saved =
      (gatePayload hq row n r k p).reverse ++ saved := by
  rw [SourceClauseRowWriterNormalize.gateSaved]
  simp only [gate_address]
  simp [gatePayload, SourceClauseRowInstruction.literal, rowQuery, orGate,
    SourceClauseGatePrepare.firstClause,
    SourceClauseGatePrepare.secondClause,
    SourceClauseGatePrepare.thirdClause,
    clauseFields, List.reverse_append, List.append_assoc]

theorem closing_saved {a q : ℕ} (n r : ℕ) (k : Fin (a ^ q))
    (saved : List Bool) :
    SourceClauseRowWriterUnitClean.unitSaved q n r a k.val (width a q)
      (q + 1) true saved =
      ((encodeClause (unit (positive (base n r k + (q + 1))))).reverse ++ saved) := by
  simp [SourceClauseRowWriterUnitClean.unitSaved,
    SourceClauseUnitMachine.unitClause, closing_address,
    SourceClauseEncoding.positive]

noncomputable def gateCircuit {a q : ℕ} (hq : 0 < q)
    (k : Fin (a ^ q)) (p : Fin (q + 1)) :
    Circuit (SourceClauseRowWriterOperands.Stack q) :=
  Circuit.of
    (SourceClauseRowWriterGateClean.program (instruction hq k p).1
      a k.val (instruction hq k p).2.1.val p.val (width a q)
      (instruction hq k p).2.2)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              SourceClausePreservingBroadcast.Label.scan)))))
    ((((((((), none), ((), none)), ()), ((), none))),
      ((SourceClauseRowIndexedGate.slotControl, ((), none)),
        SourceClauseRowIndexedGate.gateControl)), ((), none))

noncomputable def closingCircuit {a q : ℕ} (k : Fin (a ^ q)) :
    Circuit (SourceClauseRowWriterOperands.Stack q) :=
  Circuit.of
    (SourceClauseRowWriterUnitClean.program (q := q)
      a k.val (width a q) (q + 1) true)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            SourceClausePreservingBroadcast.Label.scan))))
    ((SourceClauseRowWriterUnitReady.stageControl,
      SourceClauseRowUnitMachine.startControl), ((), none))

theorem gate_circuit_run {a q : ℕ} (hq : 0 < q)
    (p : Fin (q + 1))
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool)
    (hquery : row (.inl ((instruction hq k p).1, 1)) =
      List.replicate (row (.inl ((instruction hq k p).1, 1))).length true) :
    Circuit.Run (gateCircuit hq k p)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((gatePayload hq row n r k p).reverse ++ saved)
        output (true :: true :: true :: count)) := by
  classical
  obtain ⟨t, _, ht⟩ := SourceClauseRowWriterGateClean.run
    (instruction hq k p).1 row n r a k.val
    (instruction hq k p).2.1.val p.val (width a q)
    (instruction hq k p).2.2 saved output count hquery
  have hs := SourceClauseRowWriterNormalize.gate_blank (h := hquery)
  rw [hs, gate_saved] at ht
  exact exists_run_irrel _ _ _ _ _ ⟨t, ht⟩

theorem closing_circuit_run {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool) :
    Circuit.Run (closingCircuit k)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((encodeClause (unit (positive (base n r k + (q + 1))))).reverse ++ saved)
        output (true :: count)) := by
  classical
  obtain ⟨t, _, ht⟩ := SourceClauseRowWriterUnitClean.run
    row n r a k.val (width a q) (q + 1) true saved output count
  rw [SourceClauseRowWriterUnitClean.unit_blank, closing_saved] at ht
  exact exists_run_irrel _ _ _ _ _ ⟨t, ht⟩

noncomputable def gateListCircuit {a q : ℕ} (hq : 0 < q)
    (k : Fin (a ^ q)) :
    List (Fin (q + 1)) → Circuit (SourceClauseRowWriterOperands.Stack q)
  | [] => Circuit.halt
  | p :: ps => Circuit.seq (gateCircuit hq k p) (gateListCircuit hq k ps)

theorem gate_list_run {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (ps : List (Fin (q + 1))) (saved output count : List Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.Run (gateListCircuit hq k ps)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        (gateFold hq row n r k ps saved) output
        (List.replicate (3 * ps.length) true ++ count)) := by
  induction ps generalizing saved count with
  | nil =>
      simpa [gateListCircuit, gateFold] using
        Circuit.halt_run (SourceClauseRowWriterBlank.bank row n r
          saved output count)
  | cons p ps ih =>
      let payload := gatePayload hq row n r k p
      have hhead := gate_circuit_run hq p row n r k saved output count
        (hquery (instruction hq k p).1)
      have htail := ih (payload.reverse ++ saved)
        (true :: true :: true :: count)
      have hseq := Circuit.seq_run (gateCircuit hq k p)
        (gateListCircuit hq k ps)
        (SourceClauseRowWriterBlank.bank row n r saved output count)
        (SourceClauseRowWriterBlank.bank row n r
          (payload.reverse ++ saved) output
          (true :: true :: true :: count))
        (SourceClauseRowWriterBlank.bank row n r
          (gateFold hq row n r k ps (payload.reverse ++ saved)) output
          (List.replicate (3 * ps.length) true ++
            (true :: true :: true :: count))) hhead htail
      have hnum :
          List.replicate (3 * (p :: ps).length) true ++ count =
            List.replicate (3 * ps.length) true ++
              (true :: true :: true :: count) := by
        rw [List.length_cons, Nat.mul_add, Nat.mul_one,
          List.replicate_add, List.append_assoc]
        rfl
      simpa only [gateListCircuit, gateFold, List.foldl_cons,
        hnum, payload] using hseq

noncomputable def blockCircuit {a q : ℕ} (hq : 0 < q)
    (k : Fin (a ^ q)) :
    Circuit (SourceClauseRowWriterOperands.Stack q) :=
  Circuit.seq (openingCircuit k)
    (Circuit.seq (gateListCircuit hq k
      (List.ofFn (fun p : Fin (q + 1) => p))) (closingCircuit k))

theorem block_run {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.Run (blockCircuit hq k)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((encodeClause (unit (positive (base n r k + (q + 1))))).reverse ++
          gateFold hq row n r k (List.ofFn (fun p : Fin (q + 1) => p))
            ((encodeClause (unit (negative (base n r k)))).reverse ++ saved))
        output
        (true :: (List.replicate (3 * (q + 1)) true ++ (true :: count)))) := by
  have h₀ := opening_circuit_run row n r k saved output count
  have h₁ := gate_list_run hq row n r k
    (List.ofFn (fun p : Fin (q + 1) => p))
    ((encodeClause (unit (negative (base n r k)))).reverse ++ saved)
    output (true :: count) hquery
  have h₂ := closing_circuit_run row n r k
    (gateFold hq row n r k (List.ofFn (fun p : Fin (q + 1) => p))
      ((encodeClause (unit (negative (base n r k)))).reverse ++ saved))
    output (List.replicate (3 * (q + 1)) true ++ (true :: count))
  have h₁₂ := Circuit.seq_run
    (gateListCircuit hq k (List.ofFn (fun p : Fin (q + 1) => p)))
    (closingCircuit k) _ _ _ (by simpa using h₁) h₂
  exact Circuit.seq_run (openingCircuit k)
    (Circuit.seq (gateListCircuit hq k
      (List.ofFn (fun p : Fin (q + 1) => p))) (closingCircuit k))
    _ _ _ h₀ h₁₂

/-- One accepted tuple slot, preserving the source's tautological clause
and its label.  The writer executes opening unit, `q+1` gates, and closing
unit on the physical checked-row bank.  The output and row banks are unchanged;
the saved bytes and unary clause count are exact. -/
theorem block_source_run {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.Run (blockCircuit hq k)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((clauseFields (chain (base n r k)
          (tupleClause hq k (rowQuery row) true))).reverse ++ saved)
        output (List.replicate (3 * q + 5) true ++ count)) := by
  have h := block_run hq row n r k saved output count hquery
  have hp := source_payload hq row n r k saved
  have hc :
      true :: (List.replicate (3 * (q + 1)) true ++ (true :: count)) =
      List.replicate (3 * q + 5) true ++ count := by
    rw [show 3 * q + 5 = 1 + (3 * (q + 1) + 1) by omega,
      List.replicate_add]
    simp [List.replicate_add, List.append_assoc]
  simpa only [hp, hc, List.length_ofFn] using h

end EthInapproximability.CurrentPaper.SourceClauseGenericTrue
