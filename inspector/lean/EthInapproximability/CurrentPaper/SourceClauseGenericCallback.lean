import EthInapproximability.CurrentPaper.SourceClauseCallback


/-!
# Fixed-alphabet physical tuple-clause callback

Locked v8 Section 6, thm:paper-sparse-gap-source. Generalises the actual
binary callback to a fixed alphabet a without altering its semantic source
or introducing an input-dependent instruction table. Reuses the existing
a-generic physical address, gate, reset and finite sequencing primitives.
This module alone does not prove the source converter's global runtime.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseGenericCallback

open Turing BitMachineEncoding
open SourceClauseCallback (Circuit exists_run_irrel rowQuery)
open scoped Classical
open SourceClauseRowSchedule
  SourceBooleanEncoding SourceClauseEncoding EncodedCNF

def base {a q : ℕ} (n r : ℕ) (k : Fin (a ^ q)) : ℕ :=
  n * a + SourceClauseRowSchedule.slot n a q r k *
    (SourceBooleanEncoding.width a q + 1)

def width (a q : ℕ) : ℕ := SourceBooleanEncoding.width a q + 1

theorem base_address {a q : ℕ} (n r : ℕ) (k : Fin (a ^ q)) :
    SourceClauseRowUnitMachine.p n r a q k.val (width a q) 0 =
      base n r k := by
  simp [SourceClauseRowUnitMachine.p, SourceClauseRowUnitAddress.address,
    SourceClauseRowUnitAddress.slotValue, SourceClauseRowUnitAddress.offsetValue,
    SourceClauseRowSlotAddress.slot, base, width, slot]
  ring

theorem gate_address {a q : ℕ} (n r : ℕ) (k : Fin (a ^ q))
    (j : Fin q) :
    SourceClauseRowSlotAddress.slot n r a q k.val * width a q +
      (n * a + j.val) = base n r k + j.val := by
  simp [SourceClauseRowSlotAddress.slot, base, width, slot]
  ring

theorem closing_address {a q : ℕ} (n r : ℕ) (k : Fin (a ^ q)) :
    SourceClauseRowUnitMachine.p n r a q k.val (width a q) q =
      base n r k + q := by
  simp [SourceClauseRowUnitMachine.p, SourceClauseRowUnitAddress.address,
    SourceClauseRowUnitAddress.slotValue, SourceClauseRowUnitAddress.offsetValue,
    SourceClauseRowSlotAddress.slot, base, width, slot]
  ring

theorem opening_saved {a q : ℕ} (n r : ℕ) (k : Fin (a ^ q))
    (saved : List Bool) :
    SourceClauseRowWriterUnitClean.unitSaved q n r a k.val (width a q) 0
      false saved =
      (encodeClause (unit (SourceClauseEncoding.negative (base n r k)))).reverse ++ saved := by
  simp [SourceClauseRowWriterUnitClean.unitSaved,
    SourceClauseUnitMachine.unitClause, base_address,
    SourceClauseEncoding.negative]

theorem closing_saved {a q : ℕ} (n r : ℕ) (k : Fin (a ^ q))
    (saved : List Bool) :
    SourceClauseRowWriterUnitClean.unitSaved q n r a k.val (width a q) q
      true saved =
      (encodeClause (unit (SourceClauseEncoding.positive (base n r k + q)))).reverse ++ saved := by
  simp [SourceClauseRowWriterUnitClean.unitSaved,
    SourceClauseUnitMachine.unitClause, closing_address,
    SourceClauseEncoding.positive]

theorem gate_saved {a q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q)) (saved : List Bool) :
    SourceClauseRowWriterNormalize.gateSaved j row n r a k.val
      (tuple a q k j).val j.val (width a q) false saved =
      (clauseFields
        (orGate (base n r k + j.val)
          (SourceClauseRowInstruction.literal (rowQuery row)
            (SourceClauseRowInstruction.rejected k j)))).reverse ++ saved := by
  rw [SourceClauseRowWriterNormalize.gateSaved]
  simp only [gate_address]
  simp [SourceClauseRowInstruction.literal,
    SourceClauseRowInstruction.rejected, rowQuery, orGate,
    SourceClauseGatePrepare.firstClause,
    SourceClauseGatePrepare.secondClause,
    SourceClauseGatePrepare.thirdClause,
    clauseFields, List.reverse_append, List.append_assoc]

/-- One physically staged and cleaned opening clause, with its actual
serialized payload and unary count.  No prepared operand or clause is an
input to the instruction table. -/
theorem opening_run {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool) :
    ∃ T ≤ SourceClauseRowWriterUnitReady.stageCost q n r a k.val (width a q) 0 +
      SourceClauseRowUnitMachine.cost n r a q k.val (width a q) 0 + 1 +
      SourceClauseRowWriterUnitClean.clearCost
        (SourceClauseRowWriterUnitReady.unitFinalBank
          row n r a k.val (width a q) 0 false saved output count) + 1,
      ((advance (SourceClauseRowWriterUnitClean.program (q := q)
        a k.val (width a q) 0 false))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                SourceClausePreservingBroadcast.Label.scan)))),
          ((SourceClauseRowWriterUnitReady.stageControl,
            SourceClauseRowUnitMachine.startControl), ((), none)),
          SourceClauseRowWriterBlank.bank row n r saved output count⟩) =
        ⟨none,
          ((SourceClauseRowWriterUnitReady.stageControl,
            SourceClauseRowUnitMachine.startControl), ((), none)),
          SourceClauseRowWriterBlank.bank row n r
            ((encodeClause (unit (SourceClauseEncoding.negative
              (base n r k)))).reverse ++ saved)
            output (true :: count)⟩ := by
  classical
  obtain ⟨T, hT, hr⟩ := SourceClauseRowWriterUnitClean.run
    row n r a k.val (width a q) 0 false saved output count
  refine ⟨T, hT, ?_⟩
  rw [hr, SourceClauseRowWriterUnitClean.unit_blank, opening_saved]

/-- One physically staged and cleaned row-derived negative OR gate. -/
theorem gate_run {a q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool)
    (hquery : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    ∃ T ≤ SourceClauseRowWriterGateRun.stageCost j row n r a k.val
        (tuple a q k j).val j.val (width a q) +
      SourceClauseRowIndexedGate.cost q n r a k.val
        (row (.inl (j, 1))).length (tuple a q k j).val
        j.val (width a q) false + 1 +
      SourceClauseRowWriterGateClean.clearCost
        (SourceClauseRowWriterGateRun.result j row n r a k.val
          (tuple a q k j).val j.val (width a q) false
          saved output count) + 1,
      ((advance (SourceClauseRowWriterGateClean.program j
        a k.val (tuple a q k j).val j.val (width a q) false))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  SourceClausePreservingBroadcast.Label.scan))))),
          ((((((((), none), ((), none)), ()), ((), none))),
            ((SourceClauseRowIndexedGate.slotControl, ((), none)),
              SourceClauseRowIndexedGate.gateControl)), ((), none)),
          SourceClauseRowWriterBlank.bank row n r saved output count⟩) =
        ⟨none,
          ((((((((), none), ((), none)), ()), ((), none))),
            ((SourceClauseRowIndexedGate.slotControl, ((), none)),
              SourceClauseRowIndexedGate.gateControl)), ((), none)),
          SourceClauseRowWriterBlank.bank row n r
            ((clauseFields
              (orGate (base n r k + j.val)
                (SourceClauseRowInstruction.literal (rowQuery row)
                  (SourceClauseRowInstruction.rejected k j)))).reverse ++ saved)
            output (true :: true :: true :: count)⟩ := by
  classical
  obtain ⟨T, hT, hr⟩ := SourceClauseRowWriterGateClean.run
    j row n r a k.val (tuple a q k j).val j.val (width a q)
    false saved output count hquery
  refine ⟨T, hT, ?_⟩
  rw [hr, SourceClauseRowWriterNormalize.gate_blank (h := hquery), gate_saved]

theorem closing_run {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool) :
    ∃ T ≤ SourceClauseRowWriterUnitReady.stageCost q n r a k.val (width a q) q +
      SourceClauseRowUnitMachine.cost n r a q k.val (width a q) q + 1 +
      SourceClauseRowWriterUnitClean.clearCost
        (SourceClauseRowWriterUnitReady.unitFinalBank
          row n r a k.val (width a q) q true saved output count) + 1,
      ((advance (SourceClauseRowWriterUnitClean.program (q := q)
        a k.val (width a q) q true))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                SourceClausePreservingBroadcast.Label.scan)))),
          ((SourceClauseRowWriterUnitReady.stageControl,
            SourceClauseRowUnitMachine.startControl), ((), none)),
          SourceClauseRowWriterBlank.bank row n r saved output count⟩) =
        ⟨none,
          ((SourceClauseRowWriterUnitReady.stageControl,
            SourceClauseRowUnitMachine.startControl), ((), none)),
          SourceClauseRowWriterBlank.bank row n r
            ((encodeClause (unit (SourceClauseEncoding.positive
              (base n r k + q)))).reverse ++ saved)
            output (true :: count)⟩ := by
  classical
  obtain ⟨T, hT, hr⟩ := SourceClauseRowWriterUnitClean.run
    row n r a k.val (width a q) q true saved output count
  refine ⟨T, hT, ?_⟩
  rw [hr, SourceClauseRowWriterUnitClean.unit_blank, closing_saved]

noncomputable def openingCircuit {a q : ℕ} (k : Fin (a ^ q)) :
    Circuit (SourceClauseRowWriterOperands.Stack q) :=
  Circuit.of
    (SourceClauseRowWriterUnitClean.program (q := q)
      a k.val (width a q) 0 false)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            SourceClausePreservingBroadcast.Label.scan))))
    ((SourceClauseRowWriterUnitReady.stageControl,
      SourceClauseRowUnitMachine.startControl), ((), none))

noncomputable def closingCircuit {a q : ℕ} (k : Fin (a ^ q)) :
    Circuit (SourceClauseRowWriterOperands.Stack q) :=
  Circuit.of
    (SourceClauseRowWriterUnitClean.program (q := q)
      a k.val (width a q) q true)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            SourceClausePreservingBroadcast.Label.scan))))
    ((SourceClauseRowWriterUnitReady.stageControl,
      SourceClauseRowUnitMachine.startControl), ((), none))

noncomputable def gateCircuit {a q : ℕ} (k : Fin (a ^ q)) (j : Fin q) :
    Circuit (SourceClauseRowWriterOperands.Stack q) :=
  Circuit.of
    (SourceClauseRowWriterGateClean.program j
      a k.val (tuple a q k j).val j.val (width a q) false)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              SourceClausePreservingBroadcast.Label.scan)))))
    ((((((((), none), ((), none)), ()), ((), none))),
      ((SourceClauseRowIndexedGate.slotControl, ((), none)),
        SourceClauseRowIndexedGate.gateControl)), ((), none))

theorem opening_circuit_run {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool) :
    Circuit.Run (openingCircuit k)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((encodeClause (unit (SourceClauseEncoding.negative
          (base n r k)))).reverse ++ saved)
        output (true :: count)) := by
  classical
  obtain ⟨t, _, ht⟩ := opening_run row n r k saved output count
  exact exists_run_irrel _ _ _ _ _ ⟨t, ht⟩

theorem closing_circuit_run {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool) :
    Circuit.Run (closingCircuit k)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((encodeClause (unit (SourceClauseEncoding.positive
          (base n r k + q)))).reverse ++ saved)
        output (true :: count)) := by
  classical
  obtain ⟨t, _, ht⟩ := closing_run row n r k saved output count
  exact exists_run_irrel _ _ _ _ _ ⟨t, ht⟩

theorem gate_circuit_run {a q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool)
    (hquery : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.Run (gateCircuit k j)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((clauseFields
          (orGate (base n r k + j.val)
            (SourceClauseRowInstruction.literal (rowQuery row)
              (SourceClauseRowInstruction.rejected k j)))).reverse ++ saved)
        output (true :: true :: true :: count)) := by
  classical
  obtain ⟨t, _, ht⟩ := gate_run j row n r k saved output count hquery
  exact exists_run_irrel _ _ _ _ _ ⟨t, ht⟩

def gatePayload {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q)) (j : Fin q) : List Bool :=
  clauseFields
    (orGate (base n r k + j.val)
      (SourceClauseRowInstruction.literal (rowQuery row)
        (SourceClauseRowInstruction.rejected k j)))

def gateFold {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (js : List (Fin q)) (saved : List Bool) : List Bool :=
  js.foldl (fun acc j => (gatePayload row n r k j).reverse ++ acc) saved

theorem gateFold_eq_reverse {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (js : List (Fin q)) (saved : List Bool) :
    gateFold row n r k js saved =
      (js.flatMap (gatePayload row n r k)).reverse ++ saved := by
  induction js generalizing saved with
  | nil => simp [gateFold]
  | cons j js ih =>
      rw [gateFold, List.foldl_cons]
      change gateFold row n r k js
        ((gatePayload row n r k j).reverse ++ saved) = _
      rw [ih]
      simp [List.flatMap_cons, List.reverse_append, List.append_assoc]

theorem gateFold_ofFn {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q)) (saved : List Bool) :
    gateFold row n r k (List.ofFn (fun j : Fin q => j)) saved =
      (List.ofFn (gatePayload row n r k)).reverse.flatMap List.reverse ++ saved := by
  rw [gateFold_eq_reverse, List.reverse_flatMap]
  simp [List.flatMap, List.map_ofFn, Function.comp_def]

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
    (encodeClause (unit (SourceClauseEncoding.positive
      (base n r k + q)))).reverse ++
      gateFold row n r k (List.ofFn (fun j : Fin q => j))
        ((encodeClause (unit (SourceClauseEncoding.negative
          (base n r k)))).reverse ++ saved) =
    (clauseFields (chain (base n r k)
      (tupleClause hq k (rowQuery row) false))).reverse ++ saved := by
  rw [gateFold_eq_reverse]
  rw [← SourceClauseRowInstruction.rejected_exact hq k (rowQuery row)]
  unfold chain
  simp only [clauseFields_append, clauseFields_flatMap,
    List.reverse_append, List.append_assoc]
  have hz := zipIdx_ofFn
    (List.ofFn (fun j : Fin q =>
      SourceClauseRowInstruction.literal (rowQuery row)
        (SourceClauseRowInstruction.rejected k j)))
  simp only [List.length_ofFn] at hz
  rw [hz]
  simp [List.flatMap, List.map_ofFn, Function.comp_def,
    gatePayload, clauseFields]

noncomputable def gateListCircuit {a q : ℕ} (k : Fin (a ^ q)) :
    List (Fin q) → Circuit (SourceClauseRowWriterOperands.Stack q)
  | [] => Circuit.halt
  | j :: js => Circuit.seq (gateCircuit k j) (gateListCircuit k js)

theorem gate_list_run {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (js : List (Fin q)) (saved output count : List Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.Run (gateListCircuit k js)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        (gateFold row n r k js saved) output
        (List.replicate (3 * js.length) true ++ count)) := by
  induction js generalizing saved count with
  | nil =>
      simpa [gateListCircuit, gateFold] using
        Circuit.halt_run (SourceClauseRowWriterBlank.bank row n r
          saved output count)
  | cons j js ih =>
      let payload := gatePayload row n r k j
      have hhead := gate_circuit_run j row n r k saved output count (hquery j)
      have htail := ih (payload.reverse ++ saved)
        (true :: true :: true :: count)
      have hseq := Circuit.seq_run (gateCircuit k j)
        (gateListCircuit k js)
        (SourceClauseRowWriterBlank.bank row n r saved output count)
        (SourceClauseRowWriterBlank.bank row n r
          (payload.reverse ++ saved) output
          (true :: true :: true :: count))
        (SourceClauseRowWriterBlank.bank row n r
          (gateFold row n r k js (payload.reverse ++ saved)) output
          (List.replicate (3 * js.length) true ++
            (true :: true :: true :: count))) hhead htail
      have hnum :
          List.replicate (3 * (j :: js).length) true ++ count =
            List.replicate (3 * js.length) true ++
              (true :: true :: true :: count) := by
        rw [List.length_cons, Nat.mul_add, Nat.mul_one,
          List.replicate_add, List.append_assoc]
        rfl
      simpa only [gateListCircuit, gateFold, List.foldl_cons,
        hnum, payload] using hseq

noncomputable def blockCircuit {a q : ℕ} (k : Fin (a ^ q)) :
    Circuit (SourceClauseRowWriterOperands.Stack q) :=
  Circuit.seq (openingCircuit k)
    (Circuit.seq (gateListCircuit k (List.ofFn (fun j : Fin q => j)))
      (closingCircuit k))

theorem block_run {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.Run (blockCircuit k)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((encodeClause (unit (SourceClauseEncoding.positive
          (base n r k + q)))).reverse ++
            gateFold row n r k (List.ofFn (fun j : Fin q => j))
              ((encodeClause (unit (SourceClauseEncoding.negative
                (base n r k)))).reverse ++ saved))
        output
        (true :: (List.replicate (3 * q) true ++ (true :: count)))) := by
  have h₀ := opening_circuit_run row n r k saved output count
  have h₁ := gate_list_run row n r k
    (List.ofFn (fun j : Fin q => j))
    ((encodeClause (unit (SourceClauseEncoding.negative
      (base n r k)))).reverse ++ saved)
    output (true :: count) hquery
  have h₂ := closing_circuit_run row n r k
    (gateFold row n r k (List.ofFn (fun j : Fin q => j))
      ((encodeClause (unit (SourceClauseEncoding.negative
        (base n r k)))).reverse ++ saved))
    output (List.replicate (3 * q) true ++ (true :: count))
  have h₁₂ := Circuit.seq_run
    (gateListCircuit k (List.ofFn (fun j : Fin q => j)))
    (closingCircuit k)
    (SourceClauseRowWriterBlank.bank row n r
      ((encodeClause (unit (SourceClauseEncoding.negative
        (base n r k)))).reverse ++ saved) output (true :: count))
    (SourceClauseRowWriterBlank.bank row n r
      (gateFold row n r k (List.ofFn (fun j : Fin q => j))
        ((encodeClause (unit (SourceClauseEncoding.negative
          (base n r k)))).reverse ++ saved))
      output (List.replicate (3 * q) true ++ (true :: count)))
    (SourceClauseRowWriterBlank.bank row n r
      ((encodeClause (unit (SourceClauseEncoding.positive
        (base n r k + q)))).reverse ++
          gateFold row n r k (List.ofFn (fun j : Fin q => j))
            ((encodeClause (unit (SourceClauseEncoding.negative
              (base n r k)))).reverse ++ saved))
      output (true :: (List.replicate (3 * q) true ++ (true :: count))))
    (by simpa using h₁) h₂
  exact Circuit.seq_run (openingCircuit k)
    (Circuit.seq (gateListCircuit k (List.ofFn (fun j : Fin q => j)))
      (closingCircuit k))
    _ _ _ h₀ h₁₂

theorem block_source_run {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count : List Bool)
    (hquery : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    Circuit.Run (blockCircuit k)
      (SourceClauseRowWriterBlank.bank row n r saved output count)
      (SourceClauseRowWriterBlank.bank row n r
        ((clauseFields (chain (base n r k)
          (tupleClause hq k (rowQuery row) false))).reverse ++ saved)
        output (List.replicate (3 * q + 2) true ++ count)) := by
  have h := block_run row n r k saved output count hquery
  have hp := source_payload hq row n r k saved
  have hc : true :: (List.replicate (3 * q) true ++ (true :: count)) =
      List.replicate (3 * q + 2) true ++ count := by
    rw [show 3 * q + 2 = 1 + (3 * q + 1) by omega,
      List.replicate_add]
    simp [List.replicate_add, List.append_assoc]
  simpa only [hp, hc, List.length_ofFn] using h

end EthInapproximability.CurrentPaper.SourceClauseGenericCallback


#print axioms EthInapproximability.CurrentPaper.SourceClauseGenericCallback.block_source_run
