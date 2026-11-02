import EthInapproximability.CurrentPaper.SourceClauseRowWriterNormalize
import EthInapproximability.CurrentPaper.SourceClauseRowWriterUnitClean
import EthInapproximability.CurrentPaper.SourceClauseRowInstruction

/-!
One forbidden Boolean-CSP tuple slot: exact arithmetic and serialization
interfaces for the physical opening/gate/closing writer calls.  The query
vertex is read from the checked row's unary word at each gate call.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseCallback

open Turing BitMachineEncoding
open scoped Classical
open SourceClauseRowSchedule
  SourceBooleanEncoding SourceClauseEncoding EncodedCNF

def base {q : ℕ} (n r : ℕ) (k : Fin (2 ^ q)) : ℕ :=
  n * 2 + SourceClauseRowSchedule.slot n 2 q r k *
    (SourceBooleanEncoding.width 2 q + 1)

def rowQuery {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool) : Fin q → ℕ :=
  fun j => (row (.inl (j, 1))).length

def width (q : ℕ) : ℕ := SourceBooleanEncoding.width 2 q + 1

theorem base_address {q : ℕ} (n r : ℕ) (k : Fin (2 ^ q)) :
    SourceClauseRowUnitMachine.p n r 2 q k.val (width q) 0 =
      base n r k := by
  simp [SourceClauseRowUnitMachine.p, SourceClauseRowUnitAddress.address,
    SourceClauseRowUnitAddress.slotValue, SourceClauseRowUnitAddress.offsetValue,
    SourceClauseRowSlotAddress.slot, base, width, slot]
  ring

theorem gate_address {q : ℕ} (n r : ℕ) (k : Fin (2 ^ q))
    (j : Fin q) :
    SourceClauseRowSlotAddress.slot n r 2 q k.val * width q +
      (n * 2 + j.val) = base n r k + j.val := by
  simp [SourceClauseRowSlotAddress.slot, base, width, slot]
  ring

theorem closing_address {q : ℕ} (n r : ℕ) (k : Fin (2 ^ q)) :
    SourceClauseRowUnitMachine.p n r 2 q k.val (width q) q =
      base n r k + q := by
  simp [SourceClauseRowUnitMachine.p, SourceClauseRowUnitAddress.address,
    SourceClauseRowUnitAddress.slotValue, SourceClauseRowUnitAddress.offsetValue,
    SourceClauseRowSlotAddress.slot, base, width, slot]
  ring

theorem opening_saved {q : ℕ} (n r : ℕ) (k : Fin (2 ^ q))
    (saved : List Bool) :
    SourceClauseRowWriterUnitClean.unitSaved q n r 2 k.val (width q) 0
      false saved =
      (encodeClause (unit (SourceClauseEncoding.negative (base n r k)))).reverse ++ saved := by
  simp [SourceClauseRowWriterUnitClean.unitSaved,
    SourceClauseUnitMachine.unitClause, base_address,
    SourceClauseEncoding.negative]

theorem closing_saved {q : ℕ} (n r : ℕ) (k : Fin (2 ^ q))
    (saved : List Bool) :
    SourceClauseRowWriterUnitClean.unitSaved q n r 2 k.val (width q) q
      true saved =
      (encodeClause (unit (SourceClauseEncoding.positive (base n r k + q)))).reverse ++ saved := by
  simp [SourceClauseRowWriterUnitClean.unitSaved,
    SourceClauseUnitMachine.unitClause, closing_address,
    SourceClauseEncoding.positive]

theorem gate_saved {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q)) (saved : List Bool) :
    SourceClauseRowWriterNormalize.gateSaved j row n r 2 k.val
      (tuple 2 q k j).val j.val (width q) false saved =
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
theorem opening_run {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool) :
    ∃ T ≤ SourceClauseRowWriterUnitReady.stageCost q n r 2 k.val (width q) 0 +
      SourceClauseRowUnitMachine.cost n r 2 q k.val (width q) 0 + 1 +
      SourceClauseRowWriterUnitClean.clearCost
        (SourceClauseRowWriterUnitReady.unitFinalBank
          row n r 2 k.val (width q) 0 false saved output count) + 1,
      ((advance (SourceClauseRowWriterUnitClean.program (q := q)
        2 k.val (width q) 0 false))^[T])
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
    row n r 2 k.val (width q) 0 false saved output count
  refine ⟨T, hT, ?_⟩
  rw [hr, SourceClauseRowWriterUnitClean.unit_blank, opening_saved]

/-- One physically staged and cleaned row-derived negative OR gate. -/
theorem gate_run {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool)
    (hquery : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    ∃ T ≤ SourceClauseRowWriterGateRun.stageCost j row n r 2 k.val
        (tuple 2 q k j).val j.val (width q) +
      SourceClauseRowIndexedGate.cost q n r 2 k.val
        (row (.inl (j, 1))).length (tuple 2 q k j).val
        j.val (width q) false + 1 +
      SourceClauseRowWriterGateClean.clearCost
        (SourceClauseRowWriterGateRun.result j row n r 2 k.val
          (tuple 2 q k j).val j.val (width q) false
          saved output count) + 1,
      ((advance (SourceClauseRowWriterGateClean.program j
        2 k.val (tuple 2 q k j).val j.val (width q) false))^[T])
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
    j row n r 2 k.val (tuple 2 q k j).val j.val (width q)
    false saved output count hquery
  refine ⟨T, hT, ?_⟩
  rw [hr, SourceClauseRowWriterNormalize.gate_blank (h := hquery), gate_saved]

theorem closing_run {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count : List Bool) :
    ∃ T ≤ SourceClauseRowWriterUnitReady.stageCost q n r 2 k.val (width q) q +
      SourceClauseRowUnitMachine.cost n r 2 q k.val (width q) q + 1 +
      SourceClauseRowWriterUnitClean.clearCost
        (SourceClauseRowWriterUnitReady.unitFinalBank
          row n r 2 k.val (width q) q true saved output count) + 1,
      ((advance (SourceClauseRowWriterUnitClean.program (q := q)
        2 k.val (width q) q true))^[T])
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
    row n r 2 k.val (width q) q true saved output count
  refine ⟨T, hT, ?_⟩
  rw [hr, SourceClauseRowWriterUnitClean.unit_blank, closing_saved]

/-- A finite-control physical subprogram with a distinguished initial
control.  Packaging the label type permits sequential composition even
though fixed gate indices have differently indexed finite label types. -/
structure Circuit (K : Type) where
  Label : Type
  Control : Type
  labelsFinite : Finite Label
  controlFinite : Finite Control
  program : Label → Turing.TM2.Stmt (fun _ : K => Bool) Label Control
  start : Label
  initial : Control

namespace Circuit

def of {K L V : Type} [Finite L] [Finite V]
    (P : L → Turing.TM2.Stmt (fun _ : K => Bool) L V)
    (l : L) (v : V) : Circuit K where
  Label := L
  Control := V
  labelsFinite := inferInstance
  controlFinite := inferInstance
  program := P
  start := l
  initial := v

def Run {K : Type} (A : Circuit K) (S T : K → List Bool) : Prop :=
  ∃ t, ((advance A.program)^[t])
    (⟨some A.start, A.initial, S⟩ :
      Turing.TM2.Cfg (fun _ : K => Bool) A.Label A.Control) =
      ⟨none, A.initial, T⟩

noncomputable def seq {K : Type} (A B : Circuit K) : Circuit K := by
  letI := A.labelsFinite
  letI := B.labelsFinite
  letI := A.controlFinite
  letI := B.controlFinite
  exact of (BitMachineRawSequence.program A.program B.program
      B.start A.initial B.initial)
    (BitMachineRawSequence.leftLabel A.start) (A.initial, B.initial)

theorem seq_run {K : Type} (A B : Circuit K)
    (S T U : K → List Bool)
    (hA : Run A S T) (hB : Run B T U) : Run (seq A B) S U := by
  obtain ⟨ta, ha⟩ := hA
  obtain ⟨tb, hb⟩ := hB
  obtain ⟨t, _, ht⟩ := BitMachineRawSequence.runs
    A.program B.program A.start B.start A.initial A.initial
    B.initial B.initial S T U ta tb ha hb
  exact ⟨t, ht⟩

def halt {K : Type} : Circuit K :=
  of (fun _ : Unit => Turing.TM2.Stmt.halt) () ()

theorem halt_run {K : Type} (S : K → List Bool) :
    Run (halt (K := K)) S S := by
  exact ⟨1, rfl⟩

end Circuit

theorem decidable_eq_irrel {K : Type} (d e : DecidableEq K) : d = e :=
  Subsingleton.elim d e

theorem exists_run_irrel {K L V : Type}
    (P : L → Turing.TM2.Stmt (fun _ : K => Bool) L V)
    (c u : Turing.TM2.Cfg (fun _ : K => Bool) L V)
    (d e : DecidableEq K)
    (h : ∃ t, ((@advance K L V d P)^[t]) c = u) :
    ∃ t, ((@advance K L V e P)^[t]) c = u := by
  cases decidable_eq_irrel d e
  exact h

noncomputable def openingCircuit {q : ℕ} (k : Fin (2 ^ q)) :
    Circuit (SourceClauseRowWriterOperands.Stack q) :=
  Circuit.of
    (SourceClauseRowWriterUnitClean.program (q := q)
      2 k.val (width q) 0 false)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            SourceClausePreservingBroadcast.Label.scan))))
    ((SourceClauseRowWriterUnitReady.stageControl,
      SourceClauseRowUnitMachine.startControl), ((), none))

noncomputable def closingCircuit {q : ℕ} (k : Fin (2 ^ q)) :
    Circuit (SourceClauseRowWriterOperands.Stack q) :=
  Circuit.of
    (SourceClauseRowWriterUnitClean.program (q := q)
      2 k.val (width q) q true)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            SourceClausePreservingBroadcast.Label.scan))))
    ((SourceClauseRowWriterUnitReady.stageControl,
      SourceClauseRowUnitMachine.startControl), ((), none))

noncomputable def gateCircuit {q : ℕ} (k : Fin (2 ^ q)) (j : Fin q) :
    Circuit (SourceClauseRowWriterOperands.Stack q) :=
  Circuit.of
    (SourceClauseRowWriterGateClean.program j
      2 k.val (tuple 2 q k j).val j.val (width q) false)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              SourceClausePreservingBroadcast.Label.scan)))))
    ((((((((), none), ((), none)), ()), ((), none))),
      ((SourceClauseRowIndexedGate.slotControl, ((), none)),
        SourceClauseRowIndexedGate.gateControl)), ((), none))

theorem opening_circuit_run {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
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

theorem closing_circuit_run {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
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

theorem gate_circuit_run {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
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

def gatePayload {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q)) (j : Fin q) : List Bool :=
  clauseFields
    (orGate (base n r k + j.val)
      (SourceClauseRowInstruction.literal (rowQuery row)
        (SourceClauseRowInstruction.rejected k j)))

def gateFold {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (js : List (Fin q)) (saved : List Bool) : List Bool :=
  js.foldl (fun acc j => (gatePayload row n r k j).reverse ++ acc) saved

theorem gateFold_eq_reverse {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
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

theorem gateFold_ofFn {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q)) (saved : List Bool) :
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

theorem source_payload {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q)) (saved : List Bool) :
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

noncomputable def gateListCircuit {q : ℕ} (k : Fin (2 ^ q)) :
    List (Fin q) → Circuit (SourceClauseRowWriterOperands.Stack q)
  | [] => Circuit.halt
  | j :: js => Circuit.seq (gateCircuit k j) (gateListCircuit k js)

theorem gate_list_run {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
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

noncomputable def blockCircuit {q : ℕ} (k : Fin (2 ^ q)) :
    Circuit (SourceClauseRowWriterOperands.Stack q) :=
  Circuit.seq (openingCircuit k)
    (Circuit.seq (gateListCircuit k (List.ofFn (fun j : Fin q => j)))
      (closingCircuit k))

theorem block_run {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
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

theorem block_source_run {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
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

end EthInapproximability.CurrentPaper.SourceClauseCallback
