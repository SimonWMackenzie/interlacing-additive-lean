import CurrentAdditive.V40PreparedSearchEngine
import CurrentAdditive.V40SearchInitialization
import CurrentAdditive.V22ParameterBatch

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 8192

namespace CurrentAdditive.V40RawSearchEngine

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open V39GeneratedConstruction V38Schedule
open V40PreparedSearchEngine

noncomputable section

variable (M : BitMachine.Machine)

def initialMachines : Fin 3 → BitMachine.Machine :=
  ![BankFieldProjection.machine (1 : Fin 3), BankFieldProjection.machine (2 : Fin 3),
    V40SearchInitialization.expressionMachine V40SearchInitialization.startExpr]

abbrev Stack (p : SourceConstants) := V22ParameterBatch.Stack initialMachines (V40PreparedSearchEngine.Stack M)
abbrev Bank (p : SourceConstants) := Stack M p → List Bool

def targets (p : SourceConstants) (i : Fin 3) : V40PreparedSearchEngine.Stack M :=
  V40PreparedSearchEngine.low M ⟨i.val, by omega⟩

def source (p : SourceConstants) : Stack M p := .inl (V40PreparedSearchEngine.low M 10)
def output (p : SourceConstants) : Stack M p := .inl (V40PreparedSearchEngine.low M 2)

def baseEmbedding (p : SourceConstants) : V40PreparedSearchEngine.Stack M ↪ Stack M p :=
  ⟨Sum.inl, Sum.inl_injective⟩

def batchProgram (p : SourceConstants) :=
  V22ParameterBatch.program initialMachines (V40PreparedSearchEngine.low M 10) (targets M p)

def searchProgram (p : SourceConstants) (l) :=
  BitMachineStackEmbedding.stackStmt (baseEmbedding M p) (V40PreparedSearchEngine.program M l)

def program (p : SourceConstants) := BitMachineRawSequence.program (batchProgram M p) (searchProgram M p)
  (V40PreparedSearchEngine.entry M) (V22ParameterBatch.control initialMachines) (V40PreparedSearchEngine.initial M)

def entry (p : SourceConstants) := BitMachineRawSequence.leftLabel
  (LA := V22ParameterBatch.Label initialMachines)
  (LB := V40PreparedSearchEngine.Label M) (Sum.inl (0 : Fin 4))

def initial (p : SourceConstants) :=
  (V22ParameterBatch.control initialMachines, V40PreparedSearchEngine.initial M)

def machine (p : SourceConstants) : BitMachine.Machine :=
  ofFinite (source M p) (output M p) (entry M p) (initial M p) (program M p)

def results (floor n m : Nat) : Fin 3 → List Bool :=
  ![List.replicate n true, List.replicate m true,
    List.replicate (V40DeterministicBoundedSearch.start floor n) true]

def times (floor n m : Nat) : Fin 3 → Nat :=
  ![10 * ((V40SearchInitialization.input floor n m).length + 1),
    10 * ((V40SearchInitialization.input floor n m).length + 1),
    V40SearchInitialization.expressionClock V40SearchInitialization.startExpr floor n m]

def batchCap (floor n m : Nat) : Nat :=
  V22ParameterBatch.clockPrefix (V40SearchInitialization.input floor n m)
    (results floor n m) (times floor n m) 3 + 1

def clock (p : SourceConstants) (C d : Nat) (floor n m : Nat) : Nat :=
  batchCap floor n m +
    (publicUpperLog p floor n - V40DeterministicBoundedSearch.start floor n + 1) *
      (V40PreparedSearchEngine.stepCap M C d n m (publicUpperLog p floor n) + 1) + 1

def rawBank (p : SourceConstants) (floor n m : Nat) : Bank M p :=
  fun k => if k = source M p then V40SearchInitialization.input floor n m else []

def ready (p : SourceConstants) (floor n m : Nat) : Bank M p :=
  V22ParameterBatch.banks initialMachines (targets M p) (rawBank M p floor n m)
    (V40SearchInitialization.input floor n m) (results floor n m) (times floor n m) 3

private theorem low_val (p : SourceConstants) (i : Fin 32) : (V40PreparedSearchEngine.low M i).val = i.val := rfl

private theorem targets_injective (p : SourceConstants) : Function.Injective (targets M p) := by
  intro i j h
  exact Fin.ext (congrArg (fun k : V40PreparedSearchEngine.Stack M => k.val) h)

theorem ready_target (p : SourceConstants) (floor n m : Nat) (i : Fin 3) :
    ready M p floor n m (.inl (targets M p i)) = results floor n m i := by
  simpa only [ready, i.isLt, if_pos] using V22ParameterBatch.banks_target initialMachines
    (targets M p) (targets_injective M p) (rawBank M p floor n m)
    (V40SearchInitialization.input floor n m) (results floor n m) (times floor n m) 3 le_rfl i

theorem ready_other (p : SourceConstants) (floor n m : Nat)
    (i : V40PreparedSearchEngine.Stack M) (hi : 3 ≤ i.val) :
    ready M p floor n m (.inl i) = rawBank M p floor n m (.inl i) := by
  apply V22ParameterBatch.banks_base_other
  intro j h
  have hv := congrArg (fun k : V40PreparedSearchEngine.Stack M => k.val) h
  change i.val = j.val at hv
  omega

theorem initializer_run (p : SourceConstants) (floor n m : Nat) :
    ∃ t ≤ batchCap floor n m,
      ((advance (batchProgram M p))^[t])
        (⟨some (Sum.inl (0 : Fin 4)), V22ParameterBatch.control initialMachines,
          rawBank M p floor n m⟩ : TM2.Cfg (fun _ : Stack M p => Bool) _ _) =
        ⟨none, V22ParameterBatch.control initialMachines, ready M p floor n m⟩ := by
  apply V22ParameterBatch.run initialMachines (V40PreparedSearchEngine.low M 10) (targets M p) (targets_injective M p)
  · intro i h
    have hv := congrArg (fun k : V40PreparedSearchEngine.Stack M => k.val) h
    change 10 = i.val at hv
    omega
  · simp [rawBank, source]
  · intro i
    have hne : (Sum.inl (targets M p i) : Stack M p) ≠ source M p := by
      intro h
      have hv := congrArg (fun k : V40PreparedSearchEngine.Stack M => k.val) (Sum.inl.inj h)
      change i.val = 10 at hv
      omega
    simp [rawBank, hne]
  · intro i w
    simp [rawBank, source]
  · intro i
    fin_cases i
    · simpa only [initialMachines, results, times, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, BankFieldProjection.result_encode,
        V40SearchInitialization.input] using BankFieldProjection.outputs (1 : Fin 3)
          (V40SearchInitialization.input floor n m)
    · simpa only [initialMachines, results, times, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, BankFieldProjection.result_encode,
        V40SearchInitialization.input] using BankFieldProjection.outputs (2 : Fin 3)
          (V40SearchInitialization.input floor n m)
    · exact V40SearchInitialization.start_outputs floor n m

theorem raw_outputs (p : SourceConstants) (C d floor n m : Nat)
    (hn : 0 < n) (hlow : n ≤ 2 * m) (hdegree : 2 * m ≤ p.degree * n)
    (hM : ∀ L, L ≤ publicUpperLog p floor n → M.OutputsWithin
      (V40ThreeFieldPacket.bytes (List.replicate n true) (List.replicate m true) (List.replicate L true))
      [V40DeterministicBoundedSearch.test p n m L]
      (V40PreparedSearchEngine.testCap C d n m (publicUpperLog p floor n))) :
    (machine M p).OutputsWithin (V40SearchInitialization.input floor n m)
      (List.replicate (publicLogFrom p floor n m hn hlow hdegree) true)
      (clock M p C d floor n m) := by
  let S := ready M p floor n m
  let B : V40PreparedSearchEngine.Bank M := fun k => S (.inl k)
  have ht (i : Fin 3) : B (targets M p i) = results floor n m i := ready_target M p floor n m i
  have hb (i : V40PreparedSearchEngine.Stack M) (hi : 3 ≤ i.val) (hne : i ≠ V40PreparedSearchEngine.low M 10) : B i = [] := by
    change ready M p floor n m (.inl i) = []
    rw [ready_other M p floor n m i hi]
    simp [rawBank, source, hne]
  have hblank : ∀ i : Fin 6, B ⟨i.val + 3, by omega⟩ = [] := by
    intro i
    apply hb _ (by change 3 ≤ i.val + 3; omega)
    intro h
    have hv := congrArg (fun k : V40PreparedSearchEngine.Stack M => k.val) h
    change i.val + 3 = 10 at hv
    omega
  have hscratch : B (V40PreparedSearchEngine.low M 31) = [] := hb _ (by change 3 ≤ 31; omega) (by
    intro h; have hv := congrArg (fun k : V40PreparedSearchEngine.Stack M => k.val) h
    change 31 = 10 at hv; omega)
  have hhigh : ∀ i, B ((V40PredicateBody.callSlots M).machine i) = [] := by
    intro i
    apply hb _ (by change 3 ≤ 32 + i.val; omega)
    intro h
    have hv := congrArg (fun k : V40PreparedSearchEngine.Stack M => k.val) h
    change 32 + i.val = 10 at hv
    omega
  have h2 : B (V40PreparedSearchEngine.low M 2) = List.replicate (V40DeterministicBoundedSearch.start floor n) true := ht 2
  have hflag : B (V40PreparedSearchEngine.low M 9) = [] := hb _ (by change 3 ≤ 9; omega) (by
    intro h; have hv := congrArg (fun k : V40PreparedSearchEngine.Stack M => k.val) h
    change 9 = 10 at hv; omega)
  have hstate : V40PreparedSearchEngine.state M B (V40DeterministicBoundedSearch.start floor n) = B := by
    unfold V40PreparedSearchEngine.state V40FirstPassingController.bank
    rw [← h2, Function.update_eq_self, ← hflag, Function.update_eq_self]
  obtain ⟨u, hu, hrun⟩ := V40PreparedSearchEngine.prepared_run M p C d B floor n m hn hlow hdegree (ht 0) (ht 1) hblank hscratch hhigh hM
  rw [hstate] at hrun
  have hemb := BitMachineStackRun.run (baseEmbedding M p) S (V40PreparedSearchEngine.program M)
    (⟨some (V40PreparedSearchEngine.entry M), V40PreparedSearchEngine.initial M, B⟩ :
      TM2.Cfg (fun _ : V40PreparedSearchEngine.Stack M => Bool) _ _) u
  rw [hrun] at hemb
  have hbank : BitMachineStackEmbedding.bank (baseEmbedding M p) S B = S :=
    BitMachineStackEmbedding.bank_restrict (baseEmbedding M p) S
  simp only [BitMachineStackEmbedding.stackCfg, hbank] at hemb
  obtain ⟨a, ha, hra⟩ := initializer_run M p floor n m
  obtain ⟨t, ht', hr⟩ := BitMachineRawSequence.runs (batchProgram M p) (searchProgram M p)
    (Sum.inl (0 : Fin 4)) (V40PreparedSearchEngine.entry M)
    (V22ParameterBatch.control initialMachines) (V22ParameterBatch.control initialMachines)
    (V40PreparedSearchEngine.initial M) (V40PredicateBody.initial M, some true)
    (rawBank M p floor n m) S _ a u hra hemb
  change ((advance (program M p))^[t])
    (⟨some (entry M p), initial M p, rawBank M p floor n m⟩ : TM2.Cfg (fun _ : Stack M p => Bool) _ _) =
      ⟨none, (V22ParameterBatch.control initialMachines, V40PredicateBody.initial M, some true),
        BitMachineStackEmbedding.bank (baseEmbedding M p) S
          (V40PreparedSearchEngine.state M B (publicLogFrom p floor n m hn hlow hdegree))⟩ at hr
  apply outputsWithin_of_raw_run (source M p) (output M p) (entry M p) (initial M p) (program M p)
    _ _ t _ (by change t ≤ batchCap floor n m +
    (publicUpperLog p floor n - V40DeterministicBoundedSearch.start floor n + 1) *
      (V40PreparedSearchEngine.stepCap M C d n m (publicUpperLog p floor n) + 1) + 1; omega)
  · change (((advance (program M p))^[t]) _).l = none
    change (((advance (program M p))^[t]) ⟨some (entry M p), initial M p, rawBank M p floor n m⟩).l = none
    rw [hr]
  · change (((advance (program M p))^[t]) ⟨some (entry M p), initial M p, rawBank M p floor n m⟩).stk (output M p) = _
    rw [hr]
    change BitMachineStackEmbedding.bank (baseEmbedding M p) S _
      (baseEmbedding M p (V40PreparedSearchEngine.low M 2)) = _
    rw [BitMachineStackEmbedding.bank_at]
    simp [output, baseEmbedding, V40PreparedSearchEngine.state, V40FirstPassingController.bank,
      V40PreparedSearchEngine.low, V40PredicateBody.low, Fin.ext_iff]

end
end CurrentAdditive.V40RawSearchEngine
