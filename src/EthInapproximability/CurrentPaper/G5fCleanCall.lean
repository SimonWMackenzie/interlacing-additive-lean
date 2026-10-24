import EthInapproximability.CurrentPaper.BitMachineIteration
import EthInapproximability.CurrentPaper.WeightedRawWordsCore
import EthInapproximability.CurrentPaper.ExactParameterMachineLog

/-!
# Segment 1, component: a CLEAN call of an admitted machine inside a larger bank
(private lane owner:b-g5-6)

The admitted unary machines (for example `ExactParameterMachineLog.machine`, `clog`) leave an
existential scratch bank, so a per-level call inside a loop cannot be reused as it stands. The admitted
`BitMachineIteration.program M` (fuel test, the call, the output transfer, a charged clear of EVERY local
stack, the reset) makes one call exact: `ready M input [true] ↦ finished M output`. Here that program is
lifted to a region `e` of ANY bank type `K` (the admitted `WeightedRawWords.region_run`), with the exit
bank stated cell by cell: the region's input cell holds `output`, every other region cell is blank, every
cell outside the region is unchanged. Instance: `clog_call_run` for the admitted `clog` machine.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.G5fCleanCall

open Turing BitMachineEncoding BitMachineStackEmbedding

variable {K : Type} [DecidableEq K] (M : BitMachine.Machine)

/-- The admitted budgeted-iteration program of `M`, lifted to the region `e`. -/
def callProgram (e : BitMachineIteration.Stack M ↪ K) :=
  fun l => stackStmt e (BitMachineIteration.program M l)

/-- The region contents expected at the start of one call. -/
def startRegion (input : List Bool) : BitMachineIteration.Stack M → List Bool :=
  (BitMachineIteration.ready M input [true]).stk

theorem startRegion_input (input : List Bool) :
    startRegion M input (.inl M.input) = input := by
  simp [startRegion, BitMachineIteration.ready, BitMachineIteration.adminCfg, BitMachine.Machine.init]

theorem startRegion_other (input : List Bool) (k : Fin M.stackCount) (hk : k ≠ M.input) :
    startRegion M input (.inl k) = [] := by
  simp [startRegion, BitMachineIteration.ready, BitMachineIteration.adminCfg, BitMachine.Machine.init,
    hk]

theorem startRegion_fuel (input : List Bool) : startRegion M input (.inr 0) = [true] := rfl
theorem startRegion_saved (input : List Bool) : startRegion M input (.inr 1) = [] := rfl

/-- **Clean call.** Exact exit bank. -/
theorem clean_call_run (e : BitMachineIteration.Stack M ↪ K) (S : K → List Bool)
    {input output : List Bool} {T : ℕ} (h : M.OutputsWithin input output T)
    (hS : ∀ k, S (e k) = startRegion M input k) :
    ∃ t ≤ BitMachineIteration.roundBound M input.length T + 1,
      ((advance (callProgram M e))^[t])
        (⟨some (.inr .testFuel), (M.initial, none), S⟩ :
          TM2.Cfg (fun _ : K => Bool) (BitMachineIteration.Label M) (BitMachineIteration.Control M)) =
        ⟨none, (M.initial, none), bank e S (BitMachineIteration.finished M output).stk⟩ := by
  obtain ⟨t, ht, hr⟩ := BitMachineIteration.iteration_run M
    (fun j => if j = 0 then input else output) [true] input.length T
    (by
      intro j hj
      simp only [List.length_cons, List.length_nil, zero_add, Nat.lt_one_iff] at hj
      subst hj
      simpa using h)
    (by
      intro j hj
      simp only [List.length_cons, List.length_nil, zero_add, Nat.lt_one_iff] at hj
      subst hj
      simp)
  simp only [List.length_cons, List.length_nil, zero_add, one_mul, if_pos, one_ne_zero,
    if_false] at ht hr
  have r := WeightedRawWords.region_run e (BitMachineIteration.program M)
    (BitMachineIteration.ready M input [true]) (BitMachineIteration.finished M output) t hr S
    (fun k => (hS k).symm)
  exact ⟨t, ht, r⟩

theorem finished_input (output : List Bool) :
    (BitMachineIteration.finished M output).stk (.inl M.input) = output := by
  simp [BitMachineIteration.finished, BitMachine.Machine.init]

theorem finished_other (output : List Bool) (k : BitMachineIteration.Stack M)
    (hk : k ≠ .inl M.input) : (BitMachineIteration.finished M output).stk k = [] := by
  rcases k with k | k
  · have hk' : k ≠ M.input := fun h => hk (by rw [h])
    simp [BitMachineIteration.finished, BitMachine.Machine.init, hk']
  · fin_cases k <;> rfl

/-- The exit bank, cell by cell. -/
theorem exit_bank (e : BitMachineIteration.Stack M ↪ K) (S : K → List Bool) (output : List Bool) :
    bank e S (BitMachineIteration.finished M output).stk (e (.inl M.input)) = output ∧
    (∀ k, k ≠ .inl M.input → bank e S (BitMachineIteration.finished M output).stk (e k) = []) ∧
    (∀ z, (¬ ∃ k, e k = z) → bank e S (BitMachineIteration.finished M output).stk z = S z) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bank_at]; exact finished_input M output
  · intro k hk; rw [bank_at]; exact finished_other M output k hk
  · intro z hz; exact bank_outside _ _ _ _ hz

/-- Instance: the admitted `clog` machine, one clean call. -/
theorem clog_call_run (e : BitMachineIteration.Stack ExactParameterMachineLog.machine ↪ K)
    (S : K → List Bool) (n : ℕ)
    (hS : ∀ k, S (e k) = startRegion ExactParameterMachineLog.machine (List.replicate n true) k) :
    ∃ t ≤ BitMachineIteration.roundBound ExactParameterMachineLog.machine n
        ((UnaryBinaryEncoding.coefficient + 6) * (n + 1) ^ 2) + 1,
      ((advance (callProgram ExactParameterMachineLog.machine e))^[t])
        (⟨some (.inr .testFuel), (ExactParameterMachineLog.machine.initial, none), S⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, (ExactParameterMachineLog.machine.initial, none),
          bank e S (BitMachineIteration.finished ExactParameterMachineLog.machine
            (List.replicate (Nat.clog 2 n) true)).stk⟩ := by
  have h := clean_call_run ExactParameterMachineLog.machine e S (ExactParameterMachineLog.outputs n) hS
  simpa only [List.length_replicate] using h

#print axioms startRegion_input
#print axioms startRegion_other
#print axioms clean_call_run
#print axioms finished_input
#print axioms finished_other
#print axioms exit_bank
#print axioms clog_call_run

end EthInapproximability.CurrentPaper.G5fCleanCall
