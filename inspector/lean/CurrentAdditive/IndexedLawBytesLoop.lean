import CurrentAdditive.IndexedLawBytesStep
import CurrentAdditive.IndexedLawBytesInitial
import CurrentAdditive.RatioUpdaterItemPolynomial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384
namespace CurrentAdditive.IndexedLawBytes
open EthInapproximability.CurrentPaper EntryClockPoly
open RatioUpdaterItemPolynomial

attribute [local irreducible] stepMachine

def loopMachine : BitMachine.Machine := WeightedIterationDriver.machine stepMachine

def loopBudget (M : BitMachine.Machine) (C d N : Nat) :=
  5*(2*(stateCap N+N)+3)+N*BitMachineIteration.roundBound M (stateCap N) (C*(stateCap N+1)^d)+2

theorem loopBudget_poly (M : BitMachine.Machine) (C d : Nat) :
    ∃ A E : Nat,∀N,loopBudget M C d N ≤ A*(N+1)^E := by
  have hp : PolyIn (fun N : Nat => N) (fun N => loopBudget M C d N) := by
    unfold loopBudget BitMachineIteration.roundBound stateCap
    solve_update_poly
  exact hp

theorem loopInput_length_le (xs : List (List Bool)) :
    (WeightedIterationDriver.input (state xs 0) xs.length).length  ≤
      2*(stateCap (inputSize xs)+inputSize xs)+2 := by
  have hs := state_length_le xs 0 (Nat.zero_le _)
  have hn := count_le xs
  simp only [WeightedIterationDriver.input,WeightedIterationLoader.packet,
    BitMachineBankCodec.encode_length,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    List.length_replicate]
  omega

theorem loopInput_contains_source (xs : List (List Bool)) :
    (SourceListEncoding.encode xs).length ≤ (WeightedIterationDriver.input (state xs 0) xs.length).length := by
  have hA := BitMachineBankCodec.word_length_le_encode
    (![SourceListEncoding.encode xs,[],fieldsAt xs 0] : Fin 3 → List Bool) 0
  have hB := BitMachineBankCodec.word_length_le_encode
    (![state xs 0,List.replicate xs.length true] : Fin 2 → List Bool) 0
  exact hA.trans hB

theorem loop_uniform : ∃ C E : Nat,∀xs : List (List Bool),
    loopMachine.OutputsWithin (WeightedIterationDriver.input (state xs 0) xs.length)
      (state xs xs.length) (C*((SourceListEncoding.encode xs).length+1)^E) := by
  obtain ⟨a,d,hstep⟩ := step_uniform
  obtain ⟨C,E,hcap⟩ := loopBudget_poly stepMachine a d
  refine ⟨C,E,?_⟩
  intro xs
  let N := inputSize xs
  let L := stateCap N
  let T := a*(L+1)^d
  have hs (j : Nat) (hj : j<xs.length) :
      stepMachine.OutputsWithin (state xs j) (state xs (j+1)) T := by
    apply BitMachine.outputsWithin_mono _ (hstep xs j hj)
    dsimp only [T,L,N]
    exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left (Nat.add_le_add_right
      (state_length_le xs j (Nat.le_of_lt hj)) 1) d)
  have hl (j : Nat) (hj : j<xs.length) : (state xs j).length ≤ L :=
    state_length_le xs j (Nat.le_of_lt hj)
  have h := WeightedIterationDriver.outputs_uniform stepMachine (state xs) xs.length L T hs hl
  apply BitMachine.outputsWithin_mono _ h
  have hi := loopInput_length_le xs
  have hn := count_le xs
  apply (show 5*((WeightedIterationDriver.input (state xs 0) xs.length).length+1)+
      xs.length*BitMachineIteration.roundBound stepMachine L T+2 ≤ loopBudget stepMachine a d N from ?_).trans (hcap N)
  unfold loopBudget
  change _ ≤ 5*(2*(L+N)+3)+N*BitMachineIteration.roundBound stepMachine L T+2
  have hm := Nat.mul_le_mul_right (BitMachineIteration.roundBound stepMachine L T) hn
  dsimp only [L,N] at hi hm ⊢
  omega

#print axioms loop_uniform
end CurrentAdditive.IndexedLawBytes
