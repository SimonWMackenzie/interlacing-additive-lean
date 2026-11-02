import CurrentAdditive.V40NativeIterationResource
import CurrentAdditive.V40IterationBaseChange

namespace CurrentAdditive.V40NativeIterationRuntime
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
open EthInapproximability.CurrentPaper DeterministicIteration V40NativeIterationResource

def localAmplification (M : BitMachine.Machine) (c d seedC seedD : Nat) :=
  V39UniformResource.amplification (coefficient M c seedC) (degree d seedD)
def amplificationLog (M : BitMachine.Machine) (c d seedC seedD : Nat) :=
  V39UniformResource.amplificationLog (coefficient M c seedC) (degree d seedD)+65
def amplification (M : BitMachine.Machine) (c d seedC seedD : Nat) :=
  2^(amplificationLog M c d seedC seedD)
def exponentCoefficient (M : BitMachine.Machine) (c d seedC seedD : Nat) :=
  2*(initialExponent M c d seedC seedD+5)

theorem amplification_ge (M : BitMachine.Machine) (c d seedC seedD : Nat) :
    2^64≤amplification M c d seedC seedD := by
  unfold amplification amplificationLog
  exact Nat.pow_le_pow_right (by decide : 1≤(2:Nat)) (by omega)

theorem local_amplification_le (M : BitMachine.Machine) (c d seedC seedD : Nat) :
    2*localAmplification M c d seedC seedD≤amplification M c d seedC seedD := by
  unfold localAmplification amplification amplificationLog V39UniformResource.amplification
  rw [show 2*2^(V39UniformResource.amplificationLog (coefficient M c seedC) (degree d seedD))=
      2^(V39UniformResource.amplificationLog (coefficient M c seedC) (degree d seedD)+1) by
        rw [pow_succ];ring]
  exact Nat.pow_le_pow_right (by decide : 1≤(2:Nat)) (by omega)

theorem driver_bound_at_base (M : BitMachine.Machine) (c d seedC seedD B K : Nat)
    (words : Nat → List Bool) (hB : 2≤B) (hK : K≤B)
    (hseed : (words 0).length ≤ seedC*B^seedD)
    (hstep : ∀ j, M.OutputsWithin (words j) (words (j+1)) (nativeClock c d words j)) :
    WeightedIterationDriver.clock M words (nativeClock c d words) K≤
      B^((initialExponent M c d seedC seedD+5)*(localAmplification M c d seedC seedD)^K) ∧
    (words K).length≤B^((initialExponent M c d seedC seedD+5)*
      (localAmplification M c d seedC seedD)^K) := by
  let E := initialExponent M c d seedC seedD
  let A := localAmplification M c d seedC seedD
  let U := E*A^K
  let R := B^U
  have hA : 2≤A := V39UniformResource.amplification_ge_two _ _
  have hAp : 1≤A^K := Nat.one_le_pow _ _ (by omega)
  have hR : 1≤R := Nat.one_le_pow _ _ (by omega)
  obtain ⟨hsize,htime⟩ := resource M c d seedC seedD B K words hB hseed hstep
  have hseed' := seed_bound M c d seedC seedD B (by omega) words hseed
  have henv := V39UniformResource.seed_envelope_le_power (coefficient M c seedC)
    (degree d seedD) B (words 0).length hB hseed'
  have hE : V39UniformResource.seedExponent (coefficient M c seedC) (degree d seedD)≤U := by
    dsimp only [U,E,initialExponent]
    nlinarith
  have henvR : B+(words 0).length+2≤R := henv.trans
    (Nat.pow_le_pow_right (by omega) hE)
  have hinput : (WeightedIterationDriver.input (words 0) K).length=
      2*((words 0).length+K)+2 := by
    simp only [WeightedIterationDriver.input,WeightedIterationLoader.packet,
      BitMachineBankCodec.encode_length]
    simp [Fin.sum_univ_succ]
  have hinputR : (WeightedIterationDriver.input (words 0) K).length≤2*R := by
    rw [hinput]
    omega
  have hclock : WeightedIterationDriver.clock M words (nativeClock c d words) K≤18*R := by
    unfold WeightedIterationDriver.clock
    rw [cumulative_eq]
    change totalStepTime (construction M c d words) () K≤R at htime
    omega
  have h18 : 18≤B^5 := (by norm_num : 18≤(2:Nat)^5).trans (Nat.pow_le_pow_left hB _)
  have hexp : 5+U≤(E+5)*A^K := by dsimp only [U];nlinarith
  have hfinal : 18*R≤B^((E+5)*A^K) := by
    calc
      _ ≤ B^5*B^U := Nat.mul_le_mul_right R h18
      _ = B^(5+U) := by rw [pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hexp
  constructor
  · exact hclock.trans hfinal
  · have hs : (words K).length≤R := hsize
    exact hs.trans ((Nat.le_mul_of_pos_left R (by omega : 0<18)).trans hfinal)

theorem outputs (M : BitMachine.Machine) (c d seedC seedD N K : Nat)
    (words : Nat → List Bool) (hN : 2≤N)
    (hseed : (words 0).length ≤ seedC*(N+K+1)^seedD)
    (hstep : ∀ j, M.OutputsWithin (words j) (words (j+1)) (nativeClock c d words j)) :
    (WeightedIterationDriver.machine M).OutputsWithin
      (WeightedIterationDriver.input (words 0) K) (words K)
      (N^(exponentCoefficient M c d seedC seedD*(amplification M c d seedC seedD)^K)) ∧
    (words K).length≤N^(exponentCoefficient M c d seedC seedD*(amplification M c d seedC seedD)^K) := by
  obtain ⟨hclock,hsize⟩ := driver_bound_at_base M c d seedC seedD (N+K+1) K words
    (by omega) (by omega) hseed hstep
  have hbase := V40IterationBaseChange.remove_K_from_power N K
    (initialExponent M c d seedC seedD+5) (localAmplification M c d seedC seedD) hN
  have hlarge :
      (N+K+1)^((initialExponent M c d seedC seedD+5)*(localAmplification M c d seedC seedD)^K)≤
        N^(exponentCoefficient M c d seedC seedD*(amplification M c d seedC seedD)^K) :=
    hbase.trans (Nat.pow_le_pow_right (by omega)
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (local_amplification_le M c d seedC seedD) K)))
  constructor
  · apply BitMachine.outputsWithin_mono _
      (WeightedIterationDriver.outputs M words (nativeClock c d words) K (fun j _ => hstep j))
    exact hclock.trans hlarge
  · exact hsize.trans hlarge

theorem uniform_outputs (M : BitMachine.Machine) (c d seedC seedD : Nat) :
    ∃ a C : Nat, 64≤a ∧ ∀ N K (words : Nat → List Bool), 2≤N →
      (words 0).length ≤ seedC*(N+K+1)^seedD →
      (∀ j, M.OutputsWithin (words j) (words (j+1)) (c*((words j).length+1)^d)) →
      (WeightedIterationDriver.machine M).OutputsWithin
        (WeightedIterationDriver.input (words 0) K) (words K) (N^(C*(2^a)^K)) ∧
      (words K).length≤N^(C*(2^a)^K) := by
  refine ⟨amplificationLog M c d seedC seedD,exponentCoefficient M c d seedC seedD,?_,?_⟩
  · unfold amplificationLog;omega
  · intro N K words hN hseed hstep
    exact outputs M c d seedC seedD N K words hN hseed hstep

theorem uniform_outputs_power (M : BitMachine.Machine) (c d seedC seedD : Nat) :
    ∃ A C : Nat, 2^64≤A ∧ (∃ a, A=2^a) ∧
      ∀ N K (words : Nat → List Bool), 2≤N →
      (words 0).length ≤ seedC*(N+K+1)^seedD →
      (∀ j, M.OutputsWithin (words j) (words (j+1)) (c*((words j).length+1)^d)) →
      (WeightedIterationDriver.machine M).OutputsWithin
        (WeightedIterationDriver.input (words 0) K) (words K) (N^(C*A^K)) ∧
      (words K).length≤N^(C*A^K) := by
  refine ⟨amplification M c d seedC seedD,exponentCoefficient M c d seedC seedD,
    amplification_ge M c d seedC seedD,⟨amplificationLog M c d seedC seedD,rfl⟩,?_⟩
  intro N K words hN hseed hstep
  exact outputs M c d seedC seedD N K words hN hseed hstep

#print axioms outputs
#print axioms uniform_outputs_power
end
end CurrentAdditive.V40NativeIterationRuntime
