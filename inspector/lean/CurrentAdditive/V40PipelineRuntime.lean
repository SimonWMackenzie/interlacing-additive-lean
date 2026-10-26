import CurrentAdditive.V40PipelineSeedBound
import CurrentAdditive.V40PipelineScalar

/-! A fixed physical prefix, the actual iteration driver, and a fixed
polynomial tail. The amplification is chosen before the tail machine. -/
namespace CurrentAdditive.V40PipelineRuntime
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
open EthInapproximability.CurrentPaper BitMachineComposition
open V40PipelineSeedBound

def pipeline (P M T : BitMachine.Machine) :=
  composition (composition P (WeightedIterationDriver.machine M)) T

def amplificationLog (P M : BitMachine.Machine) (inputC inputD cp dp c d : Nat) :=
  V40NativeIterationRuntime.amplificationLog M c d
    (seedCoefficient P inputC cp) (seedDegree inputD dp)
def amplification (P M : BitMachine.Machine) (inputC inputD cp dp c d : Nat) :=
  V40NativeIterationRuntime.amplification M c d
    (seedCoefficient P inputC cp) (seedDegree inputD dp)
def inputExponent (inputC inputD : Nat) := 2*V39UniformResource.seedExponent inputC inputD
def prefixExponent (cp dp : Nat) := 2*V39UniformResource.seedExponent cp dp
def driverExponent (P M : BitMachine.Machine) (inputC inputD cp dp c d : Nat) :=
  V40NativeIterationRuntime.exponentCoefficient M c d
    (seedCoefficient P inputC cp) (seedDegree inputD dp)
def exponentCoefficient (P M T : BitMachine.Machine)
    (inputC inputD cp dp c d ct dt : Nat) :=
  V40PipelineScalar.exponent P.pushBound T.pushBound ct dt
    (inputExponent inputC inputD) (prefixExponent cp dp) (driverExponent P M inputC inputD cp dp c d)

theorem amplification_ge (P M : BitMachine.Machine) (inputC inputD cp dp c d : Nat) :
    2^64 ≤ amplification P M inputC inputD cp dp c d :=
  V40NativeIterationRuntime.amplification_ge M c d _ _

theorem outputs (P M T : BitMachine.Machine) (inputC inputD cp dp c d ct dt N K : Nat)
    (x : List Bool) (words : Nat → List Bool) (Y : List Bool) (hN : 2 ≤ N)
    (hx : x.length ≤ inputC*(N+K+1)^inputD)
    (hP : P.OutputsWithin x (WeightedIterationDriver.input (words 0) K) (cp*(N+K+1)^dp))
    (hstep : ∀ j, M.OutputsWithin (words j) (words (j+1)) (c*((words j).length+1)^d))
    (hT : T.OutputsWithin (words K) Y (ct*((words K).length+1)^dt)) :
    (pipeline P M T).OutputsWithin x Y
      (N^(exponentCoefficient P M T inputC inputD cp dp c d ct dt*
        (amplification P M inputC inputD cp dp c d)^K)) ∧
    Y.length ≤ N^(exponentCoefficient P M T inputC inputD cp dp c d ct dt*
      (amplification P M inputC inputD cp dp c d)^K) := by
  let A := amplification P M inputC inputD cp dp c d
  let C := exponentCoefficient P M T inputC inputD cp dp c d ct dt
  let q := N^(A^K)
  have hA : 2 ≤ A := (by norm_num : 2 ≤ (2:Nat)^64).trans (amplification_ge P M inputC inputD cp dp c d)
  have hAp : 1 ≤ A^K := Nat.one_le_pow _ _ (by omega)
  have hq : 2 ≤ q := hN.trans (Nat.le_self_pow (by omega) N)
  have hqpow (v : Nat) : q^v=N^(v*A^K) := by
    dsimp only [q]
    rw [←pow_mul,Nat.mul_comm (A^K) v]
  have hs := seed_length P inputC inputD cp dp (N+K+1) K x (words 0) (by omega) hx hP
  have hd := V40NativeIterationRuntime.outputs M c d (seedCoefficient P inputC cp)
    (seedDegree inputD dp) N K words hN hs hstep
  change (WeightedIterationDriver.machine M).OutputsWithin
    (WeightedIterationDriver.input (words 0) K) (words K)
      (N^(driverExponent P M inputC inputD cp dp c d*A^K)) ∧
    (words K).length ≤ N^(driverExponent P M inputC inputD cp dp c d*A^K) at hd
  rw [←hqpow (driverExponent P M inputC inputD cp dp c d)] at hd
  have hxQ := hx.trans (V40IterationBaseChange.prefix_polynomial_bound inputC inputD A N K hA hN)
  change x.length ≤ N^(inputExponent inputC inputD*A^K) at hxQ
  rw [←hqpow (inputExponent inputC inputD)] at hxQ
  have hpQ := V40IterationBaseChange.prefix_polynomial_bound cp dp A N K hA hN
  change cp*(N+K+1)^dp ≤ N^(prefixExponent cp dp*A^K) at hpQ
  rw [←hqpow (prefixExponent cp dp)] at hpQ
  have hpword := BitMachine.output_length_bound P hP
  have htword := BitMachine.output_length_bound T hT
  have hb := V40PipelineScalar.bound q (inputExponent inputC inputD) (prefixExponent cp dp)
    (driverExponent P M inputC inputD cp dp c d) P.pushBound T.pushBound ct dt
    x.length (cp*(N+K+1)^dp) (WeightedIterationDriver.input (words 0) K).length
    (words K).length Y.length hq hxQ hpQ hpword hd.2 htword
  change _ ≤ q^C ∧ Y.length ≤ q^C at hb
  have hmid := composition_outputsWithin P (WeightedIterationDriver.machine M) hP hd.1
  have hj := composition_outputsWithin (composition P (WeightedIterationDriver.machine M)) T hmid hT
  have hout := BitMachine.outputsWithin_mono _ hj hb.1
  rw [hqpow C] at hout
  have hsize := hb.2
  rw [hqpow C] at hsize
  exact ⟨hout,hsize⟩

/-- The amplification is quantified before the tail, its coefficient and its
degree. Only the final exponent coefficient may change with that tail. -/
theorem uniform_outputs (P M : BitMachine.Machine) (inputC inputD cp dp c d : Nat) :
    ∃ A : Nat, 2^64 ≤ A ∧ (∃ a, A=2^a) ∧
      ∀ (T : BitMachine.Machine) (ct dt : Nat), ∃ C : Nat,
      ∀ N K (x : List Bool) (words : Nat → List Bool) (Y : List Bool), 2 ≤ N →
      x.length ≤ inputC*(N+K+1)^inputD →
      P.OutputsWithin x (WeightedIterationDriver.input (words 0) K) (cp*(N+K+1)^dp) →
      (∀ j, M.OutputsWithin (words j) (words (j+1)) (c*((words j).length+1)^d)) →
      T.OutputsWithin (words K) Y (ct*((words K).length+1)^dt) →
      (pipeline P M T).OutputsWithin x Y (N^(C*A^K)) ∧ Y.length ≤ N^(C*A^K) := by
  refine ⟨amplification P M inputC inputD cp dp c d,amplification_ge P M inputC inputD cp dp c d,
    ⟨amplificationLog P M inputC inputD cp dp c d,rfl⟩,?_⟩
  intro T ct dt
  refine ⟨exponentCoefficient P M T inputC inputD cp dp c d ct dt,?_⟩
  intro N K x words Y hN hx hP hstep hT
  exact outputs P M T inputC inputD cp dp c d ct dt N K x words Y hN hx hP hstep hT

#print axioms outputs
#print axioms uniform_outputs
end
end CurrentAdditive.V40PipelineRuntime
