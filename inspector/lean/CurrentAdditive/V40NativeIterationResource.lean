import CurrentAdditive.V39UniformResource
import CurrentAdditive.WeightedIterationDriver

/-! Actual one-step bit-machine runs supply the stored-word recurrence and
the full physical iteration-round clock. Numerical absorption is reused from
the existing uniform resource theorem. -/
namespace CurrentAdditive.V40NativeIterationResource
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
open EthInapproximability.CurrentPaper DeterministicIteration
open scoped BigOperators

def nativeClock (c d : Nat) (words : Nat → List Bool) (j : Nat) :=
  c*((words j).length+1)^d

def construction (M : BitMachine.Machine) (c d : Nat) (words : Nat → List Bool) :
    Construction Unit Nat where
  seed _ := 0
  step _ j := j+1
  cost _ := 0
  valid _ _ := True
  profile _ _ := True
  size j := (words j).length
  stepTime j := BitMachineIteration.roundBound M (words j).length (nativeClock c d words j)

theorem state_index (M : BitMachine.Machine) (c d : Nat) (words : Nat → List Bool) (j : Nat) :
    state (construction M c d words) () j=j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change state (construction M c d words) () j+1=j+1
      rw [ih]

def valid (M : BitMachine.Machine) (c d : Nat) (words : Nat → List Bool) :
    ValidContract (construction M c d words) () := ⟨True.intro,by intros;trivial⟩

def roundCoefficient (M : BitMachine.Machine) (c : Nat) :=
  c+(M.stackCount+2)*(1+c*M.pushBound)+M.stackCount+4
def coefficient (M : BitMachine.Machine) (c seedC : Nat) :=
  seedC+roundCoefficient M c+(1+c*M.pushBound)+10
def degree (d seedD : Nat) := d+seedD+2
def initialExponent (M : BitMachine.Machine) (c d seedC seedD : Nat) :=
  V39UniformResource.seedExponent (coefficient M c seedC) (degree d seedD)+1

theorem scalar_bounds (m p c d l x : Nat) (hx : 1≤x) (hl : l+1≤x) :
    l+c*(l+1)^d*p≤(1+c*p)*x^(d+1) ∧
    c*(l+1)^d+(m+2)*(l+c*(l+1)^d*p)+m+4≤
      (c+(m+2)*(1+c*p)+m+4)*x^(d+1) := by
  have hp : 1≤x^(d+1) := Nat.one_le_pow _ _ hx
  have hL : l≤x^(d+1) := (show l≤x by omega).trans (Nat.le_self_pow (by omega) x)
  have hd : (l+1)^d≤x^(d+1) :=
    (Nat.pow_le_pow_left hl d).trans (Nat.pow_le_pow_right hx (by omega))
  have ht := Nat.mul_le_mul_left c hd
  have htp := Nat.mul_le_mul_right p ht
  constructor
  · nlinarith
  · have hm := Nat.mul_le_mul_left (m+2)
      (show l+c*(l+1)^d*p≤(1+c*p)*x^(d+1) by nlinarith)
    nlinarith

theorem seed_bound (M : BitMachine.Machine) (c d seedC seedD B : Nat)
    (hB : 1≤B) (words : Nat → List Bool)
    (hs : (words 0).length ≤ seedC*B^seedD) :
    (words 0).length≤coefficient M c seedC*B^(degree d seedD) := by
  have hc : seedC≤coefficient M c seedC := by unfold coefficient;omega
  exact hs.trans (Nat.mul_le_mul hc (Nat.pow_le_pow_right hB (by unfold degree;omega)))

theorem size_clock_bounds (M : BitMachine.Machine) (c d seedC seedD B : Nat)
    (words : Nat → List Bool)
    (hstep : ∀ j, M.OutputsWithin (words j) (words (j+1)) (nativeClock c d words j)) :
    (∀ j, (construction M c d words).valid () j →
      (construction M c d words).size ((construction M c d words).step () j)≤
        coefficient M c seedC*(envelope (construction M c d words) B j)^(degree d seedD)) ∧
    (∀ j, (construction M c d words).valid () j →
      (construction M c d words).stepTime j≤
        coefficient M c seedC*(envelope (construction M c d words) B j)^(degree d seedD)) := by
  have hcS : 1+c*M.pushBound≤coefficient M c seedC := by unfold coefficient;omega
  have hcT : roundCoefficient M c≤coefficient M c seedC := by unfold coefficient;omega
  have hdeg : d+1≤degree d seedD := by unfold degree;omega
  constructor
  · intro j _
    have ho := BitMachine.output_length_bound M (hstep j)
    have hb := (scalar_bounds M.stackCount M.pushBound c d (words j).length
      (envelope (construction M c d words) B j) (by simp [envelope,construction])
      (by simp [envelope,construction] <;> omega)).1
    exact ho.trans (hb.trans (Nat.mul_le_mul hcS
      (Nat.pow_le_pow_right (by simp [envelope,construction]) hdeg)))
  · intro j _
    have hb := (scalar_bounds M.stackCount M.pushBound c d (words j).length
      (envelope (construction M c d words) B j) (by simp [envelope,construction])
      (by simp [envelope,construction] <;> omega)).2
    exact hb.trans (Nat.mul_le_mul hcT
      (Nat.pow_le_pow_right (by simp [envelope,construction]) hdeg))

theorem resource (M : BitMachine.Machine) (c d seedC seedD B K : Nat)
    (words : Nat → List Bool) (hB : 2≤B)
    (hs : (words 0).length ≤ seedC*B^seedD)
    (hstep : ∀ j, M.OutputsWithin (words j) (words (j+1)) (nativeClock c d words j)) :
    (words K).length≤B^(initialExponent M c d seedC seedD*
      (V39UniformResource.amplification (coefficient M c seedC) (degree d seedD))^K) ∧
    totalStepTime (construction M c d words) () K≤B^(initialExponent M c d seedC seedD*
      (V39UniformResource.amplification (coefficient M c seedC) (degree d seedD))^K) := by
  obtain ⟨hsize,hclock⟩ := size_clock_bounds M c d seedC seedD B words hstep
  have hr := V39UniformResource.uniform_iteration_resource (construction M c d words) () B
    (coefficient M c seedC) (degree d seedD) K hB (valid M c d words)
    (seed_bound M c d seedC seedD B (by omega) words hs) hsize hclock
  change (words (state (construction M c d words) () K)).length≤_ ∧
    totalStepTime (construction M c d words) () K≤_ at hr
  rw [state_index] at hr
  exact hr

theorem cumulative_eq (M : BitMachine.Machine) (c d : Nat) (words : Nat → List Bool) (K : Nat) :
    WeightedIterationClock.cumulative M words (nativeClock c d words) K=
      totalStepTime (construction M c d words) () K+1 := by
  unfold WeightedIterationClock.cumulative totalStepTime
  simp only [state_index]
  change (∑ j:Fin K, BitMachineIteration.roundBound M (words j.val).length (nativeClock c d words j.val))+1=
    (∑ j ∈ Finset.range K, BitMachineIteration.roundBound M (words j).length (nativeClock c d words j))+1
  exact congrArg (fun n:Nat => n+1)
    (Fin.sum_univ_eq_sum_range (fun j => BitMachineIteration.roundBound M (words j).length
      (nativeClock c d words j)) K)

#print axioms resource
#print axioms cumulative_eq
end
end CurrentAdditive.V40NativeIterationResource
