import CurrentAdditive.D22GeneratedTerms
import CurrentAdditive.V40GeneratedTestEquivalence

/-! One fixed bit machine, compiled from fixed source constants before its
three unary inputs are supplied, executes the actual GeneratedTests. -/
namespace D22GeneratedTestMachine
open EthInapproximability.CurrentPaper
open CurrentAdditive V39GeneratedConstruction V38Schedule
open D22PolynomialExpression D22GeneratedTerms
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

def testInput (n m L : ℕ) : List Bool :=
  BitMachineBankCodec.encode ![List.replicate n true,List.replicate m true,List.replicate L true]
theorem input_eq (n m L : ℕ) : D22NatExpression.input n m L=testInput n m L := by
  unfold D22NatExpression.input testInput
  congr 1
  funext j
  fin_cases j <;> rfl

noncomputable def testMachine (p : SourceConstants) : BitMachine.Machine :=
  D22PredicateCompiler.machine (tests p)
noncomputable def clockCoefficient (p : SourceConstants) : ℕ :=
  D22PredicateCompiler.coefficient (tests p)
def clockDegree (p : SourceConstants) : ℕ := D22PredicateCompiler.degree (tests p)

theorem pass_eq (p : SourceConstants) (n m L : ℕ) (hn : 0<n) :
    D22PredicateCompiler.pass (tests p) n m L=
      decide (GeneratedTests p.deletion L m (sourceDeltaV p.gamma p.degree n m) (sourceZeta p.gamma)) := by
  have hiff := (pass_iff_literal p n m L).trans
    (V40GeneratedTestEquivalence.generated_iff_literal p n m L hn).symm
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using hiff

/-- Uniform actual execution and a fixed polynomial clock in the public
dyadic size and the physical n,m input lengths. No run-time premise occurs. -/
theorem test_outputs (p : SourceConstants) (n m L : ℕ) (hn : 0<n) :
    (testMachine p).OutputsWithin (testInput n m L)
      [decide (GeneratedTests p.deletion L m (sourceDeltaV p.gamma p.degree n m) (sourceZeta p.gamma))]
      (clockCoefficient p*(2^L+n+m+1)^clockDegree p) := by
  have h := D22PredicateCompiler.outputs_polynomial (tests p) n m L
  simpa only [testMachine,clockCoefficient,clockDegree,D22PolynomialExpression.base,
    input_eq,pass_eq p n m L hn] using h

theorem test_outputs_le_upper (p : SourceConstants) (n m L U : ℕ) (hn : 0<n) (hLU : L≤U) :
    (testMachine p).OutputsWithin (testInput n m L)
      [decide (GeneratedTests p.deletion L m (sourceDeltaV p.gamma p.degree n m) (sourceZeta p.gamma))]
      (clockCoefficient p*(2^U+n+m+1)^clockDegree p) := by
  apply BitMachine.outputsWithin_mono _ (test_outputs p n m L hn)
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have h := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hLU
  omega

#print axioms test_outputs
#print axioms test_outputs_le_upper
end
end D22GeneratedTestMachine
