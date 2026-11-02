import CurrentAdditive.CodeDUpdateProductPairJoin
import CurrentAdditive.RationalCanonicalCallback
import EthInapproximability.CurrentPaper.BitMachineComposition

/-! Fixed physical product through polynomial-time closure, without unfolding its large control graph. -/

namespace CurrentAdditive.CodeDUpdateProductPolytime

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

theorem pair_clock_linear (x : List Bool) :
    CodeDUpdateProductPairJoin.clock x ≤ 50*(x.length+1) := by
  have hLam := BankFieldProjection.result_length (1 : Fin 3) x
  have hCoeff := BankFieldProjection.result_length (2 : Fin 3) x
  have hfLam := field_length (CodeDUpdateProductPairFields.lambdaWord x)
  have hfCoeff := field_length (CodeDUpdateProductPairFields.coefficientWord x)
  unfold CodeDUpdateProductPairJoin.clock
    CodeDUpdateProductPairFields.lambdaClock
    CodeDUpdateProductPairFields.coefficientClock
    CodeDUpdateProductPairFields.lambdaField
    CodeDUpdateProductPairFields.coefficientField
    CodeDUpdateProductPairFields.lambdaWord
    CodeDUpdateProductPairFields.coefficientWord at *
  omega

theorem pair_polytime :
    BitMachine.Polytime CodeDUpdateProductPairJoin.output := by
  refine ⟨CodeDUpdateProductPairJoin.machine, 50, 1, ?_⟩
  intro x
  exact BitMachine.outputsWithin_mono _
    (CodeDUpdateProductPairJoin.outputs x)
    (by simpa using pair_clock_linear x)

theorem product_polytime :
    BitMachine.Polytime
      (RationalCanonicalCallback.productResult ∘
        CodeDUpdateProductPairJoin.output) :=
  BitMachineComposition.polytime_comp pair_polytime
    RationalCanonicalCallback.product_polytime

noncomputable def machine : BitMachine.Machine := Classical.choose product_polytime

noncomputable def coefficient : Nat :=
  Classical.choose (Classical.choose_spec product_polytime)

noncomputable def exponent : Nat :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec product_polytime))

theorem outputs (x : List Bool) :
    machine.OutputsWithin x
      ((RationalCanonicalCallback.productResult ∘
        CodeDUpdateProductPairJoin.output) x)
      (coefficient * (x.length+1)^exponent) :=
  (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec product_polytime))) x

#print axioms pair_polytime
#print axioms product_polytime
#print axioms outputs

end CurrentAdditive.CodeDUpdateProductPolytime
