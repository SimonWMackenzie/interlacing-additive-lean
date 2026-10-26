import EthInapproximability.CurrentPaper.U4ItemAssembly
import EthInapproximability.CurrentPaper.SignedMidpointApproxWitness

/-!
# The main arm from the approximation premise (lane owner:b-unit4-shell-2)

Source: frozen v8 `06-eth.tex:204-243`. Quantifier order of the proof of `thm:main`: the cited
records `S D B` and the constant `c` are fixed, the allowance
`α = FinalPadding.allowance (ETHTailGrowth.repetitions c (2^e) e)` is fixed BEFORE the
hypothetical estimator; the estimator machine `M` is then obtained from
`PolynomialApproximation α` by the admitted `approximation_supplies_callback`; the post stage is
instantiated for that `M`. Correctness only: the time is the explicit `armTime` (B4-S6e NOT done).
Remaining named hypotheses: H-B2 (`PhysicalLevelRun.HB2Physical`) and the post stage
(`∀ M, PostPhysical M`, B4-S3..S5, NOT built).
-/

namespace EthInapproximability.CurrentPaper.Unit4ApproxArm

open EncodedETHSource EncodedETHSourceComposition EffectiveIteration
open Unit4Bridges Unit4PhysBridges Unit4MainArm Unit4ItemAssembly

variable {η : ℚ} (S : Sparsification η) (D : DinurReduction)
  (B : BOTReduction (booleanOccurrence D))

/-- One fixed main arm, correct on every valid formula with `1 ≤ n` and `1 ≤ L n`, from
H-B2, the post-stage interface and the approximation premise at the fixed allowance. -/
theorem main_arm_from_approx (c : ℕ)
    (hsource : 2 ^ 44 * (B.degreeBound : ℚ) / sourceGap D B ≤ c)
    (hB2 : PhysicalLevelRun.HB2Physical c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) B.degreeBound (sourceGap D B))
    (hpost : ∀ M : BitMachine.Machine, PostPhysical M)
    (happrox : EncodedETHTail.PolynomialApproximation
      (FinalPadding.allowance (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
        (sourceSizeExponent S D B)))) :
    ∃ (Mmain : BitMachine.Machine) (T : ValidFormula → ℕ),
      ∀ f : ValidFormula, 1 ≤ f.val.variables →
        1 ≤ ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables →
        Mmain.OutputsWithin (EncodedCNF.encode f.val)
          [EncodedETHTail.satAnswer (EncodedCNF.encode f.val)] (T f) := by
  obtain ⟨Msrc, Csrc, Esrc, harm⟩ := main_arm_endpoint S D B
  obtain ⟨answer, M, c', d', hM, herr, -⟩ :=
    SignedMidpointApproxWitness.approximation_supplies_callback _ happrox
  obtain ⟨Mtab, C₂, E₂, F₂, htab⟩ := (hb2_iff _ _ _ _ _).mp hB2
  obtain ⟨Mpost, Cp, Ep, hpb⟩ := hpost M
  exact ⟨_, _, fun f hn hk =>
    harm c M c' d' answer hM herr hsource Mtab C₂ E₂ F₂ htab Mpost Cp Ep hpb f hn hk⟩

end EthInapproximability.CurrentPaper.Unit4ApproxArm
