import EthInapproximability.CurrentPaper.U4PostPhysical
import EthInapproximability.CurrentPaper.U4ApproxArm

/-!
# The main arm with the post stage discharged (lane owner:b-unit4-shell-3)

The predecessor's `Unit4ApproxArm.main_arm_from_approx` (frozen object, imported unchanged)
with its `hpost : ∀ M, PostPhysical M` premise discharged by `Unit4Post.Body.post_physical`.
Remaining named hypotheses: `hsource` (choice of `c`), H-B2 in the exact `HB2Physical` form, and
the paper's approximation premise at the fixed allowance. Correctness and halting of ONE fixed
machine; the time is existential here (B4-S6e is not done).
-/

namespace EthInapproximability.CurrentPaper.Unit4Post

open EncodedETHSource EncodedETHSourceComposition EffectiveIteration

variable {η : ℚ} (S : Sparsification η) (D : DinurReduction)
  (B : BOTReduction (booleanOccurrence D))

theorem main_arm_from_approx_post (c : ℕ)
    (hsource : 2 ^ 44 * (B.degreeBound : ℚ) / sourceGap D B ≤ c)
    (hB2 : PhysicalLevelRun.HB2Physical c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) B.degreeBound (sourceGap D B))
    (happrox : EncodedETHTail.PolynomialApproximation
      (FinalPadding.allowance (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
        (sourceSizeExponent S D B)))) :
    ∃ (Mmain : BitMachine.Machine) (T : ValidFormula → ℕ),
      ∀ f : ValidFormula, 1 ≤ f.val.variables →
        1 ≤ ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) f.val.variables →
        Mmain.OutputsWithin (EncodedCNF.encode f.val)
          [EncodedETHTail.satAnswer (EncodedCNF.encode f.val)] (T f) :=
  Unit4ApproxArm.main_arm_from_approx S D B c hsource hB2 (fun M => Body.post_physical M) happrox

/-- The explicit-time arm with the post stage FIXED to `Body.postMachine M` (the consumer of
B4-S6e): one fixed source machine; then for every `c`, estimator `M`, H-B2 machine `Mtab`, the
ONE machine below answers `satAnswer` within the explicit `armTime`. Only `hM`, `herr`
(estimator), `hsource`, `HB2Body` and the per-formula side conditions remain. -/
theorem main_arm_endpoint_post :
    ∃ (Msrc : BitMachine.Machine) (Csrc Esrc : ℕ),
      ∀ (c : ℕ) (M : BitMachine.Machine) (c' d' : ℕ) (answer : List Bool → ℤ),
        M.ComputesWithin (fun table => EncodedETHTail.encodeInteger (answer table))
          (fun n => c' * (n + 1) ^ d') →
        (∀ b : EncodedETHTail.Branch, |answer b.table - (b.cost : ℤ)| ≤
          (FinalPadding.allowance (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
            (sourceSizeExponent S D B)) b.table.length : ℤ)) →
        2 ^ 44 * (B.degreeBound : ℚ) / sourceGap D B ≤ c →
        ∀ (Mtab : BitMachine.Machine) (C₂ E₂ F₂ : ℕ),
        Unit4ItemAssembly.HB2Body c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
          B.degreeBound (sourceGap D B) Mtab C₂ E₂ F₂ →
        ∀ f : ValidFormula, 1 ≤ f.val.variables →
          1 ≤ ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
            (sourceSizeExponent S D B) f.val.variables →
          (BitMachineComposition.composition Msrc
            (BitMachineComposition.composition
              (SourceListMachineOuterFramed.machine
                (BitMachineComposition.composition Mtab (Body.postMachine M)))
              (SignedMidpointApproxActualMapper.satMachine M))).OutputsWithin
            (EncodedCNF.encode f.val) [EncodedETHTail.satAnswer (EncodedCNF.encode f.val)]
            (Unit4ItemAssembly.armTime S D B c M c' d'
              (BitMachineComposition.composition Mtab (Body.postMachine M))
              (Unit4ItemAssembly.itemBound Mtab C₂ E₂ F₂ (Body.Cp M.stackCount) 6
                (FinalPadding.tableSize (ETHTailGrowth.repetitions c
                  (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)) f.val.variables))
              (Csrc * ⌈(2 : ℝ) ^ ((η : ℝ) * f.val.variables)⌉₊ *
                ((EncodedCNF.encode f.val).length + 1) ^ Esrc) f) := by
  obtain ⟨Msrc, Csrc, Esrc, h⟩ := Unit4ItemAssembly.main_arm_endpoint S D B
  exact ⟨Msrc, Csrc, Esrc, fun c M c' d' answer hM herr hsource Mtab C₂ E₂ F₂ htab f hn hk =>
    h c M c' d' answer hM herr hsource Mtab C₂ E₂ F₂ htab (Body.postMachine M)
      (Body.Cp M.stackCount) 6 (Body.post_body M) f hn hk⟩

end EthInapproximability.CurrentPaper.Unit4Post
