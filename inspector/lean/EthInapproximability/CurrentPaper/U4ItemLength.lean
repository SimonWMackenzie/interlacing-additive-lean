import EthInapproximability.CurrentPaper.MainArm
import EthInapproximability.CurrentPaper.SourceGenericPolyEnvelope
import EthInapproximability.CurrentPaper.SourceOriginalVariableCapture

/-!
# The per-item length lemma (lane owner:b-unit4-shell-4, B4-S6e step 1)

Source: frozen v8 `06-eth.tex:204-243` (proof of `thm:main`) and the construction-time bound of
`thm:paper-effective-gap-interface` ("the source-size bound makes this uniform over `j`").

The H-B1 item word of a sparse branch `g` (`Unit4MainArm.itemWord D B n g`, the original-`n`
packet of the BOT graph bytes of `booleanFormula D g`) is literally the admitted
`SourceOriginalBOTListMapper.normalizedPacket B n (booleanFormula D g)` (definitional), i.e. the
output of the cited BOT/normalizer machine on the Boolean branch packet. Its length is bounded by
the admitted canonical-mapper envelope `SourceOriginalBOTCanonicalListMapper.outputEnvelope`
at the admitted Boolean word cap `BooleanListMapper.outEnv S D n`
(`BooleanListMapper.boolean_word_le`), a function of the ORIGINAL variable count `n` alone, and
that envelope is the admitted `PolyEnvelope.botOutput_env` (monotone, `≤ C (n+1)^E`). No branch
count enters.
-/

namespace EthInapproximability.CurrentPaper.Unit4Clock

open EncodedETHSource EncodedETHSourceComposition
open SourceGenericComposite

variable {η : ℚ} (S : Sparsification η) (D : DinurReduction)
  (B : BOTReduction (booleanOccurrence D))

/-- The item word is the admitted normalized packet of the Boolean branch (definitional). -/
theorem itemWord_eq_normalizedPacket (n : ℕ) (g : ValidFormula) :
    Unit4MainArm.itemWord D B n g =
      SourceOriginalBOTListMapper.normalizedPacket B n (booleanFormula D g) := rfl

/-- Per-item length envelope in the original `n` (admitted canonical BOT mapper envelope). -/
noncomputable def itemEnv (n : ℕ) : ℕ :=
  SourceOriginalBOTCanonicalListMapper.outputEnvelope B n (BooleanListMapper.outEnv S D n)

theorem itemEnv_env : PolyEnvelope.PolyEnv (itemEnv S D B) :=
  PolyEnvelope.botOutput_env S D B

/-- **Per-item length lemma (envelope form).** -/
theorem itemWord_length_le (f : ValidFormula) (hn : 1 ≤ f.val.variables)
    (g : ValidFormula) (hg : g ∈ S.branches f) :
    (Unit4MainArm.itemWord D B f.val.variables g).length ≤ itemEnv S D B f.val.variables := by
  have hw := BooleanListMapper.boolean_word_le S D f hn (booleanFormula D g)
    (List.mem_map.mpr ⟨g, hg, rfl⟩)
  have h := SourceOriginalBOTCanonicalListMapper.output_length_le B f.val.variables
    (BooleanListMapper.outEnv S D f.val.variables) (booleanFormula D g) hw
  rw [SourceOriginalBOTListMapper.itemOutput_eq B (booleanFormula D g) f.val.variables] at h
  exact h

/-- **Per-item length lemma (polynomial in `n` alone).** Constants fixed by `S D B` only,
before the formula. -/
theorem itemWord_length_poly :
    ∃ C E : ℕ, ∀ f : ValidFormula, 1 ≤ f.val.variables → ∀ g ∈ S.branches f,
      (Unit4MainArm.itemWord D B f.val.variables g).length ≤ C * (f.val.variables + 1) ^ E := by
  obtain ⟨-, C, E, hCE⟩ := itemEnv_env S D B
  exact ⟨C, E, fun f hn g hg => (itemWord_length_le S D B f hn g hg).trans (hCE _)⟩

/-- The same bound in the encoded input length `|encode f|` (via the admitted
`SourceOriginalVariableCapture.original_n_le_input`). -/
theorem itemWord_length_poly_input :
    ∃ C E : ℕ, ∀ f : ValidFormula, 1 ≤ f.val.variables → ∀ g ∈ S.branches f,
      (Unit4MainArm.itemWord D B f.val.variables g).length ≤
        C * ((EncodedCNF.encode f.val).length + 1) ^ E := by
  obtain ⟨C, E, h⟩ := itemWord_length_poly S D B
  refine ⟨C, E, fun f hn g hg => (h f hn g hg).trans ?_⟩
  have hle := SourceOriginalVariableCapture.original_n_le_input f.val
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) E)

end EthInapproximability.CurrentPaper.Unit4Clock
