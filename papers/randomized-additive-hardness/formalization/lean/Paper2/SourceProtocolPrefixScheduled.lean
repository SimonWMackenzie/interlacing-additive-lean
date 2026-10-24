import Paper2.SourceProtocolPrefixProtected
import Paper2.SourceProfiles
import Paper2.SourceDeletionParameters

/-!
# The actual source prefix under the public schedule

Frozen v12 `src:near-full`, the common-assignment paragraph. The independent
template profile and its exact cost are obtained from `src:profiles` at the
actual dyadic widths. The protected-family mass guards are derived from
the stated minimum defining eta. Thus the caller supplies only the original
base profile, displayed public admissibility checks, and a short protocol
on the actual retained source matrix. This is not the remaining T15
collision/capacity contradiction or an end-to-end hardness theorem.
-/

namespace Paper2.SourceProtocolPrefix

open Workspace.Types.Protocol Workspace.Types.CommComplexity
open SourceMatrix SourceLawBinding SourceProtocolPrefixTree SourceProfileParameters

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have := width_admissible L
  omega⟩

/-- The schedule's natural-power density is precisely the real-power
density accepted by rational separation with `b=10L`. -/
theorem schedule_density_eq (L : ℕ) :
    (2 : ℝ) ^ (-((10 * L : ℕ) : ℝ)) = x L := by
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  simp only [x, one_div, inv_pow]

theorem schedule_L_pos (L : ℕ)
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000) : 1 ≤ L := by
  by_contra hh
  have hL : L = 0 := by omega
  subst L
  have hw : (65536 : ℝ) ≤ width 0 := by exact_mod_cast width_admissible 0
  norm_num [rho] at hinner
  linarith

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y]

set_option maxRecDepth 2048 in
/-- T15's common assignment for the actual public construction, with all
template-profile, exact-template-cost and protected-mass side conditions
discharged. No already-controlled source protocol or source lower bound
is a premise. All labels refer to the original unpruned protocol. -/
theorem scheduled_common_assignment
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (L d : ℕ) (hd : 3 ≤ d) (hD : D F = d)
    (hp : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (order : SourceConstruction.Items (width L) V ≃
      Fin (Fintype.card (SourceConstruction.Items (width L) V)))
    (edge : E → Bool → V) (r : ℕ)
    (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) E * r)
    (ξ₀ : Tail (width L) Y) (delta zeta : ℝ) (hdelta : 0 < delta) (hzeta : 0 < zeta)
    (W : Set (RawRow (width L - 2) (outerWidth L) (width L) X
      (SourceConstruction.Items (width L) V)))
    (U : Set (TaggedColumn (width L - 2) (outerWidth L) (width L) Y))
    (hW : 1 - SourceDeletionParameters.eta (width L) delta zeta ≤
      (matrixColumnLaw μ (width L - 2) (outerWidth L) (width L)
        (SourceProfiles.width_ge_four L)).toFiniteLaw.prob (· ∈ W))
    (hU : 1 - SourceDeletionParameters.eta (width L) delta zeta ≤
      (matrixRowLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob (· ∈ U))
    (P : Protocol U W Bool)
    (hP : P.Computes (fun z w => SourceConstruction.matrix order edge
      (by have := SourceProfiles.width_ge_four L; omega) r hq F ξ₀ z.val w.val))
    (hcost : P.cost ≤ d + exponent L + outerExponent L + exponent L) :
    let Praw := Workspace.UpperBound.Protocol.transpose P
    CompleteAlicePrefix (exponent L) Praw ∧
    EveryPrefixBranchActive (@Finset.univ W (Fintype.ofFinite W)) (exponent L) Praw ∧
    (∀ j, (NPCC.Protocol.rowSubtreeAtRaw (exponent L) Praw j).cost ≤
      d + exponent L + outerExponent L) ∧
    ∃ dom : Fin (width L) ≃ Fin (width L), ∀ j,
      (998 / 1000 : ℝ) < (SourceLaws.templateLaw μ (width L - 2) (outerWidth L)).toFiniteLaw.prob
        (fun t => Sum.inl (dom j, t) ∈ W ∧
          rowCode W Praw (exponent L) (Sum.inl (dom j, t)) = j) ∧
      (∀ i, i ≠ dom j → (SourceLaws.templateLaw μ (width L - 2) (outerWidth L)).toFiniteLaw.prob
        (fun t => Sum.inl (i, t) ∈ W ∧ rowCode W Praw (exponent L) (Sum.inl (i, t)) = j) <
          2 * x L) ∧
      ∃ t, ∃ ht : Sum.inl (dom j, t) ∈ W,
        NPCC.Protocol.prefixCodeRaw (exponent L) Praw ⟨Sum.inl (dom j, t), ht⟩ = j := by
  have hs := SourceProfiles.width_ge_four L
  have hs3 : 3 ≤ width L := by omega
  have hprofiles := SourceProfiles.source_profiles μ ν F L d hd hD hp
    hinner houter hwide href (SourceConstruction.activity order edge hs3 r hq) ξ₀
  have hTD := hprofiles.2.2.1
  have hTP := hprofiles.2.2.2.1
  have hTDpow : D (T (q₁ := width L - 2) (q₂ := outerWidth L)
      (s := 2 ^ exponent L) F) = d + exponent L + outerExponent L := hTD
  have hmass := SourceDeletionParameters.protected_mass_guards
    (width L) hs delta zeta hdelta hzeta
  have hb : 1 ≤ 10 * L := by have := schedule_L_pos L hinner; omega
  have ha : 1 ≤ exponent L := by have := exponent_ge L; omega
  have hDT : 2 ≤ D (T (q₁ := width L - 2) (q₂ := outerWidth L) (s := width L) F) := by
    rw [hTD]
    omega
  have hsmall : (2 ^ exponent L : ℝ) *
      (2 : ℝ) ^ (-((10 * L : ℕ) : ℝ)) ≤ 1 / 10000 := by
    simpa only [schedule_density_eq, width, Nat.cast_pow, Nat.cast_ofNat] using href
  have hout := actual_common_assignment μ ν order edge hs r hq F ξ₀ (10 * L) hb ha
    hDT (by simpa only [schedule_density_eq, hTDpow] using hTP) hsmall W U
    (SourceDeletionParameters.eta (width L) delta zeta) hW hU
    (by simpa only [width, Nat.cast_pow, Nat.cast_ofNat] using hmass.1) hmass.2
    P hP (by simpa only [hTDpow] using hcost)
  simpa only [schedule_density_eq, hTDpow] using hout

end Paper2.SourceProtocolPrefix
