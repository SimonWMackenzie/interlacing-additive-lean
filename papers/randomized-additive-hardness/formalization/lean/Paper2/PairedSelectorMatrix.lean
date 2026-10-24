import Paper2.PairedSelectorMatrixProjection
import Paper2.PairedSelectorMatrixLaws
import Paper2.RationalRowEstimates

/-!
# Profile and capacity bounds on the actual paired-selector matrix

Frozen v12 Section 5, `res:paired`. Whole retained selector pairs are
projected jointly onto genuinely distinct tagged blocks. Their ambient
law is transported exactly, and their images retain at least their mass.
The classical rational-law estimates thus lower-bound the same original
matrix restriction, in its selector-row orientation.
-/

namespace Paper2.PairedSelectorMatrix

open Workspace.Types.CommComplexity SourceProjection

variable {W J : Type*} [Fintype W] [Fintype J] {q n : ℕ}

/-- A retained word support at one genuine tagged coordinate pays the
first-rung base-profile cost against the retained selector event. -/
theorem coordinate_lower
    (μ : PositiveRationalLaw W) (ν : PositiveRationalLaw J)
    (R : W → J → Bool) (H : ℕ) (x : ℝ)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (b : Block q) (A : Set (Selector q J)) (S : Set W) (C : Set (Column q W))
    (hS : ∀ w ∈ S, (b, w) ∈ C)
    (hrow : x ≤ μ.toFiniteLaw.prob (· ∈ S))
    (hcol : (3 / 5 : ℝ) ≤ (selectorLaw ν q).toFiniteLaw.prob (· ∈ A)) :
    H ≤ Compression.restrictionD (matrix R) A C := by
  have hc := hcol.trans (coordinate_mass ν b A)
  have hfirst := (restrictionProfile_three_levels _ _ _ _ _).mp hprofile |>.1
  have hl := hfirst S ((fun z => coordinate z b) '' A) hrow hc
  have hh : H ≤ Compression.restrictionD R S ((fun z => coordinate z b) '' A) := by
    exact_mod_cast hl
  exact hh.trans (coordinate_D_le R b A S C hS)

/-- The power-capacity estimate on arbitrary selected tagged blocks of
the original retained paired matrix. -/
theorem selected_capacity_power
    (μ : PositiveRationalLaw W) (ν : PositiveRationalLaw J)
    (R : W → J → Bool) (H l : ℕ) {x : ℝ}
    (hH : 2 ≤ H) (hx : 0 < x) (hl : 2 ≤ l)
    (hscale : (2 : ℝ) ^ l * x ≤ 1)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (e : Fin n → Block q) (he : Function.Injective e)
    (A : Set (Selector q J)) (S : Set (Fin n × W))
    (Q : Finset (Fin n)) (hQ : 2 ^ (l - 1) + 1 ≤ Q.card)
    (C : Set (Column q W)) (hS : ∀ a ∈ S, (e a.1, a.2) ∈ C)
    (hrow : ∀ i ∈ Q, (2 : ℝ) ^ l * x ≤ μ.toFiniteLaw.prob (fun w => (i, w) ∈ S))
    (hcol : (9 / 25 : ℝ) ≤ (selectorLaw ν q).toFiniteLaw.prob (· ∈ A)) :
    H + l ≤ Compression.restrictionD (matrix R) A C := by
  classical
  have hc := hcol.trans (projection_mass ν e he A)
  have hh := RationalRowEstimates.small_capacity_power μ ν R H l n
    hH hx hl hscale hprofile Q hQ S.toFinset (projection e '' A).toFinset
    (fun i hi => by simpa only [Set.mem_toFinset] using hrow i hi)
    (by simpa only [PositiveRationalLaw.toFiniteLaw_iid, Set.mem_toFinset] using hc)
  change H + l ≤ Compression.restrictionD (fullInterlace R n)
    (S.toFinset : Set _) ((projection e '' A).toFinset : Set _) at hh
  simp only [Set.coe_toFinset] at hh
  exact hh.trans (selected_interlace_D_le R e A S C hS)

/-- Two genuinely distinct tagged blocks pay the extra bit. In particular
the two tags at one coordinate are distinct and may be used at a parent. -/
theorem selected_capacity_two
    (μ : PositiveRationalLaw W) (ν : PositiveRationalLaw J)
    (R : W → J → Bool) (H : ℕ) {x : ℝ}
    (hH : 2 ≤ H) (hx : 0 < x) (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (e : Fin n → Block q) (he : Function.Injective e)
    (A : Set (Selector q J)) (S : Set (Fin n × W))
    (Q : Finset (Fin n)) (hQ : 2 ≤ Q.card)
    (C : Set (Column q W)) (hS : ∀ a ∈ S, (e a.1, a.2) ∈ C)
    (hrow : ∀ i ∈ Q, 2 * x ≤ μ.toFiniteLaw.prob (fun w => (i, w) ∈ S))
    (hcol : (9 / 25 : ℝ) ≤ (selectorLaw ν q).toFiniteLaw.prob (· ∈ A)) :
    H + 1 ≤ Compression.restrictionD (matrix R) A C := by
  classical
  have hc := hcol.trans (projection_mass ν e he A)
  have hh := RationalRowEstimates.small_capacity_two μ ν R H n
    hH hx hscale hprofile Q hQ S.toFinset (projection e '' A).toFinset
    (fun i hi => by simpa only [Set.mem_toFinset] using hrow i hi)
    (by simpa only [PositiveRationalLaw.toFiniteLaw_iid, Set.mem_toFinset] using hc)
  change H + 1 ≤ Compression.restrictionD (fullInterlace R n)
    (S.toFinset : Set _) ((projection e '' A).toFinset : Set _) at hh
  simp only [Set.coe_toFinset] at hh
  exact hh.trans (selected_interlace_D_le R e A S C hS)

end Paper2.PairedSelectorMatrix

#print axioms Paper2.PairedSelectorMatrix.coordinate_lower
#print axioms Paper2.PairedSelectorMatrix.selected_capacity_power
#print axioms Paper2.PairedSelectorMatrix.selected_capacity_two
