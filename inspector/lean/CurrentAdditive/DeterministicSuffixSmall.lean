import Paper2.RationalRowEstimates
import Paper2.SourceProjection
import CurrentAdditive.ProjectionMass

/-!
Private v27 deterministic-appendix probe, source `det:suffix` in
`appendices/H-deterministic-core.tex`, the b=0 and b=1 cases at H:452--455.
This uses the actual indexed retained columns and the concrete deterministic
protocol cost. No independence or source-construction conclusion is assumed;
the selected good marginal is an explicit total-variation premise.
-/

namespace CurrentAdditive.SuffixSmall

open Paper2
open Workspace.Types.CommComplexity

variable {X Z S : Type*} [Fintype X] [Fintype Z] [Fintype S]

/-- Selected coordinate rows and the actual image of retained indexed columns
form a protocol restriction, even when distinct indices decode alike. -/
theorem selected_projection_cost_le_indexed {q n : ℕ}
    (F : X → Z → Bool) (decode : S → Fin q → Z)
    (e : Fin n → Fin q) (R : Set (Fin q × X)) (K : Set S) :
    Paper2.Compression.restrictionD (Paper2.fullInterlace F n)
      {a | (e a.1, a.2) ∈ R}
      ((fun s j => decode s (e j)) '' K) ≤
    Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) R K := by
  apply Paper2.SourceProjection.restrictionD_projected_le
    (fun a s => F a.2 (decode s a.1)) (Paper2.fullInterlace F n)
    (fun a => (e a.1, a.2)) (fun s j => decode s (e j))
    R K {a | (e a.1, a.2) ∈ R}
  · intro a ha
    exact ha
  · intro a ha s hs
    rfl

/-- The `b=0` suffix case: conditional retained mass at least `1/2`
projects to ambient mass at least `9/25`, so two actual blocks force one
additional bit. The TV cap `7/50` is only the arithmetic needed here;
the manuscript's ε is much smaller. -/
theorem suffix_zero
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z) (e : Fin 2 → Fin q)
    (R : Set (Fin q × X)) (Y K : Set S)
    (d : ℕ) (x ε : ℝ)
    (hd : 2 ≤ d) (hx : 0 < x) (hscale : 2 * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ j : Fin 2, 2 * x ≤ μ.toFiniteLaw.prob
      (fun a => (e j, a) ∈ R))
    (hY : 0 < source.prob (· ∈ Y))
    (hK : K ⊆ Y)
    (hcond : (1 / 2 : ℝ) ≤ source.prob (· ∈ K) / source.prob (· ∈ Y))
    (hε : ε ≤ 7 / 50)
    (hgood : ∀ P : (Fin 2 → Z) → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (fun j => decode s (e j))) /
        source.prob (· ∈ Y) - (ν.toFiniteLaw.iid 2).prob P| ≤ ε) :
    d + 1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) R K := by
  classical
  let p : S → Fin 2 → Z := fun s j => decode s (e j)
  let SR : Set (Fin 2 × X) := {a | (e a.1, a.2) ∈ R}
  let C : Set (Fin 2 → Z) := p '' K
  have hmass : source.prob (· ∈ K) / source.prob (· ∈ Y) - ε ≤
      (ν.toFiniteLaw.iid 2).prob (· ∈ C) := by
    have h := ProjectionMass.ambient_image_mass_ge_conditional_mass_sub
      source (ν.toFiniteLaw.iid 2) p (· ∈ Y) (· ∈ K) ε hY
      (fun _ hs => hK hs) (by simpa [p] using hgood)
    simpa only [C, p, ProjectionMass.imageEvent, Set.mem_image] using h
  have hc : (9 / 25 : ℝ) ≤ (ν.toFiniteLaw.iid 2).prob (· ∈ C) := by
    linarith
  have hr : ∀ j ∈ (Finset.univ : Finset (Fin 2)),
      2 * x ≤ μ.toFiniteLaw.prob (fun a => (j, a) ∈ SR.toFinset) := by
    intro j _
    simpa [SR] using hrow j
  have hQ : 2 ≤ (Finset.univ : Finset (Fin 2)).card := by simp
  have hh := Paper2.RationalRowEstimates.small_capacity_two
    μ ν F d 2 hd hx hscale hprofile Finset.univ hQ
    SR.toFinset C.toFinset hr (by simpa using hc)
  have heq : D (NPCC.subgame (Paper2.fullInterlace F 2)
      SR.toFinset C.toFinset) =
      Paper2.Compression.restrictionD (Paper2.fullInterlace F 2) SR C := by
    have hSR : {a | a ∈ SR.toFinset} = SR := by ext a; simp
    have hC : {z | z ∈ C.toFinset} = C := by ext z; simp
    conv_rhs => rw [← hSR, ← hC]
    rfl
  rw [heq] at hh
  exact hh.trans (selected_projection_cost_le_indexed F decode e R K)

/-- The `b=1` suffix case: three selected blocks, conditional retained mass
at least `1/4`, and ambient projected mass at least `9/50`. The second rung
of the rational row ladder gives `d+2 ≤ 1+D`, hence the required `d+1`. -/
theorem suffix_one
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Z)
    (F : X → Z → Bool) (source : FiniteLaw S)
    {q : ℕ} (decode : S → Fin q → Z) (e : Fin 3 → Fin q)
    (R : Set (Fin q × X)) (Y K : Set S)
    (d : ℕ) (x ε : ℝ)
    (hd : 2 ≤ d) (hx : 0 < x) (hscale : 4 * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (d : ℤ))
    (hrow : ∀ j : Fin 3, 4 * x ≤ μ.toFiniteLaw.prob
      (fun a => (e j, a) ∈ R))
    (hY : 0 < source.prob (· ∈ Y))
    (hK : K ⊆ Y)
    (hcond : (1 / 4 : ℝ) ≤ source.prob (· ∈ K) / source.prob (· ∈ Y))
    (hε : ε ≤ 7 / 100)
    (hgood : ∀ P : (Fin 3 → Z) → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (fun j => decode s (e j))) /
        source.prob (· ∈ Y) - (ν.toFiniteLaw.iid 3).prob P| ≤ ε) :
    d + 1 ≤ Paper2.Compression.restrictionD
      (fun a s => F a.2 (decode s a.1)) R K := by
  classical
  let p : S → Fin 3 → Z := fun s j => decode s (e j)
  let SR : Set (Fin 3 × X) := {a | (e a.1, a.2) ∈ R}
  let C : Set (Fin 3 → Z) := p '' K
  have hmass : source.prob (· ∈ K) / source.prob (· ∈ Y) - ε ≤
      (ν.toFiniteLaw.iid 3).prob (· ∈ C) := by
    have h := ProjectionMass.ambient_image_mass_ge_conditional_mass_sub
      source (ν.toFiniteLaw.iid 3) p (· ∈ Y) (· ∈ K) ε hY
      (fun _ hs => hK hs) (by simpa [p] using hgood)
    simpa only [C, p, ProjectionMass.imageEvent, Set.mem_image] using h
  have hc : (9 / 50 : ℝ) ≤ (ν.toFiniteLaw.iid 3).prob (· ∈ C) := by
    linarith
  have hr : ∀ j : Fin 3,
      (2 : ℝ) ^ 2 * x ≤ μ.toFiniteLaw.prob (fun a => (j, a) ∈ SR.toFinset) := by
    intro j
    have hnum : (2 : ℝ) ^ 2 * x = 4 * x := by ring
    rw [hnum]
    simpa [SR] using hrow j
  have h₀ : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw x
      (3 / 5) (d : ℤ) := by
    simpa using hprofile (0 : Fin 3)
  have h₁ : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw x
      ((3 / 5) / 2) ((d : ℤ) - 1) := by
    simpa [show (3 / 5 : ℝ) * (1 / 2) ^ (1 : ℕ) = (3 / 5) / 2 by norm_num]
      using hprofile (1 : Fin 3)
  have h₂ : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw x
      ((3 / 5) / 4) ((d : ℤ) - 2) := by
    convert hprofile (2 : Fin 3) using 1
    norm_num
  have hscale' : (2 : ℝ) ^ 2 * x ≤ 1 := by norm_num; exact hscale
  have hcol : ((3 / 5 : ℝ) ^ 2 / (2 : ℝ) ^ (1 : ℕ)) ≤
      (ν.toFiniteLaw.iid 3).prob (· ∈ C.toFinset) := by
    convert hc using 1 <;> norm_num
  have hh := Paper2.RationalRowEstimates.row_ladder μ ν F d 2 x (3 / 5)
    hd (by omega) hx (by norm_num) (by norm_num) hscale'
    h₀ h₁ h₂ (1 : Fin 3) SR.toFinset C.toFinset hr hcol
  have heq : D (NPCC.subgame (Paper2.fullInterlace F 3)
      SR.toFinset C.toFinset) =
      Paper2.Compression.restrictionD (Paper2.fullInterlace F 3) SR C := by
    have hSR : {a | a ∈ SR.toFinset} = SR := by ext a; simp
    have hC : {z | z ∈ C.toFinset} = C := by ext z; simp
    conv_rhs => rw [← hSR, ← hC]
    rfl
  have hh' : d + 2 ≤ 1 + D (NPCC.subgame (Paper2.fullInterlace F 3)
      SR.toFinset C.toFinset) := by
    simpa using hh
  rw [heq] at hh'
  have hlower : d + 1 ≤
      Paper2.Compression.restrictionD (Paper2.fullInterlace F 3) SR C := by
    omega
  exact hlower.trans (selected_projection_cost_le_indexed F decode e R K)

#print axioms selected_projection_cost_le_indexed
#print axioms suffix_zero
#print axioms suffix_one

end CurrentAdditive.SuffixSmall
