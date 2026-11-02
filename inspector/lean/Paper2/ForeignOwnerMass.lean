import Paper2.ForeignOwnerRectangle

/-!
# Protected mass at a foreign owner

Frozen v12 `res:foreign`, lines 388--446.  The loss fraction and the
threshold are defined from the actual owner's original retained rows.
The two protected conditional masses are measured under their fixed ambient
source laws.  No owner-count or inter-owner summation is used here.
-/

namespace Paper2.ForeignOwnerMass

open Workspace.Types.Protocol
open SourceMatrix SourceLaws SourceLawBinding SourceProfileParameters

variable {V X Y : Type*} [Fintype V] [Nonempty V] [Fintype X] [Fintype Y]

local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by
  unfold outerWidth
  positivity⟩

local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have := width_admissible L
  omega⟩

local instance (L : ℕ) : NeZero (width L) := ⟨by
  unfold width
  positivity⟩

private theorem width_ge_four (L : ℕ) : 4 ≤ width L := by
  unfold width
  have h := exponent_ge L
  have hp : 2 ^ 2 ≤ 2 ^ exponent L :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at hp
  exact hp

/-- The actual missing fraction of copy `i`'s normalized unrestricted
reference population at this owner. -/
noncomputable def referenceLoss (ν : PositiveRationalLaw Y)
    (L w : ℕ) (i : Fin w)
    (R : Set (Fin w × TaggedColumn (width L - 2)
      (outerWidth L) (width L) Y)) : ℝ :=
  1 - (rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
    (fun Z => (i, .unrestricted Z) ∈ R)

/-- The displayed foreign-owner threshold, with the original outer
width and the actual reference loss at this very owner. -/
noncomputable def foreignThreshold (ν : PositiveRationalLaw Y)
    (L w : ℕ) (i : Fin w)
    (R : Set (Fin w × TaggedColumn (width L - 2)
      (outerWidth L) (width L) Y)) : ℝ :=
  2 * outerWidth L * x L + 5 * referenceLoss ν L w i R + 2 / outerWidth L

/-- The literal sum of the two normalized protected populations of copy
`j`, multiplied by their actual mixture weight `1/256` each. -/
noncomputable def protectedMass (ν : PositiveRationalLaw Y)
    (L w : ℕ) (j : Fin w)
    (R : Set (Fin w × TaggedColumn (width L - 2)
      (outerWidth L) (width L) Y)) : ℝ :=
  (1 / 256 : ℝ) *
    ((fixedTailLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
      (fun f => (j, .fixedTail f) ∈ R) +
     (outerLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
      (fun f => (j, .diagonal f) ∈ R))

/-- Foreign-owner mass on the actual protocol rectangle.  In the
`δ_i≤1` branch, exceeding this bound forces one of the two *actual*
protected conditional populations above `δ_i`, contradicting the checked
two-stream rectangle. -/
theorem protected_mass_le
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d w : ℕ)
    (activity : SourceConstruction.Items (width L) V →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y) (i j : Fin w) (hij : i ≠ j)
    (R : Set (Fin w × TaggedColumn (width L - 2)
      (outerWidth L) (width L) Y))
    (Y' : Set (Fin w → ForeignOwnerProjection.K V X
      (width L - 2) (outerWidth L) (width L)))
    (P : Protocol (Fin w × TaggedColumn (width L - 2)
      (outerWidth L) (width L) Y)
      (Fin w → ForeignOwnerProjection.K V X
        (width L - 2) (outerWidth L) (width L)) Bool)
    (hP : ∀ a ∈ R, ∀ y ∈ Y',
      P.eval a y = fullInterlace (N base activity ξ₀) w a y)
    (δsrc ζsrc : ℝ)
    (hpair : (99 / 100 : ℝ) ≤ ProductProjections.projectionMass
      (fun _ => (matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L)
        (width L) (width_ge_four L)).toFiniteLaw)
      (· ∈ Y') {i,j})
    (hsingle : 1 - SourceDeletionParameters.eta (width L) δsrc ζsrc ≤
      ProductProjections.projectionMass
        (fun _ => (matrixColumnLaw (V := V) μ (width L - 2)
          (outerWidth L) (width L)
          (width_ge_four L)).toFiniteLaw)
        (· ∈ Y') {i})
    (hsmall : 2 * (width L : ℝ) * x L ≤ 1 / 1000)
    (hd : 3 ≤ d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (hcost : P.cost ≤ d + exponent L + outerExponent L + exponent L) :
    protectedMass ν L w j R ≤
      2 * (1 / 256 : ℝ) * foreignThreshold ν L w i R := by
  let pf := (fixedTailLaw ν (width L - 2) (outerWidth L)
    (width L)).toFiniteLaw.prob (fun f => (j, .fixedTail f) ∈ R)
  let pd := (outerLaw ν (width L - 2) (outerWidth L)
    (width L)).toFiniteLaw.prob (fun f => (j, .diagonal f) ∈ R)
  let ε := referenceLoss ν L w i R
  let δ := foreignThreshold ν L w i R
  by_cases hδ : δ ≤ 1
  · by_contra hn
    have hsum : 2 * δ < pf + pd := by
      unfold protectedMass at hn
      dsimp only [pf, pd, δ, ε] at *
      push Not at hn
      nlinarith
    have hor : δ < pf ∨ δ < pd := by
      by_contra h
      push Not at h
      nlinarith
    have hO : 1 - ε ≤
        (rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw.prob
          (fun Z => (i, .unrestricted Z) ∈ R) := by
      simp [ε, referenceLoss]
    have hslack : 2 * outerWidth L * x L + 5 * ε +
        2 / outerWidth L ≤ δ := by
      rfl
    exact ForeignOwnerRectangle.foreign_owner_impossible μ ν base L d w
      activity ξ₀ i j hij R Y' P hP δsrc ζsrc ε δ
      hpair hsingle hO
      (hor.elim (fun h => Or.inl (le_of_lt h))
        (fun h => Or.inr (le_of_lt h)))
      hδ hslack hsmall hd hp hinner houter hwide href hcost
  · have hgt : 1 < δ := lt_of_not_ge hδ
    have hpf : pf ≤ 1 :=
      (fixedTailLaw ν (width L - 2) (outerWidth L)
        (width L)).toFiniteLaw.prob_le_one _
    have hpd : pd ≤ 1 :=
      (outerLaw ν (width L - 2) (outerWidth L)
        (width L)).toFiniteLaw.prob_le_one _
    unfold protectedMass
    dsimp only [pf, pd, δ] at *
    nlinarith

end Paper2.ForeignOwnerMass

#print axioms Paper2.ForeignOwnerMass.protected_mass_le
