import EthInapproximability.CurrentPaper.ProtectedProfiles
import EthInapproximability.CurrentPaper.ExactResidualIndexing
import EthInapproximability.CurrentPaper.HardSeed

/-!
# One-copy profiles of the actual reference-row submatrix

Source: locked replacement v8, `A-stage4-details.tex`,
`lem:paper-reference-extraction` and `eq:paper-reference-profile`.
This converts the physical extraction into the exact one-copy family
interface consumed after scale alignment. Its row carrier is precisely
`JointTransfer.referenceRows`, and its column carrier is unchanged.

The generic one-copy wrapper from `ExactResidualIndexing` is reused only
for its finite one-coordinate equivalence. No exact-hardness theorem is
used. The lower-level second-matrix profiles and scalar selection gate
remain explicit, rather than being hidden inside a protected-profile
certificate.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ProtectedReferenceFamily

open scoped Classical
open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open Construction JointTransfer ProtectedProfiles

universe u
variable {X Y : Type u} [Fintype X] [Fintype Y]

def templateFraction (s L nv nb : ℕ) : ℝ :=
  (templateRows (X := X) s L nv nb).card / Fintype.card (ProtectedRows s L nv nb X)

/-- A row-subtype restriction and its actual image differ only by input
names. This direction needs no injectivity assumption beyond `Subtype.val`. -/
theorem subtype_image_cost {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (F : A → B → Bool) (S : Finset A) (E : Finset S) (T : Finset B) :
    D (subgame F (E.image Subtype.val) T) ≤
      D (subgame (fun a : S => F a.val) E T) := by
  let row : (E.image Subtype.val) → E := fun r =>
    ⟨(Finset.mem_image.mp r.property).choose, (Finset.mem_image.mp r.property).choose_spec.1⟩
  have heq : subgame F (E.image Subtype.val) T =
      fun r c => subgame (fun a : S => F a.val) E T (row r) c := by
    funext r c
    change F r.val c.val = F (row r).val.val c.val
    rw [(Finset.mem_image.mp r.property).choose_spec.2]
  rw [heq]
  exact D_mapNodes_le (subgame (fun a : S => F a.val) E T) row (id : T → T)

/-- The physical reference extraction in the exact public one-copy
restriction interface. Both densities refer to the full retained carriers. -/
theorem reference_oneCopy [Nonempty X] [Nonempty Y]
    (R : X → Y → Bool) (a s q L nv nb : ℕ)
    (hs : 0 < s) (hq : 0 < q) (hL : 0 < L) (hv : 0 < nv) (hb : 0 < nb)
    (family : SecondFamily a q L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    {p H : ℕ} {x ρ β : ℝ} (hp : 0 < p) (hx : 0 < x) (hx1 : x < 1)
    (hρ1 : ρ ≤ 1) (hβ1 : β ≤ 1)
    (hgate : p ≤ ⌈(s : ℝ) *
      ((β + templateFraction (X := X) s L nv nb - 1) /
        templateFraction (X := X) s L nv nb - x) / (1 - x)⌉₊)
    (hhard : H ≤ Dfamily (interlaceFun (fun j z => secondMatrix R a s q L family z j) p)
      (bracketGE (Fin L) (SecondRows a s q Y) p x ρ)) :
    H ≤ Dfamily (interlaceFun
      (fun r : referenceRows (Y := Y) a s q =>
        protectedMatrix R a s q L nv nb hs family order vectors cap r.val) 1)
      (bracketGE (referenceRows (Y := Y) a s q) (ProtectedRows s L nv nb X) 1 ρ β) := by
  letI := secondRows_nonempty (Y := Y) a s q hq
  have href : 0 < (referenceRows (Y := Y) a s q).card := by
    rw [referenceRows, Finset.card_image_of_injective _ (referenceEmbedding a s q).injective,
      Finset.card_univ, Fintype.card_prod]
    exact Nat.mul_pos Fintype.card_pos (reference_labels_pos a s q hq)
  letI : Nonempty (referenceRows (Y := Y) a s q) := Finset.Nonempty.to_subtype (Finset.card_pos.mp href)
  apply ExactResidualIndexing.oneCopy_family_lower_of_subgame _ hρ1 hβ1
  intro A B hA hB
  have hAc : (A.image Subtype.val).card = A.card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  have hAsub : A.image Subtype.val ⊆ referenceRows (Y := Y) a s q := by
    intro r hr
    obtain ⟨r', _, rfl⟩ := Finset.mem_image.mp hr
    exact r'.property
  have hAdensity : ρ ≤ ((A.image Subtype.val).card : ℝ) /
      (referenceRows (Y := Y) a s q).card := by
    apply (le_div_iff₀ (by exact_mod_cast href)).2
    rw [hAc]
    simpa only [Fintype.card_coe, mul_comm] using hA
  have hphys := reference_restriction_bound R a s q L nv nb hs hq hL hv hb
    family order vectors cap hp hx hx1 hgate hhard (A.image Subtype.val) B
    hAsub hAdensity (by simpa only [mul_comm] using hB)
  exact hphys.trans (subtype_image_cost _ (referenceRows (Y := Y) a s q) A B)

end EthInapproximability.CurrentPaper.ProtectedReferenceFamily
