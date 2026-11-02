import CurrentAdditive.V38RareGoodPair
import CurrentAdditive.InjectiveProjectionTVCompatible
import CurrentAdditive.ProjectionMass

/-!
An arbitrary retained indexed set has enough mass in its original product
projection. Its conditional law is not claimed to be independent.
-/

namespace V38RareBoost

open Paper2 CurrentAdditive

variable {Z S : Type*} [Fintype Z] [Fintype S]

theorem good_projected_mass
    (source : FiniteLaw S) (ν : FiniteLaw Z)
    {q n : ℕ} (decode : S → Fin q → Z)
    (Y K : Set S) (hY : 0 < source.prob (· ∈ Y)) (hK : K ⊆ Y)
    (E Good : Finset (Fin q)) (hOutside : ∀ j ∈ Good, j ∉ E)
    (ε : ℝ)
    (hTV : ∀ J : Finset (Fin q),
      J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV (condition source (· ∈ Y) hY) ν decode J ≤ ε)
    (hn : n ≤ 8) (e : Fin n → Fin q) (he : Function.Injective e)
    (heGood : ∀ j, e j ∈ Good) :
    source.prob (· ∈ K) / source.prob (· ∈ Y) - ε ≤
      (ν.iid n).prob
        (· ∈ (fun s j => decode s (e j)) '' K) := by
  let p : S → Fin n → Z := fun s j => decode s (e j)
  have hGoodSubset : Good ⊆ Finset.univ \ E := by
    intro j hj
    simp [hOutside j hj]
  have hgood : ∀ P : (Fin n → Z) → Prop,
      |source.prob (fun s => s ∈ Y ∧ P (p s)) /
          source.prob (· ∈ Y) - (ν.iid n).prob P| ≤ ε := by
    intro P
    exact injective_good_conditioned_event_abs source ν decode
      (· ∈ Y) hY E Good hGoodSubset ε hTV hn e he heGood P
  have hmass := ProjectionMass.ambient_image_mass_ge_conditional_mass_sub
    source (ν.iid n) p (· ∈ Y) (· ∈ K) ε hY
    (fun _ hs => hK hs) hgood
  simpa only [p, ProjectionMass.imageEvent, Set.mem_image] using hmass

#print axioms good_projected_mass

end V38RareBoost
