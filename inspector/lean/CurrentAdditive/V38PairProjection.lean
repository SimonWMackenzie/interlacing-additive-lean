import CurrentAdditive.V38SingletonProjection
import Paper2.ProductProjections

/-!
The two-coordinate projection inequality for the original product law.
The retained tuple set may be arbitrarily correlated. No conditional product
law is used.
-/

namespace Paper2.V38SmallBlocks

open scoped BigOperators

variable {Y : Type*} [Fintype Y]

theorem pair_projection_product_bound (ν : FiniteLaw Y)
    (V : Set (Fin 2 → Y)) :
    (ν.iid 2).prob (· ∈ V) ≤
      ν.prob (· ∈ (fun z : Fin 2 → Y => z 0) '' V) *
      ν.prob (· ∈ (fun z : Fin 2 → Y => z 1) '' V) := by
  let E : Fin 2 → Y → Prop := fun i y => y ∈ (fun z : Fin 2 → Y => z i) '' V
  have hmono : (ν.iid 2).prob (· ∈ V) ≤
      (ν.iid 2).prob (fun z => ∀ i, E i (z i)) := by
    apply FiniteLaw.prob_mono
    intro z hz i
    exact ⟨z, hz, rfl⟩
  have hproduct : (ν.iid 2).prob (fun z => ∀ i, E i (z i)) =
      ν.prob (E 0) * ν.prob (E 1) := by
    change (FiniteLaw.pi (fun _ : Fin 2 => ν)).prob
      (fun z => ∀ i, E i (z i)) = _
    rw [FiniteLaw.pi_prob_coordinatewise]
    simp [Fin.prod_univ_two]
  simpa [E] using hmono.trans hproduct.le

theorem exists_large_pair_coordinate (ν : FiniteLaw Y)
    (V : Set (Fin 2 → Y)) (t : ℝ)
    (hV : t ^ 2 ≤ (ν.iid 2).prob (· ∈ V)) :
    ∃ i : Fin 2, t ≤ ν.prob (· ∈ (fun z : Fin 2 → Y => z i) '' V) := by
  let m0 := ν.prob (· ∈ (fun z : Fin 2 → Y => z 0) '' V)
  let m1 := ν.prob (· ∈ (fun z : Fin 2 → Y => z 1) '' V)
  have hprod : t ^ 2 ≤ m0 * m1 := hV.trans (pair_projection_product_bound ν V)
  by_contra h
  have h0 : m0 < t := lt_of_not_ge (fun hm => h ⟨0, hm⟩)
  have h1 : m1 < t := lt_of_not_ge (fun hm => h ⟨1, hm⟩)
  have hm0 := FiniteLaw.prob_nonneg ν (· ∈ (fun z : Fin 2 → Y => z 0) '' V)
  have hm1 := FiniteLaw.prob_nonneg ν (· ∈ (fun z : Fin 2 → Y => z 1) '' V)
  dsimp [m0] at h0 hm0
  dsimp [m1] at h1 hm1
  dsimp [m0, m1] at hprod
  nlinarith

#print axioms pair_projection_product_bound
#print axioms exists_large_pair_coordinate

end Paper2.V38SmallBlocks
