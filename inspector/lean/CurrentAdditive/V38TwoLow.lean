import CurrentAdditive.V38ChildCost

/-!
The first line of v38 `lem:small-blocks`: two surviving full-product blocks,
row threshold `2θ`, column threshold `9/50`, cost at least `H`.
Only the v38 two-threshold profile is assumed. Bob's branch is charged after
measuring its actual child mass in the original product law.
-/

namespace Paper2.V38SmallBlocks

open Workspace.Types.CommComplexity

variable {X Y : Type*} [Fintype X] [Fintype Y]

private theorem large_coord (ν : FiniteLaw Y) (V : Set (Fin 2 → Y))
    (hV : (9 / 100 : ℝ) ≤ (ν.iid 2).prob (· ∈ V)) :
    ∃ i : Fin 2,
      (3 / 10 : ℝ) ≤ ν.prob (· ∈ (fun z : Fin 2 → Y => z i) '' V) := by
  exact exists_large_pair_coordinate ν V (3 / 10) (by norm_num at *; exact hV)

theorem row_child_mass (μ : FiniteLaw X) (U : Set (Fin 2 × X))
    (a : U → Bool) (θ : ℝ) (i : Fin 2)
    (hrow : 2 * θ ≤ μ.prob (fun x => (i, x) ∈ U)) :
    ∃ t : Bool, θ ≤ μ.prob (fun x => (i, x) ∈ childSet U a t) := by
  let U₀ : Set X := {x | (i, x) ∈ U}
  let a₀ : U₀ → Bool := fun x => a ⟨(i, x.1), x.2⟩
  obtain ⟨t, ht⟩ := exists_heavy_child μ U₀ a₀
  refine ⟨t, ?_⟩
  have heq : childSet U₀ a₀ t = {x : X | (i, x) ∈ childSet U a t} := by
    ext x
    constructor
    · rintro ⟨hx, ha⟩
      exact ⟨hx, ha⟩
    · rintro ⟨hx, ha⟩
      exact ⟨hx, ha⟩
  rw [heq] at ht
  dsimp [U₀] at ht
  linarith

theorem two_block_low (F : X → Y → Bool)
    (μ : FiniteLaw X) (ν : FiniteLaw Y) (θ : ℝ) (H : ℕ)
    (hH : 2 ≤ H) (hθ : 0 < θ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ ν θ (H : ℤ))
    (U : Set (Fin 2 × X)) (V : Set (Fin 2 → Y))
    (hrow : ∀ i : Fin 2, 2 * θ ≤ μ.prob (fun x => (i, x) ∈ U))
    (hcol : (9 / 50 : ℝ) ≤ (ν.iid 2).prob (· ∈ V)) :
    H ≤ Compression.restrictionD (fullInterlace F 2) U V := by
  have hlarge : (9 / 100 : ℝ) ≤ (ν.iid 2).prob (· ∈ V) := by linarith
  obtain ⟨i, hi⟩ := large_coord ν V hlarge
  have h0 := singleton_profile_bound F μ ν 2 θ (H : ℤ) hp U V i
    (by have h := hrow i; linarith) (⟨1, by omega⟩ : Fin 2)
    (by convert hi using 1 <;> norm_num)
  have hpos : 1 ≤ Compression.restrictionD (fullInterlace F 2) U V := by
    omega
  rcases firstMessage_rectangle (fullInterlace F 2) U V hpos with
    ⟨a, ha⟩ | ⟨b, hb⟩
  · obtain ⟨t, ht⟩ := row_child_mass μ U a θ i (hrow i)
    have h1 := singleton_profile_bound F μ ν 2 θ (H : ℤ) hp
      (childSet U a t) V i ht (⟨1, by omega⟩ : Fin 2)
      (by convert hi using 1 <;> norm_num)
    have hcost := ha t
    omega
  · obtain ⟨t, ht⟩ := exists_heavy_child (ν.iid 2) V b
    have hchildcol : (9 / 100 : ℝ) ≤
        (ν.iid 2).prob (· ∈ childSet V b t) := by linarith
    obtain ⟨j, hj⟩ := large_coord ν (childSet V b t) hchildcol
    have h1 := singleton_profile_bound F μ ν 2 θ (H : ℤ) hp
      U (childSet V b t) j (by have h := hrow j; linarith)
      (⟨1, by omega⟩ : Fin 2) (by convert hj using 1 <;> norm_num)
    have hcost := hb t
    omega

#print axioms two_block_low

end Paper2.V38SmallBlocks
