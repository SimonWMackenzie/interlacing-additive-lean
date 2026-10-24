import CurrentAdditive.V38TwoLow

/-!
The second line of v38 `lem:small-blocks`: two full-product blocks,
row mass `2θ`, column mass `9/25`, and one additional protocol bit.
The proof follows the actual first message, whoever speaks.
-/

namespace Paper2.V38SmallBlocks

open Workspace.Types.CommComplexity

variable {X Y : Type*} [Fintype X] [Fintype Y]

private theorem large_coord_high (ν : FiniteLaw Y) (V : Set (Fin 2 → Y))
    (hV : (9 / 25 : ℝ) ≤ (ν.iid 2).prob (· ∈ V)) :
    ∃ i : Fin 2,
      (3 / 5 : ℝ) ≤ ν.prob (· ∈ (fun z : Fin 2 → Y => z i) '' V) := by
  exact exists_large_pair_coordinate ν V (3 / 5) (by norm_num at *; exact hV)

theorem two_block_high (F : X → Y → Bool)
    (μ : FiniteLaw X) (ν : FiniteLaw Y) (θ : ℝ) (H : ℕ)
    (hH : 2 ≤ H) (hθ : 0 < θ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ ν θ (H : ℤ))
    (U : Set (Fin 2 × X)) (V : Set (Fin 2 → Y))
    (hrow : ∀ i : Fin 2, 2 * θ ≤ μ.prob (fun x => (i, x) ∈ U))
    (hcol : (9 / 25 : ℝ) ≤ (ν.iid 2).prob (· ∈ V)) :
    H + 1 ≤ Compression.restrictionD (fullInterlace F 2) U V := by
  have hlow := two_block_low F μ ν θ H hH hθ hp U V hrow (by linarith)
  have hpos : 1 ≤ Compression.restrictionD (fullInterlace F 2) U V := by omega
  rcases firstMessage_rectangle (fullInterlace F 2) U V hpos with
    ⟨a, ha⟩ | ⟨b, hb⟩
  · obtain ⟨i, hi⟩ := large_coord_high ν V hcol
    obtain ⟨t, ht⟩ := row_child_mass μ U a θ i (hrow i)
    have hbase := singleton_profile_bound F μ ν 2 θ (H : ℤ) hp
      (childSet U a t) V i ht (⟨0, by omega⟩ : Fin 2)
      (by convert hi using 1 <;> norm_num)
    have hbase' : H ≤ Compression.restrictionD (fullInterlace F 2)
        (childSet U a t) V := by
      exact_mod_cast (show (H : ℤ) ≤
        (Compression.restrictionD (fullInterlace F 2) (childSet U a t) V : ℤ) from
        (by simpa using hbase))
    have hcost := ha t
    omega
  · obtain ⟨t, ht⟩ := exists_heavy_child (ν.iid 2) V b
    have hchildcol : (9 / 50 : ℝ) ≤
        (ν.iid 2).prob (· ∈ childSet V b t) := by linarith
    have hsuffix := two_block_low F μ ν θ H hH hθ hp
      U (childSet V b t) hrow hchildcol
    have hcost := hb t
    omega

#print axioms two_block_high

end Paper2.V38SmallBlocks
