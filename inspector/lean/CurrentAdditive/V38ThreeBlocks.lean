import CurrentAdditive.V38BlockProjection

/-! Exact three-block small case, with original rational product law. -/

namespace Paper2.V38SmallBlocks

open Workspace.Types.CommComplexity

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem two_low_selected (F : X → Y → Bool)
    (μ : FiniteLaw X) (ν : FiniteLaw Y) (θ : ℝ) (H : ℕ)
    (hH : 2 ≤ H) (hθ : 0 < θ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ ν θ (H : ℤ))
    (p : ℕ) (U : Set (Fin p × X)) (V : Set (Fin p → Y))
    (e : Fin 2 → Fin p)
    (hrow : ∀ i : Fin 2, 2 * θ ≤ μ.prob (fun x => (e i, x) ∈ U))
    (hcol : (9 / 50 : ℝ) ≤ (ν.iid 2).prob
      (· ∈ (fun z : Fin p → Y => fun i : Fin 2 => z (e i)) '' V)) :
    H ≤ Compression.restrictionD (fullInterlace F p) U V := by
  have htwo := two_block_low F μ ν θ H hH hθ hp
    {s : Fin 2 × X | (e s.1, s.2) ∈ U}
    ((fun z : Fin p → Y => fun i : Fin 2 => z (e i)) '' V)
    hrow hcol
  exact htwo.trans (projected_blocks_cost_le F p 2 U V e)

theorem three_to_two_low (F : X → Y → Bool)
    (μ : FiniteLaw X) (ν : PositiveRationalLaw Y) (θ : ℝ) (H : ℕ)
    (hH : 2 ≤ H) (hθ : 0 < θ)
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ ν.toFiniteLaw θ (H : ℤ))
    (U : Set (Fin 3 × X)) (V : Set (Fin 3 → Y))
    (hrow : ∀ i : Fin 3, 2 * θ ≤ μ.prob (fun x => (i, x) ∈ U))
    (hcol : (9 / 100 : ℝ) ≤ (ν.toFiniteLaw.iid 3).prob (· ∈ V)) :
    H ≤ Compression.restrictionD (fullInterlace F 3) U V := by
  obtain ⟨J, hJ, hm⟩ := rational_projected_mass ν 3 2 (by omega) (by omega) V
  let e : Fin 2 → Fin 3 := J.orderEmbOfFin hJ
  have hpow : (9 / 100 : ℝ) ^ ((2 : ℝ) / 3) ≤
      ((ν.toFiniteLaw.iid 3).prob (· ∈ V)) ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow (by norm_num) hcol (by norm_num)
  have hproj : (9 / 50 : ℝ) ≤ (ν.toFiniteLaw.iid 2).prob
      (· ∈ (fun z : Fin 3 → Y => fun i : Fin 2 => z (e i)) '' V) :=
    (three_pair_numeric.trans hpow).trans hm
  exact two_low_selected F μ ν.toFiniteLaw θ H hH hθ hp 3 U V e
    (fun i => hrow (e i)) hproj

#print axioms three_to_two_low

end Paper2.V38SmallBlocks
