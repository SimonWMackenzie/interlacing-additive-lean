import CurrentAdditive.V38TwoHigh
import Paper2.AAvgProjectionJ

/-! Projection to selected named blocks keeps actual retained tuples. -/

namespace Paper2.V38SmallBlocks

open Workspace.Types.CommComplexity

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem projected_blocks_cost_le (F : X → Y → Bool) (p l : ℕ)
    (U : Set (Fin p × X)) (V : Set (Fin p → Y))
    (e : Fin l → Fin p) :
    Compression.restrictionD (fullInterlace F l)
      {s | (e s.1, s.2) ∈ U}
      ((fun z : Fin p → Y => fun i : Fin l => z (e i)) '' V) ≤
      Compression.restrictionD (fullInterlace F p) U V := by
  apply SourceProjection.restrictionD_projected_le
    (fullInterlace F p) (fullInterlace F l)
    (fun s : Fin l × X => (e s.1, s.2))
    (fun z : Fin p → Y => fun i : Fin l => z (e i))
    U V {s | (e s.1, s.2) ∈ U}
  · intro s hs
    exact hs
  · intro s hs z hz
    rfl

#print axioms projected_blocks_cost_le

theorem rational_projected_mass (ν : PositiveRationalLaw Y)
    (p l : ℕ) (hl : 1 ≤ l) (hlp : l ≤ p)
    (V : Set (Fin p → Y)) :
    ∃ (J : Finset (Fin p)) (hJ : J.card = l),
      ((ν.toFiniteLaw.iid p).prob (· ∈ V)) ^ ((l : ℝ) / (p : ℝ)) ≤
        (ν.toFiniteLaw.iid l).prob
          (· ∈ (fun z : Fin p → Y => fun i : Fin l =>
            z (J.orderEmbOfFin hJ i)) '' V) := by
  classical
  obtain ⟨J, hJ, hm⟩ :=
    AveragedProjection.rational_averaged_projection_mass ν p l hl hlp V.toFinset
  refine ⟨J, hJ, ?_⟩
  simpa using hm

#print axioms rational_projected_mass

theorem three_pair_numeric :
    (9 / 50 : ℝ) ≤ (9 / 100 : ℝ) ^ ((2 : ℝ) / 3) := by
  let t : ℝ := (9 / 100 : ℝ) ^ ((2 : ℝ) / 3)
  have ht : 0 ≤ t := Real.rpow_nonneg (by norm_num) _
  have ht3 : t ^ 3 = (9 / 100 : ℝ) ^ 2 := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 9 / 100)]
    norm_num
  have hc : (9 / 50 : ℝ) ^ 3 ≤ t ^ 3 := by rw [ht3]; norm_num
  nlinarith [sq_nonneg (t - 9 / 50)]

theorem five_pair_numeric :
    (9 / 25 : ℝ) ≤ (9 / 100 : ℝ) ^ ((2 : ℝ) / 5) := by
  let t : ℝ := (9 / 100 : ℝ) ^ ((2 : ℝ) / 5)
  have ht : 0 ≤ t := Real.rpow_nonneg (by norm_num) _
  have ht5 : t ^ 5 = (9 / 100 : ℝ) ^ 2 := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 9 / 100)]
    norm_num
  have hc : (9 / 25 : ℝ) ^ 5 ≤ t ^ 5 := by rw [ht5]; norm_num
  by_contra hn
  have hlt : t < 9 / 25 := lt_of_not_ge hn
  have hpowlt : t ^ 5 < (9 / 25 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ hlt ht (by decide)
  linarith

end Paper2.V38SmallBlocks
