import CurrentAdditive.GeneratedWProfileSchedule
import CurrentAdditive.GeneratedOwnerRowJoint

/-! The source-specific weak internal profile on the same three complete
streams and the same indexed matrix used in the near-full argument. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicParameters

theorem generated_W_profile_at_schedule
    {G V Aux X Y : Type*} [Fintype G] [Fintype V] [Fintype Aux]
    [Fintype X] [Fintype Y] [DecidableEq G] [DecidableEq V]
    [DecidableEq Aux] [DecidableEq X] [DecidableEq Y]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (L : ℕ) (hL : 2004 ≤ L)
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)] [NeZero (w L)]
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) μX μY)
    (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
    (streams : InternalStreams src μI (w L))
    (R : X → Y → Bool)
    (activity : (G × (V ⊕ Aux)) → Fin (q₂ L) → Option (Fin (s L)))
    (ξ₀ : Tail (s L) Y) (d : ℕ) (hd : 3 ≤ d)
    (hD : D R = d)
    (hp : RestrictionProfile R μX.toFiniteLaw μY.toFiniteLaw
      (ρ L : ℝ) (d : ℤ))
    (he : 128 * CurrentAdditive.conditioningExceptionCount
      (θ L : ℝ) 1 ≤ w L)
    (hx : (w L : ℝ) * (x L : ℝ) ≤ 1/10000) :
    RestrictionProfile (W src streams R activity ξ₀)
      streams.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin (w L))).prod
        (columnLaw src)).toFiniteLaw)
      (θ L : ℝ)
      ((d+(L+3)/4+4*L+(L+3)/4+2*L : ℕ) : ℤ) := by
  have hprofiles := generated_profiles_at_parameters L hL src μI
    R activity ξ₀ d hd hD hp
  obtain ⟨_, _, _, _, href⟩ := hprofiles
  have hθ : (0 : ℝ) < (θ L : ℝ) := by
    exact_mod_cast theta_pos L
  have hθ1 : (θ L : ℝ) ≤ 1 := by
    have hQ : (1 : ℚ) ≤ Q L := by exact_mod_cast Q_pos L
    have hqθ := Q_theta L
    have hθp := theta_pos L
    have hle : θ L ≤ (Q L : ℚ) * θ L := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hQ) hθp.le]
    exact_mod_cast (by linarith : θ L ≤ (1 : ℚ))
  have hscale (j : Fin 3) :
      (2 : ℝ)^(2*L-j.val) * (x L : ℝ) < 1 := by
    have hnat : 2^(2*L-j.val) ≤ w L := by
      rw [w_eq_pow]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have hreal : (2^(2*L-j.val) : ℝ) ≤ (w L : ℝ) := by
      exact_mod_cast hnat
    have hmul := mul_le_mul_of_nonneg_right hreal (x_real_pos L).le
    push_cast at hmul
    linarith
  have hwise := internal_streams_row_dwise src μI streams
  have hprofile := generated_W_profile_from_rung_guards src μI streams
    R activity ξ₀
    (d+(L+3)/4+4*L+(L+3)/4) (2*L)
    (x L : ℝ) (θ L : ℝ) 1
    (by omega) (by omega) (x_real_pos L) hθ hθ1
    (by norm_num) hwise href hscale
    (generated_W_profile_budget L hL he hx)
  simpa only using hprofile

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.generated_W_profile_at_schedule
