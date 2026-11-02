import EthInapproximability.ParameterizedNP.WrapperProtectedEarly

/-!
# A dyadic class of additional-row densities

Source: the proof of `lem:paper-early-protected-closure` and
`eq:paper-early-dyadic-class` in the v8 replacement paper, Appendix A.

Only the generic finite-weight pigeonhole and least-dyadic-width lemmas are
reused from `WrapperProtectedEarly`.  No old matrix constructor, protected
reservoir split, or communication lower-bound endpoint is used.  In particular
the lower bound on the selected density retains the current paper's factor κ.
-/

namespace EthInapproximability.CurrentPaper.DensityBucket

open scoped BigOperators

theorem old_class_count_eq (r : ℕ) :
    EthInapproximability.ParameterizedNP.WrapperProtectedEarly.Lq (2 ^ r) = r + 2 := by
  unfold EthInapproximability.ParameterizedNP.WrapperProtectedEarly.Lq
  rw [show 2 * 2 ^ r = 2 ^ (r + 1) by ring, Nat.clog_pow 2 (r + 1) (by decide)]

/-- Data actually selected from the supplied finite densities.  The dyadic
representative is `1 / 2^classExponent` and the width is `2^widthExponent`. -/
structure Selection {r : ℕ} (J : Finset (Fin (2 ^ r)))
    (d : Fin (2 ^ r) → ℝ) (B s κ : ℕ) where
  classExponent : ℕ
  widthExponent : ℕ
  coordinates : Finset (Fin (2 ^ r))
  subset : coordinates ⊆ J
  class_bounds : ∀ j ∈ coordinates,
    (1 / (2 : ℝ) ^ classExponent) / 2 < d j ∧
      d j ≤ 1 / (2 : ℝ) ^ classExponent
  width_lower : 8 * ((s : ℝ) * κ) ≤
    (2 : ℝ) ^ widthExponent * (1 / (2 : ℝ) ^ classExponent)
  width_upper : (2 : ℝ) ^ widthExponent * (1 / (2 : ℝ) ^ classExponent) <
    16 * ((s : ℝ) * κ)
  enough_coordinates : 2 ^ widthExponent * B ≤ coordinates.card
  density_lower : 32 * (B : ℝ) * (r + 2 : ℕ) * s * κ / (2 : ℝ) ^ r ≤
    1 / (2 : ℝ) ^ classExponent
  width_le_ambient : 2 ^ widthExponent ≤ 2 ^ r
  exponent_ge_four : 4 ≤ widthExponent

/-- The density bucketing step with exactly `Lq = log₂ q + 2`, at the
paper's dyadic ambient width `q = 2^r`. -/
theorem exists_selection {r B s κ : ℕ} (J : Finset (Fin (2 ^ r)))
    (d : Fin (2 ^ r) → ℝ) (hB : 1 ≤ B) (hs : 1 ≤ s) (hκ : 2 ≤ κ)
    (hd0 : ∀ j ∈ J, 0 ≤ d j) (hd1 : ∀ j ∈ J, d j ≤ 1)
    (hmass : 64 * (B : ℝ) * (r + 2 : ℕ) * s * κ ≤ ∑ j ∈ J, d j) :
    Nonempty (Selection J d B s κ) := by
  classical
  let D : ℝ := 64 * (B : ℝ) * (r + 2 : ℕ) * s * κ
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hκR : (2 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hLR : (1 : ℝ) ≤ (r + 2 : ℕ) := by exact_mod_cast (show 1 ≤ r + 2 by omega)
  have hBL : (1 : ℝ) ≤ (B : ℝ) * (r + 2 : ℕ) := by nlinarith
  have hBLs : (1 : ℝ) ≤ (B : ℝ) * (r + 2 : ℕ) * s := by nlinarith
  have hBLsκ : (2 : ℝ) ≤ (B : ℝ) * (r + 2 : ℕ) * s * κ := by nlinarith
  have hD1 : 1 ≤ D := by dsimp [D]; nlinarith
  have hq : 0 < 2 ^ r := by positivity
  have hJ : J.card ≤ 2 ^ r := by simpa using Finset.card_le_univ J
  obtain ⟨k, V, hVJ, hVclass, hVheavy, hVdensity⟩ :=
    EthInapproximability.ParameterizedNP.WrapperProtectedEarly.exists_heavy_dyadic_class
      J d hq hJ hd0 hd1 hD1 hmass
  rw [old_class_count_eq] at hVheavy
  have hL0 : (0 : ℝ) < (r + 2 : ℕ) := by positivity
  have hquot : D / (2 * (r + 2 : ℕ)) = 32 * (B : ℝ) * s * κ := by
    dsimp [D]
    field_simp
    ring
  rw [hquot] at hVheavy
  have hk0 := EthInapproximability.ParameterizedNP.WrapperProtectedEarly.classWidth_pos k
  have hk1 := EthInapproximability.ParameterizedNP.WrapperProtectedEarly.classWidth_le_one k
  obtain ⟨e, he, hlo, hhi, hsize⟩ :=
    EthInapproximability.ParameterizedNP.WrapperProtectedEarly.exists_width_u
      hk0 hk1 hs hκ hB hVheavy
  have hsize' : 2 ^ e * B ≤ V.card := by
    have hp : (0 : ℝ) ≤ (2 : ℝ) ^ e * B := by positivity
    have hh : (2 : ℝ) ^ e * B ≤ (V.card : ℝ) := by linarith
    exact_mod_cast hh
  have hVq : V.card ≤ 2 ^ r := (Finset.card_le_card hVJ).trans hJ
  have heq : 2 ^ e ≤ 2 ^ r :=
    (Nat.le_mul_of_pos_right _ hB).trans (hsize'.trans hVq)
  have he4 : 4 ≤ e := by
    have hprod : (2 : ℝ) ≤ (s : ℝ) * κ := by nlinarith
    have hpow16 : (16 : ℝ) ≤ (2 : ℝ) ^ e := by
      have hh : (2 : ℝ) ^ e *
          EthInapproximability.ParameterizedNP.WrapperProtectedEarly.classWidth k ≤
          (2 : ℝ) ^ e := mul_le_of_le_one_right (by positivity) hk1
      nlinarith
    have hpow16n : 16 ≤ (2 : ℕ) ^ e := by exact_mod_cast hpow16
    by_contra h
    have hsmall : (2 : ℕ) ^ e ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at hsmall
    omega
  refine ⟨⟨k, e, V, hVJ, ?_, hlo, hhi, hsize', ?_, heq, he4⟩⟩
  · intro j hj
    have hh := hVclass j hj
    dsimp [EthInapproximability.ParameterizedNP.WrapperProtectedEarly.classWidth] at hh
    constructor <;> linarith
  · have hquotq : D / (2 * ((2 ^ r : ℕ) : ℝ)) =
        32 * (B : ℝ) * (r + 2 : ℕ) * s * κ / (2 : ℝ) ^ r := by
      dsimp [D]
      push_cast
      ring
    rw [hquotq] at hVdensity
    exact hVdensity

/-- The selected dyadic width is divisible by four, as required for the
all-template projection step. -/
theorem Selection.four_dvd_width {r B s κ : ℕ} {J : Finset (Fin (2 ^ r))}
    {d : Fin (2 ^ r) → ℝ} (sel : Selection J d B s κ) :
    4 ∣ 2 ^ sel.widthExponent := by
  have hh : 2 ≤ sel.widthExponent := le_trans (by decide) sel.exponent_ge_four
  simpa using (pow_dvd_pow 2 hh)

/-- A concrete legal input checks that the mass hypotheses are jointly
satisfiable, including at `s = 4` and `κ = 2`. -/
theorem uniform_density_regression :
    Nonempty (Selection (r := 16) Finset.univ (fun _ => (1 : ℝ)) 1 4 2) := by
  apply exists_selection
  · norm_num
  · norm_num
  · norm_num
  · intro j hj; norm_num
  · intro j hj; norm_num
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    norm_num

end EthInapproximability.CurrentPaper.DensityBucket
