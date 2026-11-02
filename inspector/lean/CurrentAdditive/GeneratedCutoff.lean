import CurrentAdditive.V38Cutoff

/-! Every sufficiently large literal generated schedule passes all v39 tests.
The v39 mathematical source is text-identical to v38. This development uses
the exact generated `x = N⁻⁸`, and never the old `N⁻¹⁶` parameter.
Only the graph degree/size promise and the fixed positive deletion constant
are hypotheses; there is no passing-test or eventual-pass hypothesis. -/

namespace GeneratedCutoff

open V38Schedule V38Cutoff

def reciprocalCut (c : ℚ) : ℕ := Nat.ceil (1 / c)

def cutoffLog (Δ : ℕ) (c : ℚ) : ℕ :=
  8 * (reciprocalCut c + toleranceCoefficient c + restorationCoefficient c +
    Nat.ceil C128 + Δ) + 4000

theorem c_lower_dyadic (c : ℚ) (hc : 0 < c) :
    (1 : ℚ) / 2 ^ reciprocalCut c ≤ c := by
  have hceil : (1 : ℚ) / c ≤ reciprocalCut c := Nat.le_ceil _
  have hp : (reciprocalCut c : ℚ) ≤ 2 ^ reciprocalCut c := by
    exact_mod_cast coefficient_le_power (reciprocalCut c)
  have hh : (1 : ℚ) ≤ c * 2 ^ reciprocalCut c := by
    have hh := (div_le_iff₀ hc).1 hceil
    nlinarith [mul_le_mul_of_nonneg_left hp hc.le]
  exact (div_le_iff₀ (by positivity)).2 (by nlinarith)

theorem s_pos (L : ℕ) : 0 < generatedS L := by unfold generatedS; positivity
theorem N_pos (L : ℕ) : 0 < generatedN L := by unfold generatedN; positivity

theorem s_le_N (L : ℕ) (hL : 6 ≤ L) : generatedS L ≤ generatedN L := by
  exact CurrentAdditive.DeterministicParameters.s_le_N L hL

theorem s_ge_256 (L : ℕ) (hL : 32 ≤ L) : 256 ≤ generatedS L := by
  unfold generatedS quarterCeil
  exact (show 2 ^ 8 ≤ 2 ^ ((L + 3) / 4) from
    Nat.pow_le_pow_right (by decide) (by omega))

theorem s_le_cN (c : ℚ) (L : ℕ) (hc : 0 < c)
    (hL : 2 * reciprocalCut c + 4 ≤ L) :
    (generatedS L : ℚ) ≤ c * generatedN L := by
  let d := reciprocalCut c
  have he : quarterCeil L + d ≤ L := by dsimp [quarterCeil, d]; omega
  have hnat : generatedS L * 2 ^ d ≤ generatedN L := by
    unfold generatedS generatedN
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) he
  have hrat : (generatedS L : ℚ) * 2 ^ d ≤ generatedN L := by exact_mod_cast hnat
  have hlower := c_lower_dyadic c hc
  have hm : (1 : ℚ) ≤ c * 2 ^ d := by
    exact (div_le_iff₀ (by positivity)).1 hlower
  have hsQ : (0 : ℚ) ≤ generatedS L := by positivity
  have hprod := mul_le_mul_of_nonneg_right hrat hc.le
  nlinarith [mul_le_mul_of_nonneg_left hm hsQ]

theorem four_s_sq_rho (L : ℕ) (hL : 12 ≤ L) :
    4 * (generatedS L : ℚ) ^ 2 * generatedRho L ≤ 1 := by
  exact CurrentAdditive.DeterministicParameters.four_s_sq_rho L hL

theorem graph_owner (c ζ : ℚ) (L : ℕ) (hc : 0 < c)
    (hcζ : c ≤ (ζ / 256) / 2 ^ 16)
    (hL : 2 * reciprocalCut c + 6 ≤ L) :
    8 * (generatedS L : ℚ) * generatedQ₁ L ≤ ζ * generatedQ₂ L / 16 := by
  have hs := s_le_cN c L hc (by omega)
  have hq : (generatedQ₁ L : ℚ) ≤ generatedN L := by
    exact_mod_cast (Nat.sub_le (generatedS L) 2).trans (s_le_N L (by omega))
  have hN : (0 : ℚ) < generatedN L := by exact_mod_cast N_pos L
  have hN1 : (1 : ℚ) ≤ generatedN L := by exact_mod_cast N_pos L
  have hpow : (generatedN L : ℚ) ^ 2 ≤ generatedQ₂ L := by
    simpa only [generatedQ₂, Nat.cast_pow] using
      pow_le_pow_right₀ hN1 (show 2 ≤ 4 by omega)
  have h8 : 8 * c ≤ ζ / 16 := by norm_num at hcζ; linarith
  have hz : 0 ≤ ζ / 16 := by linarith
  calc
    8 * (generatedS L : ℚ) * generatedQ₁ L ≤
        8 * c * (generatedN L : ℚ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hs
        (by positivity : (0 : ℚ) ≤ generatedQ₁ L),
        mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℚ) ≤ c * generatedN L)]
    _ ≤ (ζ / 16) * (generatedN L : ℚ) ^ 2 :=
      mul_le_mul_of_nonneg_right h8 (sq_nonneg _)
    _ ≤ ζ * generatedQ₂ L / 16 := by
      nlinarith [mul_le_mul_of_nonneg_left hpow hz]

theorem q₂_mul_x (L : ℕ) :
    (generatedQ₂ L : ℚ) * generatedX L = 1 / (generatedN L : ℚ) ^ 4 := by
  unfold generatedQ₂ generatedX
  push_cast
  have hn : (generatedN L : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (N_pos L)
  field_simp

theorem scalar_x_small (L : ℕ) (hL : 6 ≤ L) :
    (generatedQ₂ L : ℚ) * generatedX L ≤ 1 / 10000 ∧
    (generatedS L : ℚ) * generatedX L ≤ 1 / 10000 ∧
    (generatedW L : ℚ) * generatedX L ≤ 1 / 10000 := by
  have hN : (16 : ℚ) ≤ generatedN L := by
    exact_mod_cast (show 2 ^ 4 ≤ 2 ^ L from Nat.pow_le_pow_right (by decide) (by omega))
  have hN1 : (1 : ℚ) ≤ generatedN L := by linarith
  have hN0 : (0 : ℚ) < generatedN L := by linarith
  have hpow : (10000 : ℚ) ≤ (generatedN L : ℚ) ^ 4 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 16) hN 4
    norm_num at hh
    linarith
  have hq : (generatedQ₂ L : ℚ) * generatedX L ≤ 1 / 10000 := by
    rw [q₂_mul_x]
    apply (div_le_iff₀ (pow_pos hN0 _)).2
    linarith
  have hs : (generatedS L : ℚ) ≤ generatedQ₂ L := by
    exact_mod_cast (s_le_N L hL).trans
      (show generatedN L ≤ generatedN L ^ 4 by
        simpa using Nat.pow_le_pow_right (N_pos L) (show 1 ≤ 4 by omega))
  have hw : (generatedW L : ℚ) ≤ generatedQ₂ L := by
    unfold generatedW generatedQ₂
    push_cast
    exact pow_le_pow_right₀ hN1 (by omega)
  have hx : 0 ≤ generatedX L := by unfold generatedX; positivity
  exact ⟨hq, (mul_le_mul_of_nonneg_right hs hx).trans hq,
    (mul_le_mul_of_nonneg_right hw hx).trans hq⟩

theorem eta_transfer (c : ℚ) (L : ℕ) (hc : 0 < c)
    (hL : 2 * reciprocalCut c + 40 ≤ L) :
    2 * (generatedW L : ℚ) ^ 2 * generatedX L ≤
        generatedEta c L / (16 * (255 / 256 : ℚ)) ∧
    4 * (1 / 256 : ℚ) * generatedW L * generatedQ₂ L * generatedX L ≤
        generatedEta c L / 32 := by
  have hs := s_le_cN c L hc (by omega)
  have hN : (32 : ℚ) ≤ generatedN L := by
    exact_mod_cast (show 2 ^ 5 ≤ 2 ^ L from Nat.pow_le_pow_right (by decide) (by omega))
  have hn : (0 : ℚ) < generatedN L := by linarith
  have hn0 : (generatedN L : ℚ) ≠ 0 := ne_of_gt hn
  have hs0 : (0 : ℚ) < generatedS L := by exact_mod_cast s_pos L
  have hη : (1 : ℚ) / generatedN L ≤ generatedEta c L := by
    unfold generatedEta
    apply (div_le_div_iff₀ hn hs0).2
    simpa only [one_mul] using hs
  have heq : 2 * (generatedW L : ℚ) ^ 2 * generatedX L =
      2 / (generatedN L : ℚ) ^ 4 := by
    unfold generatedW generatedX
    push_cast
    field_simp
  have heq2 : 4 * (1 / 256 : ℚ) * generatedW L * generatedQ₂ L * generatedX L =
      1 / (64 * (generatedN L : ℚ) ^ 2) := by
    unfold generatedW generatedQ₂ generatedX
    push_cast
    field_simp
    ring
  constructor
  · rw [heq]
    have hsmall : 2 / (generatedN L : ℚ) ^ 4 ≤
        ((1 : ℚ) / generatedN L) / (16 * (255 / 256 : ℚ)) := by
      apply (div_le_iff₀ (by positivity : (0 : ℚ) < (generatedN L : ℚ) ^ 4)).2
      field_simp
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 32) hN 3
      norm_num at hp
      nlinarith
    exact hsmall.trans (div_le_div_of_nonneg_right hη (by norm_num))
  · rw [heq2]
    have hsmall : 1 / (64 * (generatedN L : ℚ) ^ 2) ≤
        ((1 : ℚ) / generatedN L) / 32 := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℚ) < 64 * (generatedN L : ℚ) ^ 2)
        (by norm_num : (0 : ℚ) < 32)).2
      field_simp
      nlinarith
    exact hsmall.trans (div_le_div_of_nonneg_right hη (by norm_num))

theorem moment_test (L : ℕ) (hL : Nat.ceil C128 + 2004 ≤ L) :
    C128 / (generatedS L : ℚ) ^ 128 ≤ theta (generatedQ L) / 4 := by
  have hC : C128 ≤ (Nat.ceil C128 : ℚ) := Nat.le_ceil _
  have h := CurrentAdditive.DeterministicParameters.moment_guard_rational
    L (Nat.ceil C128) hL
  have hconv : ((Nat.ceil C128 : ℕ) : ℚ) / (generatedS L : ℚ) ^ 128 ≤
      theta (generatedQ L) / 4 := h
  exact (div_le_div_of_nonneg_right hC (by positivity)).trans hconv

theorem incoming_nat_bound (c : ℚ) (L : ℕ)
    (hL : 4 * (reciprocalCut c + toleranceCoefficient c) + 1000 ≤ L) :
    128 * 2 ^ reciprocalCut c * toleranceCoefficient c * generatedS L ^ 5 *
      2 ^ ((9 + generatedQlog L + 63) / 64) ≤ generatedW L := by
  let d := reciprocalCut c
  let K := toleranceCoefficient c
  let u := quarterCeil L
  let t := (9 + generatedQlog L + 63) / 64
  have he : 7 + d + K + 5 * u + t ≤ 2 * L := by
    dsimp [d, K, u, t, quarterCeil, generatedQlog]
    omega
  calc
    128 * 2 ^ d * K * generatedS L ^ 5 * 2 ^ t ≤
        128 * 2 ^ d * 2 ^ K * generatedS L ^ 5 * 2 ^ t := by
      gcongr
      exact coefficient_le_power K
    _ = 2 ^ (7 + d + K + 5 * u + t) := by
      simp only [generatedS, u]
      rw [← pow_mul]
      simp only [pow_add]
      norm_num
      ring
    _ ≤ generatedW L := by
      have hw : generatedW L = 2 ^ (2 * L) := by
        unfold generatedW generatedN
        rw [← pow_mul]
        congr 1
        omega
      rw [hw]
      exact Nat.pow_le_pow_right (by decide) he

theorem incoming_test (c : ℚ) (L : ℕ) (hc : 0 < c)
    (hL : 4 * (reciprocalCut c + toleranceCoefficient c) + 1000 ≤ L) :
    (Kstar (2 * L) (generatedS L) : ℚ) *
      Eexc (generatedQlog L) (generatedEta c L) ≤
      generatedEta c L * generatedW L / 16 := by
  let s := generatedS L
  let K := toleranceCoefficient c
  let t := (9 + generatedQlog L + 63) / 64
  let d := reciprocalCut c
  have hs : (0 : ℚ) < s := by exact_mod_cast s_pos L
  have hE := ebar_half_eta_bound (9 + generatedQlog L) s c hc (s_pos L)
  have harg : generatedEta c L / 2 = c / (2 * s) := by
    unfold generatedEta s
    ring
  have hEQ : (Eexc (generatedQlog L) (generatedEta c L) : ℚ) ≤
      2 * K * (s : ℚ) ^ 2 * (2 : ℚ) ^ t := by
    unfold Eexc e0
    rw [harg]
    have hh := Nat.mul_le_mul_left 2 hE
    have hnat : 2 * ebar (9 + generatedQlog L) (c / (2 * s)) ≤
        2 * K * s ^ 2 * 2 ^ t := by
      convert hh using 1 <;> dsimp [K, t] <;> ring
    exact_mod_cast hnat
  have hLs : L + 1 ≤ s :=
    CurrentAdditive.DeterministicParameters.L_plus_one_le_s L (by omega)
  have hK : (Kstar (2 * L) s : ℚ) ≤ 4 * (s : ℚ) ^ 2 := by
    have hLsQ : (L : ℚ) + 1 ≤ s := by exact_mod_cast hLs
    unfold Kstar
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hLsQ hs.le]
  have hnat := incoming_nat_bound c L hL
  have hnatQ : (128 : ℚ) * 2 ^ d * K * (s : ℚ) ^ 5 * 2 ^ t ≤ generatedW L := by
    exact_mod_cast hnat
  have hcdyad := c_lower_dyadic c hc
  have hcd : (1 : ℚ) ≤ c * 2 ^ d := (div_le_iff₀ (by positivity)).1 hcdyad
  have hmain : (128 : ℚ) * K * (s : ℚ) ^ 5 * 2 ^ t ≤ c * generatedW L := by
    have hp := mul_le_mul_of_nonneg_right hnatQ hc.le
    have hq := mul_le_mul_of_nonneg_right hcd
      (by positivity : (0 : ℚ) ≤ (128 : ℚ) * K * (s : ℚ) ^ 5 * 2 ^ t)
    nlinarith
  have hin : (Kstar (2 * L) s : ℚ) *
      Eexc (generatedQlog L) (generatedEta c L) ≤
      8 * K * (s : ℚ) ^ 4 * 2 ^ t := by
    calc
      _ ≤ (4 * (s : ℚ) ^ 2) * (2 * K * (s : ℚ) ^ 2 * 2 ^ t) :=
        mul_le_mul hK hEQ (by positivity) (by positivity)
      _ = _ := by ring
  change (Kstar (2 * L) s : ℚ) * Eexc (generatedQlog L) (generatedEta c L) ≤ _
  apply hin.trans
  unfold generatedEta
  change 8 * K * (s : ℚ) ^ 4 * 2 ^ t ≤ (c / s) * generatedW L / 16
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 16)).2
  apply (le_div_iff₀ hs).2
  nlinarith

theorem common_tests (c δv ζ : ℚ) (L Δ n m : ℕ)
    (hc : 0 < c) (hcmax : c ≤ min 1 (min δv (ζ / 256)) / 2 ^ 16)
    (hn : n ≤ generatedN L) (hdegree : 2 * m ≤ Δ * n)
    (hL : cutoffLog Δ c ≤ L) :
    CommonTests (generatedInput c L) m δv ζ := by
  have hbase : 4000 ≤ L := by unfold cutoffLog at hL; omega
  have hdel : 2 * reciprocalCut c + 40 ≤ L := by unfold cutoffLog at hL; omega
  have howner : 4 * toleranceCoefficient c + 800 ≤ L := by unfold cutoffLog at hL; omega
  have hin : 4 * (reciprocalCut c + toleranceCoefficient c) + 1000 ≤ L := by
    unfold cutoffLog at hL; omega
  have hmoment : Nat.ceil C128 + 2004 ≤ L := by unfold cutoffLog at hL; omega
  have hwidth : 4 * Δ + 4 ≤ L := by unfold cutoffLog at hL; omega
  have hcζ : c ≤ (ζ / 256) / 2 ^ 16 :=
    hcmax.trans (div_le_div_of_nonneg_right
      ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num))
  have hx := scalar_x_small L (by omega)
  have ht := eta_transfer c L hc hdel
  have hθ := generated_theta_ebar_budget L (by omega)
  have hη : (generatedS L : ℚ) * generatedEta c L = c := by
    unfold generatedEta
    have hs : (generatedS L : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (s_pos L)
    field_simp
  unfold CommonTests
  change 256 ≤ generatedS L ∧ _
  refine ⟨s_ge_256 L (by omega), ?_,
    generated_source_width L n m Δ hn hdegree hwidth,
    four_s_sq_rho L (by omega), graph_owner c ζ L hc hcζ (by omega),
    hx.1, hx.2.1, hx.2.2, ht.1, ?_, ht.2, ?_,
    generated_theta_quarter_ebar_budget L (by omega), moment_test L hmoment,
    generated_Eexc_quarter c L hc howner, incoming_test c L hc hin⟩
  · change (generatedS L : ℚ) * generatedEta c L ≤ _
    simpa only [hη] using hcmax
  · exact (generated_product_exact L).le
  · change ebar (9 + generatedQlog L) 1 ≤ generatedW L / 128
    omega

theorem generated_tests (c δv ζ : ℚ) (L Δ n m : ℕ)
    (hc : 0 < c) (hcmax : c ≤ min 1 (min δv (ζ / 256)) / 2 ^ 16)
    (hn : n ≤ generatedN L) (hdegree : 2 * m ≤ Δ * n)
    (hL : cutoffLog Δ c ≤ L) :
    GeneratedTests c L m δv ζ := by
  have hrest : max 800 (4 * restorationCoefficient c + 800) ≤ L := by
    unfold cutoffLog at hL; omega
  exact ⟨common_tests c δv ζ L Δ n m hc hcmax hn hdegree hL,
    generated_extra_ebar_tests c L hc hrest⟩

theorem source_delta_lower (γ : ℚ) (Δ n m : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hm : n ≤ 2 * m) :
    γ / (4 * Δ) ≤ sourceDeltaV γ Δ n m := by
  have hΔQ : (0 : ℚ) < Δ := by exact_mod_cast hΔ
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hn
  have hmQ : (n : ℚ) ≤ 2 * m := by exact_mod_cast hm
  unfold sourceDeltaV
  apply (div_le_div_iff₀ (by positivity : (0 : ℚ) < 4 * Δ)
    (by positivity : (0 : ℚ) < 2 * Δ * n)).2
  nlinarith [mul_le_mul_of_nonneg_left hmQ (by positivity : (0 : ℚ) ≤ 2 * γ * Δ)]

/-- A cutoff depending only on the fixed graph promise and deletion constant.
For every larger public exponent, every promised graph with `n ≤ 2^L`
passes the literal current-source tests. No n/m-dependent cutoff is used. -/
theorem all_large_sources (γ c : ℚ) (Δ : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hc : 0 < c)
    (hcmax : c ≤ min 1 (min (γ / (4 * Δ)) (sourceZeta γ / 256)) / 2 ^ 16) :
    ∀ (L n m : ℕ), cutoffLog Δ c ≤ L → 0 < n →
      n ≤ generatedN L → n ≤ 2 * m → 2 * m ≤ Δ * n →
      GeneratedTests c L m (sourceDeltaV γ Δ n m) (sourceZeta γ) := by
  intro L n m hL hn hnN hlow hdegree
  have hd := source_delta_lower γ Δ n m hγ hΔ hn hlow
  have hsmall : c ≤ min 1 (min (sourceDeltaV γ Δ n m) (sourceZeta γ / 256)) / 2 ^ 16 := by
    apply hcmax.trans
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact min_le_min_left _ (min_le_min_right _ hd)
  exact generated_tests c _ _ L Δ n m hc hsmall hnN hdegree hL

/-- All sufficiently large literal Boolean checks return true. -/
theorem all_large_sources_pass (γ c : ℚ) (Δ : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hc : 0 < c)
    (hcmax : c ≤ min 1 (min (γ / (4 * Δ)) (sourceZeta γ / 256)) / 2 ^ 16)
    (L n m : ℕ) (hL : cutoffLog Δ c ≤ L) (hn : 0 < n)
    (hnN : n ≤ generatedN L) (hlow : n ≤ 2 * m) (hdegree : 2 * m ≤ Δ * n) :
    generatedPass c L m (sourceDeltaV γ Δ n m) (sourceZeta γ) = true := by
  exact (generatedPass_iff ..).2
    (all_large_sources γ c Δ hγ hΔ hc hcmax L n m hL hn hnN hlow hdegree)

#print axioms c_lower_dyadic
#print axioms s_le_cN
#print axioms graph_owner
#print axioms q₂_mul_x
#print axioms scalar_x_small
#print axioms eta_transfer
#print axioms moment_test
#print axioms incoming_nat_bound
#print axioms incoming_test
#print axioms common_tests
#print axioms generated_tests
#print axioms source_delta_lower
#print axioms all_large_sources
#print axioms all_large_sources_pass

end GeneratedCutoff
