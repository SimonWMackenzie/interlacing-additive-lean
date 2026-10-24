import Paper2.SourceOverheadBounds

/-! Private v27 Appendix C overhead check. This deliberately uses the new
quartic restoration width; none of the v12 all-large checks are imported as
facts about that width. -/

namespace CurrentAdditive.RandomizedSchedule

open Paper2

open SourceProfileParameters SourceDensityScheduleScratch
  SourceRationalScheduleScratch RestorationPublicQScratch
  RestorationWidthScheduleScratch

variable {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]

def width27 (L : ℕ) : ℕ := 2 ^ (4 * ell L)

def deltaU27 (L : ℕ) (γ : ℚ) (Δ : ℕ) : ℚ :=
  SourceRationalScheduleScratch.eta (V := V) (E := E) L γ Δ / (16 * width27 L)

def Q27 (L : ℕ) (γ : ℚ) (Δ : ℕ) : ℕ :=
  RestorationPublicQScratch.publicQ L (deltaU27 (V := V) (E := E) L γ Δ)

def q27 (L : ℕ) (γ : ℚ) (Δ : ℕ) : ℕ :=
  Nat.clog 2 (Q27 (V := V) (E := E) L γ Δ)

omit [Nonempty V] in
theorem Q27_dyadic (L : ℕ) (γ : ℚ) (Δ : ℕ) :
    Q27 (V := V) (E := E) L γ Δ =
      2 ^ q27 (V := V) (E := E) L γ Δ := by
  change RestorationPublicQScratch.publicQ L
      (deltaU27 (V := V) (E := E) L γ Δ) =
    2 ^ Nat.clog 2 (RestorationPublicQScratch.publicQ L
      (deltaU27 (V := V) (E := E) L γ Δ))
  unfold RestorationPublicQScratch.publicQ SourcePadding.powTwoCeil
  rw [Nat.clog_pow 2 _ (by decide)]

def coefficient27 (Δ : ℕ) (γ : ℚ) : ℕ :=
  Nat.ceil ((2560 * 65536 : ℚ) / etaConstant Δ γ)

def coefficientExponent27 (Δ : ℕ) (γ : ℚ) : ℕ :=
  Nat.clog 2 (max 1 (coefficient27 Δ γ))

private theorem deltaU27_pos (L : ℕ) (γ : ℚ) (Δ : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hE : 0 < Fintype.card E) :
    0 < deltaU27 (V := V) (E := E) L γ Δ := by
  unfold deltaU27
  have hη := SourceRationalScheduleScratch.eta_pos (V := V) (E := E)
    L γ Δ hγ hΔ hE
  have hw : 0 < width27 L := by unfold width27; positivity
  positivity

private theorem threshold27_ge_one (L : ℕ) (hL : 1 ≤ L) (γ : ℚ) (Δ : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hE : 0 < Fintype.card E) :
    1 ≤ RestorationPublicQScratch.threshold L
      (deltaU27 (V := V) (E := E) L γ Δ) := by
  have hδ := deltaU27_pos (V := V) (E := E) L γ Δ hγ hΔ hE
  have hη := SourceRationalScheduleScratch.eta_le_inverse_65536
    (V := V) (E := E) L γ Δ
  have hw : (1 : ℚ) ≤ width27 L := by
    exact_mod_cast (show 0 < width27 L by unfold width27; positivity)
  have hδle : deltaU27 (V := V) (E := E) L γ Δ ≤ 1 := by
    unfold deltaU27
    have hd : (0 : ℚ) < 16 * width27 L := by positivity
    apply (div_le_iff₀ hd).2
    nlinarith
  unfold RestorationPublicQScratch.threshold
  apply (le_div_iff₀ hδ).2
  have hL' : (1 : ℚ) ≤ ((80 * L : ℕ) : ℚ) := by
    exact_mod_cast (show 1 ≤ 80 * L by omega)
  linarith

private theorem threshold27_graph_upper (edge : E → Bool → V)
    (L Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    RestorationPublicQScratch.threshold L
      (deltaU27 (V := V) (E := E) L γ Δ) ≤
      (1280 * L * SourceProfileParameters.width L * width27 L : ℚ) /
        etaConstant Δ γ := by
  let c := etaConstant Δ γ
  let s := SourceProfileParameters.width L
  let w := width27 L
  let η := SourceRationalScheduleScratch.eta (V := V) (E := E) L γ Δ
  let δ := deltaU27 (V := V) (E := E) L γ Δ
  have hc : 0 < c := etaConstant_pos Δ γ hΔ hγ
  have hs : (0 : ℚ) < s := by
    exact_mod_cast (show 0 < s by dsimp [s, SourceProfileParameters.width]; positivity)
  have hw : (0 : ℚ) < w := by
    exact_mod_cast (show 0 < w by dsimp [w, width27]; positivity)
  have hE := SourceDensityScheduleScratch.edges_pos edge hincident
  have hδ : 0 < δ := deltaU27_pos (V := V) (E := E) L γ Δ hγ hΔ hE
  have hη : c / s ≤ η :=
    (SourceDensityScheduleScratch.eta_bounds edge L Δ γ
      hγ hΔ hincident hdegree).1
  have hcs : c ≤ η * s := by
    have hh := (div_le_iff₀ hs).1 hη
    nlinarith
  have hδeq : δ = η / (16 * w) := rfl
  have hcd : c ≤ 16 * s * w * δ := by
    rw [hδeq]
    field_simp
    nlinarith [hcs]
  have hprod : (80 * L : ℚ) * c ≤
      (1280 * L * s * w : ℚ) * δ := by
    have h80 : (0 : ℚ) ≤ (80 * L : ℕ) := by
      exact_mod_cast Nat.zero_le (80 * L)
    have hh := mul_le_mul_of_nonneg_left hcd h80
    nlinarith [hh]
  unfold RestorationPublicQScratch.threshold
  apply (div_le_div_iff₀ hδ hc).2
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hprod

private theorem Q27_graph_upper (edge : E → Bool → V)
    (L Δ : ℕ) (γ : ℚ) (hL : 1 ≤ L) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    (Q27 (V := V) (E := E) L γ Δ : ℚ) <
      (2560 * L * SourceProfileParameters.width L * width27 L : ℚ) /
        etaConstant Δ γ := by
  have hE := SourceDensityScheduleScratch.edges_pos edge hincident
  have hδ := deltaU27_pos (V := V) (E := E) L γ Δ hγ hΔ hE
  have hround := RestorationPublicQScratch.publicQ_lt_twice_max L hL
    (deltaU27 (V := V) (E := E) L γ Δ) hδ
  rw [max_eq_right (threshold27_ge_one (V := V) (E := E)
    L hL γ Δ hγ hΔ hE)] at hround
  have hgraph := threshold27_graph_upper edge L Δ γ hγ hΔ
    hincident hdegree
  calc
    _ < 2 * RestorationPublicQScratch.threshold L
      (deltaU27 (V := V) (E := E) L γ Δ) := hround
    _ ≤ 2 * ((1280 * L * SourceProfileParameters.width L * width27 L : ℚ) /
      etaConstant Δ γ) := by
        exact mul_le_mul_of_nonneg_left hgraph (by norm_num)
    _ = _ := by ring

private theorem factor27_le (L : ℕ) :
    L * SourceProfileParameters.width L * width27 L ≤
      65536 * 2 ^ (6 * ell L) := by
  have hl : L ≤ 2 ^ ell L := by
    have h := Nat.le_pow_clog (by decide : 1 < 2) (L + 1)
    unfold ell
    omega
  have hs := SourceOverheadBounds.source_width_le L
  calc
    L * SourceProfileParameters.width L * width27 L ≤
      (2 ^ ell L) * (65536 * 2 ^ ell L) * (2 ^ (4 * ell L)) := by
        gcongr
        rfl
    _ = 65536 * 2 ^ (6 * ell L) := by
      rw [show 6 * ell L = ell L + ell L + 4 * ell L by omega,
        pow_add, pow_add]
      ring

theorem q27_upper (edge : E → Bool → V) (L Δ : ℕ) (γ : ℚ)
    (hL : 1 ≤ L) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    q27 (V := V) (E := E) L γ Δ ≤
      6 * ell L + coefficientExponent27 Δ γ := by
  let c := etaConstant Δ γ
  let A := coefficient27 Δ γ
  let t := 6 * ell L
  have hc : 0 < c := etaConstant_pos Δ γ hΔ hγ
  have hA : ((2560 * 65536 : ℚ) / c) ≤ (A : ℚ) := Nat.le_ceil _
  have hfactor := factor27_le L
  have hQ := Q27_graph_upper (V := V) (E := E)
    edge L Δ γ hL hγ hΔ hincident hdegree
  have hQrat : (Q27 (V := V) (E := E) L γ Δ : ℚ) <
      (A : ℚ) * ((2 ^ t : ℕ) : ℚ) := by
    calc
      _ < (2560 * L * SourceProfileParameters.width L * width27 L : ℚ) / c := hQ
      _ = (2560 / c : ℚ) * (L * SourceProfileParameters.width L * width27 L : ℕ) := by
        push_cast; ring
      _ ≤ (2560 / c : ℚ) * (65536 * 2 ^ t : ℕ) := by gcongr
      _ = ((2560 * 65536 : ℚ) / c) * ((2 ^ t : ℕ) : ℚ) := by
        push_cast; ring
      _ ≤ (A : ℚ) * ((2 ^ t : ℕ) : ℚ) := by gcongr
  have hQnat : Q27 (V := V) (E := E) L γ Δ ≤ A * 2 ^ t := by
    exact_mod_cast hQrat.le
  have hApow : A ≤ 2 ^ coefficientExponent27 Δ γ :=
    (le_max_right 1 A).trans (Nat.le_pow_clog (by decide) _)
  have hpow : Q27 (V := V) (E := E) L γ Δ ≤
      2 ^ (coefficientExponent27 Δ γ + t) := by
    calc
      _ ≤ A * 2 ^ t := hQnat
      _ ≤ 2 ^ coefficientExponent27 Δ γ * 2 ^ t := by gcongr
      _ = 2 ^ (coefficientExponent27 Δ γ + t) := (pow_add 2 _ _).symm
  have hq : q27 (V := V) (E := E) L γ Δ ≤
      coefficientExponent27 Δ γ + t :=
    (Nat.clog_le_iff_le_pow (by decide)).2 hpow
  dsimp [t] at hq
  omega

def overhead27 (L Δ : ℕ) (γ : ℚ) : ℕ :=
  SourceProfileParameters.exponent L +
    SourceProfileParameters.outerExponent L +
    SourceProfileParameters.exponent L +
    4 * ell L + q27 (V := V) (E := E) L γ Δ

omit [Nonempty V] in
theorem overhead27_exact (L Δ : ℕ) (γ : ℚ) :
    overhead27 (V := V) (E := E) L Δ γ =
      L + 4 * SourceProfileParameters.exponent L +
        4 * ell L + q27 (V := V) (E := E) L γ Δ := by
  unfold overhead27 SourceProfileParameters.outerExponent
  omega

theorem overhead27_bounds (edge : E → Bool → V) (L Δ : ℕ) (γ : ℚ)
    (hL : 1 ≤ L) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    L ≤ overhead27 (V := V) (E := E) L Δ γ ∧
    overhead27 (V := V) (E := E) L Δ γ ≤
      L + 14 * ell L + 64 + coefficientExponent27 Δ γ := by
  have hq := q27_upper (V := V) (E := E) edge L Δ γ
    hL hγ hΔ hincident hdegree
  have ha := SourceOverheadBounds.source_exponent_le L
  unfold overhead27 SourceProfileParameters.outerExponent
  constructor <;> omega

#print axioms q27_upper
#print axioms Q27_dyadic
#print axioms overhead27_exact
#print axioms overhead27_bounds

end CurrentAdditive.RandomizedSchedule
