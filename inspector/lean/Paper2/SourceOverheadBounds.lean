import Paper2.SourceQBounds
import Paper2.RestorationWidthSchedule

/-!
# Finite logarithmic overhead for the actual public source schedule

The dyadic `Q` is the exact rational-source choice, not an arbitrary power
of two supplied with a size certificate. All bounds remain finite.
-/

namespace Paper2.SourceOverheadBounds

open SourceProfileParameters SourceRationalScheduleScratch
  SourceDensityScheduleScratch RestorationWidthScheduleScratch

variable {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]

def actualQ (L : ℕ) (γ : ℚ) (Δ : ℕ) : ℕ :=
  SourceRationalScheduleScratch.publicQ (V := V) (E := E) L γ Δ

def q (L : ℕ) (γ : ℚ) (Δ : ℕ) : ℕ :=
  Nat.clog 2 (actualQ (V := V) (E := E) L γ Δ)

def coefficient (Δ : ℕ) (γ : ℚ) : ℕ :=
  Nat.ceil ((2560 * 65536 : ℚ) / etaConstant Δ γ)

def coefficientExponent (Δ : ℕ) (γ : ℚ) : ℕ :=
  Nat.clog 2 (max 1 (coefficient Δ γ))

omit [Nonempty V] in
theorem actualQ_pow (L : ℕ) (γ : ℚ) (Δ : ℕ) :
    actualQ (V := V) (E := E) L γ Δ =
      2 ^ q (V := V) (E := E) L γ Δ := by
  change RestorationPublicQScratch.publicQ L
      (SourceRationalScheduleScratch.deltaU (V := V) (E := E) L γ Δ) =
    2 ^ Nat.clog 2 (RestorationPublicQScratch.publicQ L
      (SourceRationalScheduleScratch.deltaU (V := V) (E := E) L γ Δ))
  unfold RestorationPublicQScratch.publicQ SourcePadding.powTwoCeil
  rw [Nat.clog_pow 2 _ (by decide)]

theorem source_width_le (L : ℕ) :
    SourceProfileParameters.width L ≤
      65536 * 2 ^ RestorationWidthScheduleScratch.ell L := by
  have hp : 65536 * (L + 1) ≤
      2 ^ (16 + RestorationWidthScheduleScratch.ell L) := by
    have hl : L + 1 ≤ 2 ^ RestorationWidthScheduleScratch.ell L :=
      Nat.le_pow_clog (by decide) _
    simpa [pow_add] using Nat.mul_le_mul_left 65536 hl
  have he := SourceProfileParameters.exponent_minimal L _ hp
  calc
    SourceProfileParameters.width L = 2 ^ SourceProfileParameters.exponent L := rfl
    _ ≤ 2 ^ (16 + RestorationWidthScheduleScratch.ell L) :=
      pow_le_pow_right₀ (by omega) he
    _ = 65536 * 2 ^ RestorationWidthScheduleScratch.ell L := by
      norm_num [pow_add]

theorem source_exponent_le (L : ℕ) :
    SourceProfileParameters.exponent L ≤
      16 + RestorationWidthScheduleScratch.ell L := by
  have hl : L + 1 ≤ 2 ^ RestorationWidthScheduleScratch.ell L :=
    Nat.le_pow_clog (by decide) _
  have hp : 65536 * (L + 1) ≤
      2 ^ (16 + RestorationWidthScheduleScratch.ell L) := by
    simpa [pow_add] using Nat.mul_le_mul_left 65536 hl
  exact SourceProfileParameters.exponent_minimal L _ hp

private theorem source_factor_le (L : ℕ) :
    L * SourceProfileParameters.width L *
      SourceRationalScheduleScratch.restorationWidth L ≤
      65536 * 2 ^ (2 * RestorationWidthScheduleScratch.ell L +
        RestorationWidthScheduleScratch.depth L) := by
  have hl : L ≤ 2 ^ RestorationWidthScheduleScratch.ell L := by
    have h := Nat.le_pow_clog (by decide : 1 < 2) (L + 1)
    unfold RestorationWidthScheduleScratch.ell
    omega
  have hs := source_width_le L
  calc
    L * SourceProfileParameters.width L *
        SourceRationalScheduleScratch.restorationWidth L ≤
      (2 ^ RestorationWidthScheduleScratch.ell L) *
        (65536 * 2 ^ RestorationWidthScheduleScratch.ell L) *
        (2 ^ RestorationWidthScheduleScratch.depth L) := by
          gcongr
          rfl
    _ = 65536 * 2 ^ (2 * RestorationWidthScheduleScratch.ell L +
        RestorationWidthScheduleScratch.depth L) := by
          rw [show 2 * RestorationWidthScheduleScratch.ell L =
            RestorationWidthScheduleScratch.ell L +
              RestorationWidthScheduleScratch.ell L by omega,
            pow_add, pow_add]
          ring

theorem q_upper (edge : E → Bool → V) (L Δ : ℕ) (γ : ℚ)
    (hL : 1 ≤ L) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    q (V := V) (E := E) L γ Δ ≤
      RestorationWidthScheduleScratch.depth L +
        2 * RestorationWidthScheduleScratch.ell L +
        coefficientExponent Δ γ := by
  let c := etaConstant Δ γ
  let A := coefficient Δ γ
  let t := 2 * RestorationWidthScheduleScratch.ell L +
    RestorationWidthScheduleScratch.depth L
  have hc : 0 < c := etaConstant_pos Δ γ hΔ hγ
  have hA : ((2560 * 65536 : ℚ) / c) ≤ (A : ℚ) := by
    exact Nat.le_ceil _
  have hfactor := source_factor_le L
  have hQ := SourceQBounds.publicQ_graph_upper (V := V) (E := E)
    edge L Δ hL γ hγ hΔ hincident hdegree
  have hQrat : (actualQ (V := V) (E := E) L γ Δ : ℚ) <
      (A : ℚ) * ((2 ^ t : ℕ) : ℚ) := by
    calc
      _ < (2560 * L * SourceProfileParameters.width L *
          SourceRationalScheduleScratch.restorationWidth L : ℚ) / c := hQ
      _ = (2560 / c : ℚ) *
          (L * SourceProfileParameters.width L *
            SourceRationalScheduleScratch.restorationWidth L : ℕ) := by
            push_cast
            ring
      _ ≤ (2560 / c : ℚ) * (65536 * 2 ^ t : ℕ) := by
            gcongr
      _ = ((2560 * 65536 : ℚ) / c) * ((2 ^ t : ℕ) : ℚ) := by
            push_cast
            ring
      _ ≤ (A : ℚ) * ((2 ^ t : ℕ) : ℚ) := by
            gcongr
  have hQnat : actualQ (V := V) (E := E) L γ Δ ≤ A * 2 ^ t := by
    exact_mod_cast hQrat.le
  have hApow : A ≤ 2 ^ coefficientExponent Δ γ := by
    exact (le_max_right 1 A).trans (Nat.le_pow_clog (by decide) _)
  have hpow : actualQ (V := V) (E := E) L γ Δ ≤
      2 ^ (coefficientExponent Δ γ + t) := by
    calc
      _ ≤ A * 2 ^ t := hQnat
      _ ≤ 2 ^ coefficientExponent Δ γ * 2 ^ t := by gcongr
      _ = 2 ^ (coefficientExponent Δ γ + t) := (pow_add 2 _ _).symm
  have hq : q (V := V) (E := E) L γ Δ ≤ coefficientExponent Δ γ + t :=
    (Nat.clog_le_iff_le_pow (by decide)).2 hpow
  dsimp [t] at hq
  omega

theorem b_upper (edge : E → Bool → V) (L Δ : ℕ) (γ : ℚ)
    (hL : 1 ≤ L) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    RestorationCoverParameters.b (actualQ (V := V) (E := E) L γ Δ) ≤
      RestorationWidthScheduleScratch.depth L +
        2 * RestorationWidthScheduleScratch.ell L +
        coefficientExponent Δ γ + 9 := by
  have hpow : 320 * actualQ (V := V) (E := E) L γ Δ ≤
      2 ^ (q (V := V) (E := E) L γ Δ + 9) := by
    rw [actualQ_pow]
    rw [pow_add]
    norm_num
    omega
  have hb : RestorationCoverParameters.b
      (actualQ (V := V) (E := E) L γ Δ) ≤
      q (V := V) (E := E) L γ Δ + 9 :=
    (Nat.clog_le_iff_le_pow (by decide)).2 hpow
  have hq := q_upper edge L Δ γ hL hγ hΔ hincident hdegree
  exact hb.trans (by omega)

theorem q_lower (L Δ : ℕ) (γ : ℚ)
    (hL : 1 ≤ L) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hE : 0 < Fintype.card E) :
    RestorationWidthScheduleScratch.depth L ≤
      q (V := V) (E := E) L γ Δ := by
  let η := SourceRationalScheduleScratch.eta (V := V) (E := E) L γ Δ
  let w := SourceRationalScheduleScratch.restorationWidth L
  let Q := actualQ (V := V) (E := E) L γ Δ
  have hη : η ≤ 1 :=
    (SourceRationalScheduleScratch.eta_le_inverse_65536
      (V := V) (E := E) L γ Δ).trans (by norm_num)
  have hw : (0 : ℚ) < 16 * w := by
    dsimp [w, SourceRationalScheduleScratch.restorationWidth]
    positivity
  have hmeet := RestorationPublicQScratch.publicQ_meets L
    (SourceRationalScheduleScratch.deltaU (V := V) (E := E) L γ Δ)
    (SourceRationalScheduleScratch.deltaU_pos
      (V := V) (E := E) L γ Δ hγ hΔ hE)
  have hquot : (((80 * L : ℕ) : ℚ)) ≤ (Q : ℚ) * η / (16 * w) := by
    change (((80 * L : ℕ) : ℚ)) ≤ (Q : ℚ) * (η / (16 * w)) at hmeet
    calc
      _ ≤ (Q : ℚ) * (η / (16 * w)) := hmeet
      _ = (Q : ℚ) * η / (16 * w) := by ring
  have hprod : (((80 * L : ℕ) : ℚ)) * (16 * w) ≤ (Q : ℚ) * η :=
    (le_div_iff₀ hw).mp hquot
  have hQpos : (0 : ℚ) ≤ Q := by positivity
  have hQη : (Q : ℚ) * η ≤ Q := by
    have hm := mul_le_mul_of_nonneg_left hη hQpos
    linarith
  have hw1 : (1 : ℚ) ≤ w := by
    exact_mod_cast (show 0 < w by dsimp [w, SourceRationalScheduleScratch.restorationWidth]; positivity)
  have hLrat : (1 : ℚ) ≤ L := by exact_mod_cast hL
  have h80 : (1 : ℚ) ≤ ((80 * L : ℕ) : ℚ) := by
    exact_mod_cast (show 1 ≤ 80 * L by omega)
  have hweight : (w : ℚ) ≤ (((80 * L : ℕ) : ℚ)) * (16 * w) := by
    nlinarith
  have hQwrat : (w : ℚ) ≤ Q := hweight.trans (hprod.trans hQη)
  have hQw : w ≤ Q := by exact_mod_cast hQwrat
  have hc := Nat.clog_mono_right 2 hQw
  have hwdef : w = 2 ^ RestorationWidthScheduleScratch.depth L := rfl
  rw [hwdef, Nat.clog_pow 2 (RestorationWidthScheduleScratch.depth L)
    (by decide)] at hc
  exact hc

/-- The exact finite one-step overhead from frozen v12, with the actual
scheduled dyadic exponent `q=clog₂(Q)`. -/
def overhead (L Δ : ℕ) (γ : ℚ) : ℕ :=
  SourceProfileParameters.exponent L +
    SourceProfileParameters.outerExponent L +
    SourceProfileParameters.exponent L +
    RestorationWidthScheduleScratch.depth L +
    q (V := V) (E := E) L γ Δ

theorem overhead_bounds (edge : E → Bool → V) (L Δ : ℕ) (γ : ℚ)
    (hL : 1 ≤ L) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ) :
    L + 2 * RestorationWidthScheduleScratch.depth L ≤
      overhead (V := V) (E := E) L Δ γ ∧
    overhead (V := V) (E := E) L Δ γ ≤
      L + 2 * RestorationWidthScheduleScratch.depth L +
        6 * RestorationWidthScheduleScratch.ell L + 64 +
        coefficientExponent Δ γ := by
  have hE := SourceDensityScheduleScratch.edges_pos edge hincident
  have hqlo := q_lower (V := V) (E := E) L Δ γ hL hγ hΔ hE
  have hqhi := q_upper (V := V) (E := E) edge L Δ γ
    hL hγ hΔ hincident hdegree
  have ha := source_exponent_le L
  unfold overhead SourceProfileParameters.outerExponent
  constructor <;> omega

end Paper2.SourceOverheadBounds

#print axioms Paper2.SourceOverheadBounds.actualQ_pow
#print axioms Paper2.SourceOverheadBounds.q_upper
#print axioms Paper2.SourceOverheadBounds.b_upper
#print axioms Paper2.SourceOverheadBounds.q_lower
#print axioms Paper2.SourceOverheadBounds.overhead_bounds
