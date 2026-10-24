import Paper2.SourceProfileParameters
import Paper2.SourceRationalSchedule

/-!
Two graph-independent source-size checks from the exact v12 Appendix C
schedule, with an explicit dyadic threshold for the rational gap constant.
-/

namespace Paper2.SourceSizeCutoffScratch

open SourceProfileParameters

/-- The least binary exponent that dominates `3072/gamma` after a rational
ceiling. `max 1` totalizes the definition outside the positive-gamma domain. -/
def witnessCutoff (γ : ℚ) : ℕ :=
  Nat.clog 2 (max 1 (Nat.ceil ((3072 : ℚ) / γ)))

/-- A deliberately conservative, graph-only common cutoff. -/
def sourceCutoff (Δ : ℕ) (γ : ℚ) : ℕ :=
  max (6 * Δ) (witnessCutoff γ)

def sizeThreshold (Δ : ℕ) (γ : ℚ) : ℕ :=
  2 ^ sourceCutoff Δ γ

theorem width_degree_guard (L Δ : ℕ) (hL : 6 * Δ ≤ L) :
    6 * Δ ≤ width L := by
  have h := width_admissible L
  omega

private theorem witness_power_guard (L : ℕ) (γ : ℚ) (hγ : 0 < γ)
    (hL : witnessCutoff γ ≤ L) :
    (3072 : ℚ) ≤ γ * (2 ^ L : ℕ) := by
  let W := Nat.ceil ((3072 : ℚ) / γ)
  have hceil : (3072 : ℚ) / γ ≤ W := Nat.le_ceil _
  have hW : W ≤ 2 ^ witnessCutoff γ := by
    unfold witnessCutoff
    exact (le_max_right 1 W).trans (Nat.le_pow_clog (by decide) _)
  have hpow : 2 ^ witnessCutoff γ ≤ 2 ^ L :=
    Nat.pow_le_pow_right (by decide) hL
  have hratio : (3072 : ℚ) / γ ≤ (2 ^ L : ℕ) :=
    hceil.trans (by exact_mod_cast hW.trans hpow)
  simpa only [mul_comm] using (div_le_iff₀ hγ).mp hratio

/-- The actual source `q₁=s-2`, `q₂=2^L*s²`, and
`ζ=gamma/24` satisfy the witness-coordinate check. -/
theorem witness_coordinate_guard (L : ℕ) (γ : ℚ) (hγ : 0 < γ)
    (hL : witnessCutoff γ ≤ L) :
    ((8 * width L * (width L - 2) : ℕ) : ℚ) ≤
      SourceRationalScheduleScratch.witnessDensity γ * outerWidth L / 16 := by
  let s := width L
  have hpower := witness_power_guard L γ hγ hL
  have hcoeff : (8 : ℚ) ≤ γ * (2 ^ L : ℕ) / 384 := by
    linarith only [hpower]
  have hs2 : (0 : ℚ) ≤ (s ^ 2 : ℕ) := by
    exact_mod_cast Nat.zero_le (s ^ 2)
  have hmul := mul_le_mul_of_nonneg_right hcoeff hs2
  have hsub : 8 * s * (s - 2) ≤ 8 * s ^ 2 := by
    have hle := Nat.sub_le s 2
    calc
      8 * s * (s - 2) ≤ 8 * s * s := Nat.mul_le_mul_left (8 * s) hle
      _ = 8 * s ^ 2 := by ring
  calc
    ((8 * s * (s - 2) : ℕ) : ℚ) ≤ (8 * s ^ 2 : ℕ) := by exact_mod_cast hsub
    _ = (8 : ℚ) * (s ^ 2 : ℕ) := by push_cast; ring
    _ ≤ (γ * (2 ^ L : ℕ) / 384) * (s ^ 2 : ℕ) := hmul
    _ = SourceRationalScheduleScratch.witnessDensity γ * outerWidth L / 16 := by
      rw [outerWidth_eq]
      simp only [SourceRationalScheduleScratch.witnessDensity]
      push_cast
      dsimp [s]
      ring

theorem both_source_size_guards (L Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hL : sourceCutoff Δ γ ≤ L) :
    6 * Δ ≤ width L ∧
    ((8 * width L * (width L - 2) : ℕ) : ℚ) ≤
      SourceRationalScheduleScratch.witnessDensity γ * outerWidth L / 16 := by
  constructor
  · exact width_degree_guard L Δ ((le_max_left _ _).trans hL)
  · exact witness_coordinate_guard L γ hγ ((le_max_right _ _).trans hL)

/-- A source-size threshold implies both checks at the actual public
`L=clog₂(|V|)`. No assumption on a colouring or the final count is used. -/
theorem checks_at_source_size (n Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ)
    (hsize : sizeThreshold Δ γ ≤ n) :
    6 * Δ ≤ width (Nat.clog 2 n) ∧
    ((8 * width (Nat.clog 2 n) * (width (Nat.clog 2 n) - 2) : ℕ) : ℚ) ≤
      SourceRationalScheduleScratch.witnessDensity γ *
        outerWidth (Nat.clog 2 n) / 16 := by
  have hcut : sourceCutoff Δ γ ≤ Nat.clog 2 n := by
    have hc := Nat.clog_mono_right 2 hsize
    simpa only [sizeThreshold, Nat.clog_pow 2 (sourceCutoff Δ γ) (by decide)] using hc
  exact both_source_size_guards _ Δ γ hγ hcut

theorem checks_at_graph_card {V : Type*} [Fintype V]
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ)
    (hsize : sizeThreshold Δ γ ≤ Fintype.card V) :
    let L := Nat.clog 2 (Fintype.card V)
    6 * Δ ≤ width L ∧
    ((8 * width L * (width L - 2) : ℕ) : ℚ) ≤
      SourceRationalScheduleScratch.witnessDensity γ * outerWidth L / 16 := by
  dsimp
  exact checks_at_source_size (Fintype.card V) Δ γ hγ hsize


end Paper2.SourceSizeCutoffScratch

