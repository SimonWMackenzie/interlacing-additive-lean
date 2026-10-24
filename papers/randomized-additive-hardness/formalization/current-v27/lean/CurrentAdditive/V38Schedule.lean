import Mathlib

/-! Arithmetic and executable tests for the two literal schedules in v38,
Appendix `parameters.tex`. This private component does not construct a source,
successor, printer, or a semantic StepInputs witness. -/

namespace V38Schedule

def ell (L : ℕ) : ℕ := Nat.clog 2 (L + 1)
def quarterCeil (L : ℕ) : ℕ := (L + 3) / 4

def fullS (L : ℕ) : ℕ := 2 ^ (16 + ell L)
def fullQ₁ (L : ℕ) : ℕ := fullS L - 2
def fullQ₂ (L : ℕ) : ℕ := 2 ^ L * (fullS L) ^ 2
def fullW (L : ℕ) : ℕ := 2 ^ (8 * ell L)
def fullQ (L : ℕ) : ℕ := (fullW L) ^ 2
def fullRho (L : ℕ) : ℚ := 1 / (2 ^ L : ℚ)
def fullX (L : ℕ) : ℚ := 1 / (2 ^ (10 * L) : ℚ)
def fullEta (c : ℚ) (L : ℕ) : ℚ := c / (2 ^ 16 * fullS L)

def sourceDeltaV (γ : ℚ) (Δ n m : ℕ) : ℚ := γ * m / (2 * Δ * n)
def sourceZeta (γ : ℚ) : ℚ := γ / 24
def fullConstant (γ : ℚ) (Δ n m : ℕ) : ℚ :=
  min 1 (min (sourceDeltaV γ Δ n m) (sourceZeta γ / 256))

def generatedN (L : ℕ) : ℕ := 2 ^ L
def generatedS (L : ℕ) : ℕ := 2 ^ quarterCeil L
def generatedQ₁ (L : ℕ) : ℕ := generatedS L - 2
def generatedQ₂ (L : ℕ) : ℕ := (generatedN L) ^ 4
def generatedW (L : ℕ) : ℕ := (generatedN L) ^ 2
def generatedQ (L : ℕ) : ℕ := (generatedN L) ^ 6
def generatedRho (L : ℕ) : ℚ := 1 / (generatedN L : ℚ)
def generatedX (L : ℕ) : ℚ := 1 / ((generatedN L : ℚ) ^ 8)
def generatedEta (cDel : ℚ) (L : ℕ) : ℚ := cDel / generatedS L

/-- The exact dyadic ceiling used for the common conditioning budget.
The argument `b` denotes a dyadic input `2⁻ᵇ`. -/
def ebar (b : ℕ) (τ : ℚ) : ℕ :=
  Nat.ceil ((2 ^ 90 : ℚ) / τ ^ 2 * (2 ^ ((b + 63) / 64) : ℚ))

def theta (Q : ℕ) : ℚ := 1 / (512 * Q : ℚ)
def deltaU (η : ℚ) (w : ℕ) : ℚ := η / (16 * w)
def e0 (qlog : ℕ) (η : ℚ) : ℕ := ebar (9 + qlog) (η / 2)
def Eexc (qlog : ℕ) (η : ℚ) : ℕ := 2 * e0 qlog η
def Kstar (wlog s : ℕ) : ℕ := 2 * (wlog + 2) * s
def C128 : ℚ := ((2 ^ 14 : ℚ) / ((255 / 256 : ℚ) - 1 / 2) ^ 2) ^ 128

def fullQlog (L : ℕ) : ℕ := 16 * ell L
def generatedQlog (L : ℕ) : ℕ := 6 * L

theorem fullW_pow (L : ℕ) : fullW L = 2 ^ (8 * ell L) := rfl

theorem fullQ_pow (L : ℕ) : fullQ L = 2 ^ fullQlog L := by
  simp only [fullQ, fullW, fullQlog]
  rw [← pow_mul]
  congr 1
  omega

theorem generatedQ_pow (L : ℕ) : generatedQ L = 2 ^ generatedQlog L := by
  simp only [generatedQ, generatedN, generatedQlog]
  rw [← pow_mul]
  congr 1
  omega

theorem full_theta_exact (L : ℕ) :
    theta (fullQ L) = 1 / (2 ^ (9 + fullQlog L) : ℚ) := by
  rw [fullQ_pow]
  simp only [theta]
  rw [pow_add]
  norm_num

theorem generated_theta_exact (L : ℕ) :
    theta (generatedQ L) = 1 / (2 ^ (9 + generatedQlog L) : ℚ) := by
  rw [generatedQ_pow]
  simp only [theta]
  rw [pow_add]
  norm_num

theorem full_theta_quarter_exact (L : ℕ) :
    theta (fullQ L) / 4 = 1 / (2 ^ (11 + fullQlog L) : ℚ) := by
  rw [full_theta_exact, pow_add, pow_add]
  ring

theorem generated_theta_quarter_exact (L : ℕ) :
    theta (generatedQ L) / 4 = 1 / (2 ^ (11 + generatedQlog L) : ℚ) := by
  rw [generated_theta_exact, pow_add, pow_add]
  ring

theorem full_Qtheta (L : ℕ) :
    (fullQ L : ℚ) * theta (fullQ L) = 1 / 512 := by
  unfold theta
  have h : (fullQ L : ℚ) ≠ 0 := by
    exact_mod_cast (show fullQ L ≠ 0 by unfold fullQ fullW; positivity)
  field_simp

theorem generated_Qtheta (L : ℕ) :
    (generatedQ L : ℚ) * theta (generatedQ L) = 1 / 512 := by
  unfold theta
  have h : (generatedQ L : ℚ) ≠ 0 := by
    exact_mod_cast (show generatedQ L ≠ 0 by unfold generatedQ generatedN; positivity)
  field_simp

theorem generated_product_exact (L : ℕ) :
    ((generatedW L : ℚ) ^ 2) * generatedQ₂ L * generatedX L = 1 := by
  unfold generatedW generatedQ₂ generatedX generatedN
  push_cast
  have h : (2 : ℚ) ^ L ≠ 0 := by positivity
  field_simp

theorem fullS_ge_256 (L : ℕ) : 256 ≤ fullS L := by
  unfold fullS
  have h : 2 ^ 8 ≤ 2 ^ (16 + ell L) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at h ⊢
  exact h

theorem fullQ₂_ge_s (L : ℕ) : fullS L ≤ fullQ₂ L := by
  unfold fullQ₂
  have hs : 1 ≤ fullS L := by
    have h : 0 < fullS L := by unfold fullS; positivity
    omega
  have hp : 1 ≤ 2 ^ L := by
    have h : 0 < 2 ^ L := by positivity
    omega
  nlinarith

theorem full_product_block_width (L : ℕ) :
    4096 * (16 * (L + 1)) ≤ fullS L := by
  have h := Nat.le_pow_clog (by decide : 1 < 2) (L + 1)
  calc
    4096 * (16 * (L + 1)) ≤ 4096 * (16 * 2 ^ ell L) := by
      unfold ell
      gcongr
    _ = fullS L := by
      simp only [fullS, pow_add]
      norm_num
      ring

theorem generated_w_deltaU (cDel : ℚ) (L : ℕ) :
    (generatedW L : ℚ) * deltaU (generatedEta cDel L) (generatedW L) =
      generatedEta cDel L / 16 := by
  unfold deltaU
  have hw : (generatedW L : ℚ) ≠ 0 := by
    exact_mod_cast (show generatedW L ≠ 0 by
      unfold generatedW generatedN; positivity)
  field_simp

theorem full_w_deltaU (c : ℚ) (L : ℕ) :
    (fullW L : ℚ) * deltaU (fullEta c L) (fullW L) =
      fullEta c L / 16 := by
  unfold deltaU
  have hw : (fullW L : ℚ) ≠ 0 := by
    exact_mod_cast (show fullW L ≠ 0 by unfold fullW; positivity)
  field_simp

theorem full_eta_scaled (c : ℚ) (L : ℕ) :
    (fullS L : ℚ) * fullEta c L = c / 2 ^ 16 := by
  unfold fullEta
  have hs : (fullS L : ℚ) ≠ 0 := by
    exact_mod_cast (show fullS L ≠ 0 by unfold fullS; positivity)
  field_simp

/-- Fixed numerical comparisons used after the public tests in v38. -/
theorem source_population_margin :
    (3 / 5 : ℚ) - 6 / (5 * 256) - 1 / 1000 > 9 / 16 ∧
    (3 / 5 : ℚ) - 1 / 10000 > 9 / 16 ∧
    (44 / 75 : ℚ) - 1 / 10000 > 9 / 16 := by
  norm_num

theorem conditioned_population_margin :
    (44 / 75 : ℚ) - 1 / 256 - 1 / 32 > 1 / 2 := by
  norm_num

theorem fixed_transfer_margins :
    (99 / 200 : ℚ) - 2 * (1 - 255 / 256) > 12 / 25 ∧
    ((99 / 100 + (255 / 256 : ℚ) ^ 2 - 1) / (255 / 256 : ℚ) ^ 2) -
      1 / 1000 > 49 / 64 ∧
    (1 / 64 : ℚ) + (1 / 256) / (2 * (255 / 256)) < 1 / 32 := by
  norm_num

theorem full_overhead (L : ℕ) :
    2 * (16 + ell L) + (L + 2 * (16 + ell L)) +
      8 * ell L + fullQlog L = L + 64 + 28 * ell L := by
  unfold fullQlog
  omega

theorem generated_overhead (L : ℕ) :
    2 * quarterCeil L + 4 * L + 2 * L + 6 * L =
      12 * L + 2 * quarterCeil L := by omega

/-- Rational and integer tests only. `m` is the edge count and `δv, ζ` are
the source-promise rational parameters. No semantic assertion is hidden here. -/
structure ScheduleInput where
  s : ℕ
  q₁ : ℕ
  q₂ : ℕ
  w : ℕ
  Q : ℕ
  ρ : ℚ
  x : ℚ
  η : ℚ
  wlog : ℕ
  qlog : ℕ

def fullInput (c : ℚ) (L : ℕ) : ScheduleInput :=
  ⟨fullS L, fullQ₁ L, fullQ₂ L, fullW L, fullQ L,
   fullRho L, fullX L, fullEta c L, 8 * ell L, fullQlog L⟩

def fullPublicInput (γ : ℚ) (Δ n m L : ℕ) : ScheduleInput :=
  fullInput (fullConstant γ Δ n m) L

def generatedInput (cDel : ℚ) (L : ℕ) : ScheduleInput :=
  ⟨generatedS L, generatedQ₁ L, generatedQ₂ L,
   generatedW L, generatedQ L, generatedRho L,
   generatedX L, generatedEta cDel L, 2 * L, generatedQlog L⟩

def pow2Ceil (a : ℕ) : ℕ := 2 ^ Nat.clog 2 a

def CommonTests (p : ScheduleInput) (m : ℕ) (δv ζ : ℚ) : Prop :=
  p.s ≥ 256 ∧ p.s * p.η ≤ (min 1 (min δv (ζ / 256))) / 2 ^ 16 ∧
  p.q₂ ≥ pow2Ceil (4 * p.s * m) ∧
  4 * (p.s : ℚ) ^ 2 * p.ρ ≤ 1 ∧
  8 * (p.s : ℚ) * p.q₁ ≤ ζ * p.q₂ / 16 ∧
  (p.q₂ : ℚ) * p.x ≤ 1 / 10000 ∧
  (p.s : ℚ) * p.x ≤ 1 / 10000 ∧
  (p.w : ℚ) * p.x ≤ 1 / 10000 ∧
  2 * (p.w : ℚ) ^ 2 * p.x ≤ p.η / (16 * (255 / 256 : ℚ)) ∧
  (p.w : ℚ) ^ 2 * p.q₂ * p.x ≤ 1 ∧
  4 * (1 / 256 : ℚ) * p.w * p.q₂ * p.x ≤ p.η / 32 ∧
  ebar (9 + p.qlog) 1 ≤ p.w / 128 ∧
  ebar (11 + p.qlog) 1 ≤ p.s * p.q₂ ∧
  C128 / (p.s : ℚ) ^ 128 ≤ theta p.Q / 4 ∧
  Eexc p.qlog p.η ≤ p.w / 4 ∧
  (Kstar p.wlog p.s : ℚ) * Eexc p.qlog p.η ≤ p.η * p.w / 16

def FullTests (c : ℚ) (L m : ℕ) (δv ζ : ℚ) : Prop :=
  CommonTests (fullInput c L) m δv ζ ∧
  (fullQ L : ℚ) * deltaU (fullEta c L) (fullW L) ≥ 80 * L ∧
  L ≥ 16 ∧ ell L + 7 ≤ L ∧ L + 64 + 28 * ell L ≤ 7 * L

def FullPublicTests (γ : ℚ) (Δ n m L : ℕ) : Prop :=
  FullTests (fullConstant γ Δ n m) L m
    (sourceDeltaV γ Δ n m) (sourceZeta γ)

def GeneratedTests (cDel : ℚ) (L m : ℕ) (δv ζ : ℚ) : Prop :=
  CommonTests (generatedInput cDel L) m δv ζ ∧
  ebar (8 * L) 1 ≤ generatedS L / 128 ∧
  generatedQ L ≥ 128 *
    (ebar L (deltaU (generatedEta cDel L) (generatedW L) / 2) + 1)

instance (p : ScheduleInput) (m : ℕ) (δv ζ : ℚ) : Decidable (CommonTests p m δv ζ) :=
  by unfold CommonTests; infer_instance
instance (c : ℚ) (L m : ℕ) (δv ζ : ℚ) : Decidable (FullTests c L m δv ζ) :=
  by unfold FullTests; infer_instance
instance (γ : ℚ) (Δ n m L : ℕ) : Decidable (FullPublicTests γ Δ n m L) :=
  by unfold FullPublicTests; infer_instance
instance (c : ℚ) (L m : ℕ) (δv ζ : ℚ) : Decidable (GeneratedTests c L m δv ζ) :=
  by unfold GeneratedTests; infer_instance

def fullPass (c : ℚ) (L m : ℕ) (δv ζ : ℚ) : Bool :=
  decide (FullTests c L m δv ζ)
def fullPublicPass (γ : ℚ) (Δ n m L : ℕ) : Bool :=
  decide (FullPublicTests γ Δ n m L)
def generatedPass (cDel : ℚ) (L m : ℕ) (δv ζ : ℚ) : Bool :=
  decide (GeneratedTests cDel L m δv ζ)

theorem fullPass_iff (c : ℚ) (L m : ℕ) (δv ζ : ℚ) :
    fullPass c L m δv ζ = true ↔ FullTests c L m δv ζ := by
  simp [fullPass]

theorem fullPublicPass_iff (γ : ℚ) (Δ n m L : ℕ) :
    fullPublicPass γ Δ n m L = true ↔ FullPublicTests γ Δ n m L := by
  simp [fullPublicPass]

theorem generatedPass_iff (cDel : ℚ) (L m : ℕ) (δv ζ : ℚ) :
    generatedPass cDel L m δv ζ = true ↔
      GeneratedTests cDel L m δv ζ := by
  simp [generatedPass]

/-- The search is executable once a mathematical all-large cutoff for the
actual tests has been proved. The latter is an explicit premise here; this
lemma does not assert it for v38. -/
def firstGeneratedExponent (cDel : ℚ) (n m : ℕ) (δv ζ : ℚ)
    (h : ∃ L, Nat.clog 2 n ≤ L ∧ GeneratedTests cDel L m δv ζ) : ℕ :=
  Nat.find h

theorem firstGeneratedExponent_spec (cDel : ℚ) (n m : ℕ) (δv ζ : ℚ)
    (h : ∃ L, Nat.clog 2 n ≤ L ∧ GeneratedTests cDel L m δv ζ) :
    Nat.clog 2 n ≤ firstGeneratedExponent cDel n m δv ζ h ∧
      generatedPass cDel (firstGeneratedExponent cDel n m δv ζ h) m δv ζ = true := by
  obtain ⟨hlo, htest⟩ := Nat.find_spec h
  exact ⟨hlo, (generatedPass_iff ..).2 htest⟩

theorem firstGeneratedExponent_le_cutoff
    (cDel : ℚ) (n m L₀ : ℕ) (δv ζ : ℚ)
    (hlarge : ∀ L ≥ L₀, GeneratedTests cDel L m δv ζ) :
    ∃ h : ∃ L, Nat.clog 2 n ≤ L ∧ GeneratedTests cDel L m δv ζ,
      firstGeneratedExponent cDel n m δv ζ h ≤ max (Nat.clog 2 n) L₀ := by
  let M := max (Nat.clog 2 n) L₀
  have hM : Nat.clog 2 n ≤ M ∧ GeneratedTests cDel M m δv ζ :=
    ⟨le_max_left _ _, hlarge M (le_max_right _ _)⟩
  let h : ∃ L, Nat.clog 2 n ≤ L ∧ GeneratedTests cDel L m δv ζ := ⟨M, hM⟩
  refine ⟨h, ?_⟩
  exact Nat.find_min' h hM

#print axioms fullQ_pow
#print axioms generatedQ_pow
#print axioms full_theta_exact
#print axioms generated_theta_exact
#print axioms full_Qtheta
#print axioms generated_Qtheta
#print axioms generated_product_exact
#print axioms fullS_ge_256
#print axioms fullQ₂_ge_s
#print axioms full_product_block_width
#print axioms generated_w_deltaU
#print axioms full_w_deltaU
#print axioms full_eta_scaled
#print axioms source_population_margin
#print axioms conditioned_population_margin
#print axioms fixed_transfer_margins
#print axioms full_overhead
#print axioms generated_overhead
#print axioms fullPass_iff
#print axioms fullPublicPass_iff
#print axioms generatedPass_iff
#print axioms firstGeneratedExponent_spec
#print axioms firstGeneratedExponent_le_cutoff

end V38Schedule
