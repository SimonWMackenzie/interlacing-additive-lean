import CurrentV43.DeterministicRate

/-! Literal real-log translation and unrestricted-input specialization for
the checked deterministic v43 runtime candidate. -/
namespace CurrentAdditive.V43DeterministicRate
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedETHSource EncodedETHSourceComposition
open V39PermittedDeterministicExtraction V40DeterministicETHEndpoint
set_option maxHeartbeats 100000
set_option maxRecDepth 4096

def rationalCoefficient (A : ℕ) : ℚ := 1/(8*(V39RuntimeETHNumerics.amplificationLog A:ℚ))

theorem coefficient_eq_rational (A : ℕ) : coefficient A=(rationalCoefficient A:ℝ) := by
  simp only [coefficient,rationalCoefficient,Rat.cast_div,Rat.cast_one,Rat.cast_mul,
    Rat.cast_ofNat,Rat.cast_natCast]

theorem quasiLog_le_real (M : ℕ) (hM : 2 ≤ M) :
    (quasiLog M:ℝ) ≤ 3*Real.logb 2 M := by
  have hMr : (2:ℝ) ≤ M := by exact_mod_cast hM
  have hlog : (1:ℝ) ≤ Real.logb 2 M := by
    have h := (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (by norm_num : (0:ℝ)<2)
      (by positivity : (0:ℝ)<M)).2 hMr
    simpa only [Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] using h
  have hm : ((M+2:ℕ):ℝ) ≤ 2*(M:ℝ) := by push_cast; linarith
  have hmono := (Real.logb_le_logb (by norm_num : (1:ℝ)<2)
    (by positivity : (0:ℝ)<(M+2:ℕ)) (by positivity : (0:ℝ)<2*(M:ℝ))).2 hm
  rw [Real.logb_mul (by norm_num : (2:ℝ)≠0) (by positivity : (M:ℝ)≠0),
    Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] at hmono
  have hc := Unit4Shell.Asymptotics.clog_le_logb_add_one (M+2) (by omega)
  change (quasiLog M:ℝ) ≤ _ at hc
  linarith

theorem quasipoly_clock_real (C M t : ℕ) (hM : 2 ≤ M)
    (ht : t ≤ 2^(C*(quasiLog M)^2)) :
    (t:ℝ) ≤ (2:ℝ)^((9*(C:ℝ))*(Real.logb 2 M)^2) := by
  have hn : (t:ℝ) ≤ ((2^(C*(quasiLog M)^2):ℕ):ℝ) := by exact_mod_cast ht
  have hn' : (t:ℝ) ≤ (2:ℝ)^((C*(quasiLog M)^2:ℕ):ℝ) := by
    simpa only [Real.rpow_natCast,Nat.cast_pow,Nat.cast_ofNat] using hn
  have hL := quasiLog_le_real M hM
  have hLp : (0:ℝ) ≤ quasiLog M := by positivity
  have hlog : (0:ℝ) ≤ Real.logb 2 M := by
    exact Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1 ≤ M by omega))
  have hsq : (quasiLog M:ℝ)^2 ≤ 9*(Real.logb 2 M)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 3*Real.logb 2 M-(quasiLog M:ℝ) by linarith)
      (show 0 ≤ 3*Real.logb 2 M+(quasiLog M:ℝ) by positivity)]
  have he : ((C*(quasiLog M)^2:ℕ):ℝ) ≤ (9*(C:ℝ))*(Real.logb 2 M)^2 := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hsq (show (0:ℝ)≤C by positivity)]
  exact hn'.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) he)

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

include D B in
/-- The unrestricted-table premise implies the square power-of-two premise
of the checked corollary, and its actual clock has the literal source rate. -/
theorem deterministic_estimation_to_sparse3SAT_real :
    ∃ c : ℝ, 0<c ∧
      ∀ A : PermittedDeterministicEstimator, ∀ T₀ : ℕ,
      GrowingAccuracy A c T₀ → ∀ cs : ℕ,
      ∃ P : DeterministicSparseETH.Algorithm,
        (∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs*Φ.val.variables →
          (P.answer (EncodedCNF.encode Φ.val)=true ↔ EncodedCNF.Satisfiable Φ.val)) ∧
        ∃ C M₀ : ℕ, ∀ Φ : ValidFormula,
          Φ.val.clauses.length ≤ cs*Φ.val.variables → M₀ ≤ Φ.val.variables →
          (P.time (EncodedCNF.encode Φ.val):ℝ) ≤
            (2:ℝ)^((C:ℝ)*(Real.logb 2 Φ.val.variables)^2) := by
  obtain ⟨c,hc,h⟩ := deterministic_estimation_to_sparse3SAT D B
  refine ⟨c,hc,?_⟩
  intro A T₀ hA cs
  obtain ⟨P,hP,C,M₀,hclock⟩ := h A T₀
    (growingSquareAccuracy_of_growingAccuracy A c T₀ hA) cs
  refine ⟨P,hP,9*C,max 2 M₀,?_⟩
  intro Φ hsp hlarge
  have hM : 2 ≤ Φ.val.variables := (le_max_left _ _).trans hlarge
  have hr := quasipoly_clock_real C Φ.val.variables (P.time (EncodedCNF.encode Φ.val)) hM
    (hclock Φ hsp ((le_max_right _ _).trans hlarge))
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hr

#print axioms coefficient_eq_rational
#print axioms quasipoly_clock_real
#print axioms deterministic_estimation_to_sparse3SAT_real
end
end CurrentAdditive.V43DeterministicRate
