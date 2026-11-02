import CurrentAdditive.V42PublicSchedule
import Paper2.A4Asymptotics

/-! Source v42 lem:full-schedule and lem:generated-schedule. These are
computable integer cutoffs and padding rules, with explicit arithmetic bounds.
No source graph, matrix constructor or probabilistic algorithm is assumed. -/
namespace CurrentAdditive.V42PublicCutoff
open V42Schedule V42PublicSchedule

/-- Sufficient length cutoff for any requested lower bound on log₂ s. -/
def fullLengthCutoff (K : ℕ) : ℕ := 2^(max K 300)

theorem full_cutoff_bounds (K L : ℕ) (hL : fullLengthCutoff K ≤ L) :
    K ≤ fullExponent L ∧ 16 ≤ L ∧ seedCost L ≤ L ∧
    fullOverhead L ≤ 7*L ∧ 4*fullExponent L ≤ L := by
  have hpow : 2^(max K 300) ≤ L := hL
  have hell : max K 300 < ell L := by
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).2
    omega
  have hell16 : 16 ≤ ell L := by omega
  have hlower : 2^(ell L-1) ≤ L := by
    have hpos : 0<2^(max K 300) := by positivity
    have hp:=Nat.pow_pred_clog_lt_self (by decide : 1<2) (show 1<L+1 by omega)
    change 2^(ell L-1)<L+1 at hp
    omega
  have hlinear : 512*ell L ≤ L :=
    (V39FullCutoff.linear_le_exp (ell L) hell16).trans hlower
  unfold fullOverhead fullExponent seedCost
  omega

theorem full_width_bit_bounds (K L : ℕ) (hL : fullLengthCutoff K ≤ L) :
    Nat.clog 2 (s (fullExponent L)) ≤ L ∧
    Nat.clog 2 (q₂ (fullExponent L) L) ≤ 3*L ∧
    Nat.clog 2 (w (fullExponent L)) ≤ 8*L ∧
    Nat.clog 2 (Q (fullExponent L)) ≤ 24*L := by
  have hk: fullExponent L ≤ L := by have h:=(full_cutoff_bounds K L hL).2.2.2.2; omega
  obtain ⟨hs,hq,hw,hQ⟩:=full_power_logs L
  rw [hs,hq,hw,hQ]
  omega

theorem full_restoration_product (L : ℕ) :
    80*(L : ℚ) ≤ (Q (fullExponent L) : ℚ)*deltaU (fullExponent L) := by
  have hL : L≤2^(ell L) := by
    have hp:=Nat.le_pow_clog (by decide : 1<2) (L+1)
    change L+1≤2^(ell L) at hp
    omega
  have hpow : (80:ℚ)*L≤(2:ℚ)^(ell L+7) := by
    have hLq : (L:ℚ)≤(2:ℚ)^(ell L) := by exact_mod_cast hL
    rw [pow_add]; norm_num; nlinarith
  rw [Q_deltaU]
  have hr:=V42Schedule.ratio_le (ell L+7) 0 (14*fullExponent L) 4
    (by unfold fullExponent; omega)
  norm_num only [pow_zero,show (2:ℚ)^4=16 by norm_num,div_one] at hr
  exact hpow.trans hr

/-- Least dyadic exponent with s at least 2^k₀ and s⁴ at least n.
It uses comparisons of integers only; no real fourth root is evaluated. -/
def generatedExponent (n k₀ : ℕ) : ℕ := max k₀ ((Nat.clog 2 n+3)/4)

theorem generatedExponent_spec (n k₀ : ℕ) :
    k₀ ≤ generatedExponent n k₀ ∧ n≤generatedN (generatedExponent n k₀) := by
  refine ⟨le_max_left _ _,?_⟩
  rw [generatedN_exact]
  have hclog : Nat.clog 2 n≤4*generatedExponent n k₀ := by
    have hm:=le_max_right k₀ ((Nat.clog 2 n+3)/4)
    unfold generatedExponent
    omega
  exact (Nat.le_pow_clog (by decide) n).trans
    (Nat.pow_le_pow_right (by decide) hclog)

theorem generatedExponent_minimal (n k₀ k : ℕ)
    (h₀ : k₀≤k) (hn : n≤generatedN k) : generatedExponent n k₀≤k := by
  apply max_le h₀
  have hc : Nat.clog 2 n≤4*k := by
    apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).2
    simpa only [generatedN_exact] using hn
  omega

theorem generated_padding (n k₀ : ℕ) :
    n≤generatedN (generatedExponent n k₀) ∧
    generatedN (generatedExponent n k₀)<16*max n (generatedN k₀) := by
  refine ⟨(generatedExponent_spec n k₀).2,?_⟩
  let k:=generatedExponent n k₀
  by_cases hk:k≤k₀
  · have he:k=k₀ := le_antisymm hk (generatedExponent_spec n k₀).1
    change generatedN k<16*max n (generatedN k₀)
    rw [he]
    have hp : 0<generatedN k₀ := by rw [generatedN_exact]; positivity
    have hm:=le_max_right n (generatedN k₀)
    omega
  · have hkpos:0<k := by omega
    have hn : generatedN (k-1)<n := by
      by_contra hbad
      have hsmall:=generatedExponent_minimal n k₀ (k-1) (by omega) (by omega)
      change k≤k-1 at hsmall
      omega
    have he:generatedN k=16*generatedN (k-1) := by
      rw [generatedN_exact,generatedN_exact]
      rw [show 4*k=4+4*(k-1) by omega,pow_add]
      norm_num
    change generatedN k<16*max n (generatedN k₀)
    rw [he]
    exact (Nat.mul_lt_mul_of_pos_left hn (by decide)).trans_le
      (Nat.mul_le_mul_left _ (le_max_left _ _))

theorem generated_width_polynomials (k : ℕ) :
    (q₂ k (generatedLog k))^2=(generatedN k)^3 ∧
    w k=(generatedN k)^2 ∧ Q k=(generatedN k)^6 := by
  simp only [q₂,generatedLog,generatedN_exact,w,Q,←pow_mul]
  refine ⟨?_,?_,?_⟩ <;> congr 1 <;> omega

open Paper2.Unit4Shell.Asymptotics

/-- Concrete real-accuracy estimate for the exact v42 full overhead. -/
theorem overhead_relative (δ : ℝ) (hδ:0<δ) (hδ1:δ≤1)
    (L : ℕ) (hL:((722:ℝ)/δ+1)^2≤(L:ℝ)+2) :
    (fullOverhead L:ℝ)≤(1+δ)*L := by
  have he : (ell L:ℝ)≤Real.logb 2 ((L:ℝ)+2)+1 := by
    have h:=clog_le_logb_add_one (L+1) (by omega)
    have hm : Real.logb 2 ((L+1:ℕ):ℝ)≤Real.logb 2 ((L:ℝ)+2) := by
      apply (Real.logb_le_logb (by norm_num : (1:ℝ)<2) (by positivity) (by positivity)).2
      push_cast; linarith
    change (ell L:ℝ)≤_ at h
    linarith
  have hs:=small_log 36 612 δ L (by norm_num) (by norm_num)
    hδ hδ1 (by positivity) (by norm_num at hL ⊢; exact hL)
  unfold fullOverhead fullExponent
  push_cast
  linarith

/-- The ordinary sequence limit asserted by h=L+O(log L). -/
theorem overhead_ratio_tendsto_one :
    Filter.Tendsto (fun L:ℕ => (fullOverhead L:ℝ)/L)
      Filter.atTop (nhds 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [Filter.eventually_ge_atTop 1] with L hL
    have hLr : (0:ℝ)<L := by exact_mod_cast hL
    have hh : (L:ℝ)≤fullOverhead L := by
      exact_mod_cast (show L≤fullOverhead L by unfold fullOverhead; omega)
    have hratio : (1:ℝ)≤(fullOverhead L:ℝ)/L := (le_div_iff₀ hLr).2 (by linarith)
    exact ha.trans_le hratio
  · intro a ha
    let δ:ℝ:=min 1 ((a-1)/2)
    have hδ : 0<δ := by dsimp [δ]; positivity
    have hδ1 : δ≤1 := min_le_left _ _
    let C:ℕ:=max 1 ⌈((722:ℝ)/δ+1)^2⌉₊
    filter_upwards [Filter.eventually_ge_atTop C] with L hL
    have hL1 : 1≤L := (le_max_left _ _).trans hL
    have hLr : (0:ℝ)<L := by exact_mod_cast hL1
    have hbig:((722:ℝ)/δ+1)^2≤(L:ℝ)+2 := by
      have hc:⌈((722:ℝ)/δ+1)^2⌉₊≤L := (le_max_right _ _).trans hL
      have hcast : (⌈((722:ℝ)/δ+1)^2⌉₊:ℝ)≤L := by exact_mod_cast hc
      exact (Nat.le_ceil _).trans (by linarith)
    have hr : (fullOverhead L:ℝ)/L≤1+δ :=
      (div_le_iff₀ hLr).2 (overhead_relative δ hδ hδ1 L hbig)
    have hd:δ≤(a-1)/2 := min_le_right _ _
    exact hr.trans_lt (by linarith)

#print axioms full_cutoff_bounds
#print axioms generated_padding
#print axioms generated_width_polynomials
#print axioms overhead_relative
#print axioms overhead_ratio_tendsto_one
end CurrentAdditive.V42PublicCutoff

