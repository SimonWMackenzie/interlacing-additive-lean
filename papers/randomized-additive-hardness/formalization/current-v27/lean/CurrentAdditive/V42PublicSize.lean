import CurrentAdditive.V42PublicCutoff

/-! Exact v42 public sample arithmetic and its uniform bit-size bounds.
The printed table recipe is numerical and has no semantic matrix premise. -/
namespace CurrentAdditive.V42PublicSize
open V42Schedule V42PublicSchedule V42PublicCutoff

 theorem fullS_above_constant (s₀ L : ℕ)
    (hL:fullLengthCutoff (Nat.clog 2 s₀) ≤ L) : s₀ ≤ s (fullExponent L) := by
  exact (Nat.le_pow_clog (by decide) s₀).trans
    (Nat.pow_le_pow_right (by decide) (full_cutoff_bounds _ _ hL).1)

theorem full_rho_admissible (K L : ℕ) (hL:fullLengthCutoff K ≤ L) :
    rho L  ≤  1/(s (fullExponent L):ℚ)^4 := by
  have h:=reciprocal_le L (4*fullExponent L) (full_cutoff_bounds K L hL).2.2.2.2
  simpa only [rho,s,Nat.cast_pow,Nat.cast_ofNat,←pow_mul,Nat.mul_comm] using h

theorem full_block_threshold (L u : ℕ) (hu:s (fullExponent L) ≤ 2*u) :
    32768*L<u := by
  have hs:=(fullS_rounding L).1
  norm_num at hs
  omega

theorem generatedExponent_le (n k₀ : ℕ) :
    generatedExponent n k₀ ≤ k₀+Nat.clog 2 n+1 := by
  unfold generatedExponent
  apply max_le <;> omega

theorem budget_linear (L i : ℕ) (hs:seedCost L ≤ L) (hh:fullOverhead L ≤ 7*L) :
    B L i  ≤  8*(i+1)*L := by
  have hi:=Nat.mul_le_mul_left i hh
  unfold B
  nlinarith

theorem log_budget_le (L i : ℕ) (hL:1 ≤ L)
    (hs:seedCost L ≤ L) (hh:fullOverhead L ≤ 7*L) :
    Nat.clog 2 (B L i+2)  ≤  (i+1)+L+4 := by
  have hb:=budget_linear L i hs hh
  have hIL:1 ≤ (i+1)*L := by nlinarith
  have hbase:B L i+2 ≤ 16*(i+1)*L := by nlinarith
  have hip:i+1 ≤ 2^(i+1) := Nat.le_of_lt Nat.lt_two_pow_self
  have hLp:L ≤ 2^L := Nat.le_of_lt Nat.lt_two_pow_self
  have hp:16*(i+1)*L ≤ 2^((i+1)+L+4) := by
    calc
      16*(i+1)*L ≤ 16*2^(i+1)*2^L := by gcongr
      _ = _ := by simp only [pow_add]; norm_num; ring
  exact (Nat.clog_le_iff_le_pow (by decide)).2 (hbase.trans hp)

theorem sampleEntries_power_bound (K L i : ℕ) (hL:fullLengthCutoff K ≤ L) :
    sampleEntries L i  ≤  2^(40*(i+1)*L) := by
  obtain ⟨_,hL16,hs,hh,_⟩:=full_cutoff_bounds K L hL
  have hb:=budget_linear L i hs hh
  have hc:=log_budget_le L i (by omega) hs hh
  have ht:=sampleEntries_clog_upper L i
  have hIL:(i+1)*L ≥ L := by nlinarith
  have hIL16:(i+1)*L ≥ 16*(i+1) := by nlinarith
  have hclog:Nat.clog 2 (sampleEntries L i) ≤ 40*(i+1)*L := by nlinarith
  exact (Nat.le_pow_clog (by decide) _).trans
    (Nat.pow_le_pow_right (by decide) hclog)

/-- All samples, including zero iterations, have a fixed polynomial in n
whose exponent is linear in the iteration count. -/
theorem sampleEntries_polynomial_bound (K n i : ℕ) (hn:2 ≤ n)
    (hL:fullLengthCutoff K ≤ Nat.clog 2 n) :
    sampleEntries (Nat.clog 2 n) i  ≤  n^(80*(i+1)) := by
  have hround:=V39PublicSchedule.pow2Ceil_lt_twice n (by omega)
  have hpow:2^(Nat.clog 2 n) ≤ n^2 := by
    change 2^(Nat.clog 2 n)<2*n at hround
    nlinarith
  calc
    sampleEntries (Nat.clog 2 n) i ≤ 2^(40*(i+1)*Nat.clog 2 n) :=
      sampleEntries_power_bound K _ i hL
    _ = (2^(Nat.clog 2 n))^(40*(i+1)) := by rw [←pow_mul]; congr 1; ring
    _  ≤  (n^2)^(40*(i+1)) := Nat.pow_le_pow_left hpow _
    _ = n^(80*(i+1)) := by rw [←pow_mul]; congr 1; ring

open Paper2.Unit4Shell.Asymptotics
noncomputable section

def lengthCutoff (ε:ℝ) : ℕ :=
  max 22 (max ⌈((722:ℝ)/(ε/12)+1)^2⌉₊ ⌈(12:ℝ)/ε⌉₊)
def iterationCutoff (ε:ℝ) : ℕ := max 1 ⌈(21:ℝ)/ε⌉₊

theorem seed_le_of_relative (δ:ℝ) (hδ1:δ ≤ 1) (L:ℕ)
    (hh:(fullOverhead L:ℝ) ≤ (1+δ)*L) : seedCost L ≤ L := by
  have h0:(0:ℝ) ≤ L := by positivity
  have he0:(0:ℝ) ≤ ell L := by positivity
  have h:(ell L:ℝ)+7 ≤ L := by
    unfold fullOverhead fullExponent at hh
    push_cast at hh
    nlinarith
  exact_mod_cast h

/-- The exact sample recipe has leading coefficient four. This estimate
uses only public integer formulas, with explicit sufficient cutoffs. -/
theorem sample_sharp (ε:ℝ) (hε:0<ε) (hε1:ε ≤ 1) (L i:ℕ)
    (hL:lengthCutoff ε ≤ L) (hi:iterationCutoff ε ≤ i) :
    (Nat.clog 2 (sampleEntries L i):ℝ) ≤ (4+ε)*i*L := by
  have hL22:22 ≤ L := (le_max_left _ _).trans hL
  have hi1:1 ≤ i := (le_max_left _ _).trans hi
  have hlarge:((722:ℝ)/(ε/12)+1)^2 ≤ (L:ℝ)+2 := by
    have hn:⌈((722:ℝ)/(ε/12)+1)^2⌉₊ ≤ L :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hL)
    have hr:((722:ℝ)/(ε/12)+1)^2 ≤ (L:ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hn)
    linarith
  have hrel:=overhead_relative (ε/12) (by positivity) (by linarith) L hlarge
  have hs:=seed_le_of_relative (ε/12) (by linarith) L hrel
  have h7:fullOverhead L ≤ 7*L := by
    have hr:(fullOverhead L:ℝ) ≤ 7*(L:ℝ) := by
      have h0:(0:ℝ) ≤ L := by positivity
      nlinarith
    exact_mod_cast hr
  have hlog:=log_budget_le L (i-1) (by omega) hs h7
  have hlog':Nat.clog 2 (B L i+2) ≤ i+L+4 := by
    have hiL:L ≤ i*L := Nat.le_mul_of_pos_left L hi1
    have hih:i*fullOverhead L ≤ i*(7*L) := Nat.mul_le_mul_left i h7
    have hb:B L i ≤ 8*i*L := by unfold B; nlinarith
    have hiL1:1 ≤ i*L := by nlinarith
    have hbase:B L i+2 ≤ 16*i*L := by nlinarith
    have hip:i ≤ 2^i := Nat.le_of_lt Nat.lt_two_pow_self
    have hLp:L ≤ 2^L := Nat.le_of_lt Nat.lt_two_pow_self
    apply (Nat.clog_le_iff_le_pow (by decide)).2
    calc
      B L i+2 ≤ 16*i*L := hbase
      _  ≤ 16*2^i*2^L := by gcongr
      _ = _ := by simp only [pow_add]; norm_num; ring
  have hb:(B L i:ℝ) ≤ L+(i:ℝ)*((1+ε/12)*L) := by
    have hsq:(seedCost L:ℝ) ≤ L := by exact_mod_cast hs
    have hm:=mul_le_mul_of_nonneg_left hrel (show (0:ℝ) ≤ i by positivity)
    unfold B; push_cast; linarith
  have hK:(21:ℝ) ≤ ε*(i:ℝ) := by
    have hn:⌈(21:ℝ)/ε⌉₊ ≤ i := (le_max_right _ _).trans hi
    have hr:(21:ℝ)/ε ≤ i := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have h:=(div_le_iff₀ hε).1 hr
    linarith
  have hLen:(12:ℝ) ≤ ε*(L:ℝ) := by
    have hn:⌈(12:ℝ)/ε⌉₊ ≤ L :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hL)
    have hr:(12:ℝ)/ε ≤ L := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have h:=(div_le_iff₀ hε).1 hr
    linarith
  have hTR:(Nat.clog 2 (sampleEntries L i):ℝ) ≤ 4*(B L i:ℝ)+2*i+
      2*(Nat.clog 2 (B L i+2):ℝ)+8 := by exact_mod_cast sampleEntries_clog_upper L i
  have hlogR:(Nat.clog 2 (B L i+2):ℝ) ≤ (i:ℝ)+L+4 := by exact_mod_cast hlog'
  have hLR:(22:ℝ) ≤ L := by exact_mod_cast hL22
  have ht1:=mul_le_mul_of_nonneg_right hK (show (0:ℝ) ≤ L by positivity)
  have ht2:=mul_le_mul_of_nonneg_right hLen (show (0:ℝ) ≤ i by positivity)
  nlinarith

#print axioms full_rho_admissible
#print axioms sampleEntries_power_bound
#print axioms sampleEntries_polynomial_bound
#print axioms sample_sharp
end
end CurrentAdditive.V42PublicSize

