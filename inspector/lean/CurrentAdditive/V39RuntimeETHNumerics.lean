import CurrentAdditive.V39ActualETHNumerics
import CurrentAdditive.DeterministicETHFullSubexp

/-! Runtime-compatible arithmetic for fixed construction constants. The
actual table-size bound is weakened, never used to infer an execution clock.
A separately proved actual clock bound can instantiate the conditional clock
lemma. Constants are fixed before input size, formula and estimator threshold.
-/

namespace CurrentAdditive.V39RuntimeETHNumerics
noncomputable section
set_option autoImplicit false

open Paper2 V38Schedule GeneratedCutoff
open EthInapproximability.CurrentPaper
open CurrentAdditive.V39GeneratedConstruction
open CurrentAdditive.V39ActualETHNumerics
open CurrentAdditive.DeterministicEndpointNumeric

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def amplificationLog (A : ℕ) : ℕ := Nat.clog 2 A
def errorCoefficient (A : ℕ) : ℚ := 1/(4*(amplificationLog A:ℚ))
def rounds (A M : ℕ) : ℕ := ethIterations (amplificationLog A) M

theorem amplificationLog_ge (A : ℕ) (hA : 2^64 ≤ A) : 64 ≤ amplificationLog A := by
  have h:=Nat.clog_mono_right 2 hA
  simpa only [amplificationLog,Nat.clog_pow 2 64 (by decide)] using h

theorem amplification_le (A : ℕ) : A ≤ 2^amplificationLog A :=
  Nat.le_pow_clog (by decide) A

theorem coefficient_cast (A : ℕ) :
    (errorCoefficient A:ℝ)=1/(4*(amplificationLog A:ℝ)) := by
  simp only [errorCoefficient,Rat.cast_div,Rat.cast_one,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast]

theorem coefficient_positive (A : ℕ) (hA : 2^64 ≤ A) : 0 < errorCoefficient A := by
  have ha:=amplificationLog_ge A hA
  unfold errorCoefficient
  have hp : (0:ℚ)<amplificationLog A := by exact_mod_cast (show 0<amplificationLog A by omega)
  exact div_pos (by norm_num) (mul_pos (by norm_num) hp)

theorem actual_size_arbitrary (A C : ℕ) (hA : 2^64 ≤ A) (hC : 1040 ≤ C)
    (p : SourceConstants) (M : ℕ) {n m : ℕ}
    (hn : 0<n) (hlow : n≤2*m) (hdegree : 2*m≤p.degree*n)
    (edge : Fin m → Bool → Fin n) (k : ℕ) :
    let N:=generatedN (publicLogFrom p M n m hn hlow hdegree)
    (publicGraphRunFrom p M hn hlow hdegree edge k).squareWord.length ≤ N^(C*A^k) := by
  have hb:=(publicGraphRunFrom_size_bounds p M hn hlow hdegree edge k).2.2
  have hpow : supportAmplification^k≤A^k := Nat.pow_le_pow_left hA k
  exact hb.trans (Nat.pow_le_pow_right (by unfold generatedN; positivity) (Nat.mul_le_mul hC hpow))

theorem actual_size_weakened (a C : ℕ) (ha : 64 ≤ a) (hC : 1040 ≤ C)
    (p : SourceConstants) (M : ℕ) {n m : ℕ}
    (hn : 0<n) (hlow : n≤2*m) (hdegree : 2*m≤p.degree*n)
    (edge : Fin m → Bool → Fin n) (k : ℕ) :
    let N:=generatedN (publicLogFrom p M n m hn hlow hdegree)
    (publicGraphRunFrom p M hn hlow hdegree edge k).squareWord.length ≤ N^(C*(2^a)^k) := by
  have hb:=(publicGraphRunFrom_size_bounds p M hn hlow hdegree edge k).2.2
  have hpow : supportAmplification^k≤(2^a)^k := by
    apply Nat.pow_le_pow_left
    exact Nat.pow_le_pow_right (by decide) ha
  have hexp : 1040*supportAmplification^k≤C*(2^a)^k := Nat.mul_le_mul hC hpow
  exact hb.trans (Nat.pow_le_pow_right (by unfold generatedN; positivity) hexp)

theorem actual_numerics_for_power (a C : ℕ) (ha : 64 ≤ a) (hC : 1040 ≤ C)
    (p : SourceConstants) (M g : ℕ) {n m : ℕ}
    (hn : 0<n) (hlow : n≤2*m) (hdegree : 2*m≤p.degree*n)
    (edge : Fin m → Bool → Fin n)
    (hM : 2≤M) (hg : 1≤g) (hgraph : n≤M^g)
    (hcutoff : generatedN (cutoffLog p.degree p.deletion)≤M)
    (hlarge : 2^(max (32*(C*(g+1))+16) (8*a))≤M) :
    let k:=ethIterations a M
    let R:=publicGraphRunFrom p M hn hlow hdegree edge k
    1≤k ∧ ((2^a)^k)^2≤M ∧ M^2≤entryCount R ∧
      2*(1/(4*(a:ℝ)))*Real.logb 2 (Real.logb 2 (entryCount R))<k ∧
      R.squareWord.length≤M^((g+1)*C*(2^a)^k) := by
  let k:=ethIterations a M
  let R:=publicGraphRunFrom p M hn hlow hdegree edge k
  let N:=generatedN (publicLogFrom p M n m hn hlow hdegree)
  have hN : N≤M^(g+1) := public_floor_polynomial p M g hn hlow hdegree hM hg hgraph hcutoff
  have hword : R.squareWord.length≤N^(C*(2^a)^k) :=
    actual_size_weakened a C ha hC p M hn hlow hdegree edge k
  have hT : entryCount R≤N^(C*(2^a)^k) := (entries_le_length R).trans hword
  have hmargin:=eth_margin_from_polynomial_source a C (g+1) M N
    (by omega) (by omega) (by omega) hN hlarge
  have hgap:=eth_loglog_gap N C a k (entryCount R) (by omega) hT hmargin
  have hmin : M^2≤entryCount R := (publicGraphRunFrom_size_bounds p M hn hlow hdegree edge k).1
  have hT2 : 2≤entryCount R := (by nlinarith only [hM] : 2≤M^2).trans hmin
  have hreal:=real_double_log_le_clog (entryCount R) hT2
  have hcoeff : 0≤2*(1/(4*(a:ℝ))) := by positivity
  have hgapR:=lt_of_le_of_lt (mul_le_mul_of_nonneg_left hreal hcoeff) hgap
  have hk : 1≤k := ethIterations_positive a M (by omega)
    ((Nat.pow_le_pow_right (by decide)
      (show 2 * a ≤ max (32 * (C * (g + 1)) + 16) (8 * a) by omega)).trans hlarge)
  have hsize : R.squareWord.length≤M^((g+1)*C*(2^a)^k) := by
    calc
      _ ≤ N^(C*(2^a)^k) := hword
      _ ≤ (M^(g+1))^(C*(2^a)^k) := Nat.pow_le_pow_left hN _
      _ = _ := by rw [←pow_mul]; congr 1; ring
  exact ⟨hk,ethIterations_square_bound a M (by omega) (by omega),hmin,hgapR,hsize⟩

/-- Arbitrary fixed amplification constants are rounded upward to a power
of two. The positive rational error coefficient adapts to that fixed choice. -/
theorem actual_numerics (A C : ℕ) (hA : 2^64≤A) (hC : 1040≤C)
    (p : SourceConstants) (M g : ℕ) {n m : ℕ}
    (hn : 0<n) (hlow : n≤2*m) (hdegree : 2*m≤p.degree*n)
    (edge : Fin m → Bool → Fin n)
    (hM : 2≤M) (hg : 1≤g) (hgraph : n≤M^g)
    (hcutoff : generatedN (cutoffLog p.degree p.deletion)≤M)
    (hlarge : 2^(max (32*(C*(g+1))+16) (8*amplificationLog A))≤M) :
    let k:=rounds A M
    let R:=publicGraphRunFrom p M hn hlow hdegree edge k
    0<errorCoefficient A ∧ 1≤k ∧ (A^k)^2≤M ∧ M^2≤entryCount R ∧
      2*(errorCoefficient A:ℝ)*Real.logb 2 (Real.logb 2 (entryCount R))<k ∧
      R.squareWord.length≤M^((g+1)*C*(2^amplificationLog A)^k) := by
  have h:=actual_numerics_for_power (amplificationLog A) C (amplificationLog_ge A hA) hC
    p M g hn hlow hdegree edge hM hg hgraph hcutoff hlarge
  have hsqrt : (A^rounds A M)^2≤M :=
    (Nat.pow_le_pow_left (Nat.pow_le_pow_left (amplification_le A) _) 2).trans h.2.1
  exact ⟨coefficient_positive A hA,h.1,hsqrt,h.2.2.1,
    by simpa only [coefficient_cast] using h.2.2.2.1,h.2.2.2.2⟩

/-- This conditional arithmetic accepts a separately proved bound on an
actual run time. It does not assert a machine run or infer time from size. -/
theorem clock_subexponential_of_bound (A C g u M N clock : ℕ)
    (hA : 2^64≤A) (hC : 1040≤C) (hu : 1≤u)
    (hN : N≤M^(g+1))
    (hclock : clock≤N^(C*A^rounds A M))
    (hlarge : 2^(max (32*(u*(g+1)*C)+16) (8*amplificationLog A))≤M) :
    clock^u≤2^M := by
  have hb : clock≤M^((g+1)*C*(2^amplificationLog A)^rounds A M) := by
    calc
      _ ≤ N^(C*A^rounds A M) := hclock
      _ ≤ (M^(g+1))^(C*A^rounds A M) := Nat.pow_le_pow_left hN _
      _ = M^((g+1)*C*A^rounds A M) := by rw [←pow_mul]; congr 1; ring
      _ ≤ _ := Nat.pow_le_pow_right
        (by have hp : 0<2^(max (32*(u*(g+1)*C)+16) (8*amplificationLog A)) := by positivity
            omega)
        (Nat.mul_le_mul_left ((g+1)*C) (Nat.pow_le_pow_left (amplification_le A) _))
  exact (Nat.pow_le_pow_left hb u).trans
    (eth_discrete_subexponential_bound (amplificationLog A) C (g+1) u M
      (by have h:=amplificationLog_ge A hA; omega) (by omega) (by omega) hu hlarge)

theorem envelope_subexponential (A C g : ℕ) (hA : 2^64≤A) (hC : 1040≤C) :
    Paper2.AEth.Subexp (fun M => M^((g+1)*C*(2^amplificationLog A)^rounds A M)) := by
  exact DeterministicETHFullSubexp.tableBound_subexp (amplificationLog A) C (g+1)
    (by have h:=amplificationLog_ge A hA; omega) (by omega) (by omega)

end
end CurrentAdditive.V39RuntimeETHNumerics

#print axioms CurrentAdditive.V39RuntimeETHNumerics.actual_numerics
#print axioms CurrentAdditive.V39RuntimeETHNumerics.clock_subexponential_of_bound
#print axioms CurrentAdditive.V39RuntimeETHNumerics.envelope_subexponential
