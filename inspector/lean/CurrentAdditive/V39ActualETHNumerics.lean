import CurrentAdditive.V39SourceFloorJoin
import CurrentAdditive.DeterministicEndpointSubexp
import CurrentAdditive.DeterministicETHGraphSize
import Paper2.A4Asymptotics

/-! The actual floor-aware current table meets the deterministic ETH size
and error arithmetic, with explicit positive coefficient 1/256. These are
actual entry/output counts. No physical execution clock follows from them.
-/

namespace CurrentAdditive.V39ActualETHNumerics

open Paper2 V38Schedule GeneratedCutoff
open EthInapproximability.CurrentPaper
open CurrentAdditive.V39GeneratedConstruction
open CurrentAdditive.DeterministicEndpointNumeric
open Paper2.Unit4Shell.Asymptotics

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

def entryCount (R : StoredMatrix) : ℕ :=
  (SquarePadding.side R.rows R.cols)^2

theorem entries_le_length (R : StoredMatrix) : entryCount R ≤ R.squareWord.length := by
  simp only [entryCount,StoredMatrix.squareWord,DeterministicETHEncodedTable.squareWord,
    Paper2.AModel.matrixWord,List.length_append,MatrixMaterialization.rowMajor_length,pow_two]
  omega

theorem public_floor_polynomial (p : SourceConstants) (M g : ℕ) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (hM : 2 ≤ M) (hg : 1 ≤ g) (hgraph : n ≤ M^g)
    (hcutoff : generatedN (cutoffLog p.degree p.deletion) ≤ M) :
    generatedN (publicLogFrom p M n m hn hlow hdegree) ≤ M^(g+1) := by
  have hMpow : M ≤ M^g := by
    calc
      M = M^1 := by simp
      _ ≤ M^g := Nat.pow_le_pow_right (by omega) hg
  have hmax : max (max M n) (generatedN (cutoffLog p.degree p.deletion)) ≤ M^g :=
    max_le (max_le hMpow hgraph) (hcutoff.trans hMpow)
  have hb := publicLogFrom_dyadic_bound p M n m hn hlow hdegree
  calc
    generatedN (publicLogFrom p M n m hn hlow hdegree) ≤ 2*M^g :=
      hb.trans (Nat.mul_le_mul_left 2 hmax)
    _ ≤ M^(g+1) := by rw [pow_succ]; nlinarith

theorem actual_size_bound (p : SourceConstants) (M g : ℕ) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (edge : Fin m → Bool → Fin n) (k : ℕ)
    (hM : 2 ≤ M) (hg : 1 ≤ g) (hgraph : n ≤ M^g)
    (hcutoff : generatedN (cutoffLog p.degree p.deletion) ≤ M) :
    let R := publicGraphRunFrom p M hn hlow hdegree edge k
    M^2 ≤ entryCount R ∧
      R.squareWord.length ≤ M^((g+1)*1040*supportAmplification^k) := by
  have hb := publicGraphRunFrom_size_bounds p M hn hlow hdegree edge k
  have hN := public_floor_polynomial p M g hn hlow hdegree hM hg hgraph hcutoff
  refine ⟨hb.1,?_⟩
  calc
    _ ≤ (generatedN (publicLogFrom p M n m hn hlow hdegree))^(1040*supportAmplification^k) := hb.2.2
    _ ≤ (M^(g+1))^(1040*supportAmplification^k) := Nat.pow_le_pow_left hN _
    _ = M^((g+1)*1040*supportAmplification^k) := by rw [← pow_mul]; congr 1; ring

theorem real_double_log_le_clog (T : ℕ) (hT : 2 ≤ T) :
    Real.logb 2 (Real.logb 2 T) ≤ (Nat.clog 2 (Nat.clog 2 T):ℝ) := by
  have hlogpos : 0 < Real.logb 2 T :=
    Real.logb_pos (by norm_num) (by exact_mod_cast (by omega : 1<T))
  have hl := logb_le_clog T (by omega)
  have hcpos : (0:ℝ) < Nat.clog 2 T := hlogpos.trans_le hl
  have hc : 1 ≤ Nat.clog 2 T := by exact_mod_cast (by exact_mod_cast hcpos : 0 < Nat.clog 2 T)
  exact ((Real.logb_le_logb (by norm_num : (1:ℝ)<2) hlogpos hcpos).2 hl).trans
    (logb_le_clog _ hc)

theorem actual_eth_numerics (p : SourceConstants) (M g : ℕ) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (edge : Fin m → Bool → Fin n)
    (hM : 2 ≤ M) (hg : 1 ≤ g) (hgraph : n ≤ M^g)
    (hcutoff : generatedN (cutoffLog p.degree p.deletion) ≤ M)
    (hlarge : 2^(max (32*(1040*(g+1))+16) (8*64)) ≤ M) :
    let k := ethIterations 64 M
    let R := publicGraphRunFrom p M hn hlow hdegree edge k
    1 ≤ k ∧ (supportAmplification^k)^2 ≤ M ∧ M^2 ≤ entryCount R ∧
      2*(1/256:ℝ)*Real.logb 2 (Real.logb 2 (entryCount R)) < k ∧
      R.squareWord.length ≤ M^((g+1)*1040*supportAmplification^k) := by
  let k := ethIterations 64 M
  let R := publicGraphRunFrom p M hn hlow hdegree edge k
  let N := generatedN (publicLogFrom p M n m hn hlow hdegree)
  have hb := publicGraphRunFrom_size_bounds p M hn hlow hdegree edge k
  have hN : N ≤ M^(g+1) := public_floor_polynomial p M g hn hlow hdegree hM hg hgraph hcutoff
  have hT : entryCount R ≤ N^(1040*(2^64)^k) := by
    exact (entries_le_length R).trans (by simpa only [supportAmplification] using hb.2.2)
  have hmargin := eth_margin_from_polynomial_source 64 1040 (g+1) M N
    (by decide) (by decide) (by omega) hN hlarge
  have hgap := eth_loglog_gap N 1040 64 k (entryCount R) (by decide) hT hmargin
  have hmin : M^2 ≤ entryCount R := hb.1
  have hT2 : 2 ≤ entryCount R := (by nlinarith only [hM] : 2 ≤ M^2).trans hmin
  have hreal := real_double_log_le_clog (entryCount R) hT2
  have hgapR : 2*(1/256:ℝ)*Real.logb 2 (Real.logb 2 (entryCount R)) < k := by
    norm_num at hgap
    linarith
  have hk : 1 ≤ k := ethIterations_positive 64 M (by decide)
    ((Nat.pow_le_pow_right (by decide) (show 2*64 ≤ max (32*(1040*(g+1))+16) (8*64) by omega)).trans hlarge)
  have hsqrt : (supportAmplification^k)^2 ≤ M := by
    simpa only [supportAmplification] using ethIterations_square_bound 64 M (by decide) (by omega)
  exact ⟨hk,hsqrt,hmin,hgapR,
    (actual_size_bound p M g hn hlow hdegree edge k hM hg hgraph hcutoff).2⟩

/-- Every fixed reciprocal power of the actual output length is eventually
bounded by `2^M`; this is an output-size theorem, with no machine premise. -/
theorem actual_output_subexponential (p : SourceConstants) (M g u : ℕ) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (edge : Fin m → Bool → Fin n)
    (hM : 2 ≤ M) (hg : 1 ≤ g) (hu : 1 ≤ u) (hgraph : n ≤ M^g)
    (hcutoff : generatedN (cutoffLog p.degree p.deletion) ≤ M)
    (hlarge : 2^(max (32*(u*(g+1)*1040)+16) (8*64)) ≤ M) :
    ((publicGraphRunFrom p M hn hlow hdegree edge (ethIterations 64 M)).squareWord.length)^u ≤ 2^M := by
  have hb := (actual_size_bound p M g hn hlow hdegree edge (ethIterations 64 M)
    hM hg hgraph hcutoff).2
  have hsub := eth_discrete_subexponential_bound 64 1040 (g+1) u M
    (by decide) (by decide) (by omega) hu hlarge
  exact (Nat.pow_le_pow_left hb u).trans (by simpa only [supportAmplification] using hsub)

end CurrentAdditive.V39ActualETHNumerics

#print axioms CurrentAdditive.V39ActualETHNumerics.actual_eth_numerics
#print axioms CurrentAdditive.V39ActualETHNumerics.actual_output_subexponential
