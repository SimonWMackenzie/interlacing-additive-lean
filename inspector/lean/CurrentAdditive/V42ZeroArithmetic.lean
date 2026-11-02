import CurrentAdditive.V42FullScheduleClock
import CurrentAdditive.V42RawSamplerClock

/-! A zero-round arithmetic cap for the actual unchanged schedule compiler.
The values and clocks here always run at K=0; only the scalar envelope is
borrowed from the K=1 arithmetic bound. No matrix at K=1 is substituted. -/
namespace CurrentAdditive.V42ZeroAccess
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open V22UnaryExpression V42FullScheduleExpressions V42FullScheduleBatch V42FullSchedulePeak
open V42RuntimeSchedule
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

theorem unary_value_mono (u : Unary) {a b : ℕ} (h : a ≤ b) : u.value a ≤ u.value b := by
  cases u with
  | pred => exact Nat.sub_le_sub_right h 1
  | clog => exact Nat.clog_mono_right 2 h
  | pow2 => exact Nat.pow_le_pow_right (by decide) h

theorem binary_value_mono (u : Binary) {a A b B : ℕ} (ha : a ≤ A) (hb : b ≤ B) :
    u.value a b ≤ u.value A B := by
  cases u with
  | add => exact Nat.add_le_add ha hb
  | mul => exact Nat.mul_le_mul ha hb
  | max => exact max_le_max ha hb

theorem eval_mono_iteration (e : Expr) (n : ℕ) {k K : ℕ} (hk : k ≤ K) :
    e.eval n k ≤ e.eval n K := by
  induction e with
  | vertex => exact le_rfl
  | iteration => exact hk
  | const c => exact le_rfl
  | unary u a ih => exact unary_value_mono u ih
  | binary u a b iha ihb => exact binary_value_mono u iha ihb

theorem peak_mono_iteration (e : Expr) (n : ℕ) {k K : ℕ} (hk : k ≤ K) :
    e.peak n k ≤ e.peak n K := by
  induction e with
  | vertex => exact le_rfl
  | iteration => exact hk
  | const c => exact le_rfl
  | unary u a ih =>
      exact max_le_max (unary_value_mono u (eval_mono_iteration a n hk)) ih
  | binary u a b iha ihb =>
      exact max_le_max (binary_value_mono u (eval_mono_iteration a n hk)
        (eval_mono_iteration b n hk)) (max_le_max iha ihb)

theorem all_peaks_zero (n edgeCount : ℕ) (cc δv ζ : ℚ)
    (hn : 2 ≤ n) (ht : FullTests cc (Nat.clog 2 n) edgeCount δv ζ) :
    ∀ i : Fin 19, (expressions i).peak n 0 ≤ cap n 1 := by
  intro i
  exact (peak_mono_iteration (expressions i) n (by omega : 0 ≤ 1)).trans
    (all_peaks n 1 edgeCount cc δv ζ hn (by omega) ht i)

private theorem prefix_le {q : ℕ} (bits : List Bool) (outs : Fin q → List Bool)
    (times : Fin q → ℕ) (C : ℕ)
    (h : ∀ i, 2*bits.length+times i+2*(outs i).length+7 ≤ C)
    (j : ℕ) (hj : j ≤ q) :
    V22ParameterBatch.clockPrefix bits outs times j ≤ j*C := by
  induction j with
  | zero => simp [V22ParameterBatch.clockPrefix]
  | succ j ih =>
      have hlt : j<q := by omega
      rw [V22ParameterBatch.clockPrefix,dif_pos hlt]
      have hp := ih (by omega)
      have hi := h ⟨j,hlt⟩
      nlinarith

/-- This clock theorem requires only actual scalar peaks, not positivity of
every subexpression. In particular a zero iteration leaf is permitted. -/
theorem batch_clock_of_peaks (n k M : ℕ)
    (hp : ∀ i : Fin 19, (expressions i).peak n k ≤ M) :
    V42FullScheduleBatch.clock n k ≤ V42FullScheduleClock.coefficient*(n+k+M+2)^2 := by
  let W := n+k+M+2
  have hW : 1 ≤ W := by dsimp [W]; omega
  have hW2 : W ≤ W^2 := by nlinarith
  have hlen : (MatrixUnaryArithmetic.encodeInput n k).length ≤ W := by
    simp only [MatrixUnaryArithmetic.encodeInput,
      List.length_append,List.length_replicate,List.length_cons]
    dsimp [W]; omega
  have hcost (i : Fin 19) :
      2*(MatrixUnaryArithmetic.encodeInput n k).length+
        times n k i+2*(results n k i).length+7 ≤ V42FullScheduleClock.coefficientSum*W^2 := by
    have hv := ((expressions i).eval_le_peak n k).trans (hp i)
    have htime := (expressions i).clock_le_of_peak n k M (hp i)
    change times n k i ≤ (expressions i).coefficient*W^2 at htime
    have hsum : (expressions i).coefficient+11 ≤ V42FullScheduleClock.coefficientSum := by
      change (expressions i).coefficient+11 ≤ ∑ j : Fin 19,((expressions j).coefficient+11)
      exact Finset.single_le_sum (f := fun j : Fin 19 => (expressions j).coefficient+11)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hmul := Nat.mul_le_mul_right (W^2) hsum
    have hval : (results n k i).length ≤ W := by
      simp only [results,List.length_replicate]
      exact hv.trans (by dsimp [W]; omega)
    nlinarith
  have hprefix := prefix_le _ (results n k) (times n k)
    (V42FullScheduleClock.coefficientSum*W^2) hcost 19 le_rfl
  change V22ParameterBatch.clockPrefix _ _ _ 19+1 ≤ V42FullScheduleClock.coefficient*W^2
  unfold V42FullScheduleClock.coefficient
  nlinarith

theorem batch_zero_exponential (n edgeCount : ℕ) (cc δv ζ : ℚ)
    (hn : 2 ≤ n) (ht : FullTests cc (Nat.clog 2 n) edgeCount δv ζ) :
    V42FullScheduleBatch.clock n 0 ≤ 2^(V42FullScheduleClock.exponent*R n 1) := by
  have hL : 16 ≤ Nat.clog 2 n := ht.1.2.2.1
  have hR : 1 ≤ R n 1 := by unfold R; nlinarith
  let M := cap n 1
  have hM : 1 ≤ M := Nat.one_le_two_pow
  have hp := all_peaks_zero n edgeCount cc δv ζ hn ht
  have hnM : n ≤ M := by simpa only [expressions,Expr.peak] using hp 3
  have hW : n+0+M+2 ≤ 5*M := by omega
  have hp2 := Nat.pow_le_pow_left hW 2
  have hclock := batch_clock_of_peaks n 0 M hp
  have hc : V42FullScheduleClock.coefficient*(n+0+M+2)^2 ≤
      25*V42FullScheduleClock.coefficient*M^2 := by nlinarith
  have hC : 25*V42FullScheduleClock.coefficient ≤
      2^(25*V42FullScheduleClock.coefficient*R n 1) := by
    exact Nat.lt_two_pow_self.le.trans
      (Nat.pow_le_pow_right (by decide) (by nlinarith))
  calc
    V42FullScheduleBatch.clock n 0 ≤ 25*V42FullScheduleClock.coefficient*M^2 := hclock.trans hc
    _ ≤ 2^(25*V42FullScheduleClock.coefficient*R n 1)*M^2 := Nat.mul_le_mul_right _ hC
    _ = _ := by
      dsimp [M,cap,V42FullScheduleClock.exponent]
      rw [←pow_mul,←pow_add]
      congr 1
      ring

theorem raw_graph_zero_exponential (bits : List Bool) (n edgeCount : ℕ) (cc δv ζ : ℚ)
    (hn : 2 ≤ n) (ht : FullTests cc (Nat.clog 2 n) edgeCount δv ζ) :
    V42RawGraphParameters.clock bits n 0 ≤
      102*(bits.length+1)^3+2^((V42FullScheduleClock.exponent+6)*R n 1) := by
  have hL : 16 ≤ Nat.clog 2 n := ht.1.2.2.1
  have hR : 1 ≤ R n 1 := by unfold R; nlinarith
  have hclock := batch_zero_exponential n edgeCount cc δv ζ hn ht
  let Z := 2^(V42FullScheduleClock.exponent*R n 1)
  have hp := all_peaks_zero n edgeCount cc δv ζ hn ht
  have hcap : cap n 1 ≤ Z := Nat.pow_le_pow_right (by decide) (by
    unfold V42FullScheduleClock.exponent
    nlinarith)
  have hnCap : n ≤ cap n 1 := by simpa only [expressions,Expr.peak] using hp 3
  have hnZ : n ≤ Z := hnCap.trans hcap
  have hZ : 1 ≤ Z := Nat.one_le_two_pow
  have hlen : bits.length ≤ (bits.length+1)^3 := by
    nlinarith [Nat.zero_le (bits.length^3),Nat.zero_le (bits.length^2)]
  have hexp : 64*Z ≤ 2^((V42FullScheduleClock.exponent+6)*R n 1) := by
    calc
      64*Z=2^(V42FullScheduleClock.exponent*R n 1+6) := by dsimp [Z]; rw [pow_add]; norm_num; ring
      _ ≤ 2^((V42FullScheduleClock.exponent+6)*R n 1) := Nat.pow_le_pow_right (by decide) (by nlinarith)
  unfold V42RawGraphParameters.clock V42RawGraphParameters.vertexClock V42RawGraphParameters.pairClock
  simp only [MatrixUnaryArithmetic.encodeInput,
    List.length_append,List.length_replicate,List.length_cons]
  change V42FullScheduleBatch.clock n 0 ≤ Z at hclock
  nlinarith

#print axioms all_peaks_zero
#print axioms batch_zero_exponential
#print axioms raw_graph_zero_exponential
end
end CurrentAdditive.V42ZeroAccess
