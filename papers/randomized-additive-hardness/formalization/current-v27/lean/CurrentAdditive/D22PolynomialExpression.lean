import CurrentAdditive.D22NatExpression

/-! A syntax for the literal scalar arithmetic in GeneratedTests, with
proved polynomial growth in 2^L+n+m+1. The dyadic constructor's exponent is
a fixed affine function of L divided by a fixed positive integer. -/
namespace D22PolynomialExpression
open D22NatExpression
open EthInapproximability.CurrentPaper
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
noncomputable section

def base (n m L : ℕ) : ℕ := 2^L+n+m+1
theorem base_pos (n m L : ℕ) : 1≤base n m L := Nat.le_add_left 1 _
theorem L_le_base (n m L : ℕ) : L≤base n m L :=
  (Nat.lt_two_pow_self.le).trans (by unfold base; omega)

def dyadicExpr (a b d : ℕ) : Expr :=
  .unary .pow2 (.binary .quot
    (.binary (.old .add) (.binary (.old .mul) (.const a) (.var 2)) (.const b))
    (.const (max 1 d)))

inductive Term where
  | var (j : Fin 3) | const (c : ℕ) | dyadic (a b d : ℕ)
  | pred (a : Term) | powCeil (a : Term)
  | binary (b : D22NatExpression.Binary) (a c : Term)
  deriving DecidableEq
def Term.expr : Term → Expr
  | .var j => .var j | .const c => .const c
  | .dyadic a b d => dyadicExpr a b d
  | .pred a => .unary .pred a.expr
  | .powCeil a => .unary .pow2 (.unary .clog a.expr)
  | .binary b a c => .binary b a.expr c.expr
def Term.eval (t : Term) := t.expr.eval
def Term.coefficient : Term → ℕ
  | .var _ => 1 | .const c => c+1
  | .dyadic a b d => 2^b+a+b+d+3
  | .pred a => a.coefficient
  | .powCeil a => 2*a.coefficient+2
  | .binary _ a c => a.coefficient+c.coefficient+a.coefficient*c.coefficient+1
def Term.degree : Term → ℕ
  | .var _ => 1 | .const _ => 0
  | .dyadic a _ _ => a+1
  | .pred a => a.degree | .powCeil a => a.degree
  | .binary _ a c => a.degree+c.degree

theorem pow_clog_bound (x : ℕ) : 2^(Nat.clog 2 x)≤2*(x+1) := by
  by_cases hx : x≤1
  · interval_cases x <;> norm_num
  · have hx1 : 1<x := by omega
    have hpos : 0<Nat.clog 2 x := by
      have h := (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).2
        (show 2^0<x by simpa using hx1)
      simpa using h
    have h := Nat.pow_pred_clog_lt_self (by decide : 1<2) hx1
    change 2^(Nat.clog 2 x-1)<x at h
    have he : Nat.clog 2 x=(Nat.clog 2 x-1)+1 := by omega
    rw [he,pow_add]
    norm_num
    nlinarith

theorem dyadic_peak (a b d n m L : ℕ) :
    (dyadicExpr a b d).peak n m L≤(2^b+a+b+d+3)*(base n m L)^(a+1) := by
  let W : ℕ := base n m L
  let C : ℕ := 2^b+a+b+d+3
  have hB : 1≤2^b := Nat.one_le_two_pow
  have hW : 1≤W := base_pos n m L
  have hL : L≤W := L_le_base n m L
  have hN : 2^L≤W := by dsimp [W,base]; omega
  have hWa : W^a≤W^(a+1) := Nat.pow_le_pow_right hW (by omega)
  have hW1 : W≤W^(a+1) := by simpa using Nat.pow_le_pow_right hW (by omega : 1≤a+1)
  have hCp : 1≤C := by dsimp [C]; omega
  have hpow : 2^((a*L+b)/(max 1 d))≤C*W^(a+1) := by
    calc
      _ ≤ 2^(a*L+b) := Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)
      _=2^b*(2^L)^a := by rw [pow_add,Nat.mul_comm a L,pow_mul]; ring
      _ ≤ C*W^(a+1) := Nat.mul_le_mul (by dsimp [C]; omega)
        ((Nat.pow_le_pow_left hN a).trans hWa)
  have hCW : W≤C*W^(a+1) := hW1.trans (Nat.le_mul_of_pos_left _ (by omega))
  have ha : a≤C*W^(a+1) := by
    have h : a≤C := by dsimp [C]; omega
    exact h.trans (Nat.le_mul_of_pos_right _ (by positivity))
  have hb : b≤C*W^(a+1) := by
    have h : b≤C := by dsimp [C]; omega
    exact h.trans (Nat.le_mul_of_pos_right _ (by positivity))
  have hd : max 1 d≤C*W^(a+1) := by
    have h : max 1 d≤C := by dsimp [C]; omega
    exact h.trans (Nat.le_mul_of_pos_right _ (by positivity))
  have hab : a*L+b≤C*W^(a+1) := by
    have hac : a+b≤C := by dsimp [C]; omega
    calc
      _ ≤ (a+b)*W := by nlinarith
      _ ≤ C*W^(a+1) := Nat.mul_le_mul hac hW1
  have ham : a*L≤C*W^(a+1) := by omega
  have hdiv : (a*L+b)/max 1 d≤C*W^(a+1) := (Nat.div_le_self _ _).trans hab
  change _≤C*W^(a+1)
  change max (2^((a*L+b)/(max 1 d)))
    (max ((a*L+b)/max 1 d) (max (max (a*L+b) (max (max (a*L) (max a L)) b))
      (max 1 d)))≤C*W^(a+1)
  exact max_le hpow (max_le hdiv (max_le (max_le hab (max_le (max_le ham (max_le ha (hL.trans hCW))) hb)) hd))

theorem binary_value_bound (b : D22NatExpression.Binary) (a c : ℕ) :
    b.value a c≤a+c+a*c+1 := by
  cases b with
  | quot => exact (Nat.div_le_self _ _).trans (by omega)
  | old b => cases b <;> simp [Binary.value,V22UnaryExpression.Binary.value] <;> omega
  | le => simp only [Binary.value]; split <;> omega

theorem Term.peak_bound (t : Term) (n m L : ℕ) :
    t.expr.peak n m L≤t.coefficient*(base n m L)^t.degree := by
  let W := base n m L
  have hW : 1≤W := base_pos n m L
  induction t with
  | var j =>
    change values n m L j≤1*W^1
    simp only [one_mul,pow_one]
    fin_cases j
    · change n≤base n m L; unfold base; have h := Nat.one_le_two_pow (n:=L); omega
    · change m≤base n m L; unfold base; have h := Nat.one_le_two_pow (n:=L); omega
    · exact L_le_base n m L
  | const c => simp only [Term.expr,Expr.peak,Term.coefficient,Term.degree,pow_zero]; omega
  | dyadic a b d => exact dyadic_peak a b d n m L
  | pred a ih =>
    change max (a.expr.eval n m L-1) (a.expr.peak n m L)≤a.coefficient*W^a.degree
    exact max_le ((Nat.sub_le _ _).trans ((a.expr.eval_le_peak n m L).trans ih)) ih
  | powCeil a ih =>
    have ha := (a.expr.eval_le_peak n m L).trans ih
    have hpow := pow_clog_bound (a.expr.eval n m L)
    have hclog : Nat.clog 2 (a.expr.eval n m L)≤a.expr.eval n m L :=
      (Nat.clog_le_iff_le_pow (by decide)).2 Nat.lt_two_pow_self.le
    have hWp : 1≤W^a.degree := one_le_pow₀ hW
    change max (2^(Nat.clog 2 (a.expr.eval n m L)))
      (max (Nat.clog 2 (a.expr.eval n m L)) (a.expr.peak n m L))≤(2*a.coefficient+2)*W^a.degree
    apply max_le
    · nlinarith
    · apply max_le <;> nlinarith
  | binary b a c iha ihc =>
    let da := a.degree
    let dc := c.degree
    change a.expr.peak n m L≤a.coefficient*W^da at iha
    change c.expr.peak n m L≤c.coefficient*W^dc at ihc
    have hpa : W^da≤W^(da+dc) := Nat.pow_le_pow_right hW (by omega)
    have hpc : W^dc≤W^(da+dc) := Nat.pow_le_pow_right hW (by omega)
    have hWp : 1≤W^(da+dc) := one_le_pow₀ hW
    have ha := (a.expr.eval_le_peak n m L).trans iha
    have hc := (c.expr.eval_le_peak n m L).trans ihc
    have ham := Nat.mul_le_mul_left a.coefficient hpa
    have hcm := Nat.mul_le_mul_left c.coefficient hpc
    have hp : a.expr.eval n m L*c.expr.eval n m L≤
        (a.coefficient*c.coefficient)*W^(da+dc) := by
      calc
        _ ≤ (a.coefficient*W^da)*(c.coefficient*W^dc) := Nat.mul_le_mul ha hc
        _=(a.coefficient*c.coefficient)*W^(da+dc) := by rw [pow_add]; ring
    have hv := binary_value_bound b (a.expr.eval n m L) (c.expr.eval n m L)
    change max (b.value (a.expr.eval n m L) (c.expr.eval n m L))
      (max (a.expr.peak n m L) (c.expr.peak n m L))≤
      (a.coefficient+c.coefficient+a.coefficient*c.coefficient+1)*W^(da+dc)
    apply max_le
    · nlinarith
    · apply max_le <;> nlinarith

theorem inputLength_bound (n m L : ℕ) : inputLength n m L≤10*base n m L := by
  have hL := L_le_base n m L
  have hW := base_pos n m L
  have hN : 1≤2^L := Nat.one_le_two_pow
  unfold inputLength input
  rw [BitMachineBankCodec.encode_length]
  simp only [List.length_replicate,Fin.sum_univ_succ,Fin.sum_univ_zero]
  change 2*(n+(m+(L+0)))+3≤10*base n m L
  unfold base at *
  omega

noncomputable def Term.clockCoefficient (t : Term) := t.expr.coefficient*(t.coefficient+12)^2
def Term.clockDegree (t : Term) := 2*(t.degree+1)
theorem Term.clock_polynomial (t : Term) (n m L : ℕ) :
    t.expr.clock n m L≤t.clockCoefficient*(base n m L)^t.clockDegree := by
  let W := base n m L
  have hW : 1≤W := base_pos n m L
  have hP : 1≤W^(t.degree+1) := one_le_pow₀ hW
  have hW1 : W≤W^(t.degree+1) := by simpa using Nat.pow_le_pow_right hW (by omega : 1≤t.degree+1)
  have hWd : W^t.degree≤W^(t.degree+1) := Nat.pow_le_pow_right hW (by omega)
  have hinput := inputLength_bound n m L
  have hp : inputLength n m L+t.coefficient*W^t.degree+2≤
      (t.coefficient+12)*W^(t.degree+1) := by nlinarith
  have hc := t.expr.clock_le_of_peak n m L (t.coefficient*W^t.degree) (t.peak_bound n m L)
  calc
    _ ≤ t.expr.coefficient*((t.coefficient+12)*W^(t.degree+1))^2 :=
      hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp 2))
    _=t.clockCoefficient*W^t.clockDegree := by
      unfold Term.clockCoefficient Term.clockDegree
      rw [Nat.mul_comm 2 (t.degree+1),pow_mul,mul_pow]
      ring

#print axioms Term.peak_bound
#print axioms Term.clock_polynomial
end
end D22PolynomialExpression
