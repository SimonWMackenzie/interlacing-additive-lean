import CurrentAdditive.D22PacketPrimitives

/-! Ordinary arithmetic subexpressions have a polynomial clock in their
three unary input lengths. This sharper bound is useful for item-law and
activity callbacks whose third input is s rather than a logarithm. -/
namespace D22ArithmeticGrowth
open D22PolynomialExpression D22NatExpression
open EthInapproximability.CurrentPaper
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

def Pure : Term → Prop
  | .var _ | .const _ => True
  | .dyadic _ _ _ => False
  | .pred a | .powCeil a => Pure a
  | .binary _ a b => Pure a ∧ Pure b
instance (t : Term) : Decidable (Pure t) := by
  induction t <;> dsimp only [Pure] <;> infer_instance

theorem peak_bound (t : Term) (ht : Pure t) (n m L W : ℕ)
    (hW : 1≤W) (hn : n≤W) (hm : m≤W) (hL : L≤W) :
    t.expr.peak n m L≤t.coefficient*W^t.degree := by
  induction t with
  | var j =>
    change values n m L j≤1*W^1
    simp only [one_mul,pow_one]
    fin_cases j <;> assumption
  | const c => simp only [Term.expr,Expr.peak,Term.coefficient,Term.degree,pow_zero]; omega
  | dyadic a b d => exact ht.elim
  | pred a ih =>
    have h := ih ht
    change max (a.expr.eval n m L-1) (a.expr.peak n m L)≤a.coefficient*W^a.degree
    exact max_le ((Nat.sub_le _ _).trans ((a.expr.eval_le_peak n m L).trans h)) h
  | powCeil a ih =>
    have h := ih ht
    have ha := (a.expr.eval_le_peak n m L).trans h
    have hpow := D22PolynomialExpression.pow_clog_bound (a.expr.eval n m L)
    have hclog : Nat.clog 2 (a.expr.eval n m L)≤a.expr.eval n m L :=
      (Nat.clog_le_iff_le_pow (by decide)).2 Nat.lt_two_pow_self.le
    have hWp : 1≤W^a.degree := one_le_pow₀ hW
    change max (2^(Nat.clog 2 (a.expr.eval n m L)))
      (max (Nat.clog 2 (a.expr.eval n m L)) (a.expr.peak n m L))≤(2*a.coefficient+2)*W^a.degree
    apply max_le
    · nlinarith
    · apply max_le <;> nlinarith
  | binary b a c iha ihc =>
    have iha := iha ht.1
    have ihc := ihc ht.2
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
    have hv := D22PolynomialExpression.binary_value_bound b (a.expr.eval n m L) (c.expr.eval n m L)
    change max (b.value (a.expr.eval n m L) (c.expr.eval n m L))
      (max (a.expr.peak n m L) (c.expr.peak n m L))≤
      (a.coefficient+c.coefficient+a.coefficient*c.coefficient+1)*W^(da+dc)
    apply max_le
    · nlinarith
    · apply max_le <;> nlinarith

theorem clock_bound (t : Term) (ht : Pure t) (n m L : ℕ) :
    t.expr.clock n m L≤t.clockCoefficient*(n+m+L+1)^t.clockDegree := by
  let W := n+m+L+1
  have hW : 1≤W := by dsimp [W]; omega
  have hP : 1≤W^(t.degree+1) := one_le_pow₀ hW
  have hW1 : W≤W^(t.degree+1) := by simpa using Nat.pow_le_pow_right hW (by omega : 1≤t.degree+1)
  have hWd : W^t.degree≤W^(t.degree+1) := Nat.pow_le_pow_right hW (by omega)
  have hinput : inputLength n m L≤10*W := by
    unfold inputLength input
    rw [BitMachineBankCodec.encode_length]
    simp only [List.length_replicate,Fin.sum_univ_succ,Fin.sum_univ_zero]
    change 2*(n+(m+(L+0)))+3≤10*W
    dsimp [W]
    omega
  have hp : inputLength n m L+t.coefficient*W^t.degree+2≤
      (t.coefficient+12)*W^(t.degree+1) := by nlinarith
  have hpeak := peak_bound t ht n m L W hW (by dsimp [W]; omega)
    (by dsimp [W]; omega) (by dsimp [W]; omega)
  have hc := t.expr.clock_le_of_peak n m L (t.coefficient*W^t.degree) hpeak
  calc
    _ ≤ t.expr.coefficient*((t.coefficient+12)*W^(t.degree+1))^2 :=
      hc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp 2))
    _=t.clockCoefficient*W^t.clockDegree := by
      unfold Term.clockCoefficient Term.clockDegree
      rw [Nat.mul_comm 2 (t.degree+1),pow_mul,mul_pow]
      ring

theorem outputs (t : Term) (ht : Pure t) (n m L : ℕ) :
    t.expr.machine.OutputsWithin (input n m L) (List.replicate (t.eval n m L) true)
      (t.clockCoefficient*(n+m+L+1)^t.clockDegree) :=
  BitMachine.outputsWithin_mono _ (t.expr.outputs n m L) (clock_bound t ht n m L)

#print axioms outputs
end
end D22ArithmeticGrowth
