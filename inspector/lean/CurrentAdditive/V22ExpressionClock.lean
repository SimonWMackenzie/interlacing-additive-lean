import CurrentAdditive.V22UnaryExpression

namespace V22UnaryExpression
open EthInapproximability.CurrentPaper
noncomputable def primitiveCoefficient : ℕ := UnaryBinaryEncoding.coefficient+20
def Expr.peak : Expr → ℕ → ℕ → ℕ
  | .vertex,n,_ => n
  | .iteration,_,k => k
  | .const c,_,_ => c
  | .unary u a,n,k => max (u.value (a.eval n k)) (a.peak n k)
  | .binary u a b,n,k => max (u.value (a.eval n k) (b.eval n k))
      (max (a.peak n k) (b.peak n k))
noncomputable def Expr.coefficient : Expr → ℕ
  | .vertex => 1 | .iteration => 1 | .const _ => 1
  | .unary _ a => a.coefficient+primitiveCoefficient+4
  | .binary _ a b => a.coefficient+b.coefficient+40
theorem Expr.eval_le_peak (e : Expr) (n k : ℕ) : e.eval n k≤e.peak n k := by
  cases e <;> simp [Expr.eval,Expr.peak]
theorem Unary.clock_le (u : Unary) (a M : ℕ) (ha : a≤M) (hv : u.value a≤M) :
    u.clock a≤primitiveCoefficient*(M+1)^2 := by
  have hM : M+1≤(M+1)^2 := by nlinarith
  have hC : 20≤primitiveCoefficient := by unfold primitiveCoefficient; omega
  cases u with
  | pred => simp only [Unary.clock]; nlinarith
  | clog =>
      simp only [Unary.clock]
      apply Nat.mul_le_mul (by unfold primitiveCoefficient; omega)
      exact Nat.pow_le_pow_left (by omega) 2
  | pow2 =>
      change 16*2^a≤_
      change 2^a≤M at hv
      nlinarith
theorem Binary.clock_le (u : Binary) (a b M : ℕ) (ha : a≤M) (hb : b≤M) :
    u.clock a b≤8*(M+1)^2 := by
  have hM : M+1≤(M+1)^2 := by nlinarith
  cases u with
  | add => simp only [Binary.clock]; nlinarith
  | mul =>
      have h := Nat.pow_le_pow_left (show a+b+2≤2*(M+1) by omega) 2
      simp only [Binary.clock]
      nlinarith
  | max => simp only [Binary.clock]; nlinarith

/-- Uniform arithmetic cost: a fixed polynomial in the supplied input lengths
and the largest unary scalar actually constructed by this fixed expression. -/
theorem Expr.clock_le_of_peak (e : Expr) (n k M : ℕ) (hpeak : e.peak n k≤M) :
    e.clock n k≤e.coefficient*(n+k+M+2)^2 := by
  let W := n+k+M+2
  have hW : 1≤W := by dsimp [W]; omega
  have hWM : M+1≤W := by dsimp [W]; omega
  have hMW : M≤W := by omega
  have hW2 : W≤W^2 := by nlinarith
  have hM2 : (M+1)^2≤W^2 := Nat.pow_le_pow_left hWM 2
  induction e with
  | vertex => simp only [Expr.clock,Expr.coefficient]; dsimp [W] at *; nlinarith
  | iteration => simp only [Expr.clock,Expr.coefficient]; dsimp [W] at *; nlinarith
  | const c => change 1≤1*W^2; nlinarith
  | unary u a ih =>
      change max (u.value (a.eval n k)) (a.peak n k)≤M at hpeak
      obtain ⟨hv,hp⟩ := max_le_iff.mp hpeak
      have ha := (a.eval_le_peak n k).trans hp
      have hc := ih hp
      change a.clock n k≤a.coefficient*W^2 at hc
      have hu := (u.clock_le (a.eval n k) M ha hv).trans (Nat.mul_le_mul_left _ hM2)
      change a.clock n k+2*a.eval n k+2+u.clock (a.eval n k)≤
        (a.coefficient+primitiveCoefficient+4)*W^2
      nlinarith
  | binary u a b iha ihb =>
      change max (u.value (a.eval n k) (b.eval n k)) (max (a.peak n k) (b.peak n k))≤M at hpeak
      obtain ⟨_,hab⟩ := max_le_iff.mp hpeak
      obtain ⟨hpa,hpb⟩ := max_le_iff.mp hab
      have ha := (a.eval_le_peak n k).trans hpa
      have hb := (b.eval_le_peak n k).trans hpb
      have hca := iha hpa
      have hcb := ihb hpb
      change a.clock n k≤a.coefficient*W^2 at hca
      change b.clock n k≤b.coefficient*W^2 at hcb
      have hu := (u.clock_le (a.eval n k) (b.eval n k) M ha hb).trans
        (Nat.mul_le_mul_left 8 hM2)
      have hinput : n+k+1≤W := by dsimp [W]; omega
      change 4*(n+k+1)+a.clock n k+b.clock n k+3*a.eval n k+3*b.eval n k+17+
        2*(a.eval n k+b.eval n k+1)+2+u.clock (a.eval n k) (b.eval n k)≤
        (a.coefficient+b.coefficient+40)*W^2
      nlinarith
theorem Expr.clock_polynomial (e : Expr) (n k : ℕ) :
    e.clock n k≤e.coefficient*(n+k+e.peak n k+2)^2 := e.clock_le_of_peak n k _ le_rfl

/-- Positivity here concerns every scalar subtree, so a product's factors
cannot be hidden by a zero factor. -/
def Expr.Positive : Expr → ℕ → ℕ → Prop
  | .vertex,n,_ => 0<n
  | .iteration,_,k => 0<k
  | .const c,_,_ => 0<c
  | .unary u a,n,k => 0<u.value (a.eval n k) ∧ a.Positive n k
  | .binary u a b,n,k => 0<u.value (a.eval n k) (b.eval n k) ∧ a.Positive n k ∧ b.Positive n k
theorem Expr.eval_pos (e : Expr) (n k : ℕ) (h : e.Positive n k) : 0<e.eval n k := by
  cases e <;> first | exact h | exact h.1

/-- Besides the leaves, only operands of the two shrinking operations need
independent bounds. All other positive arithmetic is bounded by its result. -/
def Expr.Safe (M : ℕ) : Expr → ℕ → ℕ → Prop
  | .vertex,n,_ => n≤M
  | .iteration,_,k => k≤M
  | .const c,_,_ => c≤M
  | .unary .pred a,n,k => a.eval n k≤M ∧ a.Safe M n k
  | .unary .clog a,n,k => a.eval n k≤M ∧ a.Safe M n k
  | .unary .pow2 a,n,k => a.Safe M n k
  | .binary _ a b,n,k => a.Safe M n k ∧ b.Safe M n k
theorem Expr.peak_le (e : Expr) (n k M : ℕ)
    (hp : e.Positive n k) (hs : e.Safe M n k) (hv : e.eval n k≤M) :
    e.peak n k≤M := by
  induction e with
  | vertex => exact hv
  | iteration => exact hv
  | const c => exact hv
  | unary u a ih =>
      change max (u.value (a.eval n k)) (a.peak n k)≤M
      apply max_le hv
      cases u with
      | pred => exact ih hp.2 hs.2 hs.1
      | clog => exact ih hp.2 hs.2 hs.1
      | pow2 =>
          apply ih hp.2 hs
          exact (Nat.lt_two_pow_self (n:=a.eval n k)).le.trans hv
  | binary u a b iha ihb =>
      apply max_le hv
      have ha := a.eval_pos n k hp.2.1
      have hb := b.eval_pos n k hp.2.2
      have hchild : a.eval n k≤Binary.value u (a.eval n k) (b.eval n k) := by
        cases u <;> simp only [Expr.eval,Binary.value]
        · omega
        · exact Nat.le_mul_of_pos_right _ hb
        · exact le_max_left _ _
      have hchildB : b.eval n k≤Binary.value u (a.eval n k) (b.eval n k) := by
        cases u <;> simp only [Binary.value]
        · omega
        · exact Nat.le_mul_of_pos_left _ ha
        · exact le_max_right _ _
      exact max_le (iha hp.2.1 hs.1 (hchild.trans hv))
        (ihb hp.2.2 hs.2 (hchildB.trans hv))

#print axioms Expr.clock_polynomial
#print axioms Expr.peak_le
end V22UnaryExpression
