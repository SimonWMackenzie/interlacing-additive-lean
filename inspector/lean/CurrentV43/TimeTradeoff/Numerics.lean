import CurrentAdditive.V42UniformReduction
import CurrentAdditive.V42UniversalReduction

/-! v43 main.tex 3238--3287, source SHA256
bfde23b90f50785939095a6d37b7b247965ee6c45beaca9011a8963dec3cc9d6.
Pure resource accounting for `thm:time-tradeoff`. These lemmas do not assert
existence of a SAT machine; physical callers must supply their actual runs.
The schedule is charged in N+k, without imposing k <= poly(N). -/
namespace CurrentV43.TimeTradeoff

/-- Source-variable bound in the randomized construction. -/
def randomizedSize (C N k : ℕ) : ℕ := (N+2)^(C*(k+1))
/-- Source-variable bound in the deterministic construction. -/
def deterministicSize (A C N k : ℕ) : ℕ := (N+2)^(C*A^k)

private theorem add_le_power (N k : ℕ) : N+k+2 ≤ (N+2)^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k+1+1=(k+1)+1 by omega,pow_succ]
    have hp : 1 ≤ (N+2)^(k+1) := Nat.one_le_pow _ _ (by omega)
    nlinarith

/-- Printing a unary gap and computing it in polynomial(N+k) is paid by S.
This holds even for gap functions growing faster than every polynomial. -/
theorem randomizedSize_dominates (C N k : ℕ) (hC : 1 ≤ C) :
    N+k+2 ≤ randomizedSize C N k := by
  exact (add_le_power N k).trans (Nat.pow_le_pow_right (by omega)
    (Nat.le_mul_of_pos_left _ hC))

private theorem succ_le_power (A k : ℕ) (hA : 2 ≤ A) : k+1 ≤ A^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    nlinarith

theorem deterministicSize_dominates (A C N k : ℕ) (hA : 2 ≤ A) (hC : 1 ≤ C) :
    N+k+2 ≤ deterministicSize A C N k := by
  exact (add_le_power N k).trans (Nat.pow_le_pow_right (by omega)
    ((succ_le_power A k hA).trans (Nat.le_mul_of_pos_left _ hC)))

/-- A fixed polynomial of a quantity bounded by S is a fixed polynomial of S. -/
theorem polynomial_charge {S x : ℕ} (hS : 1 ≤ S) (hx : x ≤ S) (c d : ℕ) :
    c*(x+1)^d ≤ (c*2^d)*S^d := by
  have hp : x+1 ≤ 2*S := by omega
  calc
    _ ≤ c*(2*S)^d := Nat.mul_le_mul_left c (Nat.pow_le_pow_left hp d)
    _ = _ := by rw [mul_pow]; ring

/-- Source preparation, computation of k, table construction, and the
polynomial-time estimator/comparator may all be charged separately. -/
theorem charged_composition {N k S tsource tgap tconstruct testimate : ℕ}
    (hdom : N+k+2 ≤ S) (cs ds cg dg ce de : ℕ)
    (hsource : tsource ≤ cs*(N+1)^ds)
    (hgap : tgap ≤ cg*(N+k+1)^dg)
    (hconstruct : tconstruct ≤ S)
    (hestimate : testimate ≤ ce*(S+1)^de) :
    tsource+tgap+tconstruct+testimate ≤
      (cs+cg+1+ce*2^de)*S^(ds+dg+de+1) := by
  have hS : 1 ≤ S := by omega
  have hN : N+1 ≤ S := by omega
  have hNk : N+k+1 ≤ S := by omega
  have hpow (d : ℕ) (hd : d ≤ ds+dg+de+1) : S^d ≤ S^(ds+dg+de+1) :=
    Nat.pow_le_pow_right hS hd
  have hs := hsource.trans (Nat.mul_le_mul_left cs
    ((Nat.pow_le_pow_left hN ds).trans (hpow ds (by omega))))
  have hg := hgap.trans (Nat.mul_le_mul_left cg
    ((Nat.pow_le_pow_left hNk dg).trans (hpow dg (by omega))))
  have hc := hconstruct.trans (by simpa only [pow_one] using hpow 1 (by omega))
  have he := (polynomial_charge hS (le_refl S) ce de).trans
    (Nat.mul_le_mul_left (ce*2^de) (hpow de (by omega)))
  have he' := hestimate.trans he
  nlinarith

#print axioms randomizedSize_dominates
#print axioms deterministicSize_dominates
#print axioms charged_composition
end CurrentV43.TimeTradeoff

