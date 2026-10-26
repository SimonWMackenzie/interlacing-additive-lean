import Mathlib.Tactic

set_option autoImplicit false
namespace CurrentAdditive.FeatureOuterScalarArithmetic

theorem guard (b p : Nat) :
    (2*b+2)+(6*(b+1)+20)+(2*(b+(6*(b+1)+20)*p)+2)+
      (8*(b+(6*(b+1)+20)*p)+8+2)+3 ≤ (1000+1000*p)*(b+1) := by
  nlinarith

theorem prefix_bound (A L scan a b j y c e : Nat)
    (ha : a≤L) (hb : b≤L) (hj : j≤L) (hy : y≤L) (hc : c≤L) (he : e≤L)
    (hscan : scan≤A*(L+1)^5) (hpow : L+1≤(L+1)^5) :
    (2*(a+b+j+y+c)+14+scan+1)+(b+2+2*e+2+1)+(2*y+2)+2 ≤
      (A+32)*(L+1)^5 := by
  nlinarith

theorem eligible (P A G N : Nat) (h : P≤A*N) :
    P+64*G*P+67≤(1+64*G)*A*N+67 := by nlinarith

theorem guarded (guard eligible B A G N : Nat) (hg : guard≤B*N)
    (he : eligible≤(1+64*G)*A*N+67) (hN : 1≤N) :
    guard+eligible+2≤(B+(1+64*G)*A+69)*N := by nlinarith

end CurrentAdditive.FeatureOuterScalarArithmetic
