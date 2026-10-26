import CurrentAdditive.V42WidthPrimitives
import CurrentAdditive.V42RuntimeSchedule

/-! Small arithmetic on the unary length L of the positive source size.
Only s and q1 are constructed as unary values; they are linear in L.
The remaining natural outputs are exponents for the binary dyadic writer. -/
namespace CurrentAdditive.V42FullWidthExpressions
open V22UnaryExpression V42WidthPrimitives
open V42Schedule V42PublicSchedule
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

def add := Expr.binary .add
def mul := Expr.binary .mul
def c := Expr.const
def ellE := Expr.unary .clog (add .vertex (c 1))
def kE := add (c 16) ellE
def sE := Expr.unary .pow2 kE
def q1E := Expr.unary .pred (Expr.unary .pred sE)
def q2Exponent := add .vertex (mul (c 2) kE)
def wExponent := mul (c 8) kE
def QExponent := mul (c 24) kE
def expressions : Fin 10 → Expr := ![sE,q1E,q2Exponent,wExponent,QExponent,.vertex,
  mul (c 8) .vertex,mul (c 2) kE,add (c 9) QExponent,add (c 4) (mul (c 10) kE)]
def values (L : ℕ) : Fin 10 → ℕ :=
  ![s (fullExponent L),q₁ (fullExponent L),L+2*fullExponent L,8*fullExponent L,24*fullExponent L,
    L,8*L,2*fullExponent L,9+24*fullExponent L,4+10*fullExponent L]

theorem expression_values (L : ℕ) (i : Fin 10) : (expressions i).eval L 0=values L i := by
  fin_cases i <;> simp [expressions,values,sE,q1E,q2Exponent,wExponent,QExponent,kE,ellE,add,mul,c,
    Expr.eval,Unary.value,Binary.value,fullExponent,ell,V42Schedule.s,q₁]
  omega

theorem all_peaks (i : Fin 10) (L : ℕ) : (expressions i).peak L 0≤cap L := by
  have hlog : Nat.clog 2 (L+1)≤L := V39PublicSchedule.ell_le L
  have hs : 2^(16+Nat.clog 2 (L+1))≤2^17*(L+1) := (fullS_rounding L).2.le
  norm_num only [show (2:ℕ)^17=131072 by decide] at hs
  let M:=cap L
  have hsmall (a : ℕ) (ha : a≤1000) : a≤M := by dsimp [M,cap];omega
  have hL : L≤M := by dsimp [M,cap];omega
  have hL1 : L+1≤M := by dsimp [M,cap];omega
  have hk : 16+Nat.clog 2 (L+1)≤M := by dsimp [M,cap];omega
  have hS : 2^(16+Nat.clog 2 (L+1))≤M := hs.trans (by dsimp [M,cap];omega)
  have pe : ellE.peak L 0≤M := by
    change max (Nat.clog 2 (L+1)) (max (L+1) (max L 1))≤M
    exact max_le (hlog.trans hL) (max_le hL1 (max_le hL (hsmall 1 (by decide))))
  have pk : kE.peak L 0≤M := by
    change max (16+Nat.clog 2 (L+1)) (max 16 (ellE.peak L 0))≤M
    exact max_le hk (max_le (hsmall 16 (by decide)) pe)
  have ps : sE.peak L 0≤M := by
    change max (2^(16+Nat.clog 2 (L+1))) (kE.peak L 0)≤M
    exact max_le hS pk
  have pq1 : q1E.peak L 0≤M := by
    change max ((2^(16+Nat.clog 2 (L+1))-1)-1)
      (max (2^(16+Nat.clog 2 (L+1))-1) (sE.peak L 0))≤M
    exact max_le (by omega) (max_le (by omega) ps)
  have pconstMul (a : ℕ) (ha : a≤24) : (mul (c a) kE).peak L 0≤M := by
    have hv : a*(16+Nat.clog 2 (L+1))≤M := by
      have hm:=Nat.mul_le_mul_right (16+Nat.clog 2 (L+1)) ha
      dsimp [M,cap]
      omega
    change max (a*(16+Nat.clog 2 (L+1))) (max a (kE.peak L 0))≤M
    exact max_le hv (max_le (hsmall a (by omega)) pk)
  have pq2 : q2Exponent.peak L 0≤M := by
    have hv : L+2*(16+Nat.clog 2 (L+1))≤M := by dsimp [M,cap];omega
    change max (L+2*(16+Nat.clog 2 (L+1))) (max L ((mul (c 2) kE).peak L 0))≤M
    exact max_le hv (max_le hL (pconstMul 2 (by decide)))
  have pw : wExponent.peak L 0≤M := pconstMul 8 (by decide)
  have pQ : QExponent.peak L 0≤M := pconstMul 24 (by decide)
  have px : (mul (c 8) .vertex).peak L 0≤M := by
    change max (8*L) (max 8 L)≤M
    exact max_le (by dsimp [M,cap];omega) (max_le (hsmall 8 (by decide)) hL)
  have ptheta : (add (c 9) QExponent).peak L 0≤M := by
    change max (9+24*(16+Nat.clog 2 (L+1))) (max 9 (QExponent.peak L 0))≤M
    exact max_le (by dsimp [M,cap];omega) (max_le (hsmall 9 (by decide)) pQ)
  have pdelta : (add (c 4) (mul (c 10) kE)).peak L 0≤M := by
    change max (4+10*(16+Nat.clog 2 (L+1))) (max 4 ((mul (c 10) kE).peak L 0))≤M
    exact max_le (by dsimp [M,cap];omega) (max_le (hsmall 4 (by decide)) (pconstMul 10 (by decide)))
  fin_cases i
  · exact ps
  · exact pq1
  · exact pq2
  · exact pw
  · exact pQ
  · exact hL
  · exact px
  · exact pconstMul 2 (by decide)
  · exact ptheta
  · exact pdelta

def unary (i : Fin 10) := V42WidthPrimitives.scalar (expressions i) (all_peaks i)

theorem unary_result (i : Fin 10) (x : List Bool) :
    (unary i).result x=List.replicate (values x.length i) true := by
  change List.replicate ((expressions i).eval x.length 0) true=_
  rw [expression_values]

theorem source_s_exact (L : ℕ) :
    s (fullExponent L)=V38Schedule.pow2Ceil (2^16*(L+1)) := by
  have hlow : 2^16*(L+1) ≤ s (fullExponent L) := (fullS_rounding L).1
  have hhigh:s (fullExponent L)<2^17*(L+1) := (fullS_rounding L).2
  have hclog : Nat.clog 2 (2^16*(L+1))=fullExponent L := by
    apply le_antisymm
    · exact (Nat.clog_le_iff_le_pow (by decide : 1<2)).2 hlow
    · have he : fullExponent L=(fullExponent L-1)+1 := by unfold fullExponent;omega
      have hp : 2^(fullExponent L-1)<2^16*(L+1) := by
        change 2^(fullExponent L)<2^17*(L+1) at hhigh
        rw [he,pow_succ] at hhigh
        norm_num at hhigh ⊢
        nlinarith
      have hc: fullExponent L-1<Nat.clog 2 (2^16*(L+1)) :=
        (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).2 hp
      omega
  simp only [V38Schedule.pow2Ceil,hclog,V42Schedule.s]

#print axioms expression_values
#print axioms all_peaks
#print axioms source_s_exact
end
end CurrentAdditive.V42FullWidthExpressions
