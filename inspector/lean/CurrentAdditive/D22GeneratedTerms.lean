import CurrentAdditive.D22PredicateCompiler
import CurrentAdditive.V40GeneratedTestPairs

/-! Literal syntax counterparts of the separately checked twenty natural
cross-products. Every scalar is a physical polynomial-expression program. -/
namespace D22GeneratedTerms
open D22PolynomialExpression D22NatExpression
open CurrentAdditive V39GeneratedConstruction V40GeneratedFractions
open V38Schedule
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

def add := Term.binary (.old .add)
def mul := Term.binary (.old .mul)
def quot := Term.binary .quot
def pow (a : Term) : ℕ → Term
  | 0 => .const 1 | k+1 => mul (pow a k) a
def ceilDiv (a b : Term) := quot (.pred (add a b)) b
@[simp] theorem eval_add (a b : Term) (n m L : ℕ) : (add a b).eval n m L=a.eval n m L+b.eval n m L := rfl
@[simp] theorem eval_mul (a b : Term) (n m L : ℕ) : (mul a b).eval n m L=a.eval n m L*b.eval n m L := rfl
@[simp] theorem eval_quot (a b : Term) (n m L : ℕ) : (quot a b).eval n m L=a.eval n m L/b.eval n m L := rfl
@[simp] theorem eval_const (a n m L : ℕ) : (Term.const a).eval n m L=a := rfl
@[simp] theorem eval_pred (a : Term) (n m L : ℕ) : (.pred a : Term).eval n m L=a.eval n m L-1 := rfl
@[simp] theorem eval_pow (a : Term) (k n m L : ℕ) : (pow a k).eval n m L=(a.eval n m L)^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pow,ih,pow_succ]
@[simp] theorem eval_ceilDiv (a b : Term) (n m L : ℕ) :
    (ceilDiv a b).eval n m L=V40GeneratedFractions.ceilDiv (a.eval n m L) (b.eval n m L) := rfl
@[simp] theorem eval_dyadic (a b d n m L : ℕ) :
    (Term.dyadic a b d).eval n m L=2^((a*L+b)/max 1 d) := rfl
@[simp] theorem eval_var (j : Fin 3) (n m L : ℕ) : (Term.var j).eval n m L=values n m L j := rfl
@[simp] theorem eval_powCeil (a : Term) (n m L : ℕ) :
    (Term.powCeil a).eval n m L=pow2Ceil (a.eval n m L) := rfl

def N : Term := .dyadic 1 0 1
def s : Term := .dyadic 1 3 4
def q1 : Term := .pred (.pred s)
def q2 : Term := pow N 4
def w : Term := pow N 2
def Q : Term := pow N 6
@[simp] theorem eval_N (n m L : ℕ) : N.eval n m L=generatedN L := by simp [N,generatedN]
@[simp] theorem eval_s (n m L : ℕ) : s.eval n m L=generatedS L := by simp [s,generatedS,quarterCeil]
@[simp] theorem eval_q1 (n m L : ℕ) : q1.eval n m L=generatedQ₁ L := by
  simp only [q1,eval_pred,eval_s,generatedQ₁]; omega
@[simp] theorem eval_q2 (n m L : ℕ) : q2.eval n m L=generatedQ₂ L := by simp [q2,generatedQ₂]
@[simp] theorem eval_w (n m L : ℕ) : w.eval n m L=generatedW L := by simp [w,generatedW]
@[simp] theorem eval_Q (n m L : ℕ) : Q.eval n m L=generatedQ L := by simp [Q,generatedQ]

structure SFrac where
  num : Term
  den : Term
namespace SFrac
def eval (a : SFrac) (n m L : ℕ) : V40GeneratedFractions.Fr := ⟨a.num.eval n m L,a.den.eval n m L⟩
def nat (a : Term) : SFrac := ⟨a,.const 1⟩
def ofRat (q : ℚ) : SFrac := ⟨.const q.num.toNat,.const q.den⟩
def mul (a b : SFrac) : SFrac := ⟨D22GeneratedTerms.mul a.num b.num,D22GeneratedTerms.mul a.den b.den⟩
def div (a b : SFrac) : SFrac := ⟨D22GeneratedTerms.mul a.num b.den,D22GeneratedTerms.mul a.den b.num⟩
def divNat (a : SFrac) (b : Term) : SFrac := ⟨a.num,D22GeneratedTerms.mul a.den b⟩
def pow (a : SFrac) (k : ℕ) : SFrac := ⟨D22GeneratedTerms.pow a.num k,D22GeneratedTerms.pow a.den k⟩
def cross (a b : SFrac) : Term×Term := (D22GeneratedTerms.mul a.num b.den,D22GeneratedTerms.mul b.num a.den)
@[simp] theorem eval_nat (a : Term) (n m L : ℕ) : (nat a).eval n m L=Fr.nat (a.eval n m L) := rfl
@[simp] theorem eval_ofRat (q : ℚ) (n m L : ℕ) : (ofRat q).eval n m L=Fr.ofRat q := rfl
@[simp] theorem eval_mul (a b : SFrac) (n m L : ℕ) : (mul a b).eval n m L=Fr.mul (a.eval n m L) (b.eval n m L) := rfl
@[simp] theorem eval_div (a b : SFrac) (n m L : ℕ) : (div a b).eval n m L=Fr.div (a.eval n m L) (b.eval n m L) := rfl
@[simp] theorem eval_divNat (a : SFrac) (b : Term) (n m L : ℕ) :
    (divNat a b).eval n m L=Fr.divNat (a.eval n m L) (b.eval n m L) := rfl
@[simp] theorem eval_pow (a : SFrac) (k n m L : ℕ) :
    (pow a k).eval n m L=Fr.pow (a.eval n m L) k := by
  simp [eval,pow,Fr.pow]
end SFrac

def eta (p : SourceConstants) := SFrac.divNat (SFrac.ofRat p.deletion) s
def delta (p : SourceConstants) :=
  SFrac.divNat (SFrac.mul (SFrac.ofRat p.gamma) (SFrac.nat (.var 1)))
    (mul (mul (.const 2) (.const p.degree)) (.var 0))
def zeta (p : SourceConstants) := SFrac.divNat (SFrac.ofRat p.gamma) (.const 24)
def rho := SFrac.divNat (SFrac.nat (.const 1)) N
def x := SFrac.divNat (SFrac.nat (.const 1)) (pow N 8)
def scaledEta (p : SourceConstants) :=
  SFrac.mul (SFrac.mul (SFrac.nat s) (eta p)) (SFrac.nat (.const (2^16)))
def unitCount (a b : ℕ) : Term := mul (.const (2^90)) (.dyadic a (b+63) 64)
def etaCount (p : SourceConstants) : Term :=
  ceilDiv (mul (mul (mul (.const (2^92)) (pow (.const p.deletion.den) 2)) (pow s 2))
    (.dyadic 6 72 64)) (pow (.const p.deletion.num.toNat) 2)
def restCount (p : SourceConstants) : Term :=
  ceilDiv (mul (mul (mul (mul (.const (2^100)) (pow (.const p.deletion.den) 2))
    (pow s 2)) (pow w 2)) (.dyadic 1 63 64)) (pow (.const p.deletion.num.toNat) 2)
def c128 := SFrac.ofRat C128
def Kstar : Term := mul (mul (.const 2) (add (mul (.const 2) (.var 2)) (.const 2))) s

@[simp] theorem eval_eta (p : SourceConstants) (n m L : ℕ) :
    (eta p).eval n m L=V40GeneratedTestPairs.etaFr p L := by
  simp [eta,V40GeneratedTestPairs.etaFr]
@[simp] theorem eval_delta (p : SourceConstants) (n m L : ℕ) :
    (delta p).eval n m L=V40GeneratedTestPairs.deltaFr p n m := by
  simp [delta,V40GeneratedTestPairs.deltaFr,values]
@[simp] theorem eval_zeta (p : SourceConstants) (n m L : ℕ) :
    (zeta p).eval n m L=V40GeneratedTestPairs.zetaFr p := by
  simp [zeta,V40GeneratedTestPairs.zetaFr]
@[simp] theorem eval_rho (n m L : ℕ) : rho.eval n m L=V40GeneratedTestPairs.rhoFr L := by
  simp [rho,V40GeneratedTestPairs.rhoFr]
@[simp] theorem eval_x (n m L : ℕ) : x.eval n m L=V40GeneratedTestPairs.xFr L := by
  simp [x,V40GeneratedTestPairs.xFr]
@[simp] theorem eval_scaledEta (p : SourceConstants) (n m L : ℕ) :
    (scaledEta p).eval n m L=V40GeneratedTestPairs.scaledEtaFr p L := by
  simp [scaledEta,V40GeneratedTestPairs.scaledEtaFr]
@[simp] theorem eval_unitCount (a b n m L : ℕ) :
    (unitCount a b).eval n m L=V40GeneratedTestPairs.unitCount (a*L+b) := by
  simp [unitCount,V40GeneratedTestPairs.unitCount,Nat.add_assoc]
@[simp] theorem eval_etaCount (p : SourceConstants) (n m L : ℕ) :
    (etaCount p).eval n m L=V40GeneratedTestPairs.etaCount p L := by
  simp [etaCount,V40GeneratedTestPairs.etaCount,V40GeneratedTestPairs.cN,V40GeneratedTestPairs.cD]
@[simp] theorem eval_restCount (p : SourceConstants) (n m L : ℕ) :
    (restCount p).eval n m L=V40GeneratedTestPairs.restCount p L := by
  simp [restCount,V40GeneratedTestPairs.restCount,V40GeneratedTestPairs.cN,V40GeneratedTestPairs.cD]
@[simp] theorem eval_c128 (n m L : ℕ) : c128.eval n m L=V40GeneratedTestPairs.c128Fr := rfl
@[simp] theorem eval_Kstar (n m L : ℕ) : Kstar.eval n m L=V38Schedule.Kstar (2*L) (generatedS L) := by
  simp [Kstar,V38Schedule.Kstar,values]

def fractionPairs (p : SourceConstants) : Fin 20 → SFrac×SFrac :=
  let η := eta p
  let S := SFrac.nat s
  let W := SFrac.nat w
  ![(SFrac.nat (.const 256),S),
    (scaledEta p,SFrac.nat (.const 1)),
    (scaledEta p,delta p),
    (scaledEta p,SFrac.divNat (zeta p) (.const 256)),
    (SFrac.nat (.powCeil (mul (mul (.const 4) s) (.var 1))),SFrac.nat q2),
    (SFrac.mul (SFrac.nat (.const 4)) (SFrac.mul (SFrac.pow S 2) rho),SFrac.nat (.const 1)),
    (SFrac.mul (SFrac.nat (.const 8)) (SFrac.mul S (SFrac.nat q1)),SFrac.divNat (SFrac.mul (zeta p) (SFrac.nat q2)) (.const 16)),
    (SFrac.mul (SFrac.nat q2) x,SFrac.divNat (SFrac.nat (.const 1)) (.const 10000)),
    (SFrac.mul S x,SFrac.divNat (SFrac.nat (.const 1)) (.const 10000)),
    (SFrac.mul W x,SFrac.divNat (SFrac.nat (.const 1)) (.const 10000)),
    (SFrac.mul (SFrac.nat (.const 2)) (SFrac.mul (SFrac.pow W 2) x),SFrac.div η (SFrac.mul (SFrac.nat (.const 16)) (SFrac.divNat (SFrac.nat (.const 255)) (.const 256)))),
    (SFrac.mul (SFrac.mul (SFrac.pow W 2) (SFrac.nat q2)) x,SFrac.nat (.const 1)),
    (SFrac.mul (SFrac.mul (SFrac.mul (SFrac.divNat (SFrac.nat (.const 4)) (.const 256)) W) (SFrac.nat q2)) x,SFrac.divNat η (.const 32)),
    (SFrac.nat (unitCount 6 9),SFrac.nat (quot w (.const 128))),
    (SFrac.nat (unitCount 6 11),SFrac.nat (mul s q2)),
    (SFrac.div c128 (SFrac.pow S 128),SFrac.divNat (SFrac.divNat (SFrac.nat (.const 1)) (mul (.const 512) Q)) (.const 4)),
    (SFrac.nat (mul (.const 2) (etaCount p)),SFrac.nat (quot w (.const 4))),
    (SFrac.nat (mul Kstar (mul (.const 2) (etaCount p))),SFrac.divNat (SFrac.mul η W) (.const 16)),
    (SFrac.nat (unitCount 8 0),SFrac.nat (quot s (.const 128))),
    (SFrac.nat (mul (.const 128) (add (restCount p) (.const 1))),SFrac.nat Q)]
def pairs (p : SourceConstants) (i : Fin 20) : Term×Term :=
  SFrac.cross (fractionPairs p i).1 (fractionPairs p i).2
def tests (p : SourceConstants) : List (Term×Term) := List.ofFn (pairs p)

theorem fractionPairs_eval (p : SourceConstants) (n m L : ℕ) (i : Fin 20) :
    ((fractionPairs p i).1.eval n m L,(fractionPairs p i).2.eval n m L)=
      V40GeneratedTestPairs.fractionPairs p n m L i := by
  fin_cases i <;> simp [fractionPairs,V40GeneratedTestPairs.fractionPairs,values,Nat.add_comm]

theorem pairs_eval (p : SourceConstants) (n m L : ℕ) (i : Fin 20) :
    ((pairs p i).1.eval n m L,(pairs p i).2.eval n m L)=
      V40GeneratedTestPairs.literalPairs p n m L i := by
  have h := fractionPairs_eval p n m L i
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  change (fractionPairs p i).1.eval n m L=(V40GeneratedTestPairs.fractionPairs p n m L i).1 at h1
  change (fractionPairs p i).2.eval n m L=(V40GeneratedTestPairs.fractionPairs p n m L i).2 at h2
  change Fr.cross ((fractionPairs p i).1.eval n m L) ((fractionPairs p i).2.eval n m L)=_
  rw [h1,h2]
  rfl

theorem pass_iff_literal (p : SourceConstants) (n m L : ℕ) :
    D22PredicateCompiler.pass (tests p) n m L=true ↔ V40GeneratedTestPairs.literalTests p n m L := by
  simp only [D22PredicateCompiler.pass,tests,List.all_eq_true,List.mem_ofFn,forall_exists_index,
    forall_apply_eq_imp_iff]
  unfold V40GeneratedTestPairs.literalTests
  apply forall_congr'
  intro i
  have h := pairs_eval p n m L i
  rw [←h]
  simp

#print axioms pairs_eval
#print axioms pass_iff_literal

end
end D22GeneratedTerms
