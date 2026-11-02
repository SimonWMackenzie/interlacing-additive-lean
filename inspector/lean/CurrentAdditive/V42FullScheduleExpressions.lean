import CurrentAdditive.V22UnaryExpression
import CurrentAdditive.V42RuntimeSchedule

/-! Literal selected full-product scalar schedule, expressed using only the
physical arithmetic compiler's fixed operations. Supplied k is unrestricted. -/
namespace V42FullScheduleExpressions
open V22UnaryExpression
open V42RuntimeSchedule
open CurrentAdditive.V38OneStep CurrentAdditive.V39RecursiveGenerator
def add := Expr.binary Binary.add
def mul := Expr.binary Binary.mul
def maxE := Expr.binary Binary.max
def sub1 := Expr.unary Unary.pred
def log := Expr.unary Unary.clog
def pow := Expr.unary Unary.pow2
def c := Expr.const
def L := log Expr.vertex
def ellE := log (add L (c 1))
def seed := pow (add (c 6) ellE)
def s := pow (add (c 16) ellE)
def q1 := sub1 (sub1 s)
def q2 := pow (add L (mul (c 2) (add (c 16) ellE)))
def w := pow (mul (c 8) (add (c 16) ellE))
def Q := pow (mul (c 24) (add (c 16) ellE))
def overhead := add L (mul (c 36) (add (c 16) ellE))
def B := add (add ellE (c 7)) (mul Expr.iteration overhead)
def H := add B Expr.iteration
def rank := pow (sub1 B)
def sampleArgument := mul (mul (mul (c 16) (add rank (c 1)))
  (log (add rank (c 2)))) (pow H)
def sample := pow (log sampleArgument)
def widthExponent := mul (c 16) L
def sampleExponentE := mul (mul (c 40) (add Expr.iteration (c 1))) L
def drawExponent := add (add sampleExponentE (c 1))
  (add (add (mul (add (mul (c 3) widthExponent) (c 3)) Expr.iteration) widthExponent) (c 1))
def draws := pow drawExponent
def alphabet := maxE (c 512) (maxE (mul (mul (c 4) s) (add Expr.vertex s))
  (maxE q2 (maxE w (maxE Q seed))))
def precision := log (mul (mul (c 200) alphabet) draws)
def totalBits := mul precision draws

@[simp] theorem eval_L (n k : ℕ) : L.eval n k=Nat.clog 2 n := rfl
@[simp] theorem eval_ell (n k : ℕ) : ellE.eval n k=ell (Nat.clog 2 n) := rfl
@[simp] theorem eval_seed (n k : ℕ) : seed.eval n k=seedWidth (Nat.clog 2 n) := by
  exact (CurrentAdditive.V42PublicSchedule.seedWidth_exact _).symm
@[simp] theorem eval_s (n k : ℕ) : s.eval n k=fullS (Nat.clog 2 n) := rfl
@[simp] theorem eval_q1 (n k : ℕ) : q1.eval n k=fullQ₁ (Nat.clog 2 n) := by
  change (fullS (Nat.clog 2 n)-1)-1=fullS (Nat.clog 2 n)-2
  omega
@[simp] theorem eval_q2 (n k : ℕ) : q2.eval n k=fullQ₂ (Nat.clog 2 n) := by
  rfl
@[simp] theorem eval_w (n k : ℕ) : w.eval n k=fullW (Nat.clog 2 n) := rfl
@[simp] theorem eval_Q (n k : ℕ) : Q.eval n k=fullQ (Nat.clog 2 n) := by
  rfl
@[simp] theorem eval_overhead (n k : ℕ) : overhead.eval n k=fullOverhead (Nat.clog 2 n) := rfl
@[simp] theorem eval_B (n k : ℕ) : B.eval n k=V42RuntimeSchedule.B (Nat.clog 2 n) k := rfl
@[simp] theorem eval_H (n k : ℕ) : H.eval n k=V42RuntimeSchedule.H (Nat.clog 2 n) k := rfl
@[simp] theorem eval_rank (n k : ℕ) : rank.eval n k=rankBound (Nat.clog 2 n) k := rfl
@[simp] theorem eval_sample (n k : ℕ) : sample.eval n k=sampleSide (Nat.clog 2 n) k := rfl
@[simp] theorem eval_widthExponent (n k : ℕ) : widthExponent.eval n k=fullWidthExponent (Nat.clog 2 n) := rfl
@[simp] theorem eval_sampleExponent (n k : ℕ) : sampleExponentE.eval n k=fullSampleExponent (Nat.clog 2 n) k := rfl
@[simp] theorem eval_drawExponent (n k : ℕ) : drawExponent.eval n k=fullDrawExponent (Nat.clog 2 n) k := rfl
@[simp] theorem eval_draws (n k : ℕ) : draws.eval n k=2^fullDrawExponent (Nat.clog 2 n) k := rfl
@[simp] theorem eval_alphabet (n k : ℕ) : alphabet.eval n k=fullAlphabet n (Nat.clog 2 n) := by
  simp only [alphabet,maxE,mul,add,c,Expr.eval,Binary.value,eval_s,eval_q2,eval_w,
    eval_Q,eval_seed]
  rfl
@[simp] theorem eval_precision (n k : ℕ) : precision.eval n k=
    publicBits (fullAlphabet n (Nat.clog 2 n)) (2^fullDrawExponent (Nat.clog 2 n) k) := by
  simp only [precision,log,mul,c,Expr.eval,Unary.value,Binary.value,eval_alphabet,eval_draws]
  rfl
@[simp] theorem eval_totalBits (n k : ℕ) : totalBits.eval n k=
    publicBits (fullAlphabet n (Nat.clog 2 n)) (2^fullDrawExponent (Nat.clog 2 n) k)*
      2^fullDrawExponent (Nat.clog 2 n) k := by
  simp only [totalBits,mul,Expr.eval,Binary.value,eval_precision,eval_draws]

/-- These are physical computations, including the literal max in A and the
literal dyadic ceiling in m, on the same supplied n and k. -/
theorem each_physical (e : Expr) (n k : ℕ) :
    e.machine.OutputsWithin
      (EthInapproximability.CurrentPaper.MatrixUnaryArithmetic.encodeInput n k)
      (List.replicate (e.eval n k) true) (e.clock n k) := e.outputs n k

#print axioms eval_sample
#print axioms eval_precision
#print axioms each_physical
end V42FullScheduleExpressions


