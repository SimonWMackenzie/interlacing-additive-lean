import CurrentAdditive.D22PacketPrimitives

/-! A fixed syntax for physical packet assembly. Its scalar leaves invoke
the actual three-field Term compiler; word fields and concatenations are
literal existing programs. All size and clock constants are syntax data. -/
namespace D22PacketWordExpression
open EthInapproximability.CurrentPaper
open CurrentAdditive D22PacketPrimitives D22PolynomialExpression
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 65536

inductive WExpr (q : ℕ) where
  | empty | proj (j : Fin q) | scalar (t : Term)
  | frame (a : WExpr q) | append (a b : WExpr q)

def WExpr.producer {q : ℕ} (nSlot mSlot LSlot : Fin q) : WExpr q → Producer
  | .empty => ⟨V22UnaryLeaf.constant 0,fun _ => [],fun _ => 1⟩
  | .proj j => project j
  | .scalar t => D22PacketPrimitives.scalar nSlot mSlot LSlot t
  | .frame a => D22PacketPrimitives.frame (a.producer nSlot mSlot LSlot)
  | .append a b => D22PacketPrimitives.append (a.producer nSlot mSlot LSlot) (b.producer nSlot mSlot LSlot)
def WExpr.sizeCoefficient {q : ℕ} : WExpr q → ℕ
  | .empty => 0 | .proj _ => 1 | .scalar t => t.coefficient*2^t.degree
  | .frame a => 2*a.sizeCoefficient+1
  | .append a b => a.sizeCoefficient+b.sizeCoefficient
def WExpr.sizeDegree {q : ℕ} : WExpr q → ℕ
  | .empty => 0 | .proj _ => 1 | .scalar t => t.degree
  | .frame a => a.sizeDegree | .append a b => a.sizeDegree+b.sizeDegree
noncomputable def WExpr.timeCoefficient {q : ℕ} : WExpr q → ℕ
  | .empty => 1 | .proj _ => 2*q+4
  | .scalar t => 100*(q+1)+20+t.clockCoefficient*2^t.clockDegree
  | .frame a => a.timeCoefficient+6*a.sizeCoefficient+6
  | .append a b => a.timeCoefficient+b.timeCoefficient+2*a.sizeCoefficient+2*b.sizeCoefficient+11
def WExpr.timeDegree {q : ℕ} : WExpr q → ℕ
  | .empty => 0 | .proj _ => 1 | .scalar t => t.clockDegree
  | .frame a => a.timeDegree+a.sizeDegree
  | .append a b => a.timeDegree+b.timeDegree+a.sizeDegree+b.sizeDegree+1

def measure (x : List Bool) (L : ℕ) : ℕ := 2^L+x.length+1

theorem WExpr.outputs {q : ℕ} (e : WExpr q) (a b c : Fin q) (x : List Bool) (n m L : ℕ)
    (ha : BankFieldProjection.result a x=List.replicate n true)
    (hb : BankFieldProjection.result b x=List.replicate m true)
    (hc : BankFieldProjection.result c x=List.replicate L true) :
    (e.producer a b c).machine.OutputsWithin x ((e.producer a b c).result x)
      ((e.producer a b c).clock x) := by
  induction e with
  | empty => simpa only [WExpr.producer,List.replicate_zero] using V22UnaryLeaf.constant_outputs 0 x
  | proj j => exact project_outputs j x
  | scalar t => exact scalar_outputs a b c t x n m L ha hb hc
  | frame e ih => exact frame_outputs _ x ih
  | append e f ihe ihf => exact append_outputs _ _ x ihe ihf

theorem WExpr.bounds {q : ℕ} (e : WExpr q) (a b c : Fin q) (x : List Bool) (n m L : ℕ)
    (ha : BankFieldProjection.result a x=List.replicate n true)
    (hb : BankFieldProjection.result b x=List.replicate m true)
    (hc : BankFieldProjection.result c x=List.replicate L true) :
    ((e.producer a b c).result x).length≤e.sizeCoefficient*(measure x L)^e.sizeDegree ∧
      (e.producer a b c).clock x≤e.timeCoefficient*(measure x L)^e.timeDegree := by
  let W := measure x L
  have hN : 1≤2^L := Nat.one_le_two_pow
  have hW : 1≤W := by dsimp [W,measure]; omega
  have hI : x.length+1≤W := by dsimp [W,measure]; omega
  have hnI : n≤x.length := by simpa only [ha,List.length_replicate] using BankFieldProjection.result_length a x
  have hmI : m≤x.length := by simpa only [hb,List.length_replicate] using BankFieldProjection.result_length b x
  have hB : base n m L≤2*W := by dsimp [base,W,measure]; omega
  induction e with
  | empty => simp [WExpr.producer,WExpr.sizeCoefficient,WExpr.sizeDegree,WExpr.timeCoefficient,WExpr.timeDegree]
  | proj j =>
    have hs := BankFieldProjection.result_length j x
    change _≤1*W^1 ∧ (2*q+4)*(x.length+1)≤(2*q+4)*W^1
    simp only [one_mul,pow_one]
    exact ⟨hs.trans (by omega),Nat.mul_le_mul_left _ hI⟩
  | scalar t =>
    have hs := (t.expr.eval_le_peak n m L).trans (t.peak_bound n m L)
    have hs' : t.eval n m L≤(t.coefficient*2^t.degree)*W^t.degree := by
      calc
        _ ≤ t.coefficient*(base n m L)^t.degree := hs
        _ ≤ t.coefficient*(2*W)^t.degree := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB _)
        _=(t.coefficient*2^t.degree)*W^t.degree := by rw [mul_pow]; ring
    have ht := t.clock_polynomial n m L
    have ht' : t.expr.clock n m L≤(t.clockCoefficient*2^t.clockDegree)*W^t.clockDegree := by
      calc
        _ ≤ t.clockCoefficient*(base n m L)^t.clockDegree := ht
        _ ≤ t.clockCoefficient*(2*W)^t.clockDegree := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB _)
        _=(t.clockCoefficient*2^t.clockDegree)*W^t.clockDegree := by rw [mul_pow]; ring
    have hdeg : 1≤t.clockDegree := by unfold Term.clockDegree; omega
    have hWP : W≤W^t.clockDegree := by simpa using Nat.pow_le_pow_right hW hdeg
    have hP : 1≤W^t.clockDegree := one_le_pow₀ hW
    have hF := (framer_clock a b c x).trans (Nat.mul_le_mul_left _ (hI.trans hWP))
    have hFl := (framer_length a b c x).trans (Nat.mul_le_mul_left _ (hI.trans hWP))
    constructor
    · simpa only [WExpr.producer,D22PacketPrimitives.scalar,ha,hb,hc,List.length_replicate,WExpr.sizeCoefficient,
        WExpr.sizeDegree] using hs'
    · change (D22PacketPrimitives.scalar a b c t).clock x≤(100*(q+1)+20+t.clockCoefficient*2^t.clockDegree)*W^t.clockDegree
      simp only [D22PacketPrimitives.scalar,ha,hb,hc,List.length_replicate]
      nlinarith
  | frame e ih =>
    obtain ⟨hs,ht⟩ := ih
    change ((e.producer a b c).result x).length≤e.sizeCoefficient*W^e.sizeDegree at hs
    change (e.producer a b c).clock x≤e.timeCoefficient*W^e.timeDegree at ht
    have hps : 1≤W^e.sizeDegree := one_le_pow₀ hW
    have hps' : W^e.sizeDegree≤W^(e.timeDegree+e.sizeDegree) := Nat.pow_le_pow_right hW (by omega)
    have hpt' : W^e.timeDegree≤W^(e.timeDegree+e.sizeDegree) := Nat.pow_le_pow_right hW (by omega)
    have hpss := hs.trans (Nat.mul_le_mul_left _ hps')
    have hptt := ht.trans (Nat.mul_le_mul_left _ hpt')
    have hP : 1≤W^(e.timeDegree+e.sizeDegree) := one_le_pow₀ hW
    constructor
    · change (EncodedCommunication.field ((e.producer a b c).result x)).length≤(2*e.sizeCoefficient+1)*W^e.sizeDegree
      rw [EncodedCommunication.field_length]
      nlinarith
    · change (e.producer a b c).clock x+6*((e.producer a b c).result x).length+6≤
        (e.timeCoefficient+6*e.sizeCoefficient+6)*W^(e.timeDegree+e.sizeDegree)
      nlinarith
  | append e f ihe ihf =>
    obtain ⟨hse,hte⟩ := ihe
    obtain ⟨hsf,htf⟩ := ihf
    change ((e.producer a b c).result x).length≤e.sizeCoefficient*W^e.sizeDegree at hse
    change ((f.producer a b c).result x).length≤f.sizeCoefficient*W^f.sizeDegree at hsf
    change (e.producer a b c).clock x≤e.timeCoefficient*W^e.timeDegree at hte
    change (f.producer a b c).clock x≤f.timeCoefficient*W^f.timeDegree at htf
    have hsem := hse.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW
      (show e.sizeDegree≤e.sizeDegree+f.sizeDegree by omega)))
    have hsfm := hsf.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW
      (show f.sizeDegree≤e.sizeDegree+f.sizeDegree by omega)))
    let D := e.timeDegree+f.timeDegree+e.sizeDegree+f.sizeDegree+1
    have hD : 1≤D := by dsimp [D]; omega
    have hP : 1≤W^D := one_le_pow₀ hW
    have hIP : x.length≤W^D := (show x.length≤W by omega).trans
      (by simpa using Nat.pow_le_pow_right hW hD)
    have hte' := hte.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW (show e.timeDegree≤D by dsimp [D]; omega)))
    have htf' := htf.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW (show f.timeDegree≤D by dsimp [D]; omega)))
    have hse' := hse.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW (show e.sizeDegree≤D by dsimp [D]; omega)))
    have hsf' := hsf.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hW (show f.sizeDegree≤D by dsimp [D]; omega)))
    constructor
    · change (((e.producer a b c).result x)++((f.producer a b c).result x)).length≤
        (e.sizeCoefficient+f.sizeCoefficient)*W^(e.sizeDegree+f.sizeDegree)
      rw [List.length_append]
      nlinarith
    · change (D22PacketPrimitives.append (e.producer a b c) (f.producer a b c)).clock x≤
        (e.timeCoefficient+f.timeCoefficient+2*e.sizeCoefficient+2*f.sizeCoefficient+11)*W^D
      simp only [D22PacketPrimitives.append,PhysicalConcatLocal.clock]
      nlinarith

theorem WExpr.outputs_polynomial {q : ℕ} (e : WExpr q) (a b c : Fin q) (x : List Bool) (n m L : ℕ)
    (ha : BankFieldProjection.result a x=List.replicate n true)
    (hb : BankFieldProjection.result b x=List.replicate m true)
    (hc : BankFieldProjection.result c x=List.replicate L true) :
    (e.producer a b c).machine.OutputsWithin x ((e.producer a b c).result x)
      (e.timeCoefficient*(measure x L)^e.timeDegree) :=
  BitMachine.outputsWithin_mono _ (e.outputs a b c x n m L ha hb hc)
    (e.bounds a b c x n m L ha hb hc).2

#print axioms WExpr.outputs_polynomial
end
end D22PacketWordExpression
