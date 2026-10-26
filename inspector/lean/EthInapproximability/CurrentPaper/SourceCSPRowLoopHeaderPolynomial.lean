import EthInapproximability.CurrentPaper.SourceCSPRowLoopPolynomial

/-!
# Quadratic overhead of the encoded positive header and row-bank preparation

The source alphabet and arity are fixed. We bound the header's binary scans,
unary copies, vertex-cap production, and one row-loop handoff by a generous
symbolic coefficient times the square of the encoded source length.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopHeaderPolynomial

open Turing BitMachineEncoding
open SourceCSPRowLoopAll SourceCSPRowLoopPolynomial

def headerCoefficient (a q : Nat) : Nat :=
  200 + a + 50 * q + 10 * q ^ 2

theorem headerCost_quadratic {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q)
    (hsize : SourceCSPCodec.ValidSize P) :
    SourceCSPRowLoopBridgeSequence.headerCost a q P ≤
      headerCoefficient a q *
        ((EncodedETHSource.constraintBits P).length + 1) ^ 2 := by
  let L := (EncodedETHSource.constraintBits P).length
  let X := L + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hX2 : 1 ≤ X ^ 2 := by nlinarith
  have hLX : L ≤ X ^ 2 := by dsimp [X]; nlinarith
  have hm : P.constraints ≤ L := SourceCSPCodec.constraints_le_bits P
  have hn : P.vertices ≤ q * L :=
    hsize.trans (Nat.mul_le_mul_left q hm)
  have hbitsM : P.constraints.bits.length ≤ L :=
    (UnaryBinaryEncoding.bits_length_le _).trans hm
  have hbitsN : P.vertices.bits.length ≤ q * L :=
    (UnaryBinaryEncoding.bits_length_le _).trans hn
  have ha : a.bits.length ≤ a := UnaryBinaryEncoding.bits_length_le a
  have hq : q.bits.length ≤ q := UnaryBinaryEncoding.bits_length_le q
  have hrows : (SourceCSPPositiveHeader.rows P).length ≤ L := by
    have he := SourceCSPCodec.constraintBits_eq P
    change (SourceCSPPositiveHeader.rows P).length ≤
      (EncodedETHSource.constraintBits P).length
    rw [he]
    simp only [SourceCSPPositiveHeader.rows, List.length_append]
    omega
  have hXlinear : L ≤ X := by dsimp [X]; omega
  have hmX : P.constraints ≤ X := hm.trans hXlinear
  have hB : P.constraints.bits.length ≤ X := hbitsM.trans hXlinear
  have hnX : P.vertices.bits.length ≤ q * X :=
    hbitsN.trans (Nat.mul_le_mul_left q hXlinear)
  have hqM : q * P.constraints ≤ q * L :=
    Nat.mul_le_mul_left q hm
  have hrowProd : (L + 1) * (4 * P.constraints.bits.length + 5) ≤
      5 * X ^ 2 := by
    have hfactor : 4 * P.constraints.bits.length + 5 ≤ 5 * X := by
      dsimp [X]
      omega
    calc
      _ ≤ X * (5 * X) := Nat.mul_le_mul_left X hfactor
      _ = 5 * X ^ 2 := by ring
  have hcapProd : (q * P.constraints + 1) *
      (4 * P.vertices.bits.length + 5) ≤
      ((q + 1) * (4 * q + 5)) * X ^ 2 := by
    have hleft : q * P.constraints + 1 ≤ (q + 1) * X := by
      nlinarith [Nat.mul_le_mul_left q hmX]
    have hright : 4 * P.vertices.bits.length + 5 ≤ (4 * q + 5) * X := by
      nlinarith [Nat.mul_le_mul_left 4 hnX]
    calc
      _ ≤ ((q + 1) * X) * ((4 * q + 5) * X) :=
        Nat.mul_le_mul hleft hright
      _ = ((q + 1) * (4 * q + 5)) * X ^ 2 := by ring
  have hqLX : q * L ≤ q * X ^ 2 := Nat.mul_le_mul_left q hLX
  have hqM2 : q * P.constraints ≤ q * X ^ 2 := hqM.trans hqLX
  have hnB : P.vertices.bits.length ≤ q * X ^ 2 :=
    hbitsN.trans hqLX
  have hrows2 : (SourceCSPPositiveHeader.rows P).length ≤ X ^ 2 :=
    hrows.trans hLX
  have hm2 : P.constraints ≤ X ^ 2 := hm.trans hLX
  have hn2 : P.vertices - 1 ≤ q * X ^ 2 :=
    (Nat.sub_le P.vertices 1).trans (hn.trans hqLX)
  have hB2 : P.constraints.bits.length ≤ X ^ 2 :=
    hbitsM.trans hLX
  have ha2 : a.bits.length ≤ a * X ^ 2 :=
    ha.trans (by simpa only [mul_one] using Nat.mul_le_mul_left a hX2)
  have hq2 : q.bits.length ≤ q * X ^ 2 :=
    hq.trans (by simpa only [mul_one] using Nat.mul_le_mul_left q hX2)
  have hq3 : q ≤ q * X ^ 2 := by
    simpa only [mul_one] using Nat.mul_le_mul_left q hX2
  have hcapProd2 : (q * P.constraints + 1) *
      (4 * P.vertices.bits.length + 5) ≤
      (4 * q ^ 2 + 9 * q + 5) * X ^ 2 := by
    convert hcapProd using 1 <;> ring
  unfold SourceCSPRowLoopBridgeSequence.headerCost
    SourceCSPPositiveHeader.positiveBound
    SourceCSPPositiveHeader.headerBound headerCoefficient
  dsimp only [L, X] at *
  nlinarith [hrowProd, hcapProd2, hqM2, hnB, hrows2, hm2, hn2, hB2,
    ha2, hq2, hq3, Nat.mul_le_mul_left 200 hX2]

def fullCoefficient (a q : Nat) : Nat :=
  headerCoefficient a q + rowCoefficient a q + 4

/-- Actual encoded-source header, row-bank preparation, one handoff, all
canonical rows, physical resets, and exact EOF have cubic runtime for fixed
alphabet and arity. This stage validates rows; clause emission is separate. -/
theorem encoded_full_polynomial {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q)
    (hn : 0 < P.vertices) (hsize : SourceCSPCodec.ValidSize P) :
    ∃ (t : Nat) (S : SourceCSPRowLoopBridgeSequence.Stack q → List Bool),
      t ≤ fullCoefficient a q *
        ((EncodedETHSource.constraintBits P).length + 1) ^ 3 ∧
      ((advance (SourceCSPRowLoopBridgeSequence.program a q))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (SourceCSPRowLoopBridgeSequence.headerStart a q)),
          ((SourceCSPHeaderRowBridge.headerStart,
            SourceCSPHeaderRowBridge.prepareStart),
            SourceCSPRowLoopController.initialControl),
          SourceCSPHeaderRowBridge.initial
            (EncodedETHSource.constraintBits P)⟩ :
          TM2.Cfg (fun _ : SourceCSPRowLoopBridgeSequence.Stack q => Bool)
            (SourceCSPRowLoopBridgeSequence.Label a q)
            SourceCSPRowLoopBridgeSequence.Control) =
        ⟨none, ((SourceCSPHeaderRowBridge.headerStart,
          SourceCSPHeaderRowBridge.prepareStart),
          ((SourceCSPRowLoopController.queryStart,
            SourceCSPRowLoopController.resetStart), some true)), S⟩ ∧
      (fun k => S (SourceCSPHeaderRowBridge.rowEmbedding k)) =
        Sum.elim (SourceCSPRowQueryFrame.initial []
          (List.replicate (P.vertices - 1) true))
          (fun k : Fin 4 => if k = 1 then
            List.replicate (P.vertices - 1) true else []) := by
  obtain ⟨t, S, ht, hr, hs⟩ :=
    SourceCSPRowLoopTotalCost.encoded_full_bound P hn hsize
  let X := (EncodedETHSource.constraintBits P).length + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have h23 : X ^ 2 ≤ X ^ 3 := by
    have hm := Nat.mul_le_mul_left (X ^ 2) hX
    convert hm using 1 <;> ring
  have hhead := headerCost_quadratic P hsize
  have hrows := encoded_totalBound_cubic P hsize
  have hfour : 4 ≤ 4 * X ^ 3 := by
    have h1 : 1 ≤ X ^ 3 := by nlinarith [Nat.zero_le X]
    simpa only [mul_one] using Nat.mul_le_mul_left 4 h1
  have hhead3 : SourceCSPRowLoopBridgeSequence.headerCost a q P ≤
      headerCoefficient a q * X ^ 3 :=
    hhead.trans (Nat.mul_le_mul_left (headerCoefficient a q) h23)
  refine ⟨t, S, ?_, hr, hs⟩
  dsimp only [fullCoefficient, X] at *
  nlinarith [hhead3, hrows, hfour]

end EthInapproximability.CurrentPaper.SourceCSPRowLoopHeaderPolynomial
