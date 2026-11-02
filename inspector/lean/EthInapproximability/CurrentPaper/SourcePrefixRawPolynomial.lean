import EthInapproximability.CurrentPaper.SourcePrefixRawRun
import EthInapproximability.CurrentPaper.SourceCSPRowLoopHeaderPolynomial

namespace EthInapproximability.CurrentPaper.SourcePrefixRawPolynomial

open Turing BitMachineEncoding
open SourcePrefixRawStash SourcePrefixRawRun
open EthInapproximability.CurrentPaper.SourceBooleanPrefix
open scoped Classical

noncomputable def coefficient (q : Nat) : Nat :=
  20 + 22 * q +
    SourceCSPRowLoopHeaderPolynomial.headerCoefficient 2 q +
    q * PrefixLoopPolynomial.callbackCoefficient q * (q + 2) ^ 4 +
    2 * (PrefixLoopPolynomial.byteCoefficient q + 1) * (q + 2) ^ 2

theorem savedWord_length (n q : Nat) :
    (savedWord n q).length ≤
      (PrefixLoopPolynomial.byteCoefficient q + 1) * (n + 2) ^ 2 := by
  have h := PrefixLoopPolynomial.savedAt_le n q n [] [] [] (by omega)
  rw [PrefixLoopIteration.savedAt_eq_prefix] at h
  simpa only [savedWord, PrefixLoopPolynomial.inputMass,
    List.append_nil, List.length_reverse] using h

theorem rawClock_polynomial {q : Nat}
    (P : EncodedETHSource.ConstraintInstance 2 q)
    (hsize : SourceCSPCodec.ValidSize P) :
    rawClock P ≤ coefficient q *
      ((EncodedETHSource.constraintBits P).length + 1) ^ 5 := by
  let L := (EncodedETHSource.constraintBits P).length
  let X := L + 1
  let n := P.vertices
  have hm : P.constraints ≤ L := SourceCSPCodec.constraints_le_bits P
  have hn : n ≤ q * L := hsize.trans (Nat.mul_le_mul_left q hm)
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hLX : L ≤ X := by dsimp [X]; omega
  have hX2 : X ^ 2 ≤ X ^ 5 := by
    have h1 : 1 ≤ X ^ 3 := by
      simpa using (Nat.pow_le_pow_left hX 3)
    calc
      X ^ 2 = X ^ 2 * 1 := by ring
      _ ≤ X ^ 2 * X ^ 3 := Nat.mul_le_mul_left _ h1
      _ = X ^ 5 := by ring
  have hX5 : X ≤ X ^ 5 := by
    have h1 : 1 ≤ X ^ 4 := by
      simpa using (Nat.pow_le_pow_left hX 4)
    calc
      X = X * 1 := by ring
      _ ≤ X * X ^ 4 := Nat.mul_le_mul_left _ h1
      _ = X ^ 5 := by ring
  have hNlinear : n ≤ q * X := hn.trans (Nat.mul_le_mul_left q hLX)
  have hN5 : n ≤ q * X ^ 5 := hNlinear.trans
    (Nat.mul_le_mul_left q hX5)
  have hNplus : n + 2 ≤ (q + 2) * X := by
    dsimp [X] at *
    nlinarith
  have hNpow2 : (n + 2) ^ 2 ≤ (q + 2) ^ 2 * X ^ 2 := by
    have h := Nat.pow_le_pow_left hNplus 2
    simpa only [mul_pow] using h
  have hNpow4 : (n + 2) ^ 4 ≤ (q + 2) ^ 4 * X ^ 4 := by
    have h := Nat.pow_le_pow_left hNplus 4
    simpa only [mul_pow] using h
  have hsaved := savedWord_length n q
  have hsaved2 : (savedWord n q).length ≤
      (PrefixLoopPolynomial.byteCoefficient q + 1) *
        (q + 2) ^ 2 * X ^ 5 := by
    calc
      _ ≤ (PrefixLoopPolynomial.byteCoefficient q + 1) * (n + 2) ^ 2 := hsaved
      _ ≤ (PrefixLoopPolynomial.byteCoefficient q + 1) *
          ((q + 2) ^ 2 * X ^ 2) := Nat.mul_le_mul_left _ hNpow2
      _ ≤ (PrefixLoopPolynomial.byteCoefficient q + 1) *
          (q + 2) ^ 2 * X ^ 5 := by
            have h := Nat.mul_le_mul_left
              ((PrefixLoopPolynomial.byteCoefficient q + 1) * (q + 2) ^ 2) hX2
            nlinarith
  have hloopTerm : n * PrefixLoopPolynomial.callbackCoefficient q *
      (n + 2) ^ 4 ≤
      q * PrefixLoopPolynomial.callbackCoefficient q * (q + 2) ^ 4 * X ^ 5 := by
    have hfirst := Nat.mul_le_mul_right
      (PrefixLoopPolynomial.callbackCoefficient q) hNlinear
    have hmul := Nat.mul_le_mul hfirst hNpow4
    nlinarith [hmul]
  have hheader : SourceCSPPositiveHeader.positiveBound 2 q L
        P.constraints.bits.length n P.constraints ≤
      SourceCSPRowLoopHeaderPolynomial.headerCoefficient 2 q * X ^ 5 := by
    have hfull := SourceCSPRowLoopHeaderPolynomial.headerCost_quadratic
      P hsize
    have hpart : SourceCSPPositiveHeader.positiveBound 2 q L
        P.constraints.bits.length n P.constraints ≤
      SourceCSPRowLoopBridgeSequence.headerCost 2 q P := by
      change SourceCSPPositiveHeader.positiveBound 2 q L
          P.constraints.bits.length n P.constraints ≤
        SourceCSPPositiveHeader.positiveBound 2 q L
          P.constraints.bits.length n P.constraints +
          2 * (SourceCSPPositiveHeader.rows P).length +
          4 * (n - 1) + 2 * P.constraints + 14
      omega
    have hquad : SourceCSPPositiveHeader.positiveBound 2 q L
        P.constraints.bits.length n P.constraints ≤
      SourceCSPRowLoopHeaderPolynomial.headerCoefficient 2 q * X ^ 2 :=
      hpart.trans hfull
    exact hquad.trans (Nat.mul_le_mul_left _ hX2)
  have hcount : (countWord n).length = 8 * n := by
    simp [countWord]
  have hL5 : L ≤ X ^ 5 := hLX.trans hX5
  have hXone : 1 ≤ X ^ 5 := by
    simpa using (Nat.pow_le_pow_left hX 5)
  have hlinear : 2 * L + 22 * n + 16 ≤ (20 + 22 * q) * X ^ 5 := by
    nlinarith [Nat.mul_le_mul_left 2 hL5,
      Nat.mul_le_mul_left 22 hN5,
      Nat.mul_le_mul_left 16 hXone]
  change (2 * L + 2) +
      SourceCSPPositiveHeader.positiveBound 2 q L
        P.constraints.bits.length n P.constraints +
      (2 * n + 2) + PrefixLoopPolynomial.polynomialClock n q [] [] [] +
      (2 * (savedWord n q).length + 2 +
        (2 * (countWord n).length + 2) + 1) + 4 ≤
      coefficient q * X ^ 5
  rw [hcount]
  unfold PrefixLoopPolynomial.polynomialClock coefficient
  simp only [PrefixLoopPolynomial.inputMass, List.length_nil,
    add_zero]
  nlinarith [hlinear, hheader, hsaved2, hloopTerm,
    Nat.mul_le_mul_left 2 hsaved2]

theorem raw_atLeast_stash_polynomial {q : Nat}
    (P : EncodedETHSource.ConstraintInstance 2 q)
    (hn : 0 < P.vertices) (hsize : SourceCSPCodec.ValidSize P) :
    ∃ t S, t ≤ coefficient q *
        ((EncodedETHSource.constraintBits P).length + 1) ^ 5 ∧
      ((advance (SourcePrefixRawProgram.program q))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))),
          ((((none, SourcePrefixRawHeader.initialControl q), none),
            (PrefixLoopCallback.initial, none)), (none, none)),
          SourcePrefixRawFrame.initial q
            (EncodedETHSource.constraintBits P)⟩ :
          TM2.Cfg (fun _ : SourcePrefixRawFrame.Stack q => Bool) _ _) =
        ⟨none,
          ((((none, SourcePrefixRawHeader.initialControl q), none),
            (PrefixLoopCallback.initial, none)), (none, none)), S⟩ ∧
      (∀ k : SourceCSPEntryWrapper.Ambient q,
        S (SourcePrefixRawFrame.entryEmbedding k) =
          (SourceCSPEntryWrapper.initial q
            (EncodedETHSource.constraintBits P)
            (savedWord P.vertices q) [] (countWord P.vertices)).stk k) := by
  obtain ⟨t, S, ht, hr, he⟩ := raw_atLeast_stash P hn hsize
  exact ⟨t, S, ht.trans (rawClock_polynomial P hsize), hr, he⟩

#print axioms rawClock_polynomial
#print axioms raw_atLeast_stash_polynomial

end EthInapproximability.CurrentPaper.SourcePrefixRawPolynomial
