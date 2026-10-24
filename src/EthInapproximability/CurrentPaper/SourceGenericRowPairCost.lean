import EthInapproximability.CurrentPaper.SourceGenericRowPairSplit
import EthInapproximability.CurrentPaper.SourceCSPRowCleanupPolynomial

namespace EthInapproximability.CurrentPaper.SourceGenericRowPairCost

open SourceGenericNextParserGrowth SourceGenericNextRowFrameGrowth
open scoped Classical

noncomputable def rowCellCount (q : Nat) : Nat :=
  Fintype.card (SourceClauseRowWriterTruthFrame.Stack q)

theorem inputBits_le {q H : Nat}
    (V : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : Nat) (saved output count : List Bool)
    (hn : n ≤ H) (hr : r ≤ H)
    (hV : ∀ x, (V x).length ≤ H)
    (hsaved : saved.length ≤ H)
    (houtput : output.length ≤ H)
    (hcount : count.length ≤ H) :
    SourceClauseGenericRow.inputBits V n r saved output count ≤
      rowCellCount q * H := by
  have hw := SourceClauseCallbackPolynomial.blank_words_le
    V n r H saved output count hn hr hV hsaved houtput hcount
  have hcell : ∀ x : SourceClauseRowWriterTruthFrame.Stack q,
      (SourceClauseRowWriterTruthFrame.initial V n r saved output count x).length ≤ H := by
    intro x
    cases x with
    | inl x => exact hw x
    | inr x => simp [SourceClauseRowWriterTruthFrame.initial]
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun x _ => hcell x)
  simpa [SourceClauseGenericRow.inputBits, rowCellCount] using hs

noncomputable def pairCoefficient (a q : Nat) : Nat :=
  (q * 5 + 9) + parseClockCoefficient a q +
    cleanupCoefficient a q +
    SourceClauseGenericAllSlotPolynomial.allCoefficient a q *
      (rowCellCount q * (parseWordCoefficient a q + 2) + 1)^2 + 6

theorem pair_cost_le_quartic {n M a q H G : Nat}
    (_rows : Fin M → SourceCSPCodec.Row n a q)
    (rNext : Fin M)
    (B : SourceCSPNextRowBridge.Stack q → List Bool)
    (rest : List Bool) (L : Nat)
    (V : SourceCSPRowQueryFrame.Stack q → List Bool)
    (saved output count : List Bool)
    (hB : ∀ x, (B x).length ≤ G)
    (hn : n ≤ G) (hr : rNext.val ≤ G + 1)
    (hrest : rest.length ≤ H) (hL : L ≤ H) (hHG : H ≤ G)
    (hV : ∀ x, (V x).length ≤
      parseWordCoefficient a q * (H + 1)^2)
    (hsaved : saved.length ≤ G)
    (houtput : output.length ≤ G)
    (hcount : count.length ≤ G) :
    SourceCSPNextRowBridge.resetCost B
        (List.replicate (n - 1) true) +
      parseBudget a q rest L + 2 +
      cleanupCoefficient a q * (G + 1)^2 + 3 +
      SourceClauseGenericAllSlotPolynomial.allCoefficient a q *
        (SourceClauseGenericRow.inputBits V n rNext.val
          saved output count + 1)^2 + 1 ≤
      pairCoefficient a q * (G + 1)^4 := by
  let M₀ := G + 1
  let Q := parseWordCoefficient a q
  let D := rowCellCount q
  let A := SourceClauseGenericAllSlotPolynomial.allCoefficient a q
  let T := G + Q * (H + 1)^2 + 1
  have hcap : (List.replicate (n - 1) true).length ≤ G := by
    simp only [List.length_replicate]
    omega
  have hreset := SourceCSPRowCleanupPolynomial.resetCost_le B
    (List.replicate (n - 1) true) hB hcap
  have hparse := parseBudget_le (a := a) (q := q) rest hrest hL
  have hVT : ∀ x, (V x).length ≤ T := by
    intro x
    exact (hV x).trans (by dsimp [T, Q]; omega)
  have hnT : n ≤ T := by dsimp [T]; omega
  have hrT : rNext.val ≤ T := by dsimp [T]; omega
  have hsaveT : saved.length ≤ T := by dsimp [T]; omega
  have houtT : output.length ≤ T := by dsimp [T]; omega
  have hcountT : count.length ≤ T := by dsimp [T]; omega
  have hinput := inputBits_le V n rNext.val saved output count
    hnT hrT hVT hsaveT houtT hcountT
  have hHG' : H + 1 ≤ M₀ := by dsimp [M₀]; omega
  have hsq := Nat.pow_le_pow_left hHG' 2
  have hM : 1 ≤ M₀^2 := by dsimp [M₀]; nlinarith
  have hT : T ≤ (Q + 2) * M₀^2 := by
    have hQ := Nat.mul_le_mul_left Q hsq
    have hG : G + 1 ≤ 2 * M₀^2 := by
      dsimp [M₀]
      nlinarith
    dsimp [T]
    nlinarith
  have hinput1 :
      SourceClauseGenericRow.inputBits V n rNext.val
          saved output count + 1 ≤
        (D * (Q + 2) + 1) * M₀^2 := by
    have hDT := Nat.mul_le_mul_left D hT
    dsimp [D] at hinput hDT
    nlinarith
  have hpow := Nat.pow_le_pow_left hinput1 2
  have hA := Nat.mul_le_mul_left A hpow
  have hM4 : M₀^2 ≤ M₀^4 := by
    calc
      M₀^2 = M₀^2 * 1 := by omega
      _ ≤ M₀^2 * M₀^2 := Nat.mul_le_mul_left _ hM
      _ = M₀^4 := by ring
  have hMle : M₀ ≤ M₀^4 := by
    have hsmall : M₀ ≤ M₀^2 := by
      calc
        M₀ = M₀ * 1 := by omega
        _ ≤ M₀ * M₀ := Nat.mul_le_mul_left M₀ (by dsimp [M₀]; omega)
        _ = M₀^2 := by ring
    exact hsmall.trans hM4
  have hone : 1 ≤ M₀^4 := by
    have hp : 0 < M₀ := by dsimp [M₀]; omega
    have hp4 := pow_pos hp 4
    omega
  have hreset4 := Nat.mul_le_mul_left (q * 5 + 9) hMle
  have hparse4 := Nat.mul_le_mul_left (parseClockCoefficient a q)
    (hsq.trans hM4)
  have hcleanup4 := Nat.mul_le_mul_left (cleanupCoefficient a q) hM4
  have hconst4 := Nat.mul_le_mul_left 6 hone
  have hcall4 :
      A * (SourceClauseGenericRow.inputBits V n rNext.val
          saved output count + 1)^2 ≤
        A * (D * (Q + 2) + 1)^2 * M₀^4 := by
    calc
      _ ≤ A * ((D * (Q + 2) + 1) * M₀^2)^2 := hA
      _ = A * (D * (Q + 2) + 1)^2 * M₀^4 := by ring
  dsimp only [M₀, A, Q, D] at hreset4 hparse4 hcleanup4 hconst4 hcall4
  calc
    _ ≤ (q * 5 + 9) * M₀^4 +
          parseClockCoefficient a q * M₀^4 +
          cleanupCoefficient a q * M₀^4 +
          A * (D * (Q + 2) + 1)^2 * M₀^4 + 6 * M₀^4 := by
      dsimp only [M₀, A, Q, D]
      omega
    _ = pairCoefficient a q * (G + 1)^4 := by
      dsimp [pairCoefficient, M₀, A, Q, D]
      ring

end EthInapproximability.CurrentPaper.SourceGenericRowPairCost
