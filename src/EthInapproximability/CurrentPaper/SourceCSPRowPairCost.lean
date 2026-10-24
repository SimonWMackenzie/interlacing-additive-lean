import EthInapproximability.CurrentPaper.SourceCSPRowPairSplitEnvelope
import EthInapproximability.CurrentPaper.SourceClauseAllSlotPolynomial
import EthInapproximability.CurrentPaper.SourceCSPRowCleanupPolynomial

/-! Fixed-q quartic majorant for one exact physical next-row plus all-slot pair. -/

namespace EthInapproximability.CurrentPaper.SourceCSPRowPairCostProduction

open SourceCSPNextParserGrowth SourceCSPNextRowFrameGrowth
open SourceCSPRowPairSplitProduction

noncomputable def pairCoefficient (q : ℕ) : ℕ :=
  (q * 5 + 9) + parseClockCoefficient q + cleanupCoefficient q +
    SourceClauseCallbackAllSlotPolynomial.allCoefficient q *
      (parseWordCoefficient q + 2) ^ 2 + 6

theorem pair_cost_le_quartic {n M q H G : ℕ}
    (rows : Fin M → SourceCSPCodec.Row n 2 q)
    (rNext : Fin M)
    (B : SourceCSPNextRowBridge.Stack q → List Bool)
    (rest : List Bool) (L : ℕ)
    (V : SourceCSPRowQueryFrame.Stack q → List Bool)
    (saved output count : List Bool)
    (hq : 0 < q)
    (hB : ∀ x, (B x).length ≤ G)
    (hn : n ≤ G) (hr : rNext.val ≤ G + 1)
    (hrest : rest.length ≤ H) (hL : L ≤ H) (hHG : H ≤ G)
    (hV : ∀ x, (V x).length ≤ parseWordCoefficient q * (H + 1) ^ 2)
    (hquery : ∀ j : Fin q, V (.inl (j, 1)) =
      List.replicate ((rows rNext).1 j).val true)
    (hsaved : saved.length ≤ G)
    (houtput : output.length ≤ G)
    (hcount : count.length ≤ G) :
    SourceCSPNextRowBridge.resetCost B (List.replicate (n - 1) true) +
        parseBudget q rest L + 2 +
        cleanupCoefficient q * (G + 1) ^ 2 + 3 +
        SourceClauseCallback.AllSlotsClock.allCost hq V n rNext.val
          (rows rNext).2 saved output count + 1 ≤
      pairCoefficient q * (G + 1) ^ 4 := by
  let M₀ := G + 1
  let Q := parseWordCoefficient q
  let T := G + Q * (H + 1) ^ 2 + 1
  let A := SourceClauseCallbackAllSlotPolynomial.allCoefficient q
  have hcap : (List.replicate (n - 1) true).length ≤ G := by
    simp only [List.length_replicate]
    omega
  have hreset := SourceCSPRowCleanupPolynomial.resetCost_le B
    (List.replicate (n - 1) true) hB hcap
  have hparse := parseBudget_le (q := q) rest hrest hL
  have hunary := TypedRowCorrespondence.unary_from_parsed_row
    rows rNext V hquery
  have hVT : ∀ x, (V x).length ≤ T := by
    intro x
    exact (hV x).trans (by dsimp [T, Q]; omega)
  have hnT : n ≤ T := by dsimp [T]; omega
  have hrT : rNext.val ≤ T := by dsimp [T]; omega
  have hsaveT : saved.length ≤ T := by dsimp [T]; omega
  have houtT : output.length ≤ T := by dsimp [T]; omega
  have hcountT : count.length ≤ T := by dsimp [T]; omega
  have hall := SourceClauseCallbackAllSlotPolynomial.allCost_le_quadratic
    hq V n rNext.val T (rows rNext).2 saved output count
    hnT hrT hVT hsaveT houtT hcountT hunary
  have hHG' : H + 1 ≤ M₀ := by dsimp [M₀]; omega
  have hsq := Nat.pow_le_pow_left hHG' 2
  have hM : 1 ≤ M₀ ^ 2 := by dsimp [M₀]; nlinarith
  have hT : T + 1 ≤ (Q + 2) * M₀ ^ 2 := by
    have hQ := Nat.mul_le_mul_left Q hsq
    have hG : G + 2 ≤ 2 * M₀ ^ 2 := by
      dsimp [M₀]
      nlinarith
    dsimp [T]
    nlinarith
  have hTsq := Nat.pow_le_pow_left hT 2
  have hA := Nat.mul_le_mul_left A hTsq
  have hM4 : M₀ ^ 2 ≤ M₀ ^ 4 := by
    calc
      M₀ ^ 2 = M₀ ^ 2 * 1 := by omega
      _ ≤ M₀ ^ 2 * M₀ ^ 2 := Nat.mul_le_mul_left _ hM
      _ = M₀ ^ 4 := by ring
  have hMle : M₀ ≤ M₀ ^ 4 := by
    have hsmall : M₀ ≤ M₀ ^ 2 := by
      calc
        M₀ = M₀ * 1 := by omega
        _ ≤ M₀ * M₀ := Nat.mul_le_mul_left M₀ (by dsimp [M₀]; omega)
        _ = M₀ ^ 2 := by ring
    exact hsmall.trans hM4
  have hone : 1 ≤ M₀ ^ 4 := by
    have hp : 0 < M₀ := by dsimp [M₀]; omega
    have hp4 := pow_pos hp 4
    omega
  have hreset4 := Nat.mul_le_mul_left (q * 5 + 9) (by
    exact hMle)
  have hparse4 := Nat.mul_le_mul_left (parseClockCoefficient q)
    (hsq.trans hM4)
  have hcleanup4 := Nat.mul_le_mul_left (cleanupCoefficient q) hM4
  have hconst4 := Nat.mul_le_mul_left 6 hone
  have hall4 :
      SourceClauseCallback.AllSlotsClock.allCost hq V n rNext.val
          (rows rNext).2 saved output count ≤
        A * (Q + 2) ^ 2 * M₀ ^ 4 := by
    calc
      _ ≤ A * (T + 1) ^ 2 := hall
      _ ≤ A * ((Q + 2) * M₀ ^ 2) ^ 2 := hA
      _ = A * (Q + 2) ^ 2 * M₀ ^ 4 := by ring
  dsimp only [M₀, A, Q] at hreset4 hparse4 hcleanup4 hconst4 hall4
  calc
    SourceCSPNextRowBridge.resetCost B (List.replicate (n - 1) true) +
          parseBudget q rest L + 2 + cleanupCoefficient q * (G + 1) ^ 2 +
          3 + SourceClauseCallback.AllSlotsClock.allCost hq V n rNext.val
            (rows rNext).2 saved output count + 1 ≤
        (q * 5 + 9) * M₀ ^ 4 +
          parseClockCoefficient q * M₀ ^ 4 +
          cleanupCoefficient q * M₀ ^ 4 +
          A * (Q + 2) ^ 2 * M₀ ^ 4 + 6 * M₀ ^ 4 := by
      dsimp only [M₀, A, Q]
      omega
    _ = pairCoefficient q * (G + 1) ^ 4 := by
      dsimp [pairCoefficient, M₀, A, Q]
      ring

end EthInapproximability.CurrentPaper.SourceCSPRowPairCostProduction
