import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalCodec

/-!
# Uniform all-input cost of the corrected physical row loop

The source alphabet and row arity are fixed by the reduction. The following
coefficient is symbolic in those constants and in the syntax of the two
actual finite programs. No intermediate parser or reset bank is supplied.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalPolynomial

open Turing BitMachineEncoding

private def parserCoefficient (q H : Nat) : Nat := 6 * q + 2 * H + 3

private def wordCoefficient (q H : Nat) : Nat :=
  q + BitMachineStackGrowth.perStep
    (SourceCSPRowQueryFrame.rowProgram (q := q) (H := H)) *
    parserCoefficient q H

private def combinedCoefficient (q H : Nat) : Nat :=
  parserCoefficient q H +
    q * 100 * (wordCoefficient q H + 1) ^ 2 + 2

private def resetCoefficient (q H : Nat) : Nat :=
  (q * 5 + 4) *
    (q + SourceCSPRowLoopTotalUniformOne.pushConstant q H *
      (1 + combinedCoefficient q H)) +
  (q * 5 + 4) + 2 + (2 * q + 2) + 1

def rowCoefficient (q H : Nat) : Nat :=
  combinedCoefficient q H + 3 + resetCoefficient q H

def loopCoefficient (q H : Nat) : Nat := rowCoefficient q H + 3

theorem oneBound_quadratic (q H L : Nat) (input cap : List Bool)
    (hinput : input.length ≤ L) (hcap : cap.length ≤ q * L) :
    SourceCSPRowLoopTotalUniformOne.oneBound q H input cap ≤
      rowCoefficient q H * (L + 1) ^ 2 := by
  let X := L + 1
  let P := parserCoefficient q H
  let W := wordCoefficient q H
  let T := combinedCoefficient q H
  let R := resetCoefficient q H
  let p := BitMachineStackGrowth.perStep
    (SourceCSPRowQueryFrame.rowProgram (q := q) (H := H))
  let c := SourceCSPRowLoopTotalUniformOne.pushConstant q H
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hX2 : 1 ≤ X ^ 2 := by nlinarith
  have hLX : L ≤ X := by dsimp [X]; omega
  have hXsq : X ≤ X ^ 2 := by nlinarith
  have hinputX : input.length ≤ X := hinput.trans hLX
  have hcapX : cap.length ≤ q * X :=
    hcap.trans (Nat.mul_le_mul_left q hLX)
  have hp : SourceCSPRowLoopTotalCombinedAll.parserBound q H input ≤ P * X := by
    dsimp [SourceCSPRowLoopTotalCombinedAll.parserBound, P,
      parserCoefficient, X]
    nlinarith [Nat.mul_le_mul_left (2 * q) hinput]
  have hw : SourceCSPRowLoopTotalCombinedAll.wordBound q H input cap ≤
      W * X := by
    dsimp [SourceCSPRowLoopTotalCombinedAll.wordBound, W,
      wordCoefficient, p]
    have hm := Nat.mul_le_mul_left p hp
    dsimp [p] at hm
    nlinarith
  have hwone : SourceCSPRowLoopTotalCombinedAll.wordBound q H input cap + 1 ≤
      (W + 1) * X := by nlinarith
  have hsq :
      (SourceCSPRowLoopTotalCombinedAll.wordBound q H input cap + 1) ^ 2 ≤
      ((W + 1) * X) ^ 2 := Nat.pow_le_pow_left hwone 2
  have ht : SourceCSPRowLoopTotalCombinedAll.totalBound q H input cap ≤
      T * X ^ 2 := by
    dsimp [SourceCSPRowLoopTotalCombinedAll.totalBound, T,
      combinedCoefficient]
    nlinarith [Nat.mul_le_mul_left (q * 100) hsq]
  have htone : 1 + SourceCSPRowLoopTotalCombinedAll.totalBound q H input cap ≤
      (1 + T) * X ^ 2 := by nlinarith
  have hr : SourceCSPRowLoopTotalUniformOne.resetBound q H input cap ≤
      R * X ^ 2 := by
    have hcapX2 : cap.length ≤ q * X ^ 2 := by
      exact hcapX.trans (Nat.mul_le_mul_left q hXsq)
    have hinside : cap.length + c *
        (1 + SourceCSPRowLoopTotalCombinedAll.totalBound q H input cap) ≤
        (q + c * (1 + T)) * X ^ 2 := by
      have hm := Nat.mul_le_mul_left c htone
      nlinarith
    have hfirst := Nat.mul_le_mul_left (q * 5 + 4) hinside
    have hsecond := Nat.mul_le_mul_left 2 hcapX2
    change (q * 5 + 4) *
        (cap.length + c *
          (1 + SourceCSPRowLoopTotalCombinedAll.totalBound q H input cap)) +
        (q * 5 + 4) + 2 + (2 * cap.length + 2) + 1 ≤
      ((q * 5 + 4) * (q + c * (1 + T)) +
        (q * 5 + 4) + 2 + (2 * q + 2) + 1) * X ^ 2
    nlinarith
  change SourceCSPRowLoopTotalCombinedAll.totalBound q H input cap + 3 +
      SourceCSPRowLoopTotalUniformOne.resetBound q H input cap ≤
    (T + 3 + R) * X ^ 2
  nlinarith

theorem loop_cost_cubic (q H m L : Nat) (input cap : List Bool)
    (hm : m ≤ L) (hinput : input.length ≤ L)
    (hcap : cap.length ≤ q * L) :
    m * SourceCSPRowLoopTotalUniformOne.oneBound q H input cap + 3 ≤
      loopCoefficient q H * (L + 1) ^ 3 := by
  have hb := oneBound_quadratic q H L input cap hinput hcap
  have hmX : m ≤ L + 1 := by omega
  have hmul := Nat.mul_le_mul hmX hb
  unfold loopCoefficient
  have hX : 1 ≤ L + 1 := by omega
  have hX3 : 1 ≤ (L + 1) ^ 3 := by nlinarith
  nlinarith [hmul]

/-- Arbitrary raw rows, literal EOF, and a cubic bound in the source input
length. The hypotheses are precisely the header guard's bounded unary count,
the fact that the row suffix lies in the input, and the positive-vertex cap. -/
theorem rows_total_codec_cubic (n a q m L : Nat) (input : List Bool)
    (E : Fin 4 → List Bool) (hn : 0 < n)
    (hm : m ≤ L) (hinput : input.length ≤ L)
    (hnsize : n - 1 ≤ q * L)
    (hcount : E 0 = List.replicate m true)
    (hcap : E 1 = List.replicate (n - 1) true)
    (hscratch : E 3 = []) :
    ∃ t S v b,
      t ≤ loopCoefficient q (a ^ q) * (L + 1) ^ 3 ∧
      ((advance (SourceCSPRowLoopTotalController.program q (a ^ q)))^[t])
        (⟨some (SourceCSPRowLoopController.adminLabel .check),
          SourceCSPRowLoopController.initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial input
            (List.replicate (n - 1) true)) E⟩ :
            SourceCSPRowLoopController.Config q (a ^ q)) =
        ⟨none, (v, some b), S⟩ ∧
      (b = true ↔ ∃ rows : Fin m → SourceCSPCodec.Row n a q,
        SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m input =
          some (rows, [])) := by
  obtain ⟨t, S, v, b, ht, hrun, hsem⟩ :=
    SourceCSPRowLoopTotalCodec.rows_total_codec n a q m input E
      hn hcount hcap hscratch
  refine ⟨t, S, v, b, ?_, hrun, hsem⟩
  exact ht.trans (loop_cost_cubic q (a ^ q) m L input
    (List.replicate (n - 1) true) hm hinput (by simpa using hnsize))

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalPolynomial
