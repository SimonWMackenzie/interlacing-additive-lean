import CurrentAdditive.QuarticHeaderFromBank
import CurrentAdditive.QuarticSquareActual

/-! The selected v27 square/header length is independent of the fair tape. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication (natField)

def headerLength27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) : ℕ :=
  let o := select27 hn edge Δ γ k
  let q := SquarePadding.side o.rows o.cols
  (natField (2 * o.budget + k)).length + 2 * (natField q).length + q * q

theorem headerWord_length27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) :
    (Paper2.HeaderWordRun.headeredWord k
      (Paper2.ASquare.squareInstance (selectedInstance27 hn edge Δ γ k t))).length =
      headerLength27 hn edge Δ γ k := by
  rw [headerWord27_eq_square_classifier_word hn edge Δ γ k t]
  simp only [headerLength27, Paper2.AModel.matrixWord,
    List.length_append, MatrixMaterialization.rowMajor_length]
  omega

theorem classifier_tape_length27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (C : Paper2.SelectedTape.Algorithm)
    (t : (select27 hn edge Δ γ k).Tape) :
    C.tapeLength (Paper2.HeaderWordRun.headeredWord k
      (Paper2.ASquare.squareInstance (selectedInstance27 hn edge Δ γ k t))) =
      C.cR * (headerLength27 hn edge Δ γ k + 1) ^ C.dR := by
  simp only [Paper2.SelectedTape.Algorithm.tapeLength,
    headerWord_length27]

#print axioms headerWord_length27
#print axioms classifier_tape_length27

end Paper2.CurrentAdditive.QuarticClassEndpoint
