import CurrentAdditive.QuarticHeaderFit

/-! The exact encoded square length and header-machine clock do not depend
on the selected fair-bit tape. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open EthInapproximability.CurrentPaper
open Paper2.AEth4

def squareEncodedLength27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ) : ℕ :=
  let o := select27 hn edge Δ γ k
  let q := SquarePadding.side o.rows o.cols
  2 * (q.bits.length + q.bits.length + o.budget.bits.length) + 3 + q * q

theorem squareEncodedLength_eq27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (t : (select27 hn edge Δ γ k).Tape) :
    (EncodedCommunication.encodeInstance
      (Paper2.ASquare.squareInstance
        (selectedInstance27 hn edge Δ γ k t))).length =
      squareEncodedLength27 hn edge Δ γ k := by
  rw [EncodedCommunication.encodeInstance_length]
  simp only [squareEncodedLength27, Paper2.ASquare.squareInstance,
    selectedInstance27, EncodedSelectedOutput.instanceOf,
    MatrixMaterialization.rowMajor_length]

noncomputable def squareHeaderClock27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (Φ : EncodedCNF.Formula) : ℕ :=
  let k := Paper2.Unit4Shell.Asymptotics.kOf Φ.variables
  let o := select27 hn edge Δ γ k
  let q := SquarePadding.side o.rows o.cols
  (2 * (EncodedCNF.encode Φ).length +
    Paper2.Unit4Shell.KofFront.BK * (Φ.variables + 1) ^ 2 +
    2 * k + 6) +
    2 * (2 * k + 1 + squareEncodedLength27 hn edge Δ γ k) + 2 +
    GrowHeader.clock k q q o.budget

theorem squareHeaderClock_eq27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (Φ : EncodedCNF.Formula)
    (t : (select27 hn edge Δ γ
      (Paper2.Unit4Shell.Asymptotics.kOf Φ.variables)).Tape) :
    KHeader.clock Φ
      (Paper2.ASquare.squareInstance
        (selectedInstance27 hn edge Δ γ
          (Paper2.Unit4Shell.Asymptotics.kOf Φ.variables) t)) =
      squareHeaderClock27 hn edge Δ γ Φ := by
  have hl := squareEncodedLength_eq27 hn edge Δ γ
    (Paper2.Unit4Shell.Asymptotics.kOf Φ.variables) t
  unfold KHeader.clock squareHeaderClock27
  simp only [EncodedComplexity.pair_length, List.length_replicate, hl]
  rfl

#print axioms squareEncodedLength_eq27
#print axioms squareHeaderClock_eq27

end Paper2.CurrentAdditive.QuarticClassEndpoint
