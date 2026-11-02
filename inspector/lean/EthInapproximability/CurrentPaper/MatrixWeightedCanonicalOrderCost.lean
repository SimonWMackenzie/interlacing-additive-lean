import EthInapproximability.CurrentPaper.MatrixWeightedCanonicalOrderBridge

/-! Polynomial accounting for the physical canonical ItemOrder enumerator. -/

namespace EthInapproximability.CurrentPaper.MatrixWeightedCanonicalOrderCost

open MatrixWeightedCanonicalOrderMachine
open MatrixWeightedCanonicalOrderRun
open MatrixWeightedCanonicalOrderBridge

theorem innerCost_le (r n : ℕ) :
    innerCost r n ≤ (n + 1) * (2 * (r + n) + 5) := by
  induction n generalizing r with
  | zero => simp [innerCost]
  | succ n ih =>
      simp only [innerCost]
      have h := ih (r + 1)
      nlinarith

private def outerBound (rank count skip K : ℕ) : ℕ :=
  (K + 1) *
    (2 * count + 2 * skip + 7 +
      (count + 1) * (2 * (rank + K * (count + skip) + count) + 5))

theorem outerCost_le (rank count skip K : ℕ) :
    outerCost rank count skip K ≤ outerBound rank count skip K := by
  induction K generalizing rank with
  | zero => simp [outerCost, outerBound]; omega
  | succ K ih =>
      simp only [outerCost]
      have hi := innerCost_le rank count
      have ho := ih (rank + count + skip)
      dsimp [outerBound] at ho ⊢
      have hstep :
          (rank + count + skip) + K * (count + skip) =
            rank + (K + 1) * (count + skip) := by
        simp only [Nat.succ_mul]
        omega
      rw [hstep] at ho
      have hmono :
          (count + 1) * (2 * (rank + count) + 5) ≤
            (count + 1) *
              (2 * (rank + (K + 1) * (count + skip) + count) + 5) := by
        apply Nat.mul_le_mul_left
        omega
      nlinarith

theorem innerAccum_length_le (r n : ℕ) (acc : List Bool) :
    (innerAccum r n acc).length ≤ acc.length + innerCost r n := by
  induction n generalizing r acc with
  | zero => simp [innerAccum, innerCost]
  | succ n ih =>
      simp only [innerAccum, innerCost]
      have h := ih (r + 1) (false :: List.replicate r true ++ acc)
      simp only [List.length_cons, List.length_append, List.length_replicate] at h
      omega

theorem outerAccum_length_le (rank count skip K : ℕ) (acc : List Bool) :
    (outerAccum rank count skip K acc).length ≤
      acc.length + outerCost rank count skip K := by
  induction K generalizing rank acc with
  | zero => simp [outerAccum, outerCost]
  | succ K ih =>
      simp only [outerAccum, outerCost]
      have hi := innerAccum_length_le rank count acc
      have ho := ih (rank + count + skip) (innerAccum rank count acc)
      omega

/-- A concrete polynomial majorant for all actual machine transitions. -/
def polynomialCost (v a K : ℕ) : ℕ :=
  4 * K + 4 + (K * (v + a) + 1) + (2 * v + 2) +
    2 * outerBound 0 v a K + 2 * outerBound v a v K + 1

theorem totalCost_le_polynomial (v a K : ℕ) :
    totalCost v a K ≤ polynomialCost v a K := by
  have hv := outerCost_le 0 v a K
  have ha := outerCost_le v a v K
  have hlenV := outerAccum_length_le 0 v a K []
  have hlenA := outerAccum_length_le v a v K (outerAccum 0 v a K [])
  simp only [List.length_nil, Nat.zero_add] at hlenV
  dsimp [totalCost, polynomialCost]
  omega

universe u w

variable {V : Type u} {E : Type w}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem graph_order_run_polynomial
    (G : EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (s : ℕ) :
    ∃ t ≤ polynomialCost (Fintype.card V) (s - 3) (4 * s),
      run t ⟨some start, none,
        initialBank (Fintype.card V) (s - 3) (4 * s)⟩ =
        ⟨none, none,
          outputBank (Fintype.card V) (s - 3) (4 * s)⟩ ∧
      outputBank (Fintype.card V) (s - 3) (4 * s) 8 =
        MatrixWeightedRowOrderLookup.orderWord (GraphVectors.itemOrder G s) := by
  obtain ⟨t, ht, hr, hw⟩ := graph_order_run G s
  exact ⟨t, ht.trans (totalCost_le_polynomial _ _ _), hr, hw⟩

end EthInapproximability.CurrentPaper.MatrixWeightedCanonicalOrderCost
