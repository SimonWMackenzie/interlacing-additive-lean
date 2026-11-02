import CurrentAdditive.QuarticClockBudget
import CurrentAdditive.QuarticFixedLength
import CurrentAdditive.QuarticOutputSize

/-! The actual v27 square header has a fixed graph-size polynomial bound. -/

namespace Paper2.CurrentAdditive.QuarticClassEndpoint

open Paper2 Paper2.CurrentAdditive.QuarticConstructor
open EthInapproximability.CurrentPaper

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem headerWord_length_le_poly27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (hk : 1 ≤ k)
    (t : (select27 hn edge Δ γ k).Tape) :
    (Paper2.HeaderWordRun.headeredWord k
      (Paper2.ASquare.squareInstance
        (selectedInstance27 hn edge Δ γ k t))).length + 1 ≤
      (n + 2) ^ (332 * (k + 1)) := by
  let o := select27 hn edge Δ γ k
  let S := SquarePadding.side o.rows o.cols
  let P := (n + 2) ^ (164 * (k + 1))
  let Q := (n + 2) ^ (4 * (k + 1))
  have houtput := outputBits27_length_le_poly hn edge Δ γ k hk t
  have hbudget := selected_budget_le_resource27 hn edge Δ γ k
  have hbudgetP : o.budget ≤ P := by
    apply hbudget.trans
    dsimp [P, TotalFiniteResourcesScratch.resourceBound]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hpos := select27_dimensions_pos hn edge Δ γ k
  have hrc : o.rows * o.cols ≤ P := by
    have hlen := outputBits27_length hn edge Δ γ k t
    dsimp [o] at *
    omega
  have hr : o.rows ≤ P :=
    (Nat.le_mul_of_pos_right _ hpos.2).trans hrc
  have hc : o.cols ≤ P :=
    (Nat.le_mul_of_pos_left _ hpos.1).trans hrc
  have hS : S ≤ 4 * P := by
    have hs : S ≤ 2 * (o.rows + o.cols) :=
      Paper2.Unit4Shell.SquareWriter.side_le_two_sum hpos.1
    omega
  have hkP : k ≤ P := by
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : 2 ^ k ≤ (n + 2) ^ k := Nat.pow_le_pow_left (by omega) _
    have h3 : (n + 2) ^ k ≤ P := by
      dsimp [P]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hP2 : 2 ≤ P := by
    dsimp [P]
    have h := Nat.pow_le_pow_right (by omega : 1 ≤ n + 2)
      (by omega : 1 ≤ 164 * (k + 1))
    have hbase : 2 ≤ (n + 2) ^ 1 := by
      simpa only [pow_one] using (by omega : 2 ≤ n + 2)
    exact hbase.trans h
  have hQ81 : 81 ≤ Q := by
    dsimp [Q]
    have hbase : 3 ^ 4 ≤ (n + 2) ^ 4 :=
      Nat.pow_le_pow_left (by omega) _
    have hpow : (n + 2) ^ 4 ≤ (n + 2) ^ (4 * (k + 1)) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    norm_num at hbase
    omega
  have h1 := Paper2.AEth7.natField_length_le (2 * o.budget + k)
  have h2 := Paper2.AEth7.natField_length_le S
  have hlen := headerWord_length27 hn edge Δ γ k t
  have hlen' : (Paper2.HeaderWordRun.headeredWord k
      (Paper2.ASquare.squareInstance
        (selectedInstance27 hn edge Δ γ k t))).length =
      (EncodedCommunication.natField (2 * o.budget + k)).length +
        2 * (EncodedCommunication.natField S).length + S * S := by
    simpa only [headerLength27, S, o] using hlen
  have hSS : S * S ≤ 16 * (P * P) := by
    have := Nat.mul_le_mul hS hS
    nlinarith
  have hPP : 2 * P ≤ P * P := Nat.mul_le_mul_right P hP2
  have hbase : (Paper2.HeaderWordRun.headeredWord k
      (Paper2.ASquare.squareInstance
        (selectedInstance27 hn edge Δ γ k t))).length + 1 ≤
      81 * (P * P) := by
    rw [hlen']
    omega
  have hsplit : (n + 2) ^ (332 * (k + 1)) = Q * (P * P) := by
    dsimp [P, Q]
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [hsplit]
  exact hbase.trans (Nat.mul_le_mul_right _ hQ81)

#print axioms headerWord_length_le_poly27

end Paper2.CurrentAdditive.QuarticClassEndpoint
