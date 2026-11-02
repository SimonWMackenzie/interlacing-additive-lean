import EthInapproximability.CurrentPaper.EntryClockPoly4TFJ

/-! An actual-count replacement for the coarse `U = 2^(128*t^4)*(|enc G|+1)`
clock envelope. The list below contains the scalar/table counts used by the
existing polynomial-clock proof, without the artificial `oneLevelBound` term.
No source-p identification is claimed by this file yet. -/

noncomputable section

namespace EthInapproximability.CurrentPaper.ActualCountClock

open EntryClockPoly3

def counts (i : LI) : List ℕ :=
  [tI i, 2 ^ tI i, aI i, 2 ^ aI i, sI i,
   Construction.qOne (aI i), Construction.firstLength (aI i) (sI i),
   qI i, rxI i, cyI i, LI' i, pI i, pI i ^ tI i,
   MatrixStage4Digits.wordBase (aI i) (sI i) (cyI i),
   MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i),
   MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i) ^ sI i,
   cyI i ^ (sI i + 1), Parameters.scale (PL i), (PL i).sourceConstant,
   (PL i).nextDepth, (PL i).cost, (PL i).edges, ell3 i.G,
   (gI i).vertices, eI i]

def A (i : LI) : ℕ := (counts i).sum

private theorem le_sum_of_mem (xs : List ℕ) (x : ℕ) (hx : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.sum_cons]
      rcases List.mem_cons.mp hx with rfl | h
      · omega
      · have := ih h
        omega

theorem actual_atom_bounds (i : LI) :
    tI i ≤ A i ∧ 2 ^ tI i ≤ A i ∧ aI i ≤ A i ∧ 2 ^ aI i ≤ A i ∧
    sI i ≤ A i ∧ Construction.qOne (aI i) ≤ A i ∧
    Construction.firstLength (aI i) (sI i) ≤ A i ∧ qI i ≤ A i ∧
    rxI i ≤ A i ∧ cyI i ≤ A i ∧ LI' i ≤ A i ∧ pI i ≤ A i ∧
    pI i ^ tI i ≤ A i ∧
    MatrixStage4Digits.wordBase (aI i) (sI i) (cyI i) ≤ A i ∧
    MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i) ≤ A i ∧
    MatrixStage4Digits.binBase (aI i) (sI i) (qI i) (cyI i) ^ sI i ≤ A i ∧
    cyI i ^ (sI i + 1) ≤ A i ∧ Parameters.scale (PL i) ≤ A i ∧
    (PL i).sourceConstant ≤ A i ∧ (PL i).nextDepth ≤ A i ∧
    (PL i).cost ≤ A i ∧ (PL i).edges ≤ A i ∧ ell3 i.G ≤ A i ∧
    (gI i).vertices ≤ A i ∧ eI i ≤ A i := by
  repeat' apply And.intro
  all_goals
    unfold A
    apply le_sum_of_mem
    simp [counts]

/-- The raw `q₂` exception is charged from the *actual* bin width and encoded
edge count, not by the coarse `oneLevelBound`. The source's auxiliary-width
premise supplies the separate `sI i ≤ 2^p` conversion. -/
theorem q2_le_of_actual_bin (i : LI) (p : ℕ) (hs : sI i ≤ 2 ^ p) :
    qI i ≤ 24 * 2 ^ p * ell3 i.G := by
  have hs4 : 4 ≤ sI i := by
    have hpos := Parameters.bins_pos (PL i)
    have hdiv := Parameters.sixtyfour_dvd_bins (PL i)
    have h64 := Nat.le_of_dvd hpos hdiv
    exact le_trans (by decide : 4 ≤ 64) h64
  have hq := EthInapproximability.ParameterizedNP.GuardedSourceSlab.q2_lt i.G hs4
  have he : Fintype.card i.E ≤ ell3 i.G := by
    have h := card_le_ell3 i.G
    omega
  have hmul : 24 * sI i * Fintype.card i.E ≤ 24 * 2 ^ p * ell3 i.G := by
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 24 hs) he
  exact (le_of_lt hq).trans hmul

#print axioms actual_atom_bounds
#print axioms q2_le_of_actual_bin

end EthInapproximability.CurrentPaper.ActualCountClock
