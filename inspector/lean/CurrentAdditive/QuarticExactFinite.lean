import CurrentAdditive.QuarticAsymptotics
import Paper2.ReductionDimensions

/-! Exact two-sided accounting for the rectangular quartic output.
Source: frozen v27 `sections/06-reduction.tex`, (final-dimensions) and
(quantitative-size). No independent notion of output size is introduced. -/

namespace CurrentAdditive.QuarticExactAsymptotics

open Paper2 Paper2.SourceRecursiveNoSampling

theorem entropy_three_terms (B k : ℕ) (hB : 1 ≤ B) :
    compressionEntropy (2^(B-1)) (B+k) =
      2^(3*B+k-3) + 2^(2*B+k-2) + 2^(B+k) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : B ≠ 0)
  have h1 : 3*(b+1)+k-3 = 3*b+k := by omega
  have h2 : 2*(b+1)+k-2 = 2*b+k := by omega
  have h3 : b+1+k = b+k+1 := by omega
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right, h1, h2, h3,
    compressionEntropy, pow_add]
  ring

/-- The ceiling in the row count changes the scaled entry count by less
than one column-width of rows. This is a two-sided statement for the actual
rectangular dimensions, not a newly estimated table. -/
theorem entries_ceiling_sandwich (Z L : ℕ) (hL : 1 ≤ L) :
    2*(Z+12)^2 ≤
      L * Paper2.ReductionDimensions.entries Z L ∧
    L * Paper2.ReductionDimensions.entries Z L <
      2*(Z+12)*(Z+12+L) := by
  let A := Z+12
  let c := A ⌈/⌉ L
  have hlo : A ≤ L*c := by
    exact (ceilDiv_le_iff_le_mul (by omega : 0 < L)).mp le_rfl
  have hhi : L*c < A+L := by
    have hdiv := Nat.div_mul_le_self (A+L-1) L
    have hc : L*c ≤ A+L-1 := by
      simpa only [c, Nat.ceilDiv_eq_add_pred_div, mul_comm] using hdiv
    omega
  have hentry : Paper2.ReductionDimensions.entries Z L = 2*A*c := by
    dsimp [Paper2.ReductionDimensions.entries,
      compressionRowDraws, compressionColumnDraws, A, c]
    ring
  rw [hentry]
  change 2*A^2 ≤ L*(2*A*c) ∧
    L*(2*A*c) < 2*A*(A+L)
  constructor
  · have hm := Nat.mul_le_mul_left (2*A) hlo
    nlinarith
  · have hA : 0 < 2*A := by dsimp [A]; omega
    have hm := Nat.mul_lt_mul_of_pos_left hhi hA
    nlinarith

/-- Explicit finite remainder around the manuscript's principal monomial.
Here `A = r²·2^(H-1)` and the extra entropy terms and row ceiling are both
charged. As `B` grows with `L ≤ B`, the upper/lower ratio tends to one. -/
theorem entries_principal_sandwich (B k L : ℕ)
    (hL : 1 ≤ L) :
    let r := 2^(B-1)
    let v := 2^(B+k-1)
    let A := r*r*v
    let Z := compressionEntropy r (B+k)
    2*A^2 ≤ L*Paper2.ReductionDimensions.entries Z L ∧
      L*Paper2.ReductionDimensions.entries Z L <
        2*(A+15*r*v)*(A+15*r*v+L) := by
  dsimp
  let r := 2^(B-1)
  let v := 2^(B+k-1)
  let A := r*r*v
  let Z := compressionEntropy r (B+k)
  have hr : 1 ≤ r := by
    have hh : 0 < r := by dsimp [r]; positivity
    omega
  have hv : 1 ≤ v := by
    have hh : 0 < v := by dsimp [v]; positivity
    omega
  have hrv : 1 ≤ r*v := by nlinarith
  have hZ : Z+12 = A+(r+2)*v+12 := by
    dsimp [Z, A, compressionEntropy]
    ring
  have hlo : A ≤ Z+12 := by rw [hZ]; omega
  have hhi : Z+12 ≤ A+15*r*v := by
    rw [hZ]
    nlinarith
  have hentries := entries_ceiling_sandwich Z L hL
  change 2*A^2 ≤ L*Paper2.ReductionDimensions.entries Z L ∧
    L*Paper2.ReductionDimensions.entries Z L <
      2*(A+15*r*v)*(A+15*r*v+L)
  constructor
  · have hsquare := Nat.pow_le_pow_left hlo 2
    nlinarith [hentries.1]
  · have hplus : Z+12+L ≤ A+15*r*v+L := Nat.add_le_add_right hhi L
    have hm := Nat.mul_le_mul hhi hplus
    nlinarith [hentries.2]

theorem principal_pow_exact (B k : ℕ) (hB : 1 ≤ B) :
    let r := 2^(B-1)
    let v := 2^(B+k-1)
    let A := r*r*v
    2*A^2 = 2^(6*B+2*k-5) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : B ≠ 0)
  have he : 6*(b+1)+2*k-5 = 6*b+2*k+1 := by omega
  have hv : b+1+k-1 = b+k := by omega
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right, he, hv,
    pow_add]
  rw [show 6*b=b*6 by omega, pow_mul,
    show 2*k=k*2 by omega, pow_mul]
  ring

/-- The precise central power and both finite errors for the actual source
dimensions, with the public source budget `B`, not a fabricated size
parameter. -/
theorem source_entries_two_sided (L r q k : ℕ) (hL : 1 ≤ L) :
    let B := sourceBudget L r q k
    let u := 2^(B-1)
    let v := 2^(B+k-1)
    let A := u*u*v
    let T := sourceRows L r q k * sourceCols L r q k
    2^(6*B+2*k-5) ≤ L*T ∧
      L*T < 2*(A+15*u*v)*(A+15*u*v+L) := by
  let B := sourceBudget L r q k
  have hB : 1 ≤ B := by
    dsimp [B, sourceBudget]
    omega
  have hH : sourceCost L r q k = B+k := by
    dsimp [B, sourceCost, sourceBudget]
    ring
  have hs := entries_principal_sandwich B k L hL
  have hp := principal_pow_exact B k hB
  have hT : sourceRows L r q k * sourceCols L r q k =
      Paper2.ReductionDimensions.entries
        (compressionEntropy (2^(B-1)) (B+k)) L := by
    dsimp [sourceRows, sourceCols, Paper2.ReductionDimensions.entries,
      sourceRank]
    rw [hH]
  dsimp only at hs hp ⊢
  rw [← hT] at hs
  rw [hp] at hs
  exact hs

/-- The preceding bound is for the literal v27 printed rectangle at
`L = clog₂ n`, including the quartic width and source schedule. -/
theorem printedT27_two_sided (n m Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hn : 2 ≤ n) :
    let L := Nat.clog 2 n
    let r := 4 * RestorationWidthScheduleScratch.ell L
    let q := CurrentAdditive.RandomizedSchedule.q27
      (V := Fin n) (E := Fin m) L γ Δ
    let B := sourceBudget L r q k
    let u := 2^(B-1)
    let v := 2^(B+k-1)
    let A := u*u*v
    let T := CurrentAdditive.QuarticAsymptotics.printedT27 n m Δ γ k
    2^(6*B+2*k-5) ≤ L*T ∧
      L*T < 2*(A+15*u*v)*(A+15*u*v+L) := by
  have hL : 1 ≤ Nat.clog 2 n :=
    Nat.succ_le_of_lt (Nat.clog_pos (by decide) (by omega))
  simpa only [CurrentAdditive.QuarticAsymptotics.printedT27] using
    source_entries_two_sided (Nat.clog 2 n)
      (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n))
      (CurrentAdditive.RandomizedSchedule.q27
        (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ) k hL

end CurrentAdditive.QuarticExactAsymptotics
