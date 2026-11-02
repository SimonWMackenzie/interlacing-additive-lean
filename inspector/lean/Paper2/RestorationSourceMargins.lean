import Paper2.SourceDeletionParameters

/-!
# Numerical margins for the original restoration source

Frozen v12 `eq:admissibility`, `eq:reference-loss` and `res:foreign`.
These inequalities use the actual definition of eta and the displayed
finite schedule checks. They do not assume a reference-loss or foreign
rectangle conclusion. The effective public parameter compiler is separate.
-/

namespace Paper2.RestorationSourceMargins

open SourceDeletionParameters

/-- The good singleton projection is above the reference profile's 3/5 rung. -/
theorem eta_lt_two_fifths (s : ℕ) (hs : 0 < s) (delta zeta : ℝ)
    (hd : 0 < delta) (hz : 0 < zeta) :
    eta s delta zeta < 2 / 5 := by
  have he := eta_pos s hs delta zeta hd hz
  have hb := (eta_width_bounds s hs delta zeta).1
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  nlinarith

/-- Every fixed template bin has enough mass for the two-stream floor. -/
theorem other_bin_margin (s : ℕ) (hs : 0 < s) (delta zeta x : ℝ)
    (hsmall : 2 * (s : ℝ) * x ≤ 1 / 1000) :
    2 * (s : ℝ) * x <
      1 - eta s delta zeta * s / (255 / 256 : ℝ) := by
  have hb := (eta_width_bounds s hs delta zeta).1
  linarith

/-- The original good pair projection pays the permitted pair-label loss. -/
theorem pair_margin (s : ℕ) (x : ℝ)
    (hsmall : 2 * (s : ℝ) * x ≤ 1 / 1000) :
    (49 / 64 : ℝ) + 2 * s * x <
      ((99 / 100 : ℝ) + (255 / 256 : ℝ)^2 - 1) /
        (255 / 256 : ℝ)^2 := by
  norm_num at *
  linarith

/-- The stronger displayed quadratic check pays the sum of path losses. -/
theorem reference_loss_margin (w : ℕ) (eta x : ℝ) (hx : 0 ≤ x)
    (hsmall : 2 * (w : ℝ) ^ 2 * x ≤ eta / (16 * (127 / 128 : ℝ))) :
    eta / (16 * (127 / 128 : ℝ)) +
      2 * w * ((w : ℝ) - 1) * x ≤ eta / (8 * (127 / 128 : ℝ)) := by
  have hn : 0 ≤ (w : ℝ) * x := mul_nonneg (Nat.cast_nonneg w) hx
  norm_num at hsmall ⊢
  nlinarith

/-- The three displayed receipt terms are each paid by a public check or
the fixed mixture weights. This is only arithmetic; an actual sum of
foreign transfers must first be bounded by this expression. -/
theorem foreign_receipt_margin (w q₂ : ℕ) (eta x : ℝ)
    (heta : 0 ≤ eta)
    (hfirst : 4 * (1 / 256 : ℝ) * w * q₂ * x ≤ eta / 32)
    (hlast : 4 * (1 / 256 : ℝ) * w / q₂ ≤ eta / 32) :
    (w : ℝ) * (2 * (1 / 256 : ℝ) * w * (2 * q₂ * x) +
      5 * (1 / 256 : ℝ) * eta / (4 * (127 / 128 : ℝ)) +
      4 * (1 / 256 : ℝ) * w / q₂) ≤ 3 * eta * w / 32 := by
  have hmiddle : 5 * (1 / 256 : ℝ) * eta / (4 * (127 / 128 : ℝ)) ≤
      eta / 32 := by norm_num; linarith
  have hsum : 2 * (1 / 256 : ℝ) * w * (2 * q₂ * x) +
      5 * (1 / 256 : ℝ) * eta / (4 * (127 / 128 : ℝ)) +
      4 * (1 / 256 : ℝ) * w / q₂ ≤ 3 * eta / 32 := by
    norm_num at hfirst hlast hmiddle ⊢
    nlinarith [hfirst, hlast, hmiddle]
  have hmul := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg w : (0 : ℝ) ≤ w)
  nlinarith

end Paper2.RestorationSourceMargins

#print axioms Paper2.RestorationSourceMargins.eta_lt_two_fifths
#print axioms Paper2.RestorationSourceMargins.other_bin_margin
#print axioms Paper2.RestorationSourceMargins.pair_margin
#print axioms Paper2.RestorationSourceMargins.reference_loss_margin
#print axioms Paper2.RestorationSourceMargins.foreign_receipt_margin
