import Mathlib

/-!
# Parameterized NP route: `PCut` absorption pilot

This file checks the shifted polynomial-cutoff arithmetic used by compiler
steps C6--C7 in
`routes/parameterized-np/autoformalization/sections/02-mechanical-contract.tex`
and by `eq:persistent-cutoffs` in Section 6.
-/

namespace EthInapproximability.ParameterizedNP

/-- The literal persistent-cutoff predicate from `eq:persistent-cutoffs`.
The strict degree condition `d < e` belongs to cutoff construction and
persistence; a stored certificate at one point needs only the inequality.
-/
def PCutPred (A d e r : Nat) : Prop :=
  2 ≤ r ∧ A * (r + 2) ^ d ≤ (r + 2) ^ e

/-- Absorb the manuscript's `ell + 2` base into a coefficient `2^d` once
`ell ≥ 2`.  This is the missing local inequality behind the repaired C7
successor certificate.
-/
theorem polynomial_shift_absorption {C d ell : Nat} (hell : 2 ≤ ell) :
    C * (ell + 2) ^ d ≤ (C * 2 ^ d) * ell ^ d := by
  have hbase : ell + 2 ≤ 2 * ell := by omega
  have hpow : (ell + 2) ^ d ≤ (2 * ell) ^ d := Nat.pow_le_pow_left hbase d
  calc
    C * (ell + 2) ^ d ≤ C * (2 * ell) ^ d :=
      Nat.mul_le_mul_left C hpow
    _ = (C * 2 ^ d) * ell ^ d := by simp [Nat.mul_pow]; ac_rfl

/-- **Shifted `PCut` pilot.** Store
`PCutPred (C * 2^d) d e (ell - 2)`, not `PCutPred C d e (ell - 2)`.
At `ell ≥ 4`, its endpoint is exactly `ell`; the preceding absorption lemma
then proves the successor inequality
`C (ell+2)^d ≤ ell^e` claimed in Section 2.
-/
theorem pCut_shifted_certificate {C d e ell : Nat} (hell : 4 ≤ ell)
    (hcut : PCutPred (C * 2 ^ d) d e (ell - 2)) :
    C * (ell + 2) ^ d ≤ ell ^ e := by
  have hell2 : 2 ≤ ell := by omega
  have hendpoint : ell - 2 + 2 = ell := by omega
  have hstored : (C * 2 ^ d) * ell ^ d ≤ ell ^ e := by
    simpa [PCutPred, hendpoint] using hcut.2
  exact (polynomial_shift_absorption hell2).trans hstored

end EthInapproximability.ParameterizedNP
