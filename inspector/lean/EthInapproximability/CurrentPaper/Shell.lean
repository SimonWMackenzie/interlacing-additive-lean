import EthInapproximability.CurrentPaper.FrontSpec
import EthInapproximability.CurrentPaper.ETHTailActualContradiction

/-!
# The hypothesis-parametric ETH shell (unit 4, B4-S7, main-arm form)

Source: frozen v8 `06-eth.tex:204-243` (proof of `thm:main`) and `06-eth.tex:238-242`.

This module composes the checked all-input front (`Front.front`: CNF validator B4-S1, small
input arm B4-S2, router) with the admitted ETH contradiction
`ETHTailActualContradiction.eth_forbids_actual_source_table_solver`. It proves:

under ETH there is `δ > 0` such that for every `0 ≤ ε < δ`, every `c A d`, every threshold
`N0 ≥ 1` and every machine `Mmain`, `Mmain` can NOT answer the exact encoded SAT question on all
canonical words of valid formulas with at least `N0` variables within
`C ⌈2^(ε n)⌉ tableSize(L,n)^B (|w|+1)^D`, `L = ETHTailGrowth.repetitions c A d`.

Consequently CP-ETH (`thm:main`) is reduced to ONE remaining obligation, the *main arm*: from
`PolynomialApproximation (FinalPadding.allowance L)` build such an `Mmain` (source list H-B1,
per-branch tables H-B2 with B4-S3..S5, estimator back end `SignedMidpointApproxActualMapper`,
correctness by `Unit4Bridges.branches_semantics`). Malformed inputs, small inputs, the dispatch,
every handoff and the absorption of the front's polynomial overhead are discharged here.
Nothing here depends on the author decisions D-B1 (meaning of "total computable") or D-B2
(binder shape of the cited source hypotheses).
-/

namespace EthInapproximability.CurrentPaper.Unit4Shell

open EncodedCNF EncodedETHTail BitMachine

/-- The consumer's budget shape, on a raw word. -/
noncomputable def budget (ε : ℝ) (c A d B C D : ℕ) (w : List Bool) : ℕ :=
  C * ⌈(2 : ℝ) ^ (ε * variableCount w)⌉₊ *
    FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) (variableCount w) ^ B *
    (w.length + 1) ^ D

theorem ceil_pos (ε : ℝ) (n : ℕ) : 1 ≤ ⌈(2 : ℝ) ^ (ε * n)⌉₊ :=
  Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (Real.rpow_pos_of_pos two_pos _)).ne'

theorem tableSize_pos (L : ℕ → ℕ) (n : ℕ) : 1 ≤ FinalPadding.tableSize L n :=
  Nat.one_le_two_pow

/-- Absorption of the front's overhead into the consumer's shape. -/
theorem front_budget (ε : ℝ) (c A d B C D P K : ℕ) (w : List Bool) :
    250 * (w.length + 1) ^ 3 + 2 * (w.length + 1) + 2 + (2 * w.length + 3) +
        2 * (w.length + P) + 2 + (budget ε c A d B C D w + K) ≤
      budget ε c A d B (C + 261 + 2 * P + K) (max 3 D) w := by
  unfold budget
  set X := ⌈(2 : ℝ) ^ (ε * variableCount w)⌉₊ with hX
  set Y := FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) (variableCount w) ^ B with hY
  set Z := w.length + 1 with hZ
  have hX1 : 1 ≤ X := ceil_pos ε _
  have hY1 : 1 ≤ Y := Nat.one_le_pow _ _ (tableSize_pos _ _)
  have hZ1 : 1 ≤ Z := by omega
  have hZ3 : Z ^ 3 ≤ Z ^ max 3 D := Nat.pow_le_pow_right hZ1 (le_max_left _ _)
  have hZD : Z ^ D ≤ Z ^ max 3 D := Nat.pow_le_pow_right hZ1 (le_max_right _ _)
  have hZZ : Z ≤ Z ^ max 3 D := by
    calc Z = Z ^ 1 := (pow_one Z).symm
      _ ≤ Z ^ max 3 D := Nat.pow_le_pow_right hZ1 (by omega)
  have hW1 : Z ^ max 3 D ≤ X * Y * Z ^ max 3 D := by
    have : 1 ≤ X * Y := Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  have hCW : C * X * Y * Z ^ D ≤ C * (X * Y * Z ^ max 3 D) := by
    have := Nat.mul_le_mul_left (C * X * Y) hZD
    nlinarith
  have hone : 1 ≤ Z ^ max 3 D := Nat.one_le_pow _ _ hZ1
  nlinarith

/-- **B4-S7 (main-arm shell).** Under ETH, no main arm answers exactly on all canonical words of
valid formulas with at least `N0 ≥ 1` variables within the source-table budget. -/
theorem eth_forbids_main_arm (hETH : ETH) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 ≤ ε → ε < δ →
      ∀ (c A d N0 B C D : ℕ) (Mmain : Machine), 1 ≤ N0 →
        ¬ ∀ f : Formula, f.Valid → N0 ≤ f.variables →
          Mmain.OutputsWithin (encode f) [satAnswer (encode f)]
            (C * ⌈(2 : ℝ) ^ (ε * f.variables)⌉₊ *
              FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) f.variables ^ B *
              ((encode f).length + 1) ^ D) := by
  obtain ⟨δ, hδ, hforbid⟩ := ETHTailActualContradiction.eth_forbids_actual_source_table_solver hETH
  refine ⟨δ, hδ, fun ε hε hεδ c A d N0 B C D Mmain hN0 hmain => ?_⟩
  set P := (Front.phi N0 true).length + (Front.phi N0 false).length with hP
  set K := budget ε c A d B C D (Front.phi N0 true) + budget ε c A d B C D (Front.phi N0 false)
    with hK
  apply hforbid ε hε hεδ c A d B (C + 261 + 2 * P + K) (max 3 D) (Front.front N0 Mmain)
  intro w
  have hm : ∀ f : Formula, f.Valid → N0 ≤ f.variables →
      Mmain.OutputsWithin (encode f) [satAnswer (encode f)]
        (budget ε c A d B C D (encode f)) := by
    intro f hf hn
    have h := hmain f hf hn
    unfold budget
    rw [variableCount_encode f hf]
    exact h
  have hfront := Front.front_outputs hN0 Mmain (budget ε c A d B C D) hm w
  apply outputsWithin_mono _ hfront
  have hb := front_budget ε c A d B C D P K w
  unfold budget at hb
  simp only [hK, budget] at hb ⊢
  omega

end EthInapproximability.CurrentPaper.Unit4Shell
