import EthInapproximability.CurrentPaper.FixedBin

/-!
# Indexed-family lower bounds at every protected routing scale

Source: frozen v8 `A-stage4-details.tex`,
`lem:paper-protected-routed-closure`, the ordinary-coordinate child argument.
Small scales use the proved row-doubling bound and actual balanced projection;
large scales use localized stopping on a selected subset of actual blocks.
The hypotheses contain two one-copy profiles and scalar stopping gates, not
an assumed all-scale communication lower bound.
-/

namespace EthInapproximability.CurrentPaper.ProtectedIndexedLadder

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open ProtocolSeparation CertifiedStopping TerminalExcess

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [Nonempty X] [Nonempty Y] [DecidableEq Y]

def markerCount (n : ℕ) : ℕ := if n = 0 then 2 else 3 * 2 ^ n / 4 + 1

omit [Nonempty Y] in
theorem balanced_weaken {q L t u : ℕ} {S : Fin L → Fin q → Y} {ε : ℝ}
    (hS : IsBalancedFamily t S ε) (htu : u ≤ t) : IsBalancedFamily u S ε :=
  ⟨hS.1, fun J hJ a => hS.2 J (hJ.trans htu) a⟩

theorem markerCount_le_of_weight (n k : ℕ) (hzero : n = 0 → 2 ≤ k)
    (hweight : 3 * 2 ^ n < 4 * k) : markerCount n ≤ k := by
  by_cases hn : n = 0
  · simpa only [markerCount, if_pos hn] using hzero hn
  · simp only [markerCount, if_neg hn]
    omega

theorem base_count_le (n : ℕ) : 2 ^ (max 1 n - 1) + 1 ≤ markerCount n := by
  by_cases hn : n = 0
  · subst n; norm_num [markerCount]
  · have hn1 : 1 ≤ n := by omega
    have hp : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hn1]
    simp only [markerCount, if_neg hn, max_eq_right hn1, hp]
    omega

theorem copyCount_scaled {m : ℕ} (hm : 5 ≤ m) :
    16 * HardSeed.copyCount m = 9 * 2 ^ m := by
  have hp : (2 : ℕ) ^ m = 32 * 2 ^ (m - 5) := by
    calc
      (2 : ℕ) ^ m = 2 ^ ((m - 5) + 5) := by rw [Nat.sub_add_cancel hm]
      _ = 32 * 2 ^ (m - 5) := by rw [pow_add]; ring
  unfold HardSeed.copyCount
  rw [hp]
  ring

theorem stopping_count_le {m n : ℕ} (hm : 5 ≤ m) (hmn : m ≤ n) :
    2 ^ (n - m) * HardSeed.copyCount m ≤ markerCount n := by
  have hn : n ≠ 0 := by omega
  have hp : (2 : ℕ) ^ n = 2 ^ (n - m) * 2 ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hmn]
  have hs : 16 * (2 ^ (n - m) * HardSeed.copyCount m) = 9 * 2 ^ n := by
    rw [hp]
    have hc := copyCount_scaled hm
    calc
      _ = 2 ^ (n - m) * (16 * HardSeed.copyCount m) := by ring
      _ = _ := by rw [hc]; ring
  simp only [markerCount, if_neg hn]
  omega

/-- Every dyadic scale needed by the protected Alice-child argument is a
lower bound on the literal indexed restriction, with the same original
column labels. No cost statement is assumed at any of these scales. -/
theorem dyadic_half_test (f : X → Y → Bool) {H m R L : ℕ} {x h ε : ℝ}
    (hH : 2 ≤ H) (hm : 2 ^ 20 ≤ m) (hx : 0 < x)
    (hrow : (2 : ℝ) ^ m * x ≤ 1) (hε : 0 ≤ ε) (hh : 0 < h)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 x (3 / 10)))
    (S : Fin L → Fin (2 ^ R * 2 ^ m) → Y)
    (hS : IsBalancedFamily (2 ^ m) S ε)
    (hdensity : (9 / 25 : ℝ) ≤ h / (2 * (1 + ε)))
    (hgateOne : (3 / 5 : ℝ) ≤ yLoss ε (2 ^ m) h (H + (R + m)))
    (hgateSeed : HardSeed.columnDensity ((2 : ℝ) ^ m) ≤
      h * (2 : ℝ) ^ (-((H + m : ℕ) : ℝ)) / (1 + ε))
    (n : ℕ) (hn : n ≤ R + m) :
    BlockLowerBound (relaxedInterlace f S) Prod.fst Finset.univ
      (markerCount n) ⌈(Fintype.card X : ℝ) * ((2 : ℝ) ^ (n + 1) * x)⌉₊
      (h / 2) (H + max 1 n) := by
  classical
  intro Rs Cs Q hCsub hCs hQ hRs
  have hm1 : 1 ≤ m := by omega
  by_cases hnm : n < m
  · have hk : max 1 n ≤ m := max_le (by omega) (by omega)
    have hk1 : 1 ≤ max 1 n := le_max_left _ _
    have hkn : max 1 n ≤ n + 1 := max_le (by omega) (by omega)
    have hpow : (2 : ℝ) ^ max 1 n ≤ (2 : ℝ) ^ m :=
      pow_le_pow_right₀ (by norm_num) hk
    have hpow' : (2 : ℝ) ^ max 1 n ≤ (2 : ℝ) ^ (n + 1) :=
      pow_le_pow_right₀ (by norm_num) hkn
    have hrow' : (2 : ℝ) ^ max 1 n * x ≤ 1 :=
      (mul_le_mul_of_nonneg_right hpow hx.le).trans hrow
    have hS' : IsBalancedFamily (2 ^ max 1 n) S ε :=
      balanced_weaken hS (Nat.pow_le_pow_right (by omega) hk)
    have hdensity' : (9 / 25 : ℝ) ≤ (h / 2) / (1 + ε) := by
      simpa only [div_div, mul_comm 2] using hdensity
    have hb := FixedBin.baseTest f hH hk1 hx hrow' hε h1 h2 S hS' hdensity'
    apply hb Rs Cs Q hCsub hCs ((base_count_le n).trans hQ)
    intro i hi
    apply le_trans _ (hRs i hi)
    apply Nat.ceil_mono
    dsimp [excessRows]
    simp only [pow_zero, one_mul]
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow' hx.le)
      (Nat.cast_nonneg (Fintype.card X) : (0 : ℝ) ≤ Fintype.card X)]
  · have hmn : m ≤ n := by omega
    have hR : n - m ≤ R := by omega
    have hselect := (stopping_count_le (by omega : 5 ≤ m) hmn).trans hQ
    obtain ⟨Q', hsub, hcard⟩ := Finset.exists_subset_card_eq hselect
    have hRows : ∃ Qs : Finset (Fin (2 ^ R * 2 ^ m)),
        Qs.card = 2 ^ (n - m) * HardSeed.copyCount m ∧
        IsEquipartitionedGE Rs Qs
          ⌈(2 : ℝ) ^ (n - m + m) * x * (Fintype.card X : ℝ)⌉₊ := by
      refine ⟨Q', hcard, ?_⟩
      intro i hi
      apply le_trans _ (hRs i (hsub hi))
      apply Nat.ceil_mono
      rw [Nat.sub_add_cancel hmn]
      have hp : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + 1) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hx.le)
        (Nat.cast_nonneg (Fintype.card X) : (0 : ℝ) ≤ Fintype.card X)]
    have hCols : h * (2 : ℝ) ^ (-((1 : ℕ) : ℝ)) * (L : ℝ) ≤ (Cs.card : ℝ) := by
      simpa [Real.rpow_neg_one, div_eq_mul_inv, mul_assoc] using hCs
    have hcost := localized_stopping f hH hm hx hrow hε hh h1 h2 S hS
      hgateOne hgateSeed 1 (n - m) (le_refl _) hR Rs Cs hRows hCols
    simpa only [Nat.sub_add_cancel hmn, max_eq_right (show 1 ≤ n by omega)] using hcost

end EthInapproximability.CurrentPaper.ProtectedIndexedLadder
