import EthInapproximability.CurrentPaper.ExactConstruction
import EthInapproximability.CurrentPaper.ProtocolSeparation
import EthInapproximability.CurrentPaper.ActualPrefix

/-!
# The actual two-bit bin choice in the exact reduction

Source: v8 `G-exact-control.tex`, Alice's bin choice in
`lem:exact-source-control`. The restriction to template rows is performed by
raw input pullback, without pruning the protocol. Classical separation shows
that every two-bit prefix occurs on those rows, so the full original tree has
two Alice levels. The resulting suffix correctness applies to all rows and
all columns, including the constraint rows and the joint diagonal columns.

The robustness of the transposed second matrix and the explicit integer
separation inequality remain mathematical inputs; no protocol-control
conclusion is assumed.
-/

namespace EthInapproximability.CurrentPaper.ExactBinControl

open Workspace.Types.Protocol Workspace.Types.CommComplexity
open Workspace.Types.Interlace NPCC
open ExactConstruction

/-- The integer threshold used by width-four classical separation. -/
noncomputable def threshold (N₂ b : ℕ) : ℕ :=
  ⌈(N₂ : ℝ) * (2 : ℝ) ^ (1 - (b : ℝ))⌉₊

/-- The bin threshold at the manuscript's literal real density.  In the
exact reduction `h = (log₂ d)⁻³`; no rounding of a logarithmic depth occurs. -/
noncomputable def densityThreshold (N₂ : ℕ) (h : ℝ) : ℕ :=
  ⌈2 * h * (N₂ : ℝ)⌉₊

/-- Width-four separation from the two one-copy bounds at a real row
density.  The strict integer separation gate supplies all row-density slack
needed by the two first-message tests.  Column fractions are measured in the
original four-fold column set throughout.

Source: v8 `E-exact-details.tex`, proof of `lem:exact-matrix-bounds` (iii),
using `lem:paper-two-test-rigidity` and the two-bound row ladder. -/
theorem four_bin_separation_of_oneCopy {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (f : X → Y → Bool) {H : ℕ} {h : ℝ}
    (hH : 2 ≤ H) (hh : 0 < h)
    (h1 : H ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 h (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun f 1) (bracketGE X Y 1 h ((3 / 5) / 2)))
    (hgap : 4 * densityThreshold (Fintype.card X) h < Fintype.card X)
    (P : Protocol (Fin 4 × X) (Fin 4 → Y) Bool)
    (hcost : P.cost ≤ H + 2) (hcomp : P.Computes (interlaceFun f 4)) :
    Protocol.FirstKRowBitsOn Finset.univ Finset.univ 2 P ∧
      NoWasteConclusion (Finset.univ : Finset (Fin 4)) Finset.univ
        (Protocol.prefixCodeRaw 2 P) (Fintype.card X)
        (densityThreshold (Fintype.card X) h) ∧
      ∀ j, ((Finset.univ : Finset (Fin 4 × X)).filter
        (fun a => Protocol.prefixCodeRaw 2 P a = j)).Nonempty := by
  classical
  open ProtocolSeparation in
  have hslack : 8 * h < 1 := by
    have hg : 4 * ⌈(Fintype.card X : ℝ) * (2 * h)⌉₊ <
        ⌈(Fintype.card X : ℝ) * 1⌉₊ := by
      simpa [densityThreshold, mul_comm, mul_left_comm, mul_assoc] using hgap
    have hs := ClassicalTests.strict_row_slack hg
    norm_num at hs
    linarith
  have hpow (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hℓ2 : ℓ ≤ 2) :
      H + ℓ ≤ Dfamily (interlaceFun f (2 ^ ℓ))
        (bracketGE X Y (2 ^ ℓ) ((2 : ℝ) ^ ℓ * h) (9 / 25)) := by
    have hs : (2 : ℝ) ^ ℓ * h ≤ 1 := by
      interval_cases ℓ <;> norm_num <;> linarith
    have hp := repeatedPowerOfTwo f hH hh (by norm_num : (0 : ℝ) < 3 / 5)
      (by norm_num : (3 / 5 : ℝ) ≤ 1) h1 h2 ℓ hℓ hs
    norm_num at hp ⊢
    exact hp
  have hodd : H + 2 ≤ Dfamily (interlaceFun f 3)
      (bracketGE X Y 3 (4 * h) (9 / 25)) := by
    have hp := repeatedRowDoubling f hH hh (by norm_num : (0 : ℝ) < 3 / 5)
      (by norm_num : (3 / 5 : ℝ) ≤ 1) h1 h2 2 (by omega)
      (by norm_num; linarith : (2 : ℝ) ^ 2 * h ≤ 1)
    have ht := hp.trans (min_le_left _ _)
    norm_num at ht
    exact ht
  have hCcard : ((Finset.univ : Finset (Fin 4 → Y)).card : ℝ) =
      (Fintype.card Y : ℝ) ^ 4 := by simp
  have hcol {C : Finset (Fin 4 → Y)} {z : ℝ}
      (hz : (9 / 25 : ℝ) ≤ z)
      (hc : z * ((Finset.univ : Finset (Fin 4 → Y)).card : ℝ) ≤ C.card) :
      ⌈(Fintype.card Y : ℝ) ^ 4 * (9 / 25)⌉₊ ≤ C.card := by
    apply Nat.ceil_le.mpr
    rw [hCcard] at hc
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ Fintype.card Y by positivity) 4]
  have hτ : 1 ≤ densityThreshold (Fintype.card X) h := by
    apply Nat.one_le_iff_ne_zero.mpr
    apply Nat.ne_of_gt
    apply Nat.ceil_pos.mpr
    exact mul_pos (mul_pos (by norm_num) hh)
      (by exact_mod_cast Fintype.card_pos (α := X))
  apply ProtocolSeparation.twoTestRigidity 2 H (Fintype.card X)
    (densityThreshold (Fintype.card X) h) (interlaceFun f 4) Finset.univ 1
    (by omega) (by norm_num) ?_ ?_ ?_ hτ hgap Finset.univ Finset.univ P
    Finset.univ_nonempty (Finset.Subset.refl _) (by simp) ?_ hcost
    (fun a _ c _ => hcomp a c)
  · intro j hj
    apply ProtocolSeparation.blockLowerBound_of_exact
    intro R C Q _ hc hQ hrows
    apply ProtocolSeparation.ClassicalTests.lowerBound_of_projection f Q R C hQ
      (by positivity) hrows (hcol (by norm_num) hc) ?_ (hpow (2 - j) (by omega) (by omega))
    apply ProtocolSeparation.ClassicalTests.divided_row_threshold (x := 1)
      (hT := by simp)
    interval_cases j <;> norm_num <;> linarith
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    apply ProtocolSeparation.blockLowerBound_of_exact
    intro R C Q _ hc hQ hrows
    apply ProtocolSeparation.ClassicalTests.lowerBound_of_projection f Q R C
      (by simpa using hQ) (by norm_num : 0 < 3) hrows (hcol (by norm_num) hc) ?_ hodd
    apply ProtocolSeparation.ClassicalTests.divided_row_threshold (x := 1)
      (hT := by simp)
    norm_num
    linarith
  · apply ProtocolSeparation.blockLowerBound_of_exact
    intro R C Q _ hc hQ hrows
    have hp := hpow 1 (by omega) (by omega)
    norm_num at hp
    apply ProtocolSeparation.ClassicalTests.lowerBound_of_projection f Q R C hQ
      (by norm_num : 0 < 2) hrows (hcol (by norm_num) hc) ?_ hp
    simp only [densityThreshold]
    apply Nat.ceil_mono
    ring_nf
    exact le_refl _
  · simpa only [mul_one, Nat.ceil_natCast] using
      (bracketGE.self_mem (X := X) (Y := Y) 4).1

/-- The literal exact-construction protocol has two actual Alice levels
under the real-density one-copy inputs for `Qᵀ`.  No induced protocol is
pruned, and the raw prefix labels on constraint rows are preserved. -/
theorem actual_bin_separation_of_oneCopy {a d N₁ N₂ n H : ℕ} {h : ℝ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (hd : 0 < d) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hH : 2 ≤ H) (hh : 0 < h)
    (h1 : H ≤ Dfamily (interlaceFun (fun z r => secondMatrix ha C₁ C₂ r z) 1)
      (bracketGE (Fin N₂) (Fin d × Fin N₁) 1 h (3 / 5)))
    (h2 : H - 1 ≤ Dfamily (interlaceFun (fun z r => secondMatrix ha C₁ C₂ r z) 1)
      (bracketGE (Fin N₂) (Fin d × Fin N₁) 1 h ((3 / 5) / 2)))
    (hgap : 4 * densityThreshold N₂ h < N₂)
    (P : Protocol (Rows N₂ n) (Columns d N₁) Bool)
    (hcost : P.cost ≤ H + 2)
    (hcomp : P.Computes (matrix ha C₁ C₂ v cap)) :
    ActualPrefix.AllAlice 2 P ∧
      NoWasteConclusion (Finset.univ : Finset (Fin 4)) Finset.univ
        (fun r => Protocol.prefixCodeRaw 2 P (.inl r)) N₂ (densityThreshold N₂ h) := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  letI : Nonempty (Fin N₁) := ⟨⟨0, hN₁⟩⟩
  letI : Nonempty (Fin N₂) := ⟨⟨0, hN₂⟩⟩
  let φ : Fin 4 × Fin N₂ → Rows N₂ n := Sum.inl
  let ψ : Selectors d N₁ → Columns d N₁ := fun c => (fun _ => false, c)
  let P' := Protocol.pullback φ ψ P
  have hcomp' : P'.Computes (interlaceFun (fun z r => secondMatrix ha C₁ C₂ r z) 4) := by
    intro r c
    simpa only [P', Protocol.pullback_eval] using hcomp (φ r) (ψ c)
  obtain ⟨hrow, hnw, hcodes⟩ := four_bin_separation_of_oneCopy
    (fun z r => secondMatrix ha C₁ C₂ r z) hH hh h1 h2
    (by simpa only [Fintype.card_fin] using hgap) P'
    (by simpa only [P', Protocol.pullback_cost] using hcost) hcomp'
  refine ⟨ActualPrefix.allAlice_of_pullback_codes φ ψ Finset.univ Finset.univ
    2 P hrow Finset.univ_nonempty hcodes, ?_⟩
  have hlabels : Protocol.prefixCodeRaw 2 P' =
      fun r => Protocol.prefixCodeRaw 2 P (.inl r) :=
    funext fun r => Protocol.prefixCodeRaw_pullback φ ψ 2 P r
  rw [hlabels] at hnw
  simpa only [Fintype.card_fin] using hnw

/-- Separation on the template pullback controls the original, unpruned
protocol, not merely an induced protocol on a restriction. -/
theorem actual_bin_separation {a d N₁ N₂ n b : ℕ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (hd : 0 < d) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (hrobust : IsRobustAt (fun z r => secondMatrix ha C₁ C₂ r z) b)
    (hgap : 4 * threshold N₂ b < N₂)
    (P : Protocol (Rows N₂ n) (Columns d N₁) Bool)
    (hcost : P.cost ≤ D (fun z r => secondMatrix ha C₁ C₂ r z) + 2)
    (hcomp : P.Computes (matrix ha C₁ C₂ v cap)) :
    ActualPrefix.AllAlice 2 P ∧
      NoWasteConclusion (Finset.univ : Finset (Fin 4)) Finset.univ
        (fun r => Protocol.prefixCodeRaw 2 P (.inl r)) N₂ (threshold N₂ b) := by
  classical
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  letI : Nonempty (Fin N₁) := ⟨⟨0, hN₁⟩⟩
  letI : Nonempty (Fin N₂) := ⟨⟨0, hN₂⟩⟩
  let φ : Fin 4 × Fin N₂ → Rows N₂ n := Sum.inl
  let ψ : Selectors d N₁ → Columns d N₁ := fun c => (fun _ => false, c)
  let P' := Protocol.pullback φ ψ P
  have hcost' : P'.cost ≤ D (fun z r => secondMatrix ha C₁ C₂ r z) + 2 := by
    simpa only [P', Protocol.pullback_cost] using hcost
  have hcomp' : ∀ r ∈ (Finset.univ : Finset (Fin 4 × Fin N₂)),
      ∀ c ∈ (Finset.univ : Finset (Selectors d N₁)),
        P'.eval r c = interlaceFun (fun z r => secondMatrix ha C₁ C₂ r z) 4 r c := by
    intro r _ c _
    simpa only [P', Protocol.pullback_eval] using hcomp (φ r) (ψ c)
  have hgap' : 2 ^ 2 *
      ⌈(Fintype.card (Fin N₂) : ℝ) * (2 : ℝ) ^ (1 - (b : ℝ))⌉₊ <
      ⌈(Fintype.card (Fin N₂) : ℝ) * 1⌉₊ := by
    simpa [threshold] using hgap
  obtain ⟨hrow, hnw, hcodes⟩ := ProtocolSeparation.classicalSeparationOn
    hrobust (by decide : 1 ≤ (2 : ℕ)) (le_refl (1 : ℝ))
    (by norm_num : (18 / 25 : ℝ) ≤ 1) hgap'
    Finset.univ Finset.univ (bracketGE.self_mem 4) P' hcost' hcomp'
  refine ⟨ActualPrefix.allAlice_of_pullback_codes φ ψ Finset.univ Finset.univ
    2 P hrow (Finset.univ_nonempty) hcodes, ?_⟩
  have hlabels : Protocol.prefixCodeRaw 2 P' =
      fun r => Protocol.prefixCodeRaw 2 P (.inl r) :=
    funext fun r => Protocol.prefixCodeRaw_pullback φ ψ 2 P r
  rw [hlabels] at hnw
  simpa only [Fintype.card_fin, mul_one, Nat.ceil_natCast, threshold] using hnw

/-- The retained labels in a specific template bin on an actual prefix. -/
def templateLabels {d N₁ N₂ n : ℕ}
    (P : Protocol (Rows N₂ n) (Columns d N₁) Bool)
    (j : Fin 4) (p : Fin 4) : Finset (Fin N₂) :=
  Finset.univ.filter (fun z => Protocol.prefixCodeRaw 2 P (.inl (p, z)) = j)

theorem templateLabels_card {d N₁ N₂ n : ℕ}
    (P : Protocol (Rows N₂ n) (Columns d N₁) Bool) (j p : Fin 4) :
    ((Finset.univ : Finset (Fin 4 × Fin N₂)).filter
      (fun r => Protocol.prefixCodeRaw 2 P (.inl r) = j ∧ r.1 = p)).card =
      (templateLabels P j p).card := by
  classical
  have heq : (Finset.univ : Finset (Fin 4 × Fin N₂)).filter
      (fun r => Protocol.prefixCodeRaw 2 P (.inl r) = j ∧ r.1 = p) =
      ({p} : Finset (Fin 4)) ×ˢ templateLabels P j p := by
    ext ⟨q, z⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, Finset.mem_singleton, templateLabels]
    constructor
    · rintro ⟨hr, hp⟩
      exact ⟨hp, by simpa only [hp] using hr⟩
    · rintro ⟨hp, hr⟩
      exact ⟨by simpa only [hp] using hr, hp⟩
  rw [heq, Finset.card_product, Finset.card_singleton, one_mul]

/-- The dominant block counts at the literal real-density threshold. -/
theorem dominant_template_bin_at_density {d N₁ N₂ n : ℕ} {h : ℝ}
    (P : Protocol (Rows N₂ n) (Columns d N₁) Bool)
    (hnw : NoWasteConclusion (Finset.univ : Finset (Fin 4)) Finset.univ
      (fun r => Protocol.prefixCodeRaw 2 P (.inl r)) N₂ (densityThreshold N₂ h))
    (j : Fin 4) :
    ∃! p : Fin 4, N₂ - 3 * densityThreshold N₂ h ≤ (templateLabels P j p).card ∧
      ∀ p' : Fin 4, p' ≠ p → (templateLabels P j p').card < densityThreshold N₂ h := by
  simpa only [NoWasteConclusion, Finset.mem_univ, true_and, Finset.card_univ,
    Fintype.card_fin, show 4 - 1 = (3 : ℕ) from rfl,
    templateLabels_card, forall_true_left] using hnw j

/-- The manuscript's `(1 - 8h)N₂` count follows using the exact ceiling
loss gate, on the same original row labels selected by the actual prefix. -/
theorem dominant_template_bin_density {d N₁ N₂ n : ℕ} {h : ℝ}
    (P : Protocol (Rows N₂ n) (Columns d N₁) Bool)
    (hgap : 4 * densityThreshold N₂ h < N₂)
    (hloss : (3 : ℝ) * densityThreshold N₂ h ≤ 8 * h * N₂)
    (hnw : NoWasteConclusion (Finset.univ : Finset (Fin 4)) Finset.univ
      (fun r => Protocol.prefixCodeRaw 2 P (.inl r)) N₂ (densityThreshold N₂ h))
    (j : Fin 4) :
    ∃ p : Fin 4,
      N₂ - 3 * densityThreshold N₂ h ≤ (templateLabels P j p).card ∧
      (1 - 8 * h) * N₂ ≤ ((templateLabels P j p).card : ℝ) ∧
      (templateLabels P j p).Nonempty ∧
      ∀ p' : Fin 4, p' ≠ p → (templateLabels P j p').card < densityThreshold N₂ h := by
  obtain ⟨p, hp, _⟩ := dominant_template_bin_at_density P hnw j
  refine ⟨p, hp.1, ?_, Finset.card_pos.mp (by omega), hp.2⟩
  have hcard : ((N₂ - 3 * densityThreshold N₂ h : ℕ) : ℝ) ≤
      ((templateLabels P j p).card : ℝ) := by exact_mod_cast hp.1
  rw [Nat.cast_sub (by omega : 3 * densityThreshold N₂ h ≤ N₂),
    Nat.cast_mul, Nat.cast_ofNat] at hcard
  nlinarith

/-- Every actual two-bit branch has a unique dominant template bin. Its
surviving labels are exactly the raw-prefix filter, with no relabelling or
duplicate collapse. -/
theorem dominant_template_bin {d N₁ N₂ n b : ℕ}
    (P : Protocol (Rows N₂ n) (Columns d N₁) Bool)
    (hnw : NoWasteConclusion (Finset.univ : Finset (Fin 4)) Finset.univ
      (fun r => Protocol.prefixCodeRaw 2 P (.inl r)) N₂ (threshold N₂ b))
    (j : Fin 4) :
    ∃! p : Fin 4, N₂ - 3 * threshold N₂ b ≤ (templateLabels P j p).card ∧
      ∀ p' : Fin 4, p' ≠ p → (templateLabels P j p').card < threshold N₂ b := by
  simpa only [NoWasteConclusion, Finset.mem_univ, true_and, Finset.card_univ,
    Fintype.card_fin, show 4 - 1 = (3 : ℕ) from rfl,
    templateLabels_card, forall_true_left] using hnw j

/-- Each raw prefix has a genuinely nonempty retained template block. -/
theorem dominant_template_bin_nonempty {d N₁ N₂ n b : ℕ}
    (P : Protocol (Rows N₂ n) (Columns d N₁) Bool)
    (hgap : 4 * threshold N₂ b < N₂)
    (hnw : NoWasteConclusion (Finset.univ : Finset (Fin 4)) Finset.univ
      (fun r => Protocol.prefixCodeRaw 2 P (.inl r)) N₂ (threshold N₂ b))
    (j : Fin 4) :
    ∃ p : Fin 4, N₂ - 3 * threshold N₂ b ≤ (templateLabels P j p).card ∧
      (templateLabels P j p).Nonempty := by
  obtain ⟨p, hp, _⟩ := dominant_template_bin P hnw j
  refine ⟨p, hp.1, Finset.card_pos.mp ?_⟩
  omega

/-- The actual suffix retains every vector row that chose this prefix and
all columns, with precisely the unspent two-bit budget. -/
theorem actual_bin_suffix {a d N₁ N₂ n B : ℕ}
    (ha : 2 ≤ a) (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (P : Protocol (Rows N₂ n) (Columns d N₁) Bool)
    (hall : ActualPrefix.AllAlice 2 P) (hcost : P.cost ≤ B + 2)
    (hcomp : P.Computes (matrix ha C₁ C₂ v cap)) (j : Fin 4) :
    (Protocol.rowSubtreeAtRaw 2 P j).cost ≤ B ∧
      ∀ r, Protocol.prefixCodeRaw 2 P r = j → ∀ c,
        (Protocol.rowSubtreeAtRaw 2 P j).eval r c = matrix ha C₁ C₂ v cap r c := by
  constructor
  · have hh := hall.subtree_cost j
    omega
  · intro r hr c
    rw [← hr, hall.subtree_eval]
    exact hcomp r c

end EthInapproximability.CurrentPaper.ExactBinControl
