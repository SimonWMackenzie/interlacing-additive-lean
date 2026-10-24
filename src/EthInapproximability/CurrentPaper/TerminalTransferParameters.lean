import EthInapproximability.CurrentPaper.TerminalTransfer
import EthInapproximability.CurrentPaper.ConcreteRouting
import EthInapproximability.CurrentPaper.AmplificationSecondGates
import EthInapproximability.CurrentPaper.ProtectedDeletionGates
import EthInapproximability.CurrentPaper.ConcreteReferenceErrors

/-!
# Accepted parameters for transfers between assigned terminals

Source: frozen v8 `A-stage4-details.tex`, `clm:paper-global-transfer`,
and the two-copy checks in `F-parameter-choices.tex`.
The literal sampler's balance, stopping bounds and physical-bin margins are
conclusions here. They are not certificates of terminal communication cost.
-/

noncomputable section
open scoped Classical BigOperators

namespace EthInapproximability.CurrentPaper.TerminalTransferParameters

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace
open Parameters ParameterGates Construction JointTransfer TerminalOuterBound
open ConcreteRouting TerminalTransfer
open ParameterizedNP.WrapperProjectionCovers ParameterizedNP.TerminalStateRealization

def pairLevel (i : Input) : ℕ := secondExponent i - balanceExponent i + 1

def lambda (i : Input) : ℚ :=
  2 * secondWidth i * (2 : ℚ) ^ (-(firstDepth i : ℤ))

theorem pairLevel_sum (i : Input) (hc : 0 < i.sourceConstant) (ha : Accepted i) :
    pairLevel i + balanceExponent i = secondExponent i + 1 := by
  have h := accepted_balance_exponent_le i hc ha
  unfold pairLevel
  omega

theorem pairLevel_width (i : Input) (hc : 0 < i.sourceConstant) (ha : Accepted i) :
    secondWidth i = 2 ^ pairLevel i * 2 ^ (balanceExponent i - 1) := by
  have h := pairLevel_sum i hc ha
  have hm := AmplificationSecondGates.balanceExponent_floor i
  rw [← pow_add]
  unfold secondWidth
  congr 1
  omega

theorem lambda_cast (i : Input) (hc : 0 < i.sourceConstant) (ha : Accepted i) :
    (lambda i : ℝ) = (2 : ℝ) ^ pairLevel i *
      ((2 : ℝ) ^ balanceExponent i * (2 : ℝ) ^ (-(firstDepth i : ℝ))) := by
  rw [← mul_assoc, ← pow_add, pairLevel_sum i hc ha, pow_succ]
  simp only [lambda, Rat.cast_mul, Rat.cast_ofNat,
    zpow_neg, zpow_natCast, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_natCast, secondWidth, Nat.cast_pow, Nat.cast_ofNat]
  push_cast
  ring

theorem error_small (i : Input) :
    2 * (1 / (100 * (balanceOrder i : ℝ))) +
      (1 / (100 * (balanceOrder i : ℝ))) ^ 2 ≤ 1 / 50 := by
  have hm := AmplificationSecondGates.balanceExponent_floor i
  have htN : 2 ≤ balanceOrder i := by
    change 2 ^ 1 ≤ 2 ^ balanceExponent i
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have ht : (2 : ℝ) ≤ balanceOrder i := by exact_mod_cast htN
  have hε0 : 0 ≤ 1 / (100 * (balanceOrder i : ℝ)) := by positivity
  have hε : 1 / (100 * (balanceOrder i : ℝ)) ≤ 1 / 200 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  nlinarith [sq_nonneg (1 / 200 - 1 / (100 * (balanceOrder i : ℝ)))]

/-- All non-profile fields of the physical terminal theorem follow from
the two acceptance tests and the fixed first-matrix cost. -/
theorem actual_pair_inputs (i : Input) (hc : 0 < i.sourceConstant) (ha : Accepted i)
    {Y : Type} [Fintype Y] [Nonempty Y] (R : Fin i.rows → Y → Bool)
    (h1 : i.cost + firstExponent i ≤ Dfamily
      (interlaceFun (Function.swap (firstMatrix R (firstExponent i) (bins i))) 1)
      (bracketGE (FirstColumns (firstExponent i) (bins i) Y)
        (FirstRows (firstExponent i) (Fin i.rows)) 1
        ((2 : ℝ) ^ (-(firstDepth i : ℝ))) (3 / 5)))
    (h2 : i.cost + firstExponent i - 1 ≤ Dfamily
      (interlaceFun (Function.swap (firstMatrix R (firstExponent i) (bins i))) 1)
      (bracketGE (FirstColumns (firstExponent i) (bins i) Y)
        (FirstRows (firstExponent i) (Fin i.rows)) 1
        ((2 : ℝ) ^ (-(firstDepth i : ℝ))) (3 / 10))) :
    PairInputs (Function.swap (firstMatrix R (firstExponent i) (bins i)))
      (actualFamily i ha) (i.cost + firstExponent i) (balanceExponent i) (pairLevel i)
      ((2 : ℝ) ^ (-(firstDepth i : ℝ))) (1 / (100 * (balanceOrder i : ℝ))) 0 1 := by
  letI : Nonempty (Fin i.rows) := Fin.pos_iff_nonempty.mp (by have := ha.1; omega)
  letI : Nonempty (Fin (qOne (firstExponent i))) :=
    Fin.pos_iff_nonempty.mp (firstWidth_pos i)
  have hm := AmplificationSecondGates.balanceExponent_floor i
  have hcost : 2 ≤ i.cost + firstExponent i := by
    have h := (hard_seed_exponent_domains i).2.2.1
    omega
  have hg := two_copy_stopping_gates i
  have hsmall : (2 : ℝ) ^ pairLevel i *
      ((2 : ℝ) ^ balanceExponent i * (2 : ℝ) ^ (-(firstDepth i : ℝ))) < 1 := by
    rw [← mul_assoc, ← pow_add, pairLevel_sum i hc ha, pow_succ]
    have h := inner_pair_loss i
    simp only [secondWidth, Nat.cast_pow, Nat.cast_ofNat] at h
    nlinarith
  refine ⟨secondWidth_pos i, pairLevel_width i hc ha, hcost, hm,
    by positivity, ?_, by positivity, error_small i, h1, h2,
    balanced_change_decidable (actualSecondFamily_balanced i hc ha), ?_, ?_, hsmall,
    by simpa using hsmall⟩
  · simpa only [balanceOrder, Nat.cast_pow, Nat.cast_ofNat] using sampling_row_request i
  · simpa only [yLoss, pairLevel_sum i hc ha, balanceOrder,
      Nat.cast_pow, Nat.cast_ofNat] using hg.1
  · simpa only [balanceOrder, Nat.cast_pow, Nat.cast_ofNat] using hg.2

theorem selector_fraction_small (i : Input) (ha : Accepted i) :
    (2 : ℝ) ^ (binExponent i + 1) * (2 : ℝ) ^ (-(secondDepth i : ℝ)) ≤ 1 / 100 := by
  have hs := bins_pos i
  have hf := firstWidth_pos i
  have hn : 1 ≤ firstWidth i * i.rows := by have := ha.1; nlinarith
  have hpN : 2048 * bins i ≤ 2 ^ secondDepth i := by
    have h := outer_secondDepth_power i
    nlinarith
  have hp : 2048 * (bins i : ℝ) ≤ (2 : ℝ) ^ secondDepth i := by exact_mod_cast hpN
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast,
    ← div_eq_mul_inv, div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ secondDepth i)]
  simp only [pow_succ]
  have hbins : (bins i : ℝ) = (2 : ℝ) ^ binExponent i := by simp only [bins, Nat.cast_pow, Nat.cast_ofNat]
  rw [← hbins]
  nlinarith

/-- The actual physical template proportion gives the two-coordinate margin. -/
theorem actual_pair_margin (i : Input) (ha : Accepted i) (nv nb : ℕ)
    (hv : 0 < nv) (hb : 0 < nb)
    (hraw : 1000 * ((nv + nb) * i.rows) ≤ bins i * labelCount i)
    (hL : 0 < labelCount i) :
    (49 / 64 : ℝ) ≤
      (aMin (99 / 100) (templateDensity
        (templateBin (X := Fin i.rows) (bins i) (labelCount i) nv nb)) -
        (2 : ℝ) ^ (binExponent i + 1) * (2 : ℝ) ^ (-(secondDepth i : ℝ))) /
          (1 + 1 / (100 * (balanceOrder i : ℝ))) ^ 2 := by
  letI : Nonempty (Fin i.rows) := Fin.pos_iff_nonempty.mp (by have := ha.1; omega)
  have hC : 0 < Fintype.card (ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)) := by
    have hl := template_labels_pos (X := Fin i.rows) (bins i) (labelCount i) nv nb
      (bins_pos i) hL hv hb
    have hle := Finset.card_le_univ
      (templateBin (X := Fin i.rows) (bins i) (labelCount i) nv nb ⟨0, bins_pos i⟩)
    rw [template_bin_card] at hle
    exact (Nat.mul_pos hL hl).trans_le hle
  have ht := template_proportion_of_raw_count (Fin i.rows) (bins i) (labelCount i) nv nb
    (bins_pos i) (by simpa only [Fintype.card_fin] using hraw)
  have hlam : (99 / 100 : ℝ) ≤ templateDensity
      (templateBin (X := Fin i.rows) (bins i) (labelCount i) nv nb) := by
    unfold templateDensity
    exact (le_div_iff₀ (by exact_mod_cast hC)).mpr ht
  have herr : (1 : ℝ) / (100 * (balanceOrder i : ℝ)) ≤ 1 / 100 := by
    apply one_div_le_one_div_of_le (by norm_num)
    have h := balanceOrder_pos i
    have ht : (1 : ℝ) ≤ balanceOrder i := by exact_mod_cast h
    linarith
  exact (two_copy_retained_quotient
    (pair_completion_fraction (le_refl (99 / 100 : ℝ)) hlam)
    (selector_fraction_small i ha) (by positivity) herr).2.le

theorem singleton_projection_card {Z : Type*} [Fintype Z] [DecidableEq Z] {q : ℕ}
    (S : Finset (Fin q → Z)) (j : Fin q) :
    (S.image (fun f => f j)).card = (ProductExtraction.projection {j} S).card := by
  let ev : (({j} : Finset (Fin q)) → Z) → Z := fun f => f ⟨j, by simp⟩
  have hinj : Function.Injective ev := by
    intro f g h
    funext a
    have ha : a = ⟨j, by simp⟩ := Subtype.ext (Finset.mem_singleton.mp a.property)
    simpa only [ha] using h
  have heq : S.image (fun f => f j) = (ProductExtraction.projection {j} S).image ev := by
    simp only [ProductExtraction.projection, Finset.image_image, Function.comp_def, ev]
  rw [heq, Finset.card_image_of_injective _ hinj]

theorem pair_projection_card {Z : Type*} [Fintype Z] [DecidableEq Z] {q : ℕ}
    (S : Finset (Fin q → Z)) (j k : Fin q) :
    (jointPairs S j k).card = (ProductExtraction.projection {j, k} S).card := by
  let ev : (({j, k} : Finset (Fin q)) → Z) → Z × Z :=
    fun f => (f ⟨j, by simp⟩, f ⟨k, by simp⟩)
  have hinj : Function.Injective ev := by
    intro f g h
    funext a
    rcases Finset.mem_insert.mp a.property with haj | hak
    · have heq : a = ⟨j, by simp⟩ := Subtype.ext haj
      simpa only [heq] using congrArg Prod.fst h
    · have heq : a = ⟨k, by simp⟩ := Subtype.ext (Finset.mem_singleton.mp hak)
      simpa only [heq] using congrArg Prod.snd h
  have heq : jointPairs S j k = (ProductExtraction.projection {j, k} S).image ev := by
    simp only [jointPairs, ProductExtraction.projection, Finset.image_image, Function.comp_def, ev]
  rw [heq, Finset.card_image_of_injective _ hinj]

/-- Even the extra-template copy alone makes the ordinary-bin budget
automatic under a source constant far weaker than the paper's choice. -/
theorem actual_bin_counts (i : Input) (ha : Accepted i)
    (hlarge : 2 ^ 24 ≤ i.sourceConstant) (nv nb : ℕ)
    (S : Finset (RoutingCol i nv nb)) (j : Fin (outerWidth i))
    (hsingle : (1 - (columnTolerance i : ℝ)) *
      Fintype.card (ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)) ≤
        (ProductExtraction.projection {j} S).card) :
    ∀ p : Fin (bins i), (2 : ℝ) ^ (binExponent i + 1) *
      (2 : ℝ) ^ (-(secondDepth i : ℝ)) *
        (templateBin (X := Fin i.rows) (bins i) (labelCount i) nv nb p).card ≤
      (((S.image (fun y => y j)) ∩ templateBin (bins i) (labelCount i) nv nb p).card : ℝ) := by
  intro p
  have hc : (0 : ℝ) < i.sourceConstant := by exact_mod_cast (by norm_num at hlarge; omega : 0 < i.sourceConstant)
  have hs : (0 : ℝ) < bins i := by exact_mod_cast bins_pos i
  have hlargeR : (2 : ℝ) ^ 24 ≤ i.sourceConstant := by exact_mod_cast hlarge
  have hη : (columnTolerance i : ℝ) = 2 / ((i.sourceConstant : ℝ) * bins i) := by
    simp only [columnTolerance, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast,
      Rat.cast_mul, Nat.cast_mul]
  have hη0 : (0 : ℝ) ≤ columnTolerance i := by rw [hη]; positivity
  have hbudget : (columnTolerance i : ℝ) * (2 ^ 21 * (bins i : ℝ)) ≤ 1 / 4 := by
    rw [hη]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (mul_pos hc hs)).mpr
    have hmul := mul_le_mul_of_nonneg_right hlargeR hs.le
    norm_num at hlargeR ⊢
    norm_num only [show (2 : ℝ) ^ (24 : ℕ) = 16777216 by norm_num] at hmul
    nlinarith
  have hC : (Fintype.card (ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)) : ℝ) ≤
      2 ^ 21 * (bins i : ℝ) * (templateBin (X := Fin i.rows) (bins i) (labelCount i) nv nb p).card := by
    exact_mod_cast ProtectedDeletionGates.template_bin_mass_bound (X := Fin i.rows)
      (bins i) (labelCount i) nv nb p
  have hdel := mul_le_mul_of_nonneg_left hC hη0
  have hmul := mul_le_mul_of_nonneg_right hbudget
    (Nat.cast_nonneg (templateBin (X := Fin i.rows) (bins i) (labelCount i) nv nb p).card)
  have hτ := mul_le_mul_of_nonneg_right (selector_fraction_small i ha)
    (Nat.cast_nonneg (templateBin (X := Fin i.rows) (bins i) (labelCount i) nv nb p).card)
  apply bin_count_from_singleton S j _
    (by rw [singleton_projection_card]; exact hsingle)
  nlinarith

theorem lambda_nonneg (i : Input) : 0 ≤ lambda i := by unfold lambda; positivity

/-- The explicit first-depth margin pays all destinations simultaneously. -/
theorem lambda_sum_gate (i : Input) (hc : 0 < i.sourceConstant) :
    2 * (1 / 184 : ℚ) * outerWidth i * lambda i ≤ rowTolerance i / 16 := by
  have hs := bins_pos i
  have hq := outerWidth_pos i
  have ht := balanceOrder_pos i
  have hpow := inner_integer_margin i
  have hq5 : outerWidth i ≤ outerWidth i ^ 5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hq (by decide : 1 ≤ 5)
  have ht20 : 1 ≤ balanceOrder i ^ 20 := one_le_pow₀ ht
  have hsmall : 2 ^ 100 * i.sourceConstant * bins i * secondWidth i * outerWidth i ≤
      2 ^ firstDepth i := by
    apply le_trans ?_ hpow
    calc
      _ ≤ 2 ^ 100 * i.sourceConstant * bins i * secondWidth i * outerWidth i ^ 5 := by gcongr
      _ ≤ _ := Nat.le_mul_of_pos_right _ ht20
  have hm : (2 : ℚ) ^ 100 * i.sourceConstant * bins i * secondWidth i * outerWidth i ≤
      (2 : ℚ) ^ firstDepth i := by exact_mod_cast hsmall
  have hcQ : (0 : ℚ) < i.sourceConstant := by exact_mod_cast hc
  have hsQ : (0 : ℚ) < bins i := by exact_mod_cast hs
  have hpowQ : (0 : ℚ) < 2 ^ firstDepth i := by positivity
  unfold lambda rowTolerance
  simp only [zpow_neg, zpow_natCast, Nat.cast_mul]
  apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 16)).mpr
  apply (le_div_iff₀ (mul_pos hcQ hsQ)).mpr
  apply (mul_le_mul_iff_right₀ hpowQ).mp
  field_simp
  norm_num at hm ⊢
  nlinarith [show (0 : ℚ) ≤ i.sourceConstant * bins i * secondWidth i * outerWidth i by positivity]

theorem reference_slice_card {Z Node : Type*} [Fintype Z] [DecidableEq Z]
    [DecidableEq Node] {q : ℕ} (A : Finset (Fin q × Z)) (ref : Finset Z)
    (dest : Fin q × Z → Node) (owner : Fin q → Node) (j : Fin q) :
    (slice A dest (owner j) j ref).card =
      (ConcreteReferenceErrors.terminalReference A ref dest owner j).card := by
  have heq : (slice A dest (owner j) j ref).image (fun z => (j, z)) =
      ConcreteReferenceErrors.terminalReference A ref dest owner j := by
    ext z
    simp only [slice, RoutedClosure.rowsAt, ConcreteReferenceErrors.terminalReference,
      ConcreteGlobalClosure.retainedReference, ConcreteGlobalClosure.referenceBlock,
      Finset.mem_image, Finset.mem_filter, Finset.mem_inter, Finset.mem_product,
      Finset.mem_singleton]
    constructor
    · rintro ⟨w, ⟨hw, hA, hd⟩, rfl⟩
      exact ⟨⟨hA, rfl, hw⟩, hd⟩
    · rintro ⟨⟨hA, hj, hr⟩, hd⟩
      have hz : (j, z.2) = z := Prod.ext hj.symm rfl
      refine ⟨z.2, ⟨hr, ?_, ?_⟩, hz⟩ <;> simpa only [hz]
  rw [← heq, Finset.card_image_of_injective _ (by intro x y h; exact (Prod.mk.inj h).2)]

theorem epsilon_reference_fraction {Z Node : Type*} [Fintype Z] [DecidableEq Z]
    [DecidableEq Node] {q : ℕ} (A : Finset (Fin q × Z)) (ref : Finset Z)
    (href : 0 < ref.card) (dest : Fin q × Z → Node) (owner : Fin q → Node) (j : Fin q) :
    1 - (ConcreteReferenceErrors.epsilon A ref dest owner j : ℝ) =
      (slice A dest (owner j) j ref).card / (ref.card : ℝ) := by
  have h := ConcreteReferenceErrors.epsilon_eq_one_sub A ref href dest owner j
  rw [reference_slice_card]
  have hr : (ConcreteReferenceErrors.epsilon A ref dest owner j : ℝ) =
      1 - (ConcreteReferenceErrors.terminalReference A ref dest owner j).card /
        (ref.card : ℝ) := by
    have hh := congrArg (fun x : ℚ => (x : ℝ)) h
    simpa only [Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_natCast] using hh
  linarith

theorem epsilon_small {Z Node : Type*} [Fintype Z] [DecidableEq Z]
    [DecidableEq Node] (i : Input) (hc : 0 < i.sourceConstant)
    (A : Finset (Fin (outerWidth i) × Z)) (ref : Finset Z)
    (dest : Fin (outerWidth i) × Z → Node) (owner : Fin (outerWidth i) → Node)
    (J : Finset (Fin (outerWidth i))) (j : Fin (outerWidth i)) (hj : j ∈ J)
    (hsum : (∑ k ∈ J, ConcreteReferenceErrors.epsilon A ref dest owner k) ≤
      rowTolerance i / (8 * (91 / 92))) :
    (ConcreteReferenceErrors.epsilon A ref dest owner j : ℝ) ≤ 1 / 5 := by
  have hle : ConcreteReferenceErrors.epsilon A ref dest owner j ≤
      ∑ k ∈ J, ConcreteReferenceErrors.epsilon A ref dest owner k :=
    Finset.single_le_sum (fun k _ => ConcreteReferenceErrors.epsilon_nonneg A ref dest owner k) hj
  have hcQ : (1 : ℚ) ≤ i.sourceConstant := by exact_mod_cast hc
  have hsQ : (1 : ℚ) ≤ bins i := by exact_mod_cast bins_pos i
  have hcs : (1 : ℚ) ≤ (i.sourceConstant : ℚ) * bins i := by nlinarith
  have hη : rowTolerance i ≤ 1 := by
    unfold rowTolerance
    rw [Nat.cast_mul]
    exact (div_le_one (by linarith)).mpr hcs
  have hfinal : ConcreteReferenceErrors.epsilon A ref dest owner j ≤ 1 / 5 := by
    have he := hle.trans hsum
    have ht := div_le_div_of_nonneg_right hη (by norm_num : (0 : ℚ) ≤ 8 * (91 / 92))
    exact he.trans (ht.trans (by norm_num))
  have hh := (Rat.cast_le (K := ℝ)).2 hfinal
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
  exact hh

open Workspace.Types.Protocol
open ParameterizedNP.RoutedCertificateConstruction

/-- The per-destination theorem on the literal accepted construction. The
remaining profile inputs are exactly the two first- and two second-matrix
one-copy profiles. No terminal hardness, sampler, margin or bin premise remains. -/
theorem parameters_terminal_transfer
    (i : Input) (hc : 0 < i.sourceConstant) (ha : Accepted i)
    (hlarge : 2 ^ 24 ≤ i.sourceConstant)
    {Y : Type} [Fintype Y] [Nonempty Y] (R : Fin i.rows → Y → Bool)
    (nv nb : ℕ) (hv : 0 < nv) (hb : 0 < nb)
    (hraw : 1000 * ((nv + nb) * i.rows) ≤ bins i * labelCount i)
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin (secondWidth i) → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ bins i)
    (h1 : i.cost + firstExponent i ≤ Dfamily
      (interlaceFun (Function.swap (firstMatrix R (firstExponent i) (bins i))) 1)
      (bracketGE (FirstColumns (firstExponent i) (bins i) Y)
        (FirstRows (firstExponent i) (Fin i.rows)) 1
        ((2 : ℝ) ^ (-(firstDepth i : ℝ))) (3 / 5)))
    (h2 : i.cost + firstExponent i - 1 ≤ Dfamily
      (interlaceFun (Function.swap (firstMatrix R (firstExponent i) (bins i))) 1)
      (bracketGE (FirstColumns (firstExponent i) (bins i) Y)
        (FirstRows (firstExponent i) (Fin i.rows)) 1
        ((2 : ℝ) ^ (-(firstDepth i : ℝ))) (3 / 10)))
    (hsecond : i.cost + firstExponent i + secondExponent i ≤ Dfamily
      (interlaceFun (Function.swap (secondMatrix R (firstExponent i) (bins i)
        (secondWidth i) (labelCount i) (actualFamily i ha))) 1)
      (bracketGE (Fin (labelCount i)) (SecondRows (firstExponent i) (bins i) (secondWidth i) Y)
        1 ((2 : ℝ) ^ (-(secondDepth i : ℝ))) (3 / 5)))
    (hsecondHalf : i.cost + firstExponent i + secondExponent i - 1 ≤ Dfamily
      (interlaceFun (Function.swap (secondMatrix R (firstExponent i) (bins i)
        (secondWidth i) (labelCount i) (actualFamily i ha))) 1)
      (bracketGE (Fin (labelCount i)) (SecondRows (firstExponent i) (bins i) (secondWidth i) Y)
        1 ((2 : ℝ) ^ (-(secondDepth i : ℝ))) (3 / 10)))
    (P : Protocol (RoutingRow i Y) (RoutingCol i nv nb) Bool)
    (A : Finset (RoutingRow i Y)) (S : Finset (RoutingCol i nv nb))
    (hP : ∀ z ∈ A, ∀ y ∈ S, P.eval z y = routingGame i ha R nv nb order vectors cap z y)
    (hcost : P.cost ≤ certificateCost i + outerExponent i - 1)
    (owner : Fin (outerWidth i) → List Bool) (J : Finset (Fin (outerWidth i)))
    (j k : Fin (outerWidth i)) (_hjk : j ≠ k) (hk : k ∈ J)
    (hp : owner k ∈ ProtocolFrontier.nodes P (outerExponent i) A)
    (hdepth : (owner k).length = outerExponent i)
    (hsum : (∑ l ∈ J, ConcreteReferenceErrors.epsilon A
      (referenceRows (firstExponent i) (bins i) (secondWidth i))
      (ProtocolFrontier.rowStop (outerExponent i) (completeNoBob (outerExponent i) P)) owner l) ≤
        rowTolerance i / (8 * (91 / 92)))
    (hsingle : (1 - (columnTolerance i : ℝ)) *
      Fintype.card (ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)) ≤
        (ProductExtraction.projection {k} S).card)
    (hpair : (99 / 100 : ℝ) *
      (Fintype.card (ProtectedRows (bins i) (labelCount i) nv nb (Fin i.rows)) : ℝ) ^ 2 ≤
        (ProductExtraction.projection {k, j} S).card) :
    GlobalCount.mass (Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y))
      (RoutedClosure.transferTo
        (A.filter fun z => z.2 ∈ diagonalRows (firstExponent i) (bins i) (secondWidth i))
        Prod.fst (ProtocolFrontier.rowStop (outerExponent i) (completeNoBob (outerExponent i) P))
        owner j k) ≤
      2 * (1 / 184 : ℚ) * (lambda i + ConcreteReferenceErrors.epsilon A
        (referenceRows (firstExponent i) (bins i) (secondWidth i))
        (ProtocolFrontier.rowStop (outerExponent i) (completeNoBob (outerExponent i) P)) owner k) := by
  letI : Nonempty (Fin i.rows) := Fin.pos_iff_nonempty.mp (by have := ha.1; omega)
  have hL : 0 < labelCount i := lt_of_lt_of_le (by
    exact Nat.mul_pos (firstWidth_pos i) (by have := ha.1; omega))
    (actualFamily_size_ge_alphabet i hc ha)
  have hM : 0 < Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y) := by
    have hr := ConcreteGlobalClosure.physicalReferenceCount_pos i Y
    exact hr.trans_le (Finset.card_le_univ _)
  have hD2 : 2 ≤ i.cost + firstExponent i + secondExponent i := by
    have h := (hard_seed_exponent_domains i).2.2.1
    omega
  apply physical_terminal_transfer R (firstExponent i) (bins i) (secondWidth i)
    (labelCount i) nv nb (outerWidth i) (i.cost + firstExponent i)
    (balanceExponent i) (pairLevel i) (i.cost + firstExponent i + secondExponent i)
    (binExponent i) (outerExponent i) _ (firstWidth_pos i) (bins_pos i) hL hv hb
    (actualFamily i ha) order vectors cap (actual_pair_inputs i hc ha R h1 h2)
    rfl (by have := pairLevel_sum i hc ha; omega) hD2 (by positivity) ?_
    hsecond hsecondHalf A S P hP hcost owner k j hp hdepth (1 / 184) (lambda i) _
    hM (diagonal_normalization _ _ _) (lambda_cast i hc ha)
    (epsilon_small i hc A _ _ owner J k hk hsum) ?_ ?_
    (actual_pair_margin i ha nv nb hv hb hraw hL)
    (actual_bin_counts i ha hlarge nv nb S k hsingle)
  · exact (selector_fraction_small i ha).trans (by norm_num)
  · exact (epsilon_reference_fraction A _ (ConcreteGlobalClosure.physicalReferenceCount_pos i Y)
      _ owner k).le
  · rw [pair_projection_card]
    exact hpair

end EthInapproximability.CurrentPaper.TerminalTransferParameters
