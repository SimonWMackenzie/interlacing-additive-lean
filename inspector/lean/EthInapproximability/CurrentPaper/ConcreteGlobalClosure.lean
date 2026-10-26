import EthInapproximability.CurrentPaper.ConcreteRouting
import EthInapproximability.CurrentPaper.ReferenceAssignment
import EthInapproximability.CurrentPaper.ProtectedDeletionGates

/-!
# Actual coordinates and rows for the full-cost closure

Source: frozen v8 `A-stage4-details.tex`, the full-cost bound, its projection
covers and `clm:paper-global-assignment`--`clm:paper-global-capacity`.

All finite sets here are computed from the retained rectangle. In particular,
the exceptional coordinates are obtained from its actual joint projections.
-/

noncomputable section
open scoped Classical BigOperators

namespace EthInapproximability.CurrentPaper.ConcreteGlobalClosure

open Parameters ParameterGates ConcreteRouting ProductExtraction

attribute [local irreducible] Parameters.scale Parameters.scaleBound

def singletonBudget (i : Input) : ℕ := i.sourceConstant * bins i * (retainedExponent i + 1)
def smallWidth (e : ℕ) : ℕ := 2 ^ (e - 1) + 1

/-- A common finite reference-cover bound, slightly looser than the exact
displayed geometric sum and still far below the chosen outer width. -/
def exceptionalBudget (i : Input) : ℕ :=
  (singletonBudget i - 1) + 2 * (coverBudget i - 1) +
    (coverBudget i - 1) * referenceWidth i

theorem smallWidth_pos (e : ℕ) : 1 ≤ smallWidth e := Nat.le_add_left _ _

theorem smallWidth_le_power (e : ℕ) (he : 1 ≤ e) : smallWidth e ≤ 2 ^ e := by
  have hp : 1 ≤ 2 ^ (e - 1) := Nat.one_le_pow _ _ (by decide)
  calc
    smallWidth e = 2 ^ (e - 1) + 1 := rfl
    _ ≤ 2 ^ (e - 1) * 2 := by omega
    _ = 2 ^ e := by rw [← pow_succ, Nat.sub_add_cancel he]

theorem sum_powers_two (n : ℕ) : (∑ e ∈ Finset.range n, 2 ^ e) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem sum_smallWidths_le (n : ℕ) :
    (∑ e ∈ Finset.Ico 1 n, smallWidth e) ≤ 2 ^ n := by
  calc
    _ ≤ ∑ e ∈ Finset.Ico 1 n, 2 ^ e := Finset.sum_le_sum fun e he =>
      smallWidth_le_power e (Finset.mem_Ico.mp he).1
    _ ≤ ∑ e ∈ Finset.range n, 2 ^ e := Finset.sum_le_sum_of_subset_of_nonneg
      (fun e he => Finset.mem_range.mpr (Finset.mem_Ico.mp he).2) (by intros; exact Nat.zero_le _)
    _ ≤ _ := by have h := sum_powers_two n; omega

theorem singletonBudget_pos (i : Input) (hc : 0 < i.sourceConstant) :
    1 ≤ singletonBudget i := by
  have hs := bins_pos i
  unfold singletonBudget
  exact Nat.mul_pos (Nat.mul_pos hc hs) (Nat.succ_pos _)

theorem singleton_contraction (i : Input) (hc : 0 < i.sourceConstant) :
    0 < (1 - (columnTolerance i : ℚ) : ℝ) ∧
    (1 - (columnTolerance i : ℚ) : ℝ) ≤ 1 ∧
    (1 - (columnTolerance i : ℚ) : ℝ) ^ (i.sourceConstant * bins i) < 1 / 2 := by
  have hs := Nat.le_of_dvd (bins_pos i) (sixtyfour_dvd_bins i)
  have hb : 2 < i.sourceConstant * bins i := by nlinarith
  have hbR : (2 : ℝ) < (i.sourceConstant * bins i : ℕ) := by exact_mod_cast hb
  have heq : ((columnTolerance i : ℚ) : ℝ) = 2 / (i.sourceConstant * bins i : ℕ) := by
    unfold columnTolerance
    push_cast
    rfl
  rw [heq]
  have hfrac : (2 : ℝ) / (i.sourceConstant * bins i : ℕ) < 1 :=
    (div_lt_one (by positivity)).2 hbR
  refine ⟨by linarith, sub_le_self _ (by positivity), ?_⟩
  have hexp := Real.one_sub_div_pow_le_exp_neg hbR.le
  have he : (2 : ℝ) < Real.exp 2 := by
    have h := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)
    linarith
  have hinv : Real.exp (-2) < (1 / 2 : ℝ) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) he
  exact hexp.trans_lt hinv

theorem singleton_cover_gate (i : Input) (hc : 0 < i.sourceConstant) :
    (1 - (columnTolerance i : ℚ) : ℝ) ^ singletonBudget i < (retainedFraction i : ℚ) := by
  have h := singleton_contraction i hc
  have hp : ((1 - (columnTolerance i : ℚ) : ℝ) ^ (i.sourceConstant * bins i)) ^
      (retainedExponent i + 1) < (1 / 2 : ℝ) ^ (retainedExponent i + 1) := by
    gcongr
    · exact pow_nonneg h.1.le _
    · exact h.2.2
  have hhalf : (1 / 2 : ℝ) ^ (retainedExponent i + 1) ≤
      (1 / 2 : ℝ) ^ retainedExponent i := by
    rw [pow_succ]
    nlinarith [show (0 : ℝ) ≤ (1 / 2 : ℝ) ^ retainedExponent i by positivity]
  have hid : (1 / 2 : ℝ) ^ retainedExponent i =
      (2 : ℝ) ^ (-(retainedExponent i : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, one_div, inv_pow]
  unfold singletonBudget
  rw [pow_mul]
  exact hp.trans_le (hhalf.trans (hid ▸ retainedFraction_dyadic_lower i))

theorem reference_cover_gate (i : Input) :
    (18 / 25 : ℝ) ^ coverBudget i < (retainedFraction i : ℚ) := by
  exact (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 18 / 25)
    (by norm_num : (18 / 25 : ℝ) ≤ 99 / 100) _).trans_lt (actual_cover_gate i)

theorem coverBudget_bound (i : Input) : coverBudget i ≤ 2 ^ (scale i + 8) := by
  have h := retainedExponent_power_bound i
  have hp : 1 ≤ 2 ^ scale i := Nat.one_le_pow _ _ (by decide)
  unfold coverBudget
  rw [pow_add]
  norm_num
  omega

theorem singletonBudget_bound (i : Input) : singletonBudget i ≤ 2 ^ (3 * scale i + 1) := by
  have hl := retainedExponent_power_bound i
  have hp : 1 ≤ 2 ^ scale i := Nat.one_le_pow _ _ (by decide)
  calc
    singletonBudget i ≤ 2 ^ scale i * 2 ^ scale i * (2 ^ scale i * 2) := by
      unfold singletonBudget
      gcongr
      · exact (public_bounds i).1
      · exact bins_le_scale_power i
      · omega
    _ = _ := by rw [← pow_succ, ← pow_add, ← pow_add]; congr 1; omega

theorem exceptionalBudget_bound (i : Input) :
    exceptionalBudget i ≤ 2 ^ (referenceExponent i + 3 * scale i + 12) := by
  let K := referenceExponent i + 3 * scale i + 9
  have hs : singletonBudget i ≤ 2 ^ K := (singletonBudget_bound i).trans
    (Nat.pow_le_pow_right (by decide) (by dsimp [K]; omega))
  have hb : 2 * coverBudget i ≤ 2 ^ K := by
    calc
      _ ≤ 2 * 2 ^ (scale i + 8) := Nat.mul_le_mul_left _ (coverBudget_bound i)
      _ = 2 ^ (scale i + 9) := by
        calc
          _ = 2 ^ (scale i + 8) * 2 := Nat.mul_comm _ _
          _ = _ := by simpa only [Nat.add_assoc] using (pow_succ 2 (scale i + 8)).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by dsimp [K]; omega)
  have ht : coverBudget i * referenceWidth i ≤ 2 ^ K := by
    calc
      _ ≤ 2 ^ (scale i + 8) * 2 ^ referenceExponent i :=
        Nat.mul_le_mul_right _ (coverBudget_bound i)
      _ = 2 ^ (scale i + 8 + referenceExponent i) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by dsimp [K]; omega)
  have hsmall : (coverBudget i - 1) * referenceWidth i ≤ coverBudget i * referenceWidth i :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hexp : referenceExponent i + 3 * scale i + 12 = K + 3 := by dsimp [K]
  unfold exceptionalBudget
  rw [hexp, pow_add]
  norm_num
  omega

theorem capacityCoefficient_bound (i : Input) :
    capacityCoefficient i ≤ (2 : ℚ) ^ (3 * scale i + 12) := by
  have hB : (coverBudget i : ℚ) ≤ (2 : ℚ) ^ (scale i + 8) := by
    exact_mod_cast coverBudget_bound i
  have hs : (bins i : ℚ) ≤ (2 : ℚ) ^ scale i := by exact_mod_cast bins_le_scale_power i
  have hr : (outerExponent i + 2 : ℚ) ≤ (2 : ℚ) ^ (scale i + 2) := by
    have hrN := outerExponent_le_scalePower i
    have hp : 1 ≤ 2 ^ scale i := Nat.one_le_pow _ _ (by decide)
    have hh : outerExponent i + 2 ≤ 2 ^ (scale i + 2) := by rw [pow_add]; norm_num; omega
    exact_mod_cast hh
  calc
    capacityCoefficient i ≤ (coverBudget i : ℚ) * (outerExponent i + 2) * bins i := by
      unfold capacityCoefficient
      have hn : (0 : ℚ) ≤ (coverBudget i : ℚ) * (outerExponent i + 2) * bins i := by positivity
      nlinarith
    _ ≤ (2 : ℚ) ^ (scale i + 8) * 2 ^ (scale i + 2) * 2 ^ scale i := by gcongr
    _ = (2 : ℚ) ^ (3 * scale i + 10) := by rw [← pow_add, ← pow_add]; congr 1; omega
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)

theorem aggregate_capacity_gate (i : Input) (hc : 0 < i.sourceConstant) :
    (1 + 4 * capacityCoefficient i / rowTolerance i) *
      ((exceptionalBudget i : ℚ) / (1 - (9 / 16 : ℚ))) < (outerWidth i : ℚ) := by
  have hs := bins_pos i
  have hη := rowTolerance_pos i hc
  have hinv : 1 / rowTolerance i ≤ (2 : ℚ) ^ (2 * scale i) := by
    have heq : 1 / rowTolerance i = (i.sourceConstant : ℚ) * bins i := by
      unfold rowTolerance
      push_cast
      field_simp
    rw [heq]
    calc
      _ ≤ (2 : ℚ) ^ scale i * 2 ^ scale i := by
        gcongr
        · exact_mod_cast (public_bounds i).1
        · exact_mod_cast bins_le_scale_power i
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hfactor : 1 + 4 * capacityCoefficient i / rowTolerance i ≤
      (2 : ℚ) ^ (5 * scale i + 16) := by
    have hx : 4 * capacityCoefficient i / rowTolerance i ≤
        (2 : ℚ) ^ (5 * scale i + 14) := by
      calc
        _ = 4 * capacityCoefficient i * (1 / rowTolerance i) := by ring
        _ ≤ 4 * (2 : ℚ) ^ (3 * scale i + 12) * 2 ^ (2 * scale i) := by
          gcongr
          exact capacityCoefficient_bound i
        _ = _ := by
          rw [show (4 : ℚ) = 2 ^ (2 : ℕ) by norm_num, ← pow_add, ← pow_add]
          congr 1
          omega
    have hp : (1 : ℚ) ≤ 2 ^ (5 * scale i + 14) := one_le_pow₀ (by norm_num)
    rw [show 5 * scale i + 16 = (5 * scale i + 14) + 2 by omega, pow_add]
    norm_num
    linarith
  have hE : (exceptionalBudget i : ℚ) / (1 - (9 / 16 : ℚ)) ≤
      (2 : ℚ) ^ (referenceExponent i + 3 * scale i + 14) := by
    have hbound : (exceptionalBudget i : ℚ) ≤
        (2 : ℚ) ^ (referenceExponent i + 3 * scale i + 12) := by exact_mod_cast exceptionalBudget_bound i
    rw [show referenceExponent i + 3 * scale i + 14 =
      (referenceExponent i + 3 * scale i + 12) + 2 by omega, pow_add]
    norm_num
    have hn : (0 : ℚ) ≤ exceptionalBudget i := by exact_mod_cast Nat.zero_le (exceptionalBudget i)
    linarith
  calc
    _ ≤ (2 : ℚ) ^ (5 * scale i + 16) *
        2 ^ (referenceExponent i + 3 * scale i + 14) := by
      apply mul_le_mul hfactor hE
        (div_nonneg (by exact_mod_cast Nat.zero_le (exceptionalBudget i)) (by norm_num))
        (pow_nonneg (by norm_num) _)
    _ = (2 : ℚ) ^ (referenceExponent i + 8 * scale i + 30) := by
      calc
        _ = (2 : ℚ) ^ ((5 * scale i + 16) +
            (referenceExponent i + 3 * scale i + 14)) := (pow_add _ _ _).symm
        _ = _ := congrArg (fun n : ℕ => (2 : ℚ) ^ n) (by omega)
    _ < (2 : ℚ) ^ outerExponent i := by
      apply pow_lt_pow_right₀ (by norm_num)
      have hl := scale_floor i
      norm_num at hl
      unfold referenceExponent outerExponent
      nlinarith
    _ = _ := by simp only [outerWidth, Nat.cast_pow, Nat.cast_ofNat]

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Three families of actual projection covers, united once and for all.
Every surviving coordinate, pair and required small dyadic coordinate set
has its stated ORIGINAL joint projection density. -/
theorem actual_coordinate_covers (i : Input) (hc : 0 < i.sourceConstant)
    (hC : 0 < Fintype.card C) (S : Finset (Fin (outerWidth i) → C))
    (hS : (retainedFraction i : ℚ) * (Fintype.card C : ℝ) ^ outerWidth i ≤ S.card) :
    ∃ E : Finset (Fin (outerWidth i)), E.card ≤ exceptionalBudget i ∧
      (∀ J : Finset (Fin (outerWidth i)), J.card = 1 → Disjoint E J →
        (1 - (columnTolerance i : ℚ) : ℝ) * (Fintype.card C : ℝ) ^ J.card ≤
          (projection J S).card) ∧
      (∀ J : Finset (Fin (outerWidth i)), J.card = 2 → Disjoint E J →
        (99 / 100 : ℝ) * (Fintype.card C : ℝ) ^ J.card ≤ (projection J S).card) ∧
      (∀ e ∈ Finset.Ico 1 (referenceExponent i),
        ∀ J : Finset (Fin (outerWidth i)), J.card = smallWidth e → Disjoint E J →
          (18 / 25 : ℝ) * (Fintype.card C : ℝ) ^ J.card ≤ (projection J S).card) := by
  obtain ⟨Es, hEs, hs⟩ := poor_coordinate_cover S hC (by decide : 1 ≤ 1)
    (singletonBudget_pos i hc) (singleton_contraction i hc).1
    (singleton_contraction i hc).2.1 (singleton_cover_gate i hc) hS
  obtain ⟨Ep, hEp, hp⟩ := poor_coordinate_cover S hC (by decide : 1 ≤ 2)
    (coverBudget_pos i) (by norm_num : (0 : ℝ) < 99 / 100)
    (by norm_num : (99 / 100 : ℝ) ≤ 1) (actual_cover_gate i) hS
  have hex (e : ℕ) := poor_coordinate_cover S hC (smallWidth_pos e) (coverBudget_pos i)
    (by norm_num : (0 : ℝ) < 18 / 25) (by norm_num : (18 / 25 : ℝ) ≤ 1)
    (reference_cover_gate i) hS
  choose Er hEr hr using hex
  let E := (Es ∪ Ep) ∪ (Finset.Ico 1 (referenceExponent i)).biUnion Er
  have hsE : Es ⊆ E := Finset.subset_union_left.trans Finset.subset_union_left
  have hpE : Ep ⊆ E := Finset.subset_union_right.trans Finset.subset_union_left
  have hrE (e : ℕ) (he : e ∈ Finset.Ico 1 (referenceExponent i)) : Er e ⊆ E :=
    (Finset.subset_biUnion_of_mem Er he).trans Finset.subset_union_right
  have havoids (D J : Finset (Fin (outerWidth i))) (hD : D ⊆ E)
      (hJ : Disjoint E J) : ¬(D ∩ J).Nonempty := by
    intro hn
    obtain ⟨z, hz⟩ := hn
    obtain ⟨hzD, hzJ⟩ := Finset.mem_inter.mp hz
    exact Finset.disjoint_left.mp hJ (hD hzD) hzJ
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · have hu := Finset.card_biUnion_le (s := Finset.Ico 1 (referenceExponent i)) (t := Er)
    have hsum := Finset.sum_le_sum (s := Finset.Ico 1 (referenceExponent i))
      (fun e _ => hEr e)
    have ht := Nat.mul_le_mul_right (coverBudget i - 1) (sum_smallWidths_le (referenceExponent i))
    rw [Finset.sum_mul] at ht
    rw [Nat.mul_comm (2 ^ referenceExponent i) (coverBudget i - 1)] at ht
    have hc1 := Finset.card_union_le Es Ep
    have hc2 := Finset.card_union_le (Es ∪ Ep) ((Finset.Ico 1 (referenceExponent i)).biUnion Er)
    dsimp [E, exceptionalBudget, referenceWidth]
    omega
  · intro J hJ hE
    by_contra hn
    exact havoids Es J hsE hE (hs J hJ (lt_of_not_ge hn))
  · intro J hJ hE
    by_contra hn
    exact havoids Ep J hpE hE (hp J hJ (lt_of_not_ge hn))
  · intro e he J hJ hE
    by_contra hn
    exact havoids (Er e) J (hrE e he) hE (hr e J hJ (lt_of_not_ge hn))

section ActualRows

variable {X : Type*} [Fintype X] [DecidableEq X] {q : ℕ}

def referenceBlock (ref : Finset X) (j : Fin q) : Finset (Fin q × X) := {j} ×ˢ ref

def retainedReference (A : Finset (Fin q × X)) (ref : Finset X) (j : Fin q) :
    Finset (Fin q × X) := A ∩ referenceBlock ref j

theorem referenceBlock_card (ref : Finset X) (j : Fin q) :
    (referenceBlock ref j).card = ref.card := by simp [referenceBlock]

theorem retainedReference_subset (A : Finset (Fin q × X)) (ref : Finset X) (j : Fin q) :
    retainedReference A ref j ⊆ A := Finset.inter_subset_left

/-- One coordinate may suffer EVERY initial deletion. Even this pessimistic
bound leaves the literal initial support required by the routing process. -/
theorem reference_support_survives (A : Finset (Fin q × X)) (ref : Finset X)
    (j : Fin q) (A0 : ℕ) {δ : ℝ}
    (hA : (1 - δ) * (q : ℝ) * Fintype.card X ≤ A.card)
    (hsurvival : (q : ℝ) * A0 + δ * q * Fintype.card X ≤ ref.card) :
    q * A0 ≤ (retainedReference A ref j).card := by
  have htotal : (Finset.univ \ A).card + A.card = q * Fintype.card X := by
    simpa only [Finset.inter_univ, Finset.univ_inter, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin] using
      Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin q × X)) A
  have hsplit := Finset.card_inter_add_card_sdiff (referenceBlock ref j) A
  rw [referenceBlock_card] at hsplit
  have hsub : referenceBlock ref j \ A ⊆ Finset.univ \ A := by
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hz).2⟩
  have hle := Finset.card_le_card hsub
  have htotalR : ((Finset.univ \ A).card : ℝ) + A.card = (q : ℝ) * Fintype.card X := by
    exact_mod_cast htotal
  have hsplitR : ((referenceBlock ref j ∩ A).card : ℝ) +
      (referenceBlock ref j \ A).card = ref.card := by exact_mod_cast hsplit
  have hleR : ((referenceBlock ref j \ A).card : ℝ) ≤ (Finset.univ \ A).card := by
    exact_mod_cast hle
  have hres : (q : ℝ) * A0 ≤ (referenceBlock ref j ∩ A).card := by nlinarith
  unfold retainedReference
  rw [Finset.inter_comm]
  exact_mod_cast hres

end ActualRows

open Construction JointTransfer

/-- The two actual physical reservoirs partition the entire protected row
carrier. There is no third, uncounted group. -/
theorem reference_or_diagonal {Y : Type*} [Fintype Y] (a s q : ℕ)
    (z : ProtectedColumns a s q Y) :
    z ∈ referenceRows a s q ∨ z ∈ diagonalRows a s q := by
  rcases z with ⟨⟨tag, z, k⟩, l⟩
  fin_cases tag
  · left
    exact Finset.mem_image.mpr ⟨(z.2, z.1, k, l), Finset.mem_univ _, rfl⟩
  · right
    exact Finset.mem_image.mpr ⟨(z, k, l), Finset.mem_univ _, rfl⟩

/-- The same additional rows occur in the outflow partition and receiver
theorem: deleting the full reference reservoir is exactly the diagonal tag. -/
theorem additional_rows_eq {Y : Type*} [Fintype Y] {Q : ℕ} (a s q : ℕ)
    (A : Finset (Fin Q × ProtectedColumns a s q Y)) :
    A \ (Finset.univ ×ˢ referenceRows a s q) =
      A.filter (fun z => z.2 ∈ diagonalRows a s q) := by
  ext z
  simp only [Finset.mem_sdiff, Finset.mem_product, Finset.mem_univ, true_and,
    Finset.mem_filter]
  constructor
  · rintro ⟨hz, hnot⟩
    exact ⟨hz, (reference_or_diagonal a s q z.2).resolve_left hnot⟩
  · rintro ⟨hz, hdiag⟩
    exact ⟨hz, fun href => Finset.disjoint_left.mp (reference_diagonal_disjoint a s q) href hdiag⟩

/-- The physical reference reservoir is large enough to pay the literal
integer ceiling, including uniform copies. -/
theorem reference_count_ge_square {Y : Type*} [Fintype Y] [Nonempty Y]
    (a s q : ℕ) (hs : 2 ≤ s) (hq : 0 < q) :
    q ^ 2 ≤ (referenceRows (Y := Y) a s q).card := by
  have hlabels := reference_labels_pos (Y := Y) a s q hq
  have hbase : q ≤ Fintype.card (SecondRows a s q Y) := by
    rw [card_secondRows]
    exact Nat.le_mul_of_pos_right _ (pow_pos Fintype.card_pos _)
  have hthird : q ^ 2 ≤ Fintype.card (ThirdColumns a s q Y) := by
    simp only [ThirdColumns, Fintype.card_fun, Fintype.card_fin]
    exact (Nat.pow_le_pow_left hbase _).trans
      (Nat.pow_le_pow_right (lt_of_lt_of_le hq hbase) hs)
  rw [referenceRows, Finset.card_image_of_injective _ (referenceEmbedding a s q).injective,
    Finset.card_univ, Fintype.card_prod]
  exact hthird.trans (Nat.le_mul_of_pos_right _ hlabels)

def physicalReferenceCount (i : Input) (Y : Type*) [Fintype Y] : ℕ :=
  (referenceRows (Y := Y) (firstExponent i) (bins i) (secondWidth i)).card

def referenceFloor (i : Input) (Y : Type*) [Fintype Y] : ℕ :=
  ⌈2 * (2 : ℝ) ^ (-(tailDepth i : ℝ)) * physicalReferenceCount i Y⌉₊

theorem physicalReferenceCount_lower (i : Input) (Y : Type*) [Fintype Y] [Nonempty Y] :
    secondWidth i ^ 2 ≤ physicalReferenceCount i Y := by
  apply reference_count_ge_square
  · have h := Nat.le_of_dvd (bins_pos i) (sixtyfour_dvd_bins i)
    omega
  · exact secondWidth_pos i

theorem physicalReferenceCount_pos (i : Input) (Y : Type*) [Fintype Y] [Nonempty Y] :
    0 < physicalReferenceCount i Y :=
  (pow_pos (secondWidth_pos i) _).trans_le (physicalReferenceCount_lower i Y)

theorem referenceFloor_pos (i : Input) (Y : Type*) [Fintype Y] [Nonempty Y] :
    0 < referenceFloor i Y := by
  apply Nat.ceil_pos.mpr
  have hN : (0 : ℝ) < physicalReferenceCount i Y := by exact_mod_cast physicalReferenceCount_pos i Y
  exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)) hN

/-- All three physical owner-survival inequalities, with the real ceiling
and the actual `91/92` reference proportion. -/
theorem actual_reference_survival (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) (Y : Type*) [Fintype Y] [Nonempty Y] :
    let M := Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y)
    (outerWidth i : ℝ) * referenceFloor i Y / M ≤ ((rowTolerance i : ℚ) : ℝ) / 16 ∧
      (outerWidth i : ℝ) * referenceFloor i Y +
        ((columnLoss i : ℚ) : ℝ) * outerWidth i * M ≤ physicalReferenceCount i Y ∧
      (outerWidth i : ℝ) * (outerWidth i - 1) * referenceFloor i Y /
        physicalReferenceCount i Y ≤ ((rowTolerance i : ℚ) : ℝ) / (16 * (91 / 92)) := by
  dsimp only
  have hR := ProtectedDeletionGates.reference_count (Y := Y)
    (firstExponent i) (bins i) (secondWidth i)
  have hR0 : (0 : ℝ) < physicalReferenceCount i Y := by
    exact_mod_cast physicalReferenceCount_pos i Y
  have hM : (0 : ℝ) < Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y) := by
    change (physicalReferenceCount i Y : ℝ) = _ at hR
    nlinarith
  have hq : (1 : ℝ) ≤ outerWidth i := by exact_mod_cast outerWidth_pos i
  have hη : (0 : ℝ) ≤ ((rowTolerance i : ℚ) : ℝ) := by
    exact_mod_cast (rowTolerance_pos i hc).le
  have hη1 : ((rowTolerance i : ℚ) : ℝ) ≤ 1 := by
    have hd : (1 : ℚ) ≤ (i.sourceConstant * bins i : ℕ) := by
      exact_mod_cast Nat.mul_pos hc (bins_pos i)
    have hηQ : rowTolerance i ≤ 1 := by
      unfold rowTolerance
      exact (one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 1) hd).trans (by norm_num)
    exact_mod_cast hηQ
  have hδQ : columnLoss i * outerWidth i = rowTolerance i / 16 := by
    have hq0 : (outerWidth i : ℚ) ≠ 0 := by exact_mod_cast (outerWidth_pos i).ne'
    unfold columnLoss
    field_simp
  have hδ : ((columnLoss i : ℚ) : ℝ) * outerWidth i = ((rowTolerance i : ℚ) : ℝ) / 16 := by
    exact_mod_cast hδQ
  exact owner_initial_survival hq hM (by norm_num : (0 : ℝ) < 91 / 92)
    (by norm_num : (91 / 92 : ℝ) ≤ 1) hR
    (by exact_mod_cast Nat.zero_le (referenceFloor i Y)) hη
    (actual_owner_ceiling_budget i hc ha _ (physicalReferenceCount_lower i Y)) hδ
    (by linarith : ((rowTolerance i : ℚ) : ℝ) / 8 ≤ 91 / 92)

/-- The routed supports are sufficiently large even at the worst coordinate.
This uses the near-full row density and the proved physical ceiling budget. -/
theorem actual_reference_support_floor (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) (Y : Type) [Fintype Y] [Nonempty Y]
    (A : Finset (RoutingRow i Y))
    (hA : (1 - ((columnLoss i : ℚ) : ℝ)) * outerWidth i *
      Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) Y) ≤ A.card)
    (j : Fin (outerWidth i)) :
    outerWidth i * referenceFloor i Y ≤
      (retainedReference A (referenceRows (firstExponent i) (bins i) (secondWidth i)) j).card := by
  exact reference_support_survives A _ j _ hA (actual_reference_survival i hc ha Y).2.1

end EthInapproximability.CurrentPaper.ConcreteGlobalClosure
