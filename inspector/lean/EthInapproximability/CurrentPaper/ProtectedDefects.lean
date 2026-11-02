import EthInapproximability.CurrentPaper.IndexedProjection
import EthInapproximability.CurrentPaper.Construction
import EthInapproximability.CurrentPaper.ProtectedGraphItems
import EthInapproximability.CurrentPaper.JointTransfer
import EthInapproximability.ParameterizedNP.DenseSourceOwners

/-!
# Deficient coordinates of an actual retained indexed family

Source: locked replacement v8, `A-stage4-details.tex`,
`lem:paper-protected-preparation`, lines 459--465.

The marginal and joint supports are constructed from one retained label set.
Balancedness bounds the actual fibres of its joint projection. The generic
finite/analytic lemma `DenseSourceOwners.templateDefect` is reused only after
discharging its product-containment and joint-density inputs here.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ProtectedDefects

open scoped BigOperators Classical
open NPCC
open EthInapproximability.ParameterizedNP.DenseSourceOwners

section Projection

variable {Y : Type*} [Fintype Y] [DecidableEq Y] {q L : ℕ}

def coordinateSupport (family : Fin L → Fin q → Y) (K : Finset (Fin L))
    (α : Fin q) : Finset Y := K.image fun ℓ => family ℓ α

/-- A joint support retains correlations among all selected coordinates. -/
def jointSupport (family : Fin L → Fin q → Y) (K : Finset (Fin L))
    (Q : Finset (Fin q)) : Finset (Q → Y) :=
  K.image fun ℓ => fun α : Q => family ℓ α.val

def coordinateDensity (family : Fin L → Fin q → Y) (K : Finset (Fin L))
    (α : Fin q) : ℝ := (coordinateSupport family K α).card / Fintype.card Y

def jointDensity (family : Fin L → Fin q → Y) (K : Finset (Fin L))
    (Q : Finset (Fin q)) : ℝ :=
  (jointSupport family K Q).card / (Fintype.card Y : ℝ) ^ Q.card

theorem jointSupport_subset_product (family : Fin L → Fin q → Y)
    (K : Finset (Fin L)) (Q : Finset (Fin q)) :
    jointSupport family K Q ⊆
      Fintype.piFinset (fun α : Q => coordinateSupport family K α.val) := by
  intro f hf
  obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp hf
  rw [Fintype.mem_piFinset]
  intro α
  exact Finset.mem_image.mpr ⟨ℓ, hℓ, rfl⟩

theorem jointDensity_le_product (family : Fin L → Fin q → Y)
    (K : Finset (Fin L)) (Q : Finset (Fin q)) :
    jointDensity family K Q ≤ ∏ α ∈ Q, coordinateDensity family K α := by
  have hcard := Finset.card_le_card (jointSupport_subset_product family K Q)
  rw [Fintype.card_piFinset] at hcard
  have hcardR : ((jointSupport family K Q).card : ℝ) ≤
      ∏ α : Q, ((coordinateSupport family K α.val).card : ℝ) := by
    exact_mod_cast hcard
  have hdiv := div_le_div_of_nonneg_right hcardR
    (show (0 : ℝ) ≤ (Fintype.card Y : ℝ) ^ Q.card by positivity)
  rw [Finset.prod_coe_sort Q
    (fun α => ((coordinateSupport family K α).card : ℝ))] at hdiv
  simpa only [jointDensity, coordinateDensity, Finset.prod_div_distrib,
    Finset.prod_const] using hdiv

/-- Upper balancedness for a specified joint value, still counting retained
family labels before any deduplication. -/
theorem joint_fibre_upper [Nonempty Y]
    (family : Fin L → Fin q → Y) (K : Finset (Fin L)) (Q : Finset (Fin q))
    {t : ℕ} {ε : ℝ} (hbal : IsBalancedFamily t family ε) (hQ : Q.card ≤ t)
    (c : Q → Y) :
    ((K.filter (fun ℓ => (fun α : Q => family ℓ α.val) = c)).card : ℝ) ≤
      (1 + ε) * L / (Fintype.card Y : ℝ) ^ Q.card := by
  let extension : Fin q → Y := fun α => if h : α ∈ Q then c ⟨α, h⟩
    else Classical.choice inferInstance
  have hsub : K.filter (fun ℓ => (fun α : Q => family ℓ α.val) = c) ⊆
      Finset.univ.filter (fun ℓ : Fin L => ∀ α ∈ Q, family ℓ α = extension α) := by
    intro ℓ hℓ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro α hα
    have heq := congrFun (Finset.mem_filter.mp hℓ).2 ⟨α, hα⟩
    simpa [extension, hα] using heq
  have hupper := (abs_le.mp (hbal.2 Q hQ extension)).2
  have hL : (0 : ℝ) < L := by exact_mod_cast hbal.1
  have hN : (0 : ℝ) < (Fintype.card Y : ℝ) ^ Q.card := by positivity
  have hh : (((Finset.univ.filter (fun ℓ : Fin L =>
      ∀ α ∈ Q, family ℓ α = extension α)).card : ℝ) / L) ≤
      (1 + ε) / (Fintype.card Y : ℝ) ^ Q.card := by
    rw [add_div]
    linarith
  have hh' := (div_le_iff₀ hL).mp hh
  calc
    _ ≤ ((Finset.univ.filter (fun ℓ : Fin L =>
        ∀ α ∈ Q, family ℓ α = extension α)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := by simpa only [div_mul_eq_mul_div, mul_div_assoc, mul_comm] using hh'

theorem jointDensity_ge_of_balanced [Nonempty Y]
    (family : Fin L → Fin q → Y) (K : Finset (Fin L)) (Q : Finset (Fin q))
    {t : ℕ} {ε x : ℝ} (hbal : IsBalancedFamily t family ε)
    (hQ : Q.card ≤ t) (hε : 0 ≤ ε) (hK : x * L ≤ K.card) :
    x / (1 + ε) ≤ jointDensity family K Q := by
  have hN : (0 : ℝ) < (Fintype.card Y : ℝ) ^ Q.card := by positivity
  have h := IndexedProjection.image_card_ge_of_density
    K (fun ℓ => fun α : Q => family ℓ α.val)
    (by exact_mod_cast hbal.1) hN (by linarith : (0 : ℝ) < 1 + ε)
    (joint_fibre_upper family K Q hbal hQ) hK
  rw [Nat.ceil_le] at h
  exact (le_div_iff₀ hN).2 (by simpa only [mul_comm] using h)

end Projection

/-- Fewer than `8*q1` deficient coordinates for a literal retained balanced
family. No joint-density or support-containment certificate is assumed. -/
theorem deficient_coordinates_lt {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] {q1 q2 L t2 t : ℕ}
    (family : Fin L → Fin q2 → (Fin q1 × X)) (K : Finset (Fin L))
    (hq1 : 1 ≤ q1) {ε xdom : ℝ} (hε : 0 ≤ ε)
    (hbal : IsBalancedFamily t2 family ε)
    (ht : (t : ℝ) - 1 < (Fintype.card X : ℝ) / 8)
    (hwidth : 8 * q1 ≤ t2) (hK : xdom * L ≤ K.card)
    (hxdom : 98 / 100 ≤ xdom / (1 + ε)) :
    (templateBadSet t (coordinateSupport family K)).card < 8 * q1 := by
  letI : Nonempty (Fin q1) := ⟨⟨0, by omega⟩⟩
  apply templateDefect (coordinateSupport family K) (coordinateDensity family K)
    (jointDensity family K) hq1 Fintype.card_pos ht
  · intro α
    simp [coordinateDensity, Fintype.card_prod, Fintype.card_fin]
  · intro α
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact hwidth
  · exact jointDensity_le_product family K
  · intro Q hQ
    exact jointDensity_ge_of_balanced family K Q hbal hQ hε hK
  · exact hxdom

/-- Current-paper specialization: a missing seed-row threshold in a block of
the actual `FirstRows` coordinate alphabet. -/
theorem actual_family_defects_lt {X : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] {a q L t2 t : ℕ}
    (family : Construction.SecondFamily a q L X) (K : Finset (Fin L))
    (hq1 : 1 ≤ Construction.qOne a)
    {ε xdom : ℝ} (hε : 0 ≤ ε) (hbal : IsBalancedFamily t2 family ε)
    (ht : (t : ℝ) - 1 < (Fintype.card X : ℝ) / 8)
    (hwidth : 8 * Construction.qOne a ≤ t2) (hK : xdom * L ≤ K.card)
    (hxdom : 98 / 100 ≤ xdom / (1 + ε)) :
    (templateBadSet t (coordinateSupport family K)).card < 8 * Construction.qOne a := by
  apply deficient_coordinates_lt family K hq1
    hε hbal ht hwidth hK hxdom

section Diagonal

open Construction JointTransfer ProtectedGraphItems

variable {Y : Type*} [Fintype Y]

/-- The additional diagonal group is indexed by one original coordinate,
one common seed-column tuple, and the two actual duplication labels. -/
def diagonalCoordinateEmbedding (a s q : ℕ) :
    Fin q × (FirstColumns a s Y × DiagonalLabels a s q Y) ↪
      ProtectedColumns a s q Y where
  toFun z := diagonalEmbedding a s q ((z.1, z.2.1), z.2.2)
  inj' := by
    rintro ⟨α, γ, k⟩ ⟨β, δ, l⟩ h
    have hh := (diagonalEmbedding (Y := Y) a s q).injective h
    cases hh
    rfl

def diagonalDefects (a s q : ℕ) (A : Finset (ProtectedColumns a s q Y)) :
    Finset (Fin q) :=
  badItems (diagonalCoordinateEmbedding a s q) A
    ⌈(3 / 4 : ℝ) * Fintype.card (FirstColumns a s Y)⌉₊

/-- A coordinate whose actual quotient supports less than three quarters of
the seed-column alphabet has lost more than one quarter of all its copies. -/
theorem diagonal_coordinate_charge (a s q : ℕ)
    (A : Finset (ProtectedColumns a s q Y)) {α : Fin q}
    (hα : α ∈ diagonalDefects a s q A) :
    Fintype.card (FirstColumns a s Y) * Fintype.card (DiagonalLabels a s q Y) ≤
      4 * (deletedItemCopies (diagonalCoordinateEmbedding a s q) A α).card := by
  let e := diagonalCoordinateEmbedding (Y := Y) a s q
  have hb : (survivingRows e A α).card <
      ⌈(3 / 4 : ℝ) * Fintype.card (FirstColumns a s Y)⌉₊ :=
    (mem_badItems ..).1 hα
  have hbR := (Nat.lt_ceil).mp hb
  have hquarter : 4 * (survivingRows e A α).card <
      3 * Fintype.card (FirstColumns a s Y) := by
    exact_mod_cast (show (4 : ℝ) * (survivingRows e A α).card <
      3 * Fintype.card (FirstColumns a s Y) by linarith)
  have hc := Finset.card_le_univ (survivingRows e A α)
  have hm : Fintype.card (FirstColumns a s Y) ≤
      4 * (Fintype.card (FirstColumns a s Y) - (survivingRows e A α).card) := by omega
  have hmul := Nat.mul_le_mul_right (Fintype.card (DiagonalLabels a s q Y)) hm
  have hcharge := missing_rows_charge e A α
  nlinarith

/-- The diagonal deficiency set is common to all branches. Its count is
charged once to the actual globally deleted diagonal input copies. -/
theorem diagonal_defects_charge (a s q : ℕ)
    (A : Finset (ProtectedColumns a s q Y)) :
    (diagonalDefects a s q A).card *
        (Fintype.card (FirstColumns a s Y) * Fintype.card (DiagonalLabels a s q Y)) ≤
      4 * ((Finset.univ : Finset (ProtectedColumns a s q Y)) \ A).card := by
  have hsum := Finset.sum_le_sum (fun α hα => diagonal_coordinate_charge a s q A hα)
  have htotal := sum_deletedItemCopies_le (diagonalCoordinateEmbedding a s q) A
    (diagonalDefects a s q A)
  simp only [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at hsum
  simp only [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ] at htotal ⊢
  omega

/-- An exact carrier identity: the additional diagonal group has mass `1/92`,
or `2*mu` in the source notation, in the physical carrier. -/
theorem diagonal_group_card (a s q : ℕ) :
    Fintype.card (ProtectedColumns a s q Y) =
      92 * (q * Fintype.card (FirstColumns a s Y) * Fintype.card (DiagonalLabels a s q Y)) := by
  let S := WeightedDuplication.columnSupport (RawColumns a s q Y) (SecondRows a s q Y)
  have hg := WeightedDuplication.card_group S WeightedDuplication.columnWeight 1
  let e : WeightedDuplication.Group S WeightedDuplication.columnWeight 1 ≃
      ((Fin q × FirstColumns a s Y) × Fin (diagonalMultiplicity (Y := Y) a s q)) :=
    Equiv.refl _
  have hg' : q * Fintype.card (FirstColumns a s Y) * diagonalMultiplicity (Y := Y) a s q =
      2 * ∏ i, Fintype.card (S i) := by
    calc
      _ = Fintype.card ((Fin q × FirstColumns a s Y) ×
          Fin (diagonalMultiplicity (Y := Y) a s q)) := by
        simp only [Fintype.card_prod, Fintype.card_fin]
      _ = Fintype.card (WeightedDuplication.Group S WeightedDuplication.columnWeight 1) :=
        (Fintype.card_congr e).symm
      _ = _ := hg
  have hc : Fintype.card (ProtectedColumns a s q Y) =
      184 * (∏ i, Fintype.card (S i)) * uniformCopies (Y := Y) a s q := by
    change Fintype.card (WeightedDuplication.Carrier S WeightedDuplication.columnWeight ×
      Fin (uniformCopies (Y := Y) a s q)) = _
    rw [Fintype.card_prod, Fintype.card_fin, WeightedDuplication.card_carrier]
    norm_num [WeightedDuplication.columnWeight, Fin.sum_univ_succ]
  rw [hc]
  simp only [DiagonalLabels, Fintype.card_prod, Fintype.card_fin]
  nlinarith [congrArg (fun n => n * uniformCopies (Y := Y) a s q) hg']

/-- Density-form diagonal count, with the correct current two-support mass:
`4*eta*q/(2*mu) = 368*eta*q`. -/
theorem diagonal_defects_le [Nonempty Y] (a s q : ℕ) (hq : 0 < q)
    (A : Finset (ProtectedColumns a s q Y)) {η : ℝ}
    (hdelete : (((Finset.univ : Finset (ProtectedColumns a s q Y)) \ A).card : ℝ) ≤
      η * Fintype.card (ProtectedColumns a s q Y)) :
    ((diagonalDefects a s q A).card : ℝ) ≤ 368 * η * q := by
  have hp : (0 : ℝ) < Fintype.card (FirstColumns a s Y) *
      Fintype.card (DiagonalLabels a s q Y) := by
    exact_mod_cast Nat.mul_pos Fintype.card_pos (diagonal_labels_pos a s q hq)
  have hcharge : ((diagonalDefects a s q A).card : ℝ) *
      (Fintype.card (FirstColumns a s Y) * Fintype.card (DiagonalLabels a s q Y)) ≤
      4 * (((Finset.univ : Finset (ProtectedColumns a s q Y)) \ A).card : ℝ) := by
    exact_mod_cast diagonal_defects_charge a s q A
  have hcard : (Fintype.card (ProtectedColumns a s q Y) : ℝ) =
      92 * (q * Fintype.card (FirstColumns a s Y) * Fintype.card (DiagonalLabels a s q Y)) := by
    exact_mod_cast diagonal_group_card (Y := Y) a s q
  rw [hcard] at hdelete
  apply (mul_le_mul_iff_left₀ hp).mp
  nlinarith

end Diagonal

open Construction

/-- The actual deficient sets over all prefix branches. The common diagonal
set is counted once per branch, exactly as in the preparation argument. -/
theorem aggregate_defects_lt {X Y : Type*} [Fintype X] [DecidableEq X]
    [Nonempty X] [Fintype Y] [Nonempty Y] {a s q L t2 t : ℕ}
    (hs : 0 < s) (hq : 0 < q) (hq1 : 1 ≤ qOne a)
    (family : SecondFamily a q L X) (K : Fin s → Finset (Fin L))
    (A : Finset (ProtectedColumns a s q Y)) {ε xdom η ζ : ℝ}
    (hε : 0 ≤ ε) (hbal : IsBalancedFamily t2 family ε)
    (ht : (t : ℝ) - 1 < (Fintype.card X : ℝ) / 8)
    (hwidth : 8 * qOne a ≤ t2) (hK : ∀ b, xdom * L ≤ (K b).card)
    (hxdom : 98 / 100 ≤ xdom / (1 + ε))
    (hdelete : (((Finset.univ : Finset (ProtectedColumns a s q Y)) \ A).card : ℝ) ≤
      η * Fintype.card (ProtectedColumns a s q Y))
    (hζ : 0 < ζ) (hscale : 64 * (s : ℝ) * qOne a ≤ ζ * q)
    (hη : η < (1 / 184 : ℝ) * ζ / (32 * s)) :
    (∑ b : Fin s,
      ((templateBadSet t (coordinateSupport family (K b)) ∪ diagonalDefects a s q A).card : ℝ)) <
        ζ * q / 4 := by
  let temp := fun b => templateBadSet t (coordinateSupport family (K b))
  let diag := diagonalDefects a s q A
  have htemp : ∀ b : Fin s, ((temp b).card : ℝ) < 8 * qOne a := by
    intro b
    exact_mod_cast actual_family_defects_lt family (K b) hq1 hε hbal ht hwidth (hK b) hxdom
  have hsumTemp : (∑ b : Fin s, ((temp b).card : ℝ)) < 8 * (s : ℝ) * qOne a := by
    have h := Finset.sum_lt_sum_of_nonempty
      (show (Finset.univ : Finset (Fin s)).Nonempty from ⟨⟨0, hs⟩, Finset.mem_univ _⟩)
      (fun b _ => htemp b)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_assoc, mul_left_comm] using h
  have hdiag := diagonal_defects_le a s q hq A hdelete
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hη' := (lt_div_iff₀ (show (0 : ℝ) < 32 * s by positivity)).mp hη
  have hηq := mul_lt_mul_of_pos_right hη' hqR
  have hdiagSum : (s : ℝ) * diag.card < ζ * q / 16 := by
    have hh := mul_le_mul_of_nonneg_left hdiag hsR.le
    dsimp only [diag]
    nlinarith
  have htotal : (∑ b : Fin s, (((temp b) ∪ diag).card : ℝ)) ≤
      (∑ b : Fin s, ((temp b).card : ℝ)) + (s : ℝ) * diag.card := by
    calc
      _ ≤ ∑ b : Fin s, (((temp b).card : ℝ) + diag.card) := by
        apply Finset.sum_le_sum
        intro b _
        exact_mod_cast Finset.card_union_le (temp b) diag
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change (∑ b : Fin s, (((temp b) ∪ diag).card : ℝ)) < _
  have hzq := mul_pos hζ hqR
  nlinarith

/-- Select a real branch whose source witnesses outnumber its defects four
to one, then remove those very defects from both actual coordinate sets.
Only the two already-derived aggregate counts are inputs to this final
finite counting step. No prepared mass or branchwise conclusion is assumed. -/
theorem select_prepared_branch {s q : ℕ} (U bad : Fin s → Finset (Fin q)) {ζ : ℝ}
    (hsupply : ζ * q ≤ ∑ b : Fin s, ((U b).card : ℝ))
    (hdefect : (∑ b : Fin s, ((bad b).card : ℝ)) < ζ * q / 4) :
    ∃ b : Fin s,
      q ≤ ((Finset.univ : Finset (Fin q)) \ bad b).card + (bad b).card ∧
      (U b).card ≤ (U b \ bad b).card + (bad b).card ∧
      4 * (bad b).card < (U b).card := by
  have hex : ∃ b : Fin s, 4 * (bad b).card < (U b).card := by
    by_contra h
    push_neg at h
    have hsum : (∑ b : Fin s, ((U b).card : ℝ)) ≤
        4 * ∑ b : Fin s, ((bad b).card : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro b _
      exact_mod_cast h b
    linarith
  obtain ⟨b, hb⟩ := hex
  refine ⟨b, ?_, ?_, hb⟩
  · have hcard := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (bad b))
    simpa only [Finset.card_univ, Fintype.card_fin] using hcard.ge
  · rw [Finset.card_sdiff_add_card]
    exact Finset.card_le_card Finset.subset_union_left

end EthInapproximability.CurrentPaper.ProtectedDefects
