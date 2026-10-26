import EthInapproximability.CurrentPaper.ConcreteGlobalAssignment

/-!
# Compulsory outflow from actual assigned coordinates

Source: frozen v8 `A-stage4-details.tex`, `clm:paper-global-outflow`.
The dense N restriction is applied to the actual singleton projection of the
same retained columns, and its protocol is pulled back from the actual node.
-/

noncomputable section
open scoped Classical BigOperators

namespace EthInapproximability.CurrentPaper.ConcreteOutflow

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace Workspace.Types.Protocol
open Parameters ConcreteRouting ConcreteGlobalClosure ConcreteGlobalAssignment
open ProtocolFrontier ProductExtraction
open EthInapproximability.ParameterizedNP.RoutedCertificateConstruction

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {q : ℕ}

def rowSlice (A : Finset (Fin q × X)) (j : Fin q) : Finset X :=
  Finset.univ.filter fun x => (j, x) ∈ A

def columnSlice (S : Finset (Fin q → Y)) (j : Fin q) : Finset Y :=
  S.image fun f => f j

theorem columnSlice_card (S : Finset (Fin q → Y)) (j : Fin q) :
    (columnSlice S j).card = (projection {j} S).card := by
  let ev : (({j} : Finset (Fin q)) → Y) → Y := fun f => f ⟨j, by simp⟩
  have hinj : Function.Injective ev := by
    intro f g h
    funext a
    have ha : a = ⟨j, by simp⟩ := Subtype.ext (Finset.mem_singleton.mp a.property)
    simpa only [ha] using h
  have heq : columnSlice S j = (projection {j} S).image ev := by
    simp only [columnSlice, projection, Finset.image_image, Function.comp_def, ev]
  rw [heq, Finset.card_image_of_injective _ hinj]

theorem rowSlice_card (A : Finset (Fin q × X)) (j : Fin q)
    (hA : ∀ z ∈ A, z.1 = j) : (rowSlice A j).card = A.card := by
  have heq : (rowSlice A j).image (fun x => (j, x)) = A := by
    ext z
    simp only [rowSlice, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hz
      refine ⟨z.2, ?_, ?_⟩
      · simpa only [← hA z hz, Prod.mk.eta] using hz
      · exact Prod.ext (hA z hz).symm rfl
  calc
    _ = ((rowSlice A j).image (fun x => (j, x))).card :=
      (Finset.card_image_of_injective _ (by intro a b h; exact Prod.mk.inj h |>.2)).symm
    _ = _ := congrArg Finset.card heq

/-- Every chosen column has an original common-tuple representative. -/
theorem slice_cost_le (N : X → Y → Bool) (A : Finset (Fin q × X))
    (S : Finset (Fin q → Y)) (j : Fin q) :
    D (subgame N (rowSlice A j) (columnSlice S j)) ≤
      D (subgame (interlaceFun N q) A S) := by
  let row : rowSlice A j → A := fun x => ⟨(j, x.val), (Finset.mem_filter.mp x.property).2⟩
  have hcol (y : columnSlice S j) : ∃ f ∈ S, f j = y.val := Finset.mem_image.mp y.property
  let col : columnSlice S j → S := fun y =>
    ⟨(hcol y).choose, (hcol y).choose_spec.1⟩
  have heq : subgame N (rowSlice A j) (columnSlice S j) =
      fun x y => subgame (interlaceFun N q) A S (row x) (col y) := by
    funext x y
    change N x.val y.val = N x.val ((col y).val j)
    exact congrArg (N x.val) (hcol y).choose_spec.2.symm
  rw [heq]
  exact D_mapNodes_le _ row col

/-- A dense restriction of one original N copy is a genuine restriction of
the outer interlace, using the same retained columns. -/
theorem singleton_lower (N : X → Y → Bool) (A : Finset (Fin q × X))
    (S : Finset (Fin q → Y)) (j : Fin q) (C : ℕ) (α β : ℝ)
    (hrows : ∀ z ∈ A, z.1 = j)
    (hA : α * Fintype.card X ≤ A.card)
    (hS : β * Fintype.card Y ≤ (projection {j} S).card)
    (hN : ∀ R : Finset X, ∀ T : Finset Y,
      α * Fintype.card X ≤ R.card → β * Fintype.card Y ≤ T.card →
      C ≤ D (subgame N R T)) :
    C ≤ D (subgame (interlaceFun N q) A S) := by
  have hr : α * Fintype.card X ≤ (rowSlice A j).card := by
    rw [rowSlice_card A j hrows]
    exact hA
  have hs : β * Fintype.card Y ≤ (columnSlice S j).card := by
    rw [columnSlice_card]
    exact hS
  exact (hN _ _ hr hs).trans (slice_cost_le N A S j)

theorem original_block (j : Fin q) :
    RoutedClosure.originalBlock (Finset.univ : Finset (Fin q × X)) Prod.fst j =
      ({j} ×ˢ Finset.univ) := by
  ext z
  simp only [RoutedClosure.originalBlock, Finset.mem_filter, Finset.mem_univ,
    Finset.mem_product, Finset.mem_singleton, true_and, and_true]

theorem lost_reference_eq (A : Finset (Fin q × X)) (ref : Finset X)
    (dest : Fin q × X → List Bool) (j : Fin q) (p : List Bool) :
    RoutedClosure.lostReference A (Finset.univ ×ˢ ref) Prod.fst dest j p =
      (retainedReference A ref j).filter (fun z => dest z ≠ p) := by
  ext z
  simp only [RoutedClosure.lostReference, retainedReference, referenceBlock,
    Finset.mem_filter, Finset.mem_inter, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_univ, true_and]
  tauto

/-- Near-full physical rows bound EVERY coordinate's initial deletion count;
this is an actual finite-set inequality, not an assumed local error budget. -/
theorem initial_deletion_bound (i : Input) (A : Finset (Fin (outerWidth i) × X))
    (hA : (1 - ((columnLoss i : ℚ) : ℝ)) * outerWidth i * Fintype.card X ≤ A.card)
    (j : Fin (outerWidth i)) :
    ((RoutedClosure.originalBlock Finset.univ Prod.fst j \ A).card : ℚ) ≤
      rowTolerance i * Fintype.card X / 16 := by
  have ht : ((Finset.univ \ A).card : ℝ) + A.card =
      (outerWidth i : ℝ) * Fintype.card X := by
    exact_mod_cast (show (Finset.univ \ A).card + A.card =
      outerWidth i * Fintype.card X by
      simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] using
        Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A))
  have hsub : RoutedClosure.originalBlock Finset.univ Prod.fst j \ A ⊆ Finset.univ \ A := by
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hz).2⟩
  have hle : ((RoutedClosure.originalBlock Finset.univ Prod.fst j \ A).card : ℝ) ≤
      (Finset.univ \ A).card := by exact_mod_cast Finset.card_le_card hsub
  have hdQ : columnLoss i * outerWidth i = rowTolerance i / 16 := by
    have hq : (outerWidth i : ℚ) ≠ 0 := by exact_mod_cast (outerWidth_pos i).ne'
    unfold columnLoss
    field_simp
  have hd : ((columnLoss i : ℚ) : ℝ) * outerWidth i = ((rowTolerance i : ℚ) : ℝ) / 16 := by
    exact_mod_cast hdQ
  have hh : ((RoutedClosure.originalBlock Finset.univ Prod.fst j \ A).card : ℝ) ≤
      ((rowTolerance i : ℚ) : ℝ) * Fintype.card X / 16 := by nlinarith
  exact_mod_cast hh

open Construction JointTransfer

/-- The physical outflow estimate at an actual assigned terminal node.
The sole communication input is the earlier dense N restriction theorem. -/
theorem physical_outflow (i : Input) (hc : 0 < i.sourceConstant) (ha : Accepted i)
    (B Z : Type) [Fintype B] [Nonempty B] [Fintype Z]
    (N : ProtectedColumns (firstExponent i) (bins i) (secondWidth i) B → Z → Bool)
    (P : Protocol (RoutingRow i B) (Fin (outerWidth i) → Z) Bool)
    (A : Finset (RoutingRow i B)) (S : Finset (Fin (outerWidth i) → Z))
    (owner : Fin (outerWidth i) → List Bool) (j : Fin (outerWidth i))
    (hA : (1 - ((columnLoss i : ℚ) : ℝ)) * outerWidth i *
      Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) B) ≤ A.card)
    (hS : (1 - ((columnTolerance i : ℚ) : ℝ)) * Fintype.card Z ≤ (projection {j} S).card)
    (hP : ∀ z ∈ A, ∀ y ∈ S, P.eval z y = interlaceFun N (outerWidth i) z y)
    (hcost : P.cost ≤ certificateCost i + outerExponent i - 1)
    (howner : owner j ∈ nodes P (outerExponent i) A)
    (hdepth : (owner j).length = outerExponent i)
    (hlost : ((retainedReference A
      (referenceRows (firstExponent i) (bins i) (secondWidth i)) j).filter fun z =>
      rowStop (outerExponent i) (completeNoBob (outerExponent i) P) z ≠ owner j).card <
      (outerWidth i - 1) * referenceFloor i B)
    (hN : ∀ R : Finset (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) B),
      ∀ T : Finset Z,
      (1 - ((rowTolerance i : ℚ) : ℝ)) *
        Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) B) ≤ R.card →
      (1 - ((columnTolerance i : ℚ) : ℝ)) * Fintype.card Z ≤ T.card →
      certificateCost i ≤ D (subgame N R T)) :
    7 * rowTolerance i / 8 < GlobalCount.mass
      (Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) B))
      (GlobalCount.outgoing (A.filter fun z => z.2 ∈
        diagonalRows (firstExponent i) (bins i) (secondWidth i)) Prod.fst
        (rowStop (outerExponent i) (completeNoBob (outerExponent i) P)) owner j) := by
  let M := Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) B)
  have hm : 0 < M := by
    have h := (Finset.card_le_univ
      (referenceRows (Y := B) (firstExponent i) (bins i) (secondWidth i)))
    exact lt_of_lt_of_le (physicalReferenceCount_pos i B) h
  have hC : 1 ≤ certificateCost i := by unfold certificateCost; omega
  have hblock : (RoutedClosure.originalBlock (Finset.univ : Finset (RoutingRow i B))
      Prod.fst j).card = M := by rw [original_block]; simp [M]
  have hreference : ((RoutedClosure.lostReference A
      (Finset.univ ×ˢ referenceRows (firstExponent i) (bins i) (secondWidth i)) Prod.fst
      (rowStop (outerExponent i) (completeNoBob (outerExponent i) P)) j (owner j)).card : ℚ) <
      rowTolerance i * M / 16 := by
    rw [lost_reference_eq]
    have hupper := (actual_reference_survival i hc ha B).1
    have hmR : (0 : ℝ) < M := by exact_mod_cast hm
    have hbound : (outerWidth i : ℝ) * referenceFloor i B ≤
        ((rowTolerance i : ℚ) : ℝ) * M / 16 := by
      have h := (div_le_iff₀ hmR).mp hupper
      simpa only [div_mul_eq_mul_div] using h
    have hlt : (((retainedReference A
        (referenceRows (firstExponent i) (bins i) (secondWidth i)) j).filter fun z =>
        rowStop (outerExponent i) (completeNoBob (outerExponent i) P) z ≠ owner j).card : ℝ) <
        ((rowTolerance i : ℚ) : ℝ) * M / 16 := by
      have hle : (outerWidth i - 1) * referenceFloor i B ≤ outerWidth i * referenceFloor i B :=
        Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      have hlt' : (((retainedReference A
        (referenceRows (firstExponent i) (bins i) (secondWidth i)) j).filter fun z =>
        rowStop (outerExponent i) (completeNoBob (outerExponent i) P) z ≠ owner j).card : ℝ) <
          (outerWidth i : ℝ) * referenceFloor i B := by exact_mod_cast hlost.trans_le hle
      exact hlt'.trans_le hbound
    exact_mod_cast hlt
  have hdense (rows : Finset (RoutingRow i B))
      (hsub : rows ⊆ RoutedClosure.originalBlock Finset.univ Prod.fst j)
      (hrow : (1 - rowTolerance i) * M ≤ (rows.card : ℚ)) :
      certificateCost i ≤ D (subgame (interlaceFun N (outerWidth i)) rows S) := by
    apply singleton_lower N rows S j (certificateCost i)
      (1 - ((rowTolerance i : ℚ) : ℝ)) (1 - ((columnTolerance i : ℚ) : ℝ))
    · intro z hz
      exact (Finset.mem_filter.mp (hsub hz)).2
    · exact_mod_cast hrow
    · exact hS
    · exact hN
  have hout := RoutedClosure.compulsory_outflow P (outerExponent i) (certificateCost i) M
    Finset.univ A (Finset.univ ×ˢ referenceRows (firstExponent i) (bins i) (secondWidth i))
    (Finset.subset_univ _) S (interlaceFun N (outerWidth i)) hP hC hm hcost
    Prod.fst owner j howner hdepth (rowTolerance i) hblock
    (initial_deletion_bound i A hA j) hreference hdense
  rw [additional_rows_eq] at hout
  exact hout

end EthInapproximability.CurrentPaper.ConcreteOutflow
