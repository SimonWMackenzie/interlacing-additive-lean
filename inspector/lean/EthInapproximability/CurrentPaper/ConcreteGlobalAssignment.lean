import EthInapproximability.CurrentPaper.ConcreteGlobalClosure
import EthInapproximability.CurrentPaper.ConcreteReferenceExclusions

/-!
# Actual reference assignments outside the projection covers

Source: frozen v8 `A-stage4-details.tex`, `clm:paper-global-assignment`.
The two communication exclusions are proved from the reference profiles;
the coordinate supports and every column projection remain literal finite sets.
-/

noncomputable section
open scoped Classical BigOperators

namespace EthInapproximability.CurrentPaper.ConcreteGlobalAssignment

open NPCC Workspace.Types.CommComplexity Workspace.Types.Interlace Workspace.Types.Protocol
open Parameters ConcreteRouting ConcreteGlobalClosure ConcreteReferenceExclusions
open ProtocolFrontier ReferenceAssignment ProductExtraction
open EthInapproximability.ParameterizedNP
open DenseWeightedCount DenseSynchronisation DenseWrapperFrontier
open RoutedCertificateSystem RoutingDynamics FrontierIndexing RoutedCertificateConstruction

variable {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem referenceSupport_subtype (ref : Finset X) {q : ℕ}
    (A : Finset (Fin q × X)) (j : Fin q) :
    referenceSupport (Function.Embedding.subtype (fun x => x ∈ ref)) A j =
      retainedReference A ref j := by
  ext z
  simp only [referenceSupport, retainedReference, referenceBlock,
    Finset.mem_filter, Finset.mem_inter, Finset.mem_product, Finset.mem_singleton,
    Function.Embedding.subtype_apply]
  constructor
  · rintro ⟨hz, heq, x, hx⟩
    exact ⟨hz, heq, hx ▸ x.property⟩
  · rintro ⟨hz, heq, hx⟩
    exact ⟨hz, heq, ⟨⟨z.2, hx⟩, rfl⟩⟩

/-- Complement coordinates are carried with their original labels. -/
abbrev outside {q : ℕ} (E : Finset (Fin q)) := {j : Fin q // j ∉ E}

def outsideEmbedding {q : ℕ} (E : Finset (Fin q)) : outside E ↪ Fin q :=
  Function.Embedding.subtype _

theorem outside_count {q : ℕ} (E : Finset (Fin q)) :
    Fintype.card (outside E) + E.card = q := by
  have h := Fintype.card_subtype_compl (fun j : Fin q => j ∈ E)
  simp only [Fintype.card_coe, Fintype.card_fin] at h
  change Fintype.card (outside E) = q - E.card at h
  have hh := Finset.card_le_univ E
  simp only [Fintype.card_fin] at hh
  omega

theorem outside_projection_disjoint {q : ℕ} (E Q : Finset (Fin q))
    (hQ : Q ⊆ Finset.univ.image (outsideEmbedding E)) : Disjoint E Q := by
  apply Finset.disjoint_left.mpr
  intro j hj hq
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp (hQ hq)
  apply k.property
  change outsideEmbedding E k ∈ E
  rw [hk]
  exact hj

/-- The actual low-cost protocol would assign almost all surviving original
coordinates to distinct terminal nodes. The local communication exclusions
are conclusions of the two reference profiles, not hypotheses. -/
theorem reference_assignment_from_profiles (N : X → Y → Bool)
    (ref : Finset X) [Nonempty ref] [Nonempty Y]
    (i : Input) (P : Protocol (Fin (outerWidth i) × X) (Fin (outerWidth i) → Y) Bool)
    (A : Finset (Fin (outerWidth i) × X)) (S : Finset (Fin (outerWidth i) → Y))
    (E : Finset (Fin (outerWidth i))) (A0 : ℕ)
    (h1 : certificateCost i - 1 ≤ Dfamily
      (interlaceFun (fun a : ref => N a.val) 1)
      (bracketGE ref Y 1 ((2 : ℝ) ^ (-(tailDepth i : ℝ))) (3 / 5)))
    (h2 : certificateCost i - 2 ≤ Dfamily
      (interlaceFun (fun a : ref => N a.val) 1)
      (bracketGE ref Y 1 ((2 : ℝ) ^ (-(tailDepth i : ℝ))) (3 / 10)))
    (hApos : 0 < A0)
    (hA0 : ⌈(ref.card : ℝ) * (2 * (2 : ℝ) ^ (-(tailDepth i : ℝ)))⌉₊ ≤ A0)
    (hR : ∀ j, outerWidth i * A0 ≤ (retainedReference A ref j).card)
    (hS : ((retainedFraction i : ℚ) : ℝ) *
      (Fintype.card Y : ℝ) ^ outerWidth i ≤ S.card)
    (hsmall : ∀ ell ∈ Finset.Ico 1 (referenceExponent i),
      ∀ Q : Finset (Fin (outerWidth i)), Q.card = smallWidth ell → Disjoint E Q →
      (18 / 25 : ℝ) * (Fintype.card Y : ℝ) ^ Q.card ≤ (projection Q S).card)
    (hpairs : ∀ Q : Finset (Fin (outerWidth i)), Q.card = 2 → Disjoint E Q →
      (99 / 100 : ℝ) * (Fintype.card Y : ℝ) ^ Q.card ≤ (projection Q S).card)
    (hP : ∀ z ∈ A, ∀ y ∈ S, P.eval z y = interlaceFun N (outerWidth i) z y)
    (hcost : P.cost ≤ certificateCost i + outerExponent i - 1) :
    ∃ (J : Finset (Fin (outerWidth i))) (owner : Fin (outerWidth i) → List Bool),
      Disjoint E J ∧ Set.InjOn owner J ∧
      (∀ j ∈ J, owner j ∈ nodes P (outerExponent i) A ∧
        (owner j).length = outerExponent i ∧
        ((retainedReference A ref j).filter fun z =>
          rowStop (outerExponent i) (completeNoBob (outerExponent i) P) z ≠ owner j).card <
          (outerWidth i - 1) * A0) ∧
      ((outerWidth i : ℝ) - E.card / (1 - (9 / 16 : ℝ)) ≤ (J.card : ℝ)) := by
  let e : ref ↪ X := Function.Embedding.subtype _
  let loc := outsideEmbedding E
  have hR' (j : outside E) : refRowFloor A0 (outerExponent i) ≤
      (referenceSupport e A (loc j)).card := by
    rw [referenceSupport_subtype]
    exact hR j.val
  have hS' : ((retainedFraction i : ℚ) : ℝ) *
      (Fintype.card (Fin (outerWidth i) → Y) : ℝ) ≤ S.card := by
    simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hS
  have hsmall' (ell : ℕ) (he : 1 ≤ ell) (he' : ell < referenceExponent i)
      (Q : Finset (Fin (outerWidth i))) (hQ : Q ⊆ Finset.univ.image loc)
      (hn : Q.card = 2 ^ (ell - 1) + 1) :
      (18 / 25 : ℝ) * (Fintype.card Y : ℝ) ^ Q.card ≤ (projection Q S).card :=
    hsmall ell (Finset.mem_Ico.mpr ⟨he, he'⟩) Q hn (outside_projection_disjoint E Q hQ)
  have hpairs' (j k : outside E) (hjk : j ≠ k) :
      (9 / 25 : ℝ) * (Fintype.card Y : ℝ) ^ 2 ≤
        (projection {loc j, loc k} S).card := by
    have hne : loc j ≠ loc k := fun h => hjk (loc.injective h)
    have hcard : ({loc j, loc k} : Finset (Fin (outerWidth i))).card = 2 := by simp [hne]
    have hdis : Disjoint E ({loc j, loc k} : Finset (Fin (outerWidth i))) := by
      apply Finset.disjoint_left.mpr
      intro z hz hz'
      rcases Finset.mem_insert.mp hz' with h | h
      · apply j.property
        change loc j ∈ E
        rw [← h]
        exact hz
      · apply k.property
        change loc k ∈ E
        rw [← Finset.mem_singleton.mp h]
        exact hz
    have hh := hpairs {loc j, loc k} hcard hdis
    rw [hcard] at hh
    exact (mul_le_mul_of_nonneg_right (by norm_num : (9 / 25 : ℝ) ≤ 99 / 100)
      (pow_nonneg (Nat.cast_nonneg _) _)).trans hh
  have hA0' : ⌈(Fintype.card ref : ℝ) *
      (2 * (2 : ℝ) ^ (-(tailDepth i : ℝ)))⌉₊ ≤ A0 := by simpa using hA0
  obtain ⟨hb, ht⟩ := reference_exclusions_parameters N e i P A S loc A0
    h1 h2 hA0' hR' hS' hsmall' hpairs' hP hcost
  have hr : 0 < outerExponent i := by
    have hs := scale_floor i
    unfold outerExponent
    positivity
  have hcoord : (2 : ℝ) ^ outerExponent i - E.card ≤ Fintype.card (outside E) := by
    have hh : (Fintype.card (outside E) : ℝ) + E.card = outerWidth i := by
      exact_mod_cast outside_count E
    simp only [Parameters.outerWidth, Nat.cast_pow, Nat.cast_ofNat] at hh
    exact (sub_le_iff_le_add).2 (by simpa only [add_comm] using hh.symm.le)
  obtain ⟨J0, own, hinj, hown, hcount, _, _⟩ := global_assignment P A
    (fun j => referenceSupport e A (loc j)) hApos hr hR'
    (fun j => referenceSupport_subset e A (loc j)) (E.card : ℝ) hcoord hb ht
  let J := J0.image loc
  let owner : Fin (outerWidth i) → List Bool := fun j =>
    if h : j ∉ E then own ⟨j, h⟩ else []
  have howner (j : outside E) : owner (loc j) = own j := by
    change (if h : j.val ∉ E then own ⟨j.val, h⟩ else []) = own j
    simp only [dif_pos j.property]
  have hc : J.card = J0.card := Finset.card_image_of_injective _ loc.injective
  refine ⟨J, owner, outside_projection_disjoint E J ?_, ?_, ?_, ?_⟩
  · exact Finset.image_subset_image (Finset.subset_univ _)
  · intro j hj k hk heq
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hk
    rw [howner, howner] at heq
    exact congrArg loc (hinj hj' hk' heq)
  · intro j hj
    obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
    have hh := hown j' hj'
    rw [howner]
    refine ⟨hh.1, hh.2.1, ?_⟩
    simpa only [e, referenceSupport_subtype, Parameters.outerWidth] using hh.2.2.2.2
  · rw [hc]
    simpa only [outerWidth, Nat.cast_pow, Nat.cast_ofNat] using hcount

open Construction JointTransfer

/-- Physical protected rows, accepted parameter values and the retained
rectangle supply all coordinate-cover and initial-support premises. -/
theorem physical_assignment_from_profiles (i : Input) (hc : 0 < i.sourceConstant)
    (ha : Accepted i) (B Z : Type) [Fintype B] [Nonempty B] [Fintype Z] [Nonempty Z]
    (N : ProtectedColumns (firstExponent i) (bins i) (secondWidth i) B → Z → Bool)
    (P : Protocol (RoutingRow i B) (Fin (outerWidth i) → Z) Bool)
    (A : Finset (RoutingRow i B)) (S : Finset (Fin (outerWidth i) → Z))
    (h1 : certificateCost i - 1 ≤ Dfamily
      (interlaceFun (fun a : referenceRows (Y := B)
        (firstExponent i) (bins i) (secondWidth i) => N a.val) 1)
      (bracketGE (referenceRows (Y := B) (firstExponent i) (bins i) (secondWidth i))
        Z 1 ((2 : ℝ) ^ (-(tailDepth i : ℝ))) (3 / 5)))
    (h2 : certificateCost i - 2 ≤ Dfamily
      (interlaceFun (fun a : referenceRows (Y := B)
        (firstExponent i) (bins i) (secondWidth i) => N a.val) 1)
      (bracketGE (referenceRows (Y := B) (firstExponent i) (bins i) (secondWidth i))
        Z 1 ((2 : ℝ) ^ (-(tailDepth i : ℝ))) (3 / 10)))
    (hA : (1 - ((columnLoss i : ℚ) : ℝ)) * outerWidth i *
      Fintype.card (ProtectedColumns (firstExponent i) (bins i) (secondWidth i) B) ≤ A.card)
    (hS : ((retainedFraction i : ℚ) : ℝ) * (Fintype.card Z : ℝ) ^ outerWidth i ≤ S.card)
    (hP : ∀ z ∈ A, ∀ y ∈ S, P.eval z y = interlaceFun N (outerWidth i) z y)
    (hcost : P.cost ≤ certificateCost i + outerExponent i - 1) :
    ∃ (E J : Finset (Fin (outerWidth i))) (owner : Fin (outerWidth i) → List Bool),
      E.card ≤ exceptionalBudget i ∧ Disjoint E J ∧ Set.InjOn owner J ∧
      (∀ Q : Finset (Fin (outerWidth i)), Q.card = 1 → Disjoint E Q →
        (1 - (columnTolerance i : ℚ) : ℝ) * (Fintype.card Z : ℝ) ^ Q.card ≤
          (projection Q S).card) ∧
      (∀ Q : Finset (Fin (outerWidth i)), Q.card = 2 → Disjoint E Q →
        (99 / 100 : ℝ) * (Fintype.card Z : ℝ) ^ Q.card ≤ (projection Q S).card) ∧
      (∀ j ∈ J, owner j ∈ nodes P (outerExponent i) A ∧
        (owner j).length = outerExponent i ∧
        ((retainedReference A (referenceRows (firstExponent i) (bins i) (secondWidth i)) j).filter
          fun z => rowStop (outerExponent i) (completeNoBob (outerExponent i) P) z ≠
            owner j).card < (outerWidth i - 1) * referenceFloor i B) ∧
      ((outerWidth i : ℝ) - E.card / (1 - (9 / 16 : ℝ)) ≤ (J.card : ℝ)) := by
  let ref := referenceRows (Y := B) (firstExponent i) (bins i) (secondWidth i)
  letI : Nonempty ref := Finset.nonempty_coe_sort.mpr
    (Finset.card_pos.mp (physicalReferenceCount_pos i B))
  obtain ⟨E, hE, hsingle, hpair, hsmall⟩ := actual_coordinate_covers i hc Fintype.card_pos S hS
  have hceil : ⌈(ref.card : ℝ) * (2 * (2 : ℝ) ^ (-(tailDepth i : ℝ)))⌉₊ ≤
      referenceFloor i B := by
    unfold referenceFloor physicalReferenceCount
    rw [mul_comm (ref.card : ℝ)]
  obtain ⟨J, owner, hd, hi, ho, hn⟩ := reference_assignment_from_profiles N ref i P A S E
    (referenceFloor i B) h1 h2 (referenceFloor_pos i B) hceil
    (actual_reference_support_floor i hc ha B A hA) hS hsmall hpair hP hcost
  exact ⟨E, J, owner, hE, hd, hi, hsingle, hpair, ho, hn⟩

end EthInapproximability.CurrentPaper.ConcreteGlobalAssignment
