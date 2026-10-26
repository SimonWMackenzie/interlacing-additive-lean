import CurrentAdditive.DeterministicPairProductLaw
import CurrentAdditive.ProjectionTVBridge

namespace CurrentAdditive.SuffixLong

open Paper2
open CurrentAdditive.FourthMoment.ProjectionTVBridge

variable {Z S : Type*} [Fintype Z] [Fintype S]

def quarticSupport {m q : ℕ} (e : Fin (2*m) → Fin q)
    (i j k l : Fin m) : Finset (Fin q) :=
  pairBlock e i ∪ pairBlock e j ∪ pairBlock e k ∪ pairBlock e l

private theorem pairBlock_card_le_two {m q : ℕ}
    (e : Fin (2*m) → Fin q) (i : Fin m) :
    (pairBlock e i).card ≤ 2 := by
  simpa only [pairBlock, Fintype.card_fin] using
    (Finset.card_image_le (s := (Finset.univ : Finset (Fin 2)))
      (f := fun j : Fin 2 => e (pairPosition i j)))

private theorem quarticSupport_card_le_eight {m q : ℕ}
    (e : Fin (2*m) → Fin q) (i j k l : Fin m) :
    (quarticSupport e i j k l).card ≤ 8 := by
  have hi := pairBlock_card_le_two e i
  have hj := pairBlock_card_le_two e j
  have hk := pairBlock_card_le_two e k
  have hl := pairBlock_card_le_two e l
  have h1 := Finset.card_union_le (pairBlock e i) (pairBlock e j)
  have h2 := Finset.card_union_le (pairBlock e i ∪ pairBlock e j) (pairBlock e k)
  have h3 := Finset.card_union_le
    (pairBlock e i ∪ pairBlock e j ∪ pairBlock e k) (pairBlock e l)
  dsimp [quarticSupport]
  omega

private theorem pairBlock_good {m q : ℕ}
    (e : Fin (2*m) → Fin q) (E : Finset (Fin q))
    (hgood : ∀ t : Fin (2*m), e t ∉ E) (i : Fin m) :
    Disjoint (pairBlock e i) E := by
  apply Finset.disjoint_left.mpr
  intro x hx hE
  rcases Finset.mem_image.mp hx with ⟨j, _, rfl⟩
  exact hgood (pairPosition i j) hE

private theorem quarticSupport_good {m q : ℕ}
    (e : Fin (2*m) → Fin q) (E : Finset (Fin q))
    (hgood : ∀ t : Fin (2*m), e t ∉ E) (i j k l : Fin m) :
    quarticSupport e i j k l ⊆ Finset.univ \ E := by
  intro x hx
  have hnot : x ∉ E := by
    simp only [quarticSupport, Finset.mem_union] at hx
    rcases hx with (((hx | hx) | hx) | hx)
    · exact (Finset.disjoint_left.mp (pairBlock_good e E hgood i)) hx
    · exact (Finset.disjoint_left.mp (pairBlock_good e E hgood j)) hx
    · exact (Finset.disjoint_left.mp (pairBlock_good e E hgood k)) hx
    · exact (Finset.disjoint_left.mp (pairBlock_good e E hgood l)) hx
  simpa [hnot]

private theorem pairBlock_subset_quartic {m q : ℕ}
    (e : Fin (2*m) → Fin q) (i j k l r : Fin m)
    (hr : r = i ∨ r = j ∨ r = k ∨ r = l) :
    pairBlock e r ⊆ quarticSupport e i j k l := by
  intro x hx
  simp only [quarticSupport, Finset.mem_union]
  rcases hr with (rfl | rfl | rfl | rfl)
  · exact Or.inl (Or.inl (Or.inl hx))
  · exact Or.inl (Or.inl (Or.inr hx))
  · exact Or.inl (Or.inr hx)
  · exact Or.inr hx

noncomputable def projectedPairFactor (ν : FiniteLaw Z) {m q : ℕ}
    (decode : S → Fin q → Z) (e : Fin (2*m) → Fin q)
    (K : Set S) (J : Finset (Fin q)) (i : Fin m)
    (hi : pairBlock e i ⊆ J) (z : J → Z) : ℝ :=
  (if localPairHit decode e K i
      (fun t => z ⟨t.val, hi t.property⟩) then 1 else 0) -
    pairBaseMass ν decode e K i

private theorem projectedPairFactor_abs_le_one (ν : FiniteLaw Z)
    {m q : ℕ} (decode : S → Fin q → Z)
    (e : Fin (2*m) → Fin q) (K : Set S)
    (J : Finset (Fin q)) (i : Fin m)
    (hi : pairBlock e i ⊆ J) (z : J → Z) :
    |projectedPairFactor ν decode e K J i hi z| ≤ 1 := by
  have hp0 := (ν.iid q).prob_nonneg
    (fun c => pairHit decode e K i c)
  have hp1 := (ν.iid q).prob_le_one
    (fun c => pairHit decode e K i c)
  unfold projectedPairFactor pairBaseMass
  split_ifs <;> apply abs_le.mpr <;> constructor <;> linarith

private theorem projectedPairFactor_restrict (ν : FiniteLaw Z)
    {m q : ℕ} (decode : S → Fin q → Z)
    (e : Fin (2*m) → Fin q) (K : Set S)
    (J : Finset (Fin q)) (i : Fin m)
    (hi : pairBlock e i ⊆ J) (c : Fin q → Z) :
    projectedPairFactor ν decode e K J i hi
      (projection id J c) = centeredPairAmbient ν decode e K i c := by
  unfold projectedPairFactor centeredPairAmbient FourthMoment.centeredPair
  simp only [projection]
  simp only [localPairHit_restrict, id_eq]

private theorem abs_mul_le_one (a b : ℝ)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a * b| ≤ 1 := by
  rw [abs_mul]
  calc
    |a| * |b| ≤ 1 * |b| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
    _ ≤ 1 := by simpa using hb

/-- The exact ordered quartic comparison in `suffix_many_from_moments_1024`.
The four pair tests read at most eight distinct original coordinates, all
outside the exceptional set. The projected statistic is bounded by one. -/
theorem quartic_terms_of_good_projection
    (source : FiniteLaw S) (ν : FiniteLaw Z)
    {m q : ℕ} (decode : S → Fin q → Z)
    (e : Fin (2*m) → Fin q) (K Y : Set S)
    (hY : 0 < source.prob (· ∈ Y))
    (E : Finset (Fin q)) (ε : ℝ)
    (hgood : ∀ t : Fin (2*m), e t ∉ E)
    (hTV : ∀ J : Finset (Fin q),
      J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV (conditionedIndexedLaw source Y hY)
        ν decode J ≤ ε) :
    ∀ i j k l : Fin m,
      FourthMoment.expect (conditionedIndexedLaw source Y hY)
        (fun s => centeredPairAmbient ν decode e K l (decode s) *
          centeredPairAmbient ν decode e K k (decode s) *
          centeredPairAmbient ν decode e K j (decode s) *
          centeredPairAmbient ν decode e K i (decode s)) ≤
      FourthMoment.expect (ν.iid q)
        (fun c => centeredPairAmbient ν decode e K l c *
          centeredPairAmbient ν decode e K k c *
          centeredPairAmbient ν decode e K j c *
          centeredPairAmbient ν decode e K i c) + 2 * ε := by
  classical
  intro i j k l
  let J := quarticSupport e i j k l
  have hi : pairBlock e i ⊆ J :=
    pairBlock_subset_quartic e i j k l i (Or.inl rfl)
  have hj : pairBlock e j ⊆ J :=
    pairBlock_subset_quartic e i j k l j (Or.inr (Or.inl rfl))
  have hk : pairBlock e k ⊆ J :=
    pairBlock_subset_quartic e i j k l k (Or.inr (Or.inr (Or.inl rfl)))
  have hl : pairBlock e l ⊆ J :=
    pairBlock_subset_quartic e i j k l l (Or.inr (Or.inr (Or.inr rfl)))
  let g : (J → Z) → ℝ := fun z =>
    projectedPairFactor ν decode e K J l hl z *
    projectedPairFactor ν decode e K J k hk z *
    projectedPairFactor ν decode e K J j hj z *
    projectedPairFactor ν decode e K J i hi z
  have hg : ∀ z, |g z| ≤ 1 := by
    intro z
    exact abs_mul_le_one _ _
      (abs_mul_le_one _ _
        (abs_mul_le_one _ _
          (projectedPairFactor_abs_le_one ν decode e K J l hl z)
          (projectedPairFactor_abs_le_one ν decode e K J k hk z))
        (projectedPairFactor_abs_le_one ν decode e K J j hj z))
      (projectedPairFactor_abs_le_one ν decode e K J i hi z)
  have htvJ : projectionTV (conditionedIndexedLaw source Y hY)
      ν decode J ≤ ε :=
    hTV J (quarticSupport_good e E hgood i j k l)
      (quarticSupport_card_le_eight e i j k l)
  have h := projection_expect_abs_le_two
    (conditionedIndexedLaw source Y hY) ν decode J ε htvJ g hg
  have hle := (abs_le.mp h).2
  have hpoint (c : Fin q → Z) :
      g (projection id J c) =
        centeredPairAmbient ν decode e K l c *
        centeredPairAmbient ν decode e K k c *
        centeredPairAmbient ν decode e K j c *
        centeredPairAmbient ν decode e K i c := by
    simp only [g, projectedPairFactor_restrict]
  have hsource (s : S) : g (projection decode J s) =
      centeredPairAmbient ν decode e K l (decode s) *
      centeredPairAmbient ν decode e K k (decode s) *
      centeredPairAmbient ν decode e K j (decode s) *
      centeredPairAmbient ν decode e K i (decode s) := by
    change g (projection id J (decode s)) = _
    exact hpoint (decode s)
  simp_rw [hsource, hpoint] at hle
  linarith

/-- The suffix proof and the conditioning theorem construct the same
conditional law; their two names have identical weights. -/
theorem conditionedIndexedLaw_eq_condition
    (source : FiniteLaw S) (Y : Set S)
    (hY : 0 < source.prob (· ∈ Y)) :
    conditionedIndexedLaw source Y hY =
      condition source (· ∈ Y) hY := by
  classical
  rfl

theorem quartic_terms_of_condition_good_projection
    (source : FiniteLaw S) (ν : FiniteLaw Z)
    {m q : ℕ} (decode : S → Fin q → Z)
    (e : Fin (2*m) → Fin q) (K Y : Set S)
    (hY : 0 < source.prob (· ∈ Y))
    (E : Finset (Fin q)) (ε : ℝ)
    (hgood : ∀ t : Fin (2*m), e t ∉ E)
    (hTV : ∀ J : Finset (Fin q),
      J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV (condition source (· ∈ Y) hY)
        ν decode J ≤ ε) :
    ∀ i j k l : Fin m,
      FourthMoment.expect (conditionedIndexedLaw source Y hY)
        (fun s => centeredPairAmbient ν decode e K l (decode s) *
          centeredPairAmbient ν decode e K k (decode s) *
          centeredPairAmbient ν decode e K j (decode s) *
          centeredPairAmbient ν decode e K i (decode s)) ≤
      FourthMoment.expect (ν.iid q)
        (fun c => centeredPairAmbient ν decode e K l c *
          centeredPairAmbient ν decode e K k c *
          centeredPairAmbient ν decode e K j c *
          centeredPairAmbient ν decode e K i c) + 2 * ε := by
  have h := quartic_terms_of_good_projection source ν decode e K Y hY
    E ε hgood (by
      intro J hsub hcard
      rw [conditionedIndexedLaw_eq_condition source Y hY]
      exact hTV J hsub hcard)
  intro i j k l
  exact h i j k l

#print axioms quartic_terms_of_good_projection
#print axioms quartic_terms_of_condition_good_projection

end CurrentAdditive.SuffixLong
