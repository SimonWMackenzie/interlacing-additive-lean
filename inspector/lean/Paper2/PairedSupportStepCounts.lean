import Paper2.PairedSupportStep

/-!
# Exact counts when independently heavy paired supports separate

Frozen v12, Section 5, `res:paired`. Both tags of a separated pair remain
active. Thus splitting one pair raises the primary count by one and lowers
the paired count by one; it does not discard the foreign member.
-/

namespace Paper2.PairedSupportStep

variable {I W : Type*}

theorem primary_subset_active (S : Finset (Bool × I)) (P : Finset I) :
    primary S P ⊆ active S P := by
  intro a ha
  rcases (mem_primary S P a).mp ha with ha | ⟨_, ha⟩
  · exact (mem_active S P a).mpr (Or.inl ha)
  · exact (mem_active S P a).mpr (Or.inr ha)

theorem primary_card (S : Finset (Bool × I)) (P : Finset I)
    (hv : Valid S P) : (primary S P).card = S.card + P.card := by
  classical
  have hd : Disjoint S (P.image (fun i => (false, i))) := by
    apply Finset.disjoint_left.mpr
    intro a ha hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact hv i hi false ha
  rw [primary, Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective]
  intro i j h
  exact congrArg Prod.snd h

theorem active_card (S : Finset (Bool × I)) (P : Finset I)
    (hv : Valid S P) : (active S P).card = S.card + P.card + P.card := by
  classical
  have hd : Disjoint S (pairBlocks P) := by
    apply Finset.disjoint_left.mpr
    intro a ha hp
    exact hv a.2 ((mem_pairBlocks P a).mp hp) a.1 ha
  rw [active, Finset.card_union_of_disjoint hd]
  simp [pairBlocks, Finset.card_product, two_mul, Nat.add_assoc]

variable [Fintype W]

theorem child_active_eq_filter (μ : FiniteLaw W)
    (S : Finset (Bool × I)) (P : Finset I)
    (F : (Bool × I) → Finset W) (query : (Bool × I) → W → Bool)
    (b : Bool) :
    active (childSingles μ S P F query b) (childPairs μ P F query b) =
      (active S P).filter (fun a => choice μ F query a = b) := by
  classical
  ext a
  simp only [child_active_iff, Finset.mem_filter]

theorem child_active_card_sum (μ : FiniteLaw W)
    (S : Finset (Bool × I)) (P : Finset I)
    (F : (Bool × I) → Finset W) (query : (Bool × I) → W → Bool) :
    (active (childSingles μ S P F query false) (childPairs μ P F query false)).card +
      (active (childSingles μ S P F query true) (childPairs μ P F query true)).card =
        (active S P).card := by
  classical
  rw [child_active_eq_filter, child_active_eq_filter]
  have hb : (active S P).filter (fun a => choice μ F query a = true) =
      (active S P).filter (fun a => ¬ choice μ F query a = false) := by
    ext a
    cases choice μ F query a <;> simp
  rw [hb]
  exact Finset.card_filter_add_card_filter_not _

theorem z_conservation (μ : FiniteLaw W) (P : Finset I)
    (F : (Bool × I) → Finset W) (query : (Bool × I) → W → Bool) :
    (childPairs μ P F query false).card + (childPairs μ P F query true).card +
      (splitPairs μ P F query).card = P.card := by
  classical
  have hd : Disjoint (childPairs μ P F query false) (childPairs μ P F query true) := by
    apply Finset.disjoint_left.mpr
    intro i h0 h1
    have h0' := ((mem_childPairs μ P F query false i).mp h0).2.1
    have h1' := ((mem_childPairs μ P F query true i).mp h1).2.1
    exact Bool.false_ne_true (h0'.symm.trans h1')
  have hu : childPairs μ P F query false ∪ childPairs μ P F query true =
      P.filter (fun i => ¬ choice μ F query (false, i) ≠ choice μ F query (true, i)) := by
    ext i
    cases h0 : choice μ F query (false, i) <;>
      cases h1 : choice μ F query (true, i) <;> simp [h0, h1]
  rw [← Finset.card_union_of_disjoint hd, hu]
  have h := Finset.card_filter_add_card_filter_not (s := P)
    (fun i => choice μ F query (false, i) ≠ choice μ F query (true, i))
  change _ + (P.filter _).card = P.card
  omega

theorem h_conservation (μ : FiniteLaw W)
    (S : Finset (Bool × I)) (P : Finset I)
    (F : (Bool × I) → Finset W) (query : (Bool × I) → W → Bool)
    (hValid : Valid S P) :
    ((childSingles μ S P F query false).card + (childPairs μ P F query false).card) +
      ((childSingles μ S P F query true).card + (childPairs μ P F query true).card) =
        S.card + P.card + (splitPairs μ P F query).card := by
  have ha := child_active_card_sum μ S P F query
  rw [active_card _ _ (child_valid μ S P F query false hValid),
    active_card _ _ (child_valid μ S P F query true hValid),
    active_card S P hValid] at ha
  have hz := z_conservation μ P F query
  omega

end Paper2.PairedSupportStep
