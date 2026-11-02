import NPCC.Control

/-!
# Dominant blocks at the end of the Alice prefix

Source: Paper 2, frozen `2026-09-22-protocol-labels-v12`, Appendix A,
the paragraph following `cl:separation` (unnumbered obligation U25).

This is the finite counting consequence of the inherited no-waste conclusion,
not a replacement for the protocol-order or separation theorem. If every
outer block has at least `T0` rows, there are exactly `q` possible prefix
labels, and `q * T < T0`, the dominant-block map is a permutation. Its
dominant fibres, and hence all prefix fibres, are nonempty.
-/

namespace Paper2.DominantBlocks

open scoped BigOperators
open NPCC

variable {X : Type*} {q T0 T : ℕ}

/-- A block's rows are partitioned by their prefix labels. -/
theorem block_card_eq_sum_labels (R : Finset (Fin q × X))
    (lab : Fin q × X → Fin q) (i : Fin q) :
    (R.filter (fun p => p.1 = i)).card =
      ∑ j : Fin q, (R.filter (fun p => lab p = j ∧ p.1 = i)).card := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := R.filter (fun p => p.1 = i)) (t := (Finset.univ : Finset (Fin q)))
    (f := lab) (by intro a _; exact Finset.mem_univ (lab a))
  simpa [Finset.filter_filter, and_comm, and_left_comm, and_assoc] using h

/-- A missing dominant block would have at most `q * T` rows in total. -/
theorem dominantIndex_surjective (R : Finset (Fin q × X))
    (lab : Fin q × X → Fin q)
    (hEq : IsEquipartitionedGE R Finset.univ T0) (hgap : q * T < T0)
    (hNW : NoWasteConclusion Finset.univ R lab T0 T) :
    Function.Surjective (NPCC.Protocol.dominantIndex Finset.univ R lab hNW) := by
  classical
  intro i
  by_contra hmissing
  have hsmall (j : Fin q) :
      (R.filter (fun p => lab p = j ∧ p.1 = i)).card < T := by
    apply (NPCC.Protocol.dominantIndex_spec Finset.univ R lab hNW j).2.2
      i (Finset.mem_univ i)
    intro heq
    exact hmissing ⟨j, heq.symm⟩
  have hsum :
      (∑ j : Fin q, (R.filter (fun p => lab p = j ∧ p.1 = i)).card) ≤ q * T := by
    calc
      _ ≤ ∑ _j : Fin q, T := Finset.sum_le_sum (fun j _ => (hsmall j).le)
      _ = q * T := by simp
  have hrow := hEq i (Finset.mem_univ i)
  rw [block_card_eq_sum_labels R lab i] at hrow
  omega

/-- Domain and codomain have the same finite cardinality, so surjectivity
also proves distinctness of the dominant blocks. -/
theorem dominantIndex_bijective (R : Finset (Fin q × X))
    (lab : Fin q × X → Fin q)
    (hEq : IsEquipartitionedGE R Finset.univ T0) (hgap : q * T < T0)
    (hNW : NoWasteConclusion Finset.univ R lab T0 T) :
    Function.Bijective (NPCC.Protocol.dominantIndex Finset.univ R lab hNW) := by
  exact (Fintype.bijective_iff_surjective_and_card _).2
    ⟨dominantIndex_surjective R lab hEq hgap hNW, rfl⟩

/-- The actual dominant-block permutation, obtained from the inherited
no-waste witnesses. This definition carries no new lower-bound assumption. -/
noncomputable def dominantBlockEquiv (R : Finset (Fin q × X))
    (lab : Fin q × X → Fin q)
    (hEq : IsEquipartitionedGE R Finset.univ T0) (hgap : q * T < T0)
    (hNW : NoWasteConclusion Finset.univ R lab T0 T) : Fin q ≃ Fin q :=
  Equiv.ofBijective _ (dominantIndex_bijective R lab hEq hgap hNW)

/-- The manuscript's dominant size, small foreign fibres, and nonempty
prefix conclusion, with the bijection made explicit. No assumption that
`q` is positive is needed: at `q = 0` the universal conclusions are empty. -/
theorem exists_dominantBlockEquiv (R : Finset (Fin q × X))
    (lab : Fin q × X → Fin q)
    (hEq : IsEquipartitionedGE R Finset.univ T0) (hgap : q * T < T0)
    (hNW : NoWasteConclusion Finset.univ R lab T0 T) :
    ∃ dom : Fin q ≃ Fin q, ∀ j : Fin q,
      T0 - (q - 1) * T ≤ (R.filter (fun p => lab p = j ∧ p.1 = dom j)).card ∧
      (∀ i : Fin q, i ≠ dom j →
        (R.filter (fun p => lab p = j ∧ p.1 = i)).card < T) ∧
      (R.filter (fun p => lab p = j ∧ p.1 = dom j)).Nonempty ∧
      (R.filter (fun p => lab p = j)).Nonempty := by
  classical
  let dom := dominantBlockEquiv R lab hEq hgap hNW
  refine ⟨dom, ?_⟩
  intro j
  have hspec := NPCC.Protocol.dominantIndex_spec Finset.univ R lab hNW j
  have hlarge :
      T0 - (q - 1) * T ≤ (R.filter (fun p => lab p = j ∧ p.1 = dom j)).card := by
    simpa [dom, dominantBlockEquiv] using hspec.2.1
  have hothers (i : Fin q) (hne : i ≠ dom j) :
      (R.filter (fun p => lab p = j ∧ p.1 = i)).card < T := by
    exact hspec.2.2 i (Finset.mem_univ i) hne
  have hmul : (q - 1) * T ≤ q * T := Nat.mul_le_mul_right T (Nat.sub_le q 1)
  have hpos : 0 < T0 - (q - 1) * T := Nat.sub_pos_of_lt (lt_of_le_of_lt hmul hgap)
  have hne : (R.filter (fun p => lab p = j ∧ p.1 = dom j)).Nonempty :=
    Finset.card_pos.mp (lt_of_lt_of_le hpos hlarge)
  refine ⟨hlarge, hothers, hne, ?_⟩
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.1⟩⟩

end Paper2.DominantBlocks
