import EthInapproximability.ParameterizedNP.FrontierIndexing

/-!
# Unsplit reference routes

This module transcribes the last paragraph of
`clm:paper-global-assignment` in the v8 source `A-stage4-details.tex`.
The reference rows, branching routes, and clean/low history are the actual
finite protocol dynamics from `RoutingDynamics` and `FrontierIndexing`.
No row-loss bound is supplied as a hypothesis.
-/

namespace EthInapproximability.CurrentPaper.ReferenceRouteLoss

open Finset
open Workspace.Types.Protocol
open EthInapproximability.ParameterizedNP.DenseSynchronisation
open EthInapproximability.ParameterizedNP.DenseWeightedCount
open EthInapproximability.ParameterizedNP.DenseWrapperFrontier
open EthInapproximability.ParameterizedNP.RoutedCertificateSystem
open EthInapproximability.ParameterizedNP.RoutingDynamics
open EthInapproximability.ParameterizedNP.FrontierIndexing

variable {X Y Z : Type*} [Fintype X] [DecidableEq X]

/-- Every prefix of a clean route is clean. -/
theorem kindAlong_clean_prefix {P : Protocol X Y Z} {R : Finset X}
    {A0 r : ℕ} {p q : List Bool} (hpq : p <+: q)
    (hq : kindAlong P R A0 r q = CertKind.clean) :
    kindAlong P R A0 r p = CertKind.clean := by
  obtain ⟨s, rfl⟩ := hpq
  induction s using List.reverseRecOn with
  | nil => simpa using hq
  | append_singleton s b ih =>
      exact ih (kindAlong_clean_of_clean (by simpa [List.append_assoc] using hq))

/-- A proper prefix of a clean route cannot have split. -/
theorem not_splitsAt_of_clean_extension {P : Protocol X Y Z} {R : Finset X}
    {A0 r : ℕ} {p q : List Bool} {b : Bool} (hpq : p ++ [b] <+: q)
    (hq : kindAlong P R A0 r q = CertKind.clean) :
    splitsAt P R A0 r p ≠ true := by
  have hc := kindAlong_clean_prefix hpq hq
  rw [kindAlong_append_bit] at hc
  intro hs
  simp [hs] at hc

/-- If a clean descendant exists, no second address is reached by this
coordinate's branching process.  Only one endpoint needs to be clean. -/
theorem descendants_clean_unique (P : Protocol X Y Z) (R : Finset X)
    (A0 r : ℕ) : ∀ (n : ℕ) (p q q' : List Bool),
    q ∈ descendants P R A0 r n p →
    kindAlong P R A0 r q = CertKind.clean →
    q' ∈ descendants P R A0 r n p → q' = q := by
  intro n
  induction n with
  | zero =>
      intro p q q' hq hc hq'
      simpa using (List.mem_singleton.mp hq').trans (List.mem_singleton.mp hq).symm
  | succ n ih =>
      intro p q q' hq hc hq'
      rw [descendants_succ] at hq hq'
      by_cases ha : isANodeB (descend P p) = true ∧ p.length < r
      · rw [if_pos ha] at hq hq'
        by_cases hs : splitsAt P R A0 r p = true
        · rw [if_pos hs, List.mem_append] at hq
          rcases hq with hq | hq
          · exact False.elim ((not_splitsAt_of_clean_extension
              (descendants_prefix P R A0 r n _ _ hq) hc) hs)
          · exact False.elim ((not_splitsAt_of_clean_extension
              (descendants_prefix P R A0 r n _ _ hq) hc) hs)
        · rw [if_neg hs] at hq hq'
          exact ih _ _ _ hq hc hq'
      · rw [if_neg ha, List.mem_singleton] at hq hq'
        exact hq'.trans hq.symm

/-- The child not chosen at an unsplit step fails the actual qualification
threshold.  The row count lost at that step is therefore strictly smaller
than the child floor. -/
theorem unsplit_step_card_lt {P : Protocol X Y Z} {R : Finset X}
    {A0 r : ℕ} {p : List Bool} (ha : IsANode (descend P p))
    (hs : splitsAt P R A0 r p ≠ true) :
    (rowsAt P R p).card <
      (rowsAt P R (p ++ [routeBit P R A0 r p])).card + childFloor A0 r p := by
  have hsum := card_rowsAt_children_add (R := R) ha
  by_cases hf : Qualifies P R A0 r p false
  · have ht : ¬ Qualifies P R A0 r p true := by
      intro ht
      exact hs (splitsAt_eq_true_iff.mpr ⟨hf, ht⟩)
    have hlt : (rowsAt P R (p ++ [true])).card < childFloor A0 r p :=
      Nat.lt_of_not_ge ht
    simp only [routeBit, if_pos hf]
    omega
  · have hlt : (rowsAt P R (p ++ [false])).card < childFloor A0 r p :=
      Nat.lt_of_not_ge hf
    simp only [routeBit, if_neg hf]
    omega

private theorem refRowFloor_eq_twice_child (A0 r : ℕ) (p : List Bool)
    (hp : p.length < r) :
    refRowFloor A0 (r - p.length) = 2 * childFloor A0 r p := by
  have he : r - p.length = (r - p.length - 1) + 1 := by omega
  unfold childFloor refRowFloor
  conv_lhs => rw [he, pow_succ]
  ring

/-- Exact finite accounting along a clean terminal route.  At a nonterminal
starting address the inequality is strict, because the first unchosen child
already fails its threshold strictly. -/
theorem descendants_clean_card_accounting (P : Protocol X Y Z) (R : Finset X)
    (A0 r : ℕ) : ∀ (n : ℕ) (p q : List Bool),
    q ∈ descendants P R A0 r n p →
    kindAlong P R A0 r q = CertKind.clean → q.length = r →
    (rowsAt P R p).card + A0 ≤
      (rowsAt P R q).card + refRowFloor A0 (r - p.length) ∧
    (p.length < r → (rowsAt P R p).card + A0 <
      (rowsAt P R q).card + refRowFloor A0 (r - p.length)) := by
  intro n
  induction n with
  | zero =>
      intro p q hq hc hlen
      have he : q = p := List.mem_singleton.mp hq
      subst q
      simp [hlen, refRowFloor]
  | succ n ih =>
      intro p q hq hc hlen
      rw [descendants_succ] at hq
      by_cases ha : isANodeB (descend P p) = true ∧ p.length < r
      · rw [if_pos ha] at hq
        have hs : splitsAt P R A0 r p ≠ true := by
          intro hs
          rw [if_pos hs, List.mem_append] at hq
          rcases hq with hq | hq
          · exact (not_splitsAt_of_clean_extension
              (descendants_prefix P R A0 r n _ _ hq) hc) hs
          · exact (not_splitsAt_of_clean_extension
              (descendants_prefix P R A0 r n _ _ hq) hc) hs
        rw [if_neg hs] at hq
        have hchild := (ih _ _ hq hc hlen).1
        have hstep := unsplit_step_card_lt (isANodeB_eq_true_iff.mp ha.1) hs
        have hfloor := refRowFloor_eq_twice_child A0 r p ha.2
        have he : refRowFloor A0
            (r - (p ++ [routeBit P R A0 r p]).length) = childFloor A0 r p := by
          unfold childFloor
          congr 1
          simp only [List.length_append, List.length_singleton]
          omega
        rw [he] at hchild
        constructor <;> omega
      · rw [if_neg ha, List.mem_singleton] at hq
        subst q
        simp [hlen, refRowFloor]

/-- Unsplit terminal routes lose fewer than `(2^r - 1) A0` initially
retained rows.  This is derived solely from membership in the routing process;
an initial row-floor assumption is not needed for this upper bound. -/
theorem coordRoutes_clean_loss_lt {Coord : Type} {P : Protocol X Y Z}
    {R : Coord → Finset X} {A0 r : ℕ} {i : Coord} {p : List Bool}
    (hp : p ∈ coordRoutes P R A0 r i)
    (hc : kindAlong P (R i) A0 r p = CertKind.clean)
    (hlen : p.length = r) (hr : 0 < r) :
    ((R i) \ rowsAt P (R i) p).card < (2 ^ r - 1) * A0 := by
  have h := (descendants_clean_card_accounting P (R i) A0 r r [] p
    (List.mem_toFinset.mp hp) hc hlen).2 (by simpa using hr)
  simp only [rowsAt_nil, List.length_nil, Nat.sub_zero, refRowFloor] at h
  have hcard := Finset.card_sdiff_add_card_eq_card (rowsAt_subset P (R i) p)
  have hpow : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by omega)
  have hmul : (2 ^ r - 1) * A0 + A0 = 2 ^ r * A0 := by
    calc
      (2 ^ r - 1) * A0 + A0 = ((2 ^ r - 1) + 1) * A0 := by ring
      _ = 2 ^ r * A0 := by rw [Nat.sub_add_cancel hpow]
  omega

/-- The terminal node assigned to a clean coordinate is unique. -/
theorem coordRoutes_clean_unique {Coord : Type} {P : Protocol X Y Z}
    {R : Coord → Finset X} {A0 r : ℕ} {i : Coord} {p q : List Bool}
    (hp : p ∈ coordRoutes P R A0 r i)
    (hc : kindAlong P (R i) A0 r p = CertKind.clean)
    (hq : q ∈ coordRoutes P R A0 r i) : q = p :=
  descendants_clean_unique P (R i) A0 r r [] p q
    (List.mem_toFinset.mp hp) hc (List.mem_toFinset.mp hq)

/-- A nonempty legal initial support reaches a clean terminal node, so the
strict loss theorem is not only a statement about impossible clean routes. -/
theorem clean_terminal_route_regression :
    let P := aliceLadder (X := Bool) (Y := Bool) (fun _ => true) true 1
    let R : Unit → Finset Bool := fun _ => Finset.univ
    refRowFloor 1 1 ≤ (R ()).card ∧
    [true] ∈ coordRoutes P R 1 1 () ∧
    kindAlong P (R ()) 1 1 [true] = CertKind.clean ∧
    ((R ()) \ rowsAt P (R ()) [true]).card < (2 ^ 1 - 1) * 1 := by
  decide

end EthInapproximability.CurrentPaper.ReferenceRouteLoss
