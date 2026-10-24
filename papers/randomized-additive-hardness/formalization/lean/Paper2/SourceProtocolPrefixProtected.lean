import Paper2.SourceProtocolPrefixResidual

/-!
# Protected-mass entry to the source's actual common prefix

Frozen v12 Section 4, `src:near-full`. This adapter starts with a protocol
on the retained, graph-constructed matrix `N`. It derives the template-bin
and fixed-tail masses from the two source mixture laws, transposes the
actual protocol, and applies separation without pruning its query tree.
-/

namespace Paper2.SourceProtocolPrefix

open Workspace.Types.Protocol Workspace.Types.CommComplexity
open SourceMatrix SourceLawBinding SourceProtocolPrefixTree

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y] {q₁ q₂ a : ℕ} [NeZero q₁] [NeZero q₂]

/-- These are the precise protected-mass guards used by the common-
assignment argument. They are derived from retained source masses, not
provided as retained-input or protocol-control certificates. -/
theorem common_assignment_masses
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y) (hs : 4 ≤ 2 ^ a)
    (W : Set (RawRow q₁ q₂ (2 ^ a) X (SourceConstruction.Items (2 ^ a) V)))
    (U : Set (TaggedColumn q₁ q₂ (2 ^ a) Y)) (η : ℝ)
    (hW : 1 - η ≤ (matrixColumnLaw μ q₁ q₂ (2 ^ a) hs).toFiniteLaw.prob (· ∈ W))
    (hU : 1 - η ≤ (matrixRowLaw ν q₁ q₂ (2 ^ a)).toFiniteLaw.prob (· ∈ U))
    (hηW : η * (2 ^ a : ℝ) / (255 / 256 : ℝ) ≤ 1 / 1000)
    (hηU : 256 * η ≤ 1 / 100) :
    (∀ i, (999 / 1000 : ℝ) ≤ (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob
      (fun t => Sum.inl (i, t) ∈ W)) ∧
    (99 / 100 : ℝ) ≤ (SourceLaws.fixedTailLaw ν q₁ q₂ (2 ^ a)).toFiniteLaw.prob
      (fun z => TaggedColumn.fixedTail z ∈ U) := by
  constructor
  · intro i
    have hh := SourceProjectionRetention.template_bin_retained μ hs (· ∈ W) η hW i
    simp only [Nat.cast_pow, Nat.cast_ofNat] at hh
    linarith
  · have hh := SourceProjectionRetention.fixed_tail_rows_retained ν (· ∈ U) η hU
    linarith

/-- The common assignment for the actual graph-constructed retained N
protocol. The original N orientation is transposed exactly once. The
returned branch labels are actual transcript labels, chosen before any
coordinate or witness. There is no NO-source lower-bound assumption.

The independent T13 profile and its actual cost remain explicit premises
until the source-parameter owner instantiates them. The two schedule
inequalities displayed here are the only extra retained-mass guards. -/
theorem actual_common_assignment
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (order : SourceConstruction.Items (2 ^ a) V ≃
      Fin (Fintype.card (SourceConstruction.Items (2 ^ a) V)))
    (edge : E → Bool → V) (hs : 4 ≤ 2 ^ a) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * 2 ^ a)) E * r)
    (F : X → Y → Bool) (ξ₀ : Tail (2 ^ a) Y) (b : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a)
    (hD : 2 ≤ D (T (q₁ := q₁) (q₂ := q₂) (s := 2 ^ a) F))
    (hprofile : RestrictionProfile (T F) (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
      (SourceLaws.outerLaw ν q₁ q₂ (2 ^ a)).toFiniteLaw
      ((2 : ℝ) ^ (-(b : ℝ))) (D (T (q₁ := q₁) (q₂ := q₂) (s := 2 ^ a) F) : ℤ))
    (hsmall : (2 ^ a : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) ≤ 1 / 10000)
    (W : Set (RawRow q₁ q₂ (2 ^ a) X (SourceConstruction.Items (2 ^ a) V)))
    (U : Set (TaggedColumn q₁ q₂ (2 ^ a) Y)) (η : ℝ)
    (hW : 1 - η ≤ (matrixColumnLaw μ q₁ q₂ (2 ^ a) hs).toFiniteLaw.prob (· ∈ W))
    (hU : 1 - η ≤ (matrixRowLaw ν q₁ q₂ (2 ^ a)).toFiniteLaw.prob (· ∈ U))
    (hηW : η * (2 ^ a : ℝ) / (255 / 256 : ℝ) ≤ 1 / 1000)
    (hηU : 256 * η ≤ 1 / 100)
    (P : Protocol U W Bool)
    (hP : P.Computes (fun z w =>
      SourceConstruction.matrix order edge (by omega) r hq F ξ₀ z.val w.val))
    (hcost : P.cost ≤ D (T (q₁ := q₁) (q₂ := q₂) (s := 2 ^ a) F) + a) :
    let Praw := Workspace.UpperBound.Protocol.transpose P
    CompleteAlicePrefix a Praw ∧
    EveryPrefixBranchActive (@Finset.univ W (Fintype.ofFinite W)) a Praw ∧
    (∀ j, (NPCC.Protocol.rowSubtreeAtRaw a Praw j).cost ≤
      D (T (q₁ := q₁) (q₂ := q₂) (s := 2 ^ a) F)) ∧
    ∃ dom : Fin (2 ^ a) ≃ Fin (2 ^ a), ∀ j,
      (998 / 1000 : ℝ) < (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob
        (fun t => Sum.inl (dom j, t) ∈ W ∧ rowCode W Praw a (Sum.inl (dom j, t)) = j) ∧
      (∀ i, i ≠ dom j → (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob
        (fun t => Sum.inl (i, t) ∈ W ∧ rowCode W Praw a (Sum.inl (i, t)) = j) <
          2 * (2 : ℝ) ^ (-(b : ℝ))) ∧
      ∃ t, ∃ ht : Sum.inl (dom j, t) ∈ W,
        NPCC.Protocol.prefixCodeRaw a Praw ⟨Sum.inl (dom j, t), ht⟩ = j := by
  classical
  obtain ⟨hW', hU'⟩ := common_assignment_masses μ ν hs W U η hW hU hηW hηU
  have hraw := raw_common_assignment μ ν F (SourceConstruction.activity order edge (by omega) r hq)
    ξ₀ b hb ha hD hprofile hsmall W U hW' hU'
    (Workspace.UpperBound.Protocol.transpose P)
    (by intro w z; rw [Workspace.UpperBound.Protocol.transpose_eval]; exact hP z w)
    (by simpa only [Workspace.UpperBound.Protocol.transpose_cost] using hcost)
  obtain ⟨hp, hc, dom, hd⟩ := hraw
  refine ⟨hp, ?_, hc, dom, hd⟩
  apply active_branches_of_complete_and_all_codes (@Finset.univ W (Fintype.ofFinite W)) a
    (Workspace.UpperBound.Protocol.transpose P) hp
  intro j
  obtain ⟨t, ht, hj⟩ := (hd j).2.2
  exact ⟨⟨Sum.inl (dom j, t), ht⟩,
    @Finset.mem_univ W (Fintype.ofFinite W) ⟨Sum.inl (dom j, t), ht⟩, hj⟩

end Paper2.SourceProtocolPrefix
