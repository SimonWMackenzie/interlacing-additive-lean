import Paper2.SourceProtocolPrefixTree
import Paper2.SourceProjectionProtected
import Paper2.RationalSeparationDescent

/-!
# The actual common prefix of a retained source protocol

Frozen v12 Section 4, `src:near-full`, the common-assignment paragraph.
The source protocol is pulled back along literal template rows and literal
fixed-tail tagged columns. This operation preserves every query, including
queries fixed on the retained inputs; no pruning is performed. Separation
and its dominant-bin bijection then force the entire binary Alice prefix
in the original protocol, not only on a replacement matrix.
-/

namespace Paper2.SourceProtocolPrefix

open Workspace.Types.Protocol Workspace.Types.CommComplexity
open SourceMatrix SourceLawBinding SourceProtocolPrefixTree

variable {A B : Type*}

/-- An ambient row's actual Alice-prefix label. Rows outside the retained
set get a harmless default; all mass statements also require retention. -/
noncomputable def rowCode (W : Set A) (P : Protocol W B Bool) (a : ℕ)
    (x : A) : Fin (2 ^ a) := by
  classical
  exact if hx : x ∈ W then NPCC.Protocol.prefixCodeRaw a P ⟨x, hx⟩
    else NPCC.Protocol.zeroPow2 a

section LiteralPullback

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  {q₁ q₂ a : ℕ}

noncomputable def retainedTemplates
    (W : Set (RawRow q₁ q₂ (2 ^ a) X I)) :
    Finset (Fin (2 ^ a) × Template q₁ q₂ X) := by
  classical
  exact (Sum.inl ⁻¹' W).toFinset

noncomputable def retainedFixedTail
    (U : Set (TaggedColumn q₁ q₂ (2 ^ a) Y)) :
    Finset (Fin (2 ^ a) → OuterColumn q₁ q₂ (2 ^ a) Y) := by
  classical
  exact (TaggedColumn.fixedTail ⁻¹' U).toFinset

@[simp] theorem mem_retainedTemplates
    (W : Set (RawRow q₁ q₂ (2 ^ a) X I)) (x : Fin (2 ^ a) × Template q₁ q₂ X) :
    x ∈ retainedTemplates W ↔ Sum.inl x ∈ W := by simp [retainedTemplates]

@[simp] theorem mem_retainedFixedTail
    (U : Set (TaggedColumn q₁ q₂ (2 ^ a) Y))
    (z : Fin (2 ^ a) → OuterColumn q₁ q₂ (2 ^ a) Y) :
    z ∈ retainedFixedTail U ↔ TaggedColumn.fixedTail z ∈ U := by
  simp [retainedFixedTail]

def templateInput (W : Set (RawRow q₁ q₂ (2 ^ a) X I)) :
    {x // x ∈ retainedTemplates W} → W :=
  fun x => ⟨Sum.inl x.val, (mem_retainedTemplates W x.val).mp x.property⟩

def fixedTailInput (U : Set (TaggedColumn q₁ q₂ (2 ^ a) Y)) :
    {z // z ∈ retainedFixedTail U} → U :=
  fun z => ⟨TaggedColumn.fixedTail z.val, (mem_retainedFixedTail U z.val).mp z.property⟩

noncomputable def templateProtocol
    (W : Set (RawRow q₁ q₂ (2 ^ a) X I))
    (U : Set (TaggedColumn q₁ q₂ (2 ^ a) Y)) (P : Protocol W U Bool) :=
  NPCC.Protocol.pullback (templateInput W) (fixedTailInput U) P

theorem templateProtocol_computes
    (F : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin (2 ^ a)))
    (ξ₀ : Tail (2 ^ a) Y)
    (W : Set (RawRow q₁ q₂ (2 ^ a) X I))
    (U : Set (TaggedColumn q₁ q₂ (2 ^ a) Y)) (P : Protocol W U Bool)
    (hP : P.Computes (fun w z => N F activity ξ₀ z.val w.val)) :
    (templateProtocol W U P).Computes
      (NPCC.subgame (fullInterlace (T F) (2 ^ a))
        (retainedTemplates W) (retainedFixedTail U)) := by
  intro x z
  exact (NPCC.Protocol.pullback_eval _ _ P x z).trans (hP _ _)

theorem prefixLabel_templateProtocol
    (W : Set (RawRow q₁ q₂ (2 ^ a) X I))
    (U : Set (TaggedColumn q₁ q₂ (2 ^ a) Y)) (P : Protocol W U Bool)
    (x : Fin (2 ^ a) × Template q₁ q₂ X) :
    NPCC.Protocol.prefixLabelFinQ (retainedTemplates W) (templateProtocol W U P) x =
      rowCode W P a (Sum.inl x) := by
  classical
  by_cases hx : Sum.inl x ∈ W
  · have hx' : x ∈ retainedTemplates W := (mem_retainedTemplates W x).mpr hx
    simp only [NPCC.Protocol.prefixLabelFinQ, dif_pos hx', rowCode, dif_pos hx,
      templateProtocol, PrefixPullback.prefixCodeRaw_pullback]
    rfl
  · have hx' : x ∉ retainedTemplates W := by simpa using hx
    simp only [NPCC.Protocol.prefixLabelFinQ, dif_neg hx', rowCode, dif_neg hx]

end LiteralPullback

section CommonAssignment

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  {q₁ q₂ a : ℕ} [NeZero q₁] [NeZero q₂]

/-- The actual unpruned source protocol has a complete depth-`a` Alice
prefix. Every prefix branch has a distinct dominant bin of template mass
greater than `0.998`, and has at most `D(T)` bits remaining. The supplied
base profile is the independent T13 result; no source lower bound or
source-prefix certificate is an assumption. -/
theorem raw_common_assignment
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin (2 ^ a)))
    (ξ₀ : Tail (2 ^ a) Y) (b : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a)
    (hD : 2 ≤ D (T (q₁ := q₁) (q₂ := q₂) (s := 2 ^ a) F))
    (hprofile : RestrictionProfile (T F) (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
      (SourceLaws.outerLaw ν q₁ q₂ (2 ^ a)).toFiniteLaw
      ((2 : ℝ) ^ (-(b : ℝ))) (D (T (q₁ := q₁) (q₂ := q₂) (s := 2 ^ a) F) : ℤ))
    (hsmall : (2 ^ a : ℝ) * (2 : ℝ) ^ (-(b : ℝ)) ≤ 1 / 10000)
    (W : Set (RawRow q₁ q₂ (2 ^ a) X I))
    (U : Set (TaggedColumn q₁ q₂ (2 ^ a) Y))
    (hW : ∀ i, (999 / 1000 : ℝ) ≤ (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob
      (fun t => Sum.inl (i, t) ∈ W))
    (hU : (99 / 100 : ℝ) ≤ (SourceLaws.fixedTailLaw ν q₁ q₂ (2 ^ a)).toFiniteLaw.prob
      (fun z => TaggedColumn.fixedTail z ∈ U))
    (P : Protocol W U Bool)
    (hP : P.Computes (fun w z => N F activity ξ₀ z.val w.val))
    (hcost : P.cost ≤ D (T (q₁ := q₁) (q₂ := q₂) (s := 2 ^ a) F) + a) :
    CompleteAlicePrefix a P ∧
    (∀ j, (NPCC.Protocol.rowSubtreeAtRaw a P j).cost ≤
      D (T (q₁ := q₁) (q₂ := q₂) (s := 2 ^ a) F)) ∧
    ∃ dom : Fin (2 ^ a) ≃ Fin (2 ^ a), ∀ j,
      (998 / 1000 : ℝ) < (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob
        (fun t => Sum.inl (dom j, t) ∈ W ∧ rowCode W P a (Sum.inl (dom j, t)) = j) ∧
      (∀ i, i ≠ dom j → (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob
        (fun t => Sum.inl (i, t) ∈ W ∧ rowCode W P a (Sum.inl (i, t)) = j) <
          2 * (2 : ℝ) ^ (-(b : ℝ))) ∧
      ∃ t, ∃ ht : Sum.inl (dom j, t) ∈ W,
        NPCC.Protocol.prefixCodeRaw a P ⟨Sum.inl (dom j, t), ht⟩ = j := by
  classical
  let PT := templateProtocol W U P
  have hK : (99 / 100 : ℝ) ≤
      ((SourceLaws.outerLaw ν q₁ q₂ (2 ^ a)).toFiniteLaw.iid (2 ^ a)).prob
      (· ∈ retainedFixedTail U) := by
    simpa only [mem_retainedFixedTail, SourceLaws.fixedTailLaw,
      PositiveRationalLaw.toFiniteLaw_iid] using hU
  obtain ⟨hfirst, dom, hdom⟩ := RationalSeparation.rational_separation_manuscript
    (SourceLaws.templateLaw μ q₁ q₂) (SourceLaws.outerLaw ν q₁ q₂ (2 ^ a))
    (T F) b hb hD hprofile a ha (99 / 100) (by norm_num) (by norm_num) hsmall
    (retainedTemplates W) (retainedFixedTail U)
    (by simpa only [mem_retainedTemplates] using hW) hK PT
    (templateProtocol_computes F activity ξ₀ W U P hP)
    (by simpa only [PT, templateProtocol, NPCC.Protocol.pullback_cost] using hcost)
  have hall : ∀ j, ∃ x : {x // x ∈ retainedTemplates W},
      NPCC.Protocol.prefixCodeRaw a PT x = j := by
    intro j
    obtain ⟨x, hx, hj, _⟩ := (hdom j).2.2
    refine ⟨⟨x, hx⟩, ?_⟩
    simpa only [NPCC.Protocol.prefixLabelFinQ, dif_pos hx] using hj
  have hKne : (retainedFixedTail U).Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, Finset.notMem_empty, FiniteLaw.prob_false] at hK
    norm_num at hK
  have hCne : (Finset.univ : Finset {z // z ∈ retainedFixedTail U}).Nonempty := by
    obtain ⟨z, hz⟩ := hKne
    exact ⟨⟨z, hz⟩, Finset.mem_univ _⟩
  have hc : CompleteAlicePrefix a PT :=
    complete_of_firstK_and_all_codes Finset.univ Finset.univ a PT hfirst hCne
      (fun j => by obtain ⟨x, hx⟩ := hall j; exact ⟨x, Finset.mem_univ _, hx⟩)
  have hcP : CompleteAlicePrefix a P :=
    (complete_pullback_iff (templateInput W) (fixedTailInput U) a P).mp hc
  refine ⟨hcP, ?_, dom, ?_⟩
  · intro j
    have := subtree_cost_add_le a P hcP j
    omega
  · intro j
    have hd := hdom j
    refine ⟨?_, ?_, ?_⟩
    · simpa only [PT, mem_retainedTemplates, prefixLabel_templateProtocol] using hd.1
    · intro i hi
      simpa only [PT, mem_retainedTemplates, prefixLabel_templateProtocol] using hd.2.1 i hi
    · obtain ⟨x, hx, hj, hi⟩ := hd.2.2
      have ht : Sum.inl (dom j, x.2) ∈ W := by
        simpa only [mem_retainedTemplates, ← hi] using hx
      refine ⟨x.2, ht, ?_⟩
      have he : rowCode W P a (Sum.inl x) = j := by
        simpa only [PT, prefixLabel_templateProtocol] using hj
      simpa only [← hi, rowCode, dif_pos ((mem_retainedTemplates W x).mp hx)] using he

end CommonAssignment

end Paper2.SourceProtocolPrefix
