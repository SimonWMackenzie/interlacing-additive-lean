import Paper2.FiniteSampling
import Workspace.ProofLemmas.SublemmaPrecompNoIncrease

/-!
Private v27 deterministic-appendix probe. Source:
`appendices/H-deterministic-core.tex`, equation `det:projection-mass`
in "Small projections are actual protocol restrictions".

This isolates the probability step after a good-coordinate marginal estimate:
the ambient mass of the *actual image* of a retained event is at least its
conditional mass, minus the stated total-variation error. No independence
of the retained event is assumed.
-/

namespace CurrentAdditive.ProjectionMass

open Paper2

variable {S T : Type*} [Fintype S] [Fintype T]

/-- The labels actually attained by the retained source indices. -/
def imageEvent (decode : S → T) (K : S → Prop) (t : T) : Prop :=
  ∃ s, K s ∧ decode s = t

/-- Source equation `det:projection-mass`: good conditional marginals bound
the ambient mass of the projection of any retained set. The total-variation
premise is stated eventwise, so it applies to the image event itself. -/
theorem ambient_image_mass_ge_conditional_mass_sub
    (source : FiniteLaw S) (ambient : FiniteLaw T)
    (decode : S → T) (Y K : S → Prop) (ε : ℝ)
    (hY : 0 < source.prob Y)
    (hK : ∀ s, K s → Y s)
    (hgood : ∀ P : T → Prop,
      |source.prob (fun s => Y s ∧ P (decode s)) / source.prob Y -
        ambient.prob P| ≤ ε) :
    source.prob K / source.prob Y - ε ≤
      ambient.prob (imageEvent decode K) := by
  let P : T → Prop := imageEvent decode K
  have hsubset : ∀ s, K s → Y s ∧ P (decode s) := by
    intro s hs
    exact ⟨hK s hs, s, hs, rfl⟩
  have hmono : source.prob K ≤
      source.prob (fun s => Y s ∧ P (decode s)) :=
    source.prob_mono hsubset
  have hdiv : source.prob K / source.prob Y ≤
      source.prob (fun s => Y s ∧ P (decode s)) / source.prob Y := by
    exact div_le_div_of_nonneg_right hmono hY.le
  have htail := (abs_le.mp (hgood P)).2
  dsimp [P] at htail ⊢
  linarith

/-- Select one original retained index for each value in the decoded image.
This choice is used only to restrict a protocol; the source construction
still retains all indexed labels and their original weights. -/
noncomputable def representative (decode : S → T) (K : S → Prop) :
    {t : T // imageEvent decode K t} → {s : S // K s} := by
  intro t
  let s := Classical.choose t.property
  exact ⟨s, (Classical.choose_spec t.property).1⟩

omit [Fintype S] [Fintype T] in
theorem representative_decodes (decode : S → T) (K : S → Prop)
    (t : {t : T // imageEvent decode K t}) :
    decode (representative decode K t).val = t.val := by
  exact (Classical.choose_spec t.property).2

omit [Fintype S] [Fintype T] in
/-- The matrix on actual retained indices contains the matrix on projected
labels as a restriction. Consequently every lower bound for the latter is a
lower bound for the former, for arbitrary row restrictions. -/
theorem projected_cost_le_indexed_cost {X : Type*} [Fintype X]
    (F : X → T → Bool) (decode : S → T)
    (R : X → Prop) (K : S → Prop)
    [Fintype {x : X // R x}] [Fintype {s : S // K s}]
    [Fintype {t : T // imageEvent decode K t}] :
    Workspace.Types.CommComplexity.D
        (fun (x : {x : X // R x}) (t : {t : T // imageEvent decode K t}) =>
          F x.val t.val) ≤
      Workspace.Types.CommComplexity.D
        (fun (x : {x : X // R x}) (s : {s : S // K s}) =>
          F x.val (decode s.val)) := by
  classical
  have h := Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (fun (x : {x : X // R x}) (s : {s : S // K s}) =>
      F x.val (decode s.val))
    (id : {x : X // R x} → {x : X // R x})
    (representative decode K)
  simpa only [id_eq, representative_decodes] using h

omit [Fintype S] in
/-- The preceding restriction statement for the literal indexed-interlace
entry rule. The row predicate may retain a different set of base rows in
each block. Duplicate decoded columns remain distinct on the right. -/
theorem projected_interlace_cost_le_indexed
    {X Z : Type*} [Fintype X] [Fintype Z]
    {q : ℕ} (F : X → Z → Bool) (decode : S → Fin q → Z)
    (R : (Fin q × X) → Prop) (K : S → Prop)
    [Fintype {r : Fin q × X // R r}]
    [Fintype {s : S // K s}]
    [Fintype {t : Fin q → Z // imageEvent decode K t}] :
    Workspace.Types.CommComplexity.D
        (fun (r : {r : Fin q × X // R r})
             (t : {t : Fin q → Z // imageEvent decode K t}) =>
          F r.val.2 (t.val r.val.1)) ≤
      Workspace.Types.CommComplexity.D
        (fun (r : {r : Fin q × X // R r})
             (s : {s : S // K s}) =>
          F r.val.2 (decode s.val r.val.1)) := by
  exact projected_cost_le_indexed_cost
    (fun a z => F a.2 (z a.1)) decode R K

#print axioms ambient_image_mass_ge_conditional_mass_sub
#print axioms projected_cost_le_indexed_cost
#print axioms projected_interlace_cost_le_indexed

end CurrentAdditive.ProjectionMass
