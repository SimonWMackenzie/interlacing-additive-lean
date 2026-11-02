import CurrentAdditive.DeterministicIndexedProfileEntries
import Paper2.SourceProjection

/-!
Actual ordinary-column projection for v27 `det:profiles`, `det:near-full`,
and `det:two-stream`.  The ordinary column is a complete outer-source
index together with an independent tail index.  Selected bin coordinates
have their prescribed joint law only up to the source degree D.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.FiniteLaw Paper2.SourceMatrix
open Workspace.Types.CommComplexity

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- Projection onto a set of selected *original* ordinary-bin coordinates.
The tail index is forgotten, but the source index `js` stays an input. -/
def ordinarySelected (C : Finset (Fin s))
    (z : src.outer.Label × src.gamma.Label) : C → J src :=
  fun p => src.outer.decode z.1 p.val

/-- The independent tail makes the ordinary source's first marginal exactly
the indexed outer-source law, for every event on its complete index. -/
theorem ordinary_first_marginal (E : src.outer.Label → Prop) :
    (ordinaryLaw src).toFiniteLaw.prob (fun z => E z.1) =
      src.outer.law.toFiniteLaw.prob E := by
  rw [ordinaryLaw, PositiveRationalLaw.toFiniteLaw_prod]
  rw [FiniteLaw.prod_prob _ _ (fun js _ => E js)]
  unfold FiniteLaw.prob
  apply Finset.sum_congr rfl
  intro js _
  by_cases h : E js
  · simp [h, src.gamma.law.toFiniteLaw.total]
  · simp [h]

/-- Selected distinct bin images are an exact joint product marginal under
the original ordinary law. This uses `src.outer.exactLaw` and has no claim
about the law after columns have been retained. -/
theorem ordinary_selected_pushes
    (C : Finset (Fin s)) (hC : C.card ≤ D) :
    (ordinaryLaw src).toFiniteLaw.PushesTo
      (FiniteLaw.pi (fun _ : C =>
        ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw))
      (ordinarySelected src C) := by
  intro E
  calc
    (ordinaryLaw src).toFiniteLaw.prob
        (fun z => E (ordinarySelected src C z)) =
      src.outer.law.toFiniteLaw.prob
        (fun js => E (fun p : C => src.outer.decode js p.val)) :=
      (by
        have h := ordinary_first_marginal src
          (fun js => E (fun p : C => src.outer.decode js p.val))
        simpa only [ordinarySelected] using h)
    _ = (FiniteLaw.pi (fun _ : C =>
          ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw)).prob E :=
      src.outer.exactLaw C hC E

/-- For any arbitrarily correlated retained ordinary event, its selected
image consists of actual surviving labels and has at least its original
ordinary-source mass under the ambient product marginal. -/
theorem ordinary_selected_image_mass
    (C : Finset (Fin s)) (hC : C.card ≤ D)
    (K : Set (src.outer.Label × src.gamma.Label)) :
    (ordinaryLaw src).toFiniteLaw.prob (· ∈ K) ≤
      (FiniteLaw.pi (fun _ : C =>
        ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw)).prob
        (· ∈ ordinarySelected src C '' K) := by
  exact FiniteLaw.prob_le_image _ _ _ (ordinary_selected_pushes src C hC) K

/-- The selected full interlace of the literal generated `T` is an actual
restriction of the generated `Nref` on surviving ordinary labels. The
representative ordinary label chosen for a projected word is shared by
all rows. -/
theorem selected_ordinary_cost_le
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) {n : ℕ} (e : Fin n → Fin s)
    (Rows : Set (Row (I := I) src))
    (Cols : Set (src.outer.Label × src.gamma.Label))
    (S : Set (Fin n × src.inner.Label))
    (hrows : ∀ a ∈ S, Sum.inl (e a.1, a.2) ∈ Rows) :
    Paper2.Compression.restrictionD
        (Paper2.fullInterlace (fun z j => T src R z j) n) S
        ((fun c i => src.outer.decode c.1 (e i)) '' Cols) ≤
      Paper2.Compression.restrictionD
        (fun r c => Nref src R activity ξ₀ c r) Rows Cols := by
  exact Paper2.SourceProjection.restrictionD_projected_le
    (fun r c => Nref src R activity ξ₀ c r)
    (Paper2.fullInterlace (fun z j => T src R z j) n)
    (fun a : Fin n × src.inner.Label => Sum.inl (e a.1, a.2))
    (fun c i => src.outer.decode c.1 (e i))
    Rows Cols S hrows (by intro a ha c hc; rfl)

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinary_selected_pushes
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinary_selected_image_mass
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.selected_ordinary_cost_le
