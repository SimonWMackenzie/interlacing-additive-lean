import CurrentAdditive.V39GraphStreamTransfer

/-! Actual surviving full-product columns represent the selected template
selector values. Ignored auxiliary stream values are never visible inputs. -/

namespace CurrentAdditive.V39ActualSelectorRepresentatives

open Paper2 Paper2.SourceMatrix

variable {X V : Type*} [Fintype X] [Fintype V] [Nonempty V]
  {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero s]

abbrev Meta := V39CompleteStreams.Metadata s (Fin (4*s) × V)
  (Fin (4*s) × Fin (s-3))

abbrev ActualWord := Fin w → RawRow q₁ q₂ s X (EdgeSourceMatrix.Items s V)

def sectionDecode (m : Fin w → Meta (V := V) (s := s))
    (b : Fin w → X) (z : Fin w → Template q₁ q₂ X) :
    ActualWord (X := X) (V := V) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w) :=
  V39GraphStreamTransfer.graphDecode (m,(b,z))

def projectedSelector (C : Finset (Fin w × Fin q₂))
    (z : Fin w → Template q₁ q₂ X) : C → Fin q₁ × X :=
  fun c => z c.val.1 c.val.2

/-- From an actual tuple, selected template coordinates recover exactly
the visible selector values. A default is used only outside template rows. -/
def actualProjection (j₀ : Fin q₁ × X) (C : Finset (Fin w × Fin q₂))
    (a : ActualWord (X := X) (V := V) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)) :
    C → Fin q₁ × X :=
  fun c => match a c.val.1 with
    | .inl (_,z) => z c.val.2
    | .inr _ => j₀

theorem actualProjection_sectionDecode
    (j₀ : Fin q₁ × X) (C : Finset (Fin w × Fin q₂))
    (m : Fin w → Meta (V := V) (s := s)) (b : Fin w → X)
    (htemplate : ∀ c : C, ∃ p : Fin s, m c.val.1 = .inl p)
    (z : Fin w → Template q₁ q₂ X) :
    actualProjection j₀ C (sectionDecode m b z) = projectedSelector C z := by
  funext c
  obtain ⟨p,hp⟩ := htemplate c
  simp [actualProjection,sectionDecode,V39GraphStreamTransfer.graphDecode,
    V39CompleteStreams.decode,V39CompleteStreams.decodeTriple,hp,
    SourceLawBinding.rawRowEquiv,projectedSelector]

/-- Choose one surviving actual tuple per selected projected selector
value. The choice depends on that value, never on the protocol's row input.
Distinct selected values have distinct actual tuple representatives. -/
theorem actual_representatives
    (j₀ : Fin q₁ × X) (C : Finset (Fin w × Fin q₂))
    (m : Fin w → Meta (V := V) (s := s)) (b : Fin w → X)
    (htemplate : ∀ c : C, ∃ p : Fin s, m c.val.1 = .inl p)
    (Y : Set (ActualWord (X := X) (V := V) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (K : Set (Fin w → Template q₁ q₂ X))
    (hK : ∀ z ∈ K, sectionDecode m b z ∈ Y) :
    ∃ rep : (projectedSelector C '' K) → Y,
      Function.Injective rep ∧
      ∀ v, actualProjection j₀ C (rep v).val = v.val := by
  classical
  let r := SourceProjection.representative (projectedSelector (X := X) C) K
  let rep : (projectedSelector (X := X) C '' K) → Y :=
    fun v => ⟨sectionDecode m b (r v).val,hK _ (r v).property⟩
  have hr (v : projectedSelector (X := X) C '' K) :
      actualProjection j₀ C (rep v).val = v.val := by
    change actualProjection j₀ C (sectionDecode m b (r v).val) = v.val
    rw [actualProjection_sectionDecode j₀ C m b htemplate]
    exact SourceProjection.representative_maps (projectedSelector (X := X) C) K v
  refine ⟨rep,?_,hr⟩
  intro u v huv
  apply Subtype.ext
  rw [← hr u,← hr v,huv]

end CurrentAdditive.V39ActualSelectorRepresentatives

#print axioms CurrentAdditive.V39ActualSelectorRepresentatives.actualProjection_sectionDecode
#print axioms CurrentAdditive.V39ActualSelectorRepresentatives.actual_representatives
