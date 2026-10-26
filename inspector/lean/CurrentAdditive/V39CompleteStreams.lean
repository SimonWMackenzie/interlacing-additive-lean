import CurrentAdditive.IndependentStreams
import Paper2.SourceLawBinding
import Paper2.SourceProjection

/-! v39 robustness.tex:329--348. Complete auxiliary streams for the actual
full-product K alphabet. This does not enlarge that alphabet. -/

namespace CurrentAdditive.V39CompleteStreams

open Paper2 Paper2.SourceMatrix
open scoped BigOperators

section General

variable {A B C Z : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype Z]

def tripleEquiv (w : ℕ) :
    ((Fin w → A) × ((Fin w → B) × (Fin w → C))) ≃
      (Fin w → A × (B × C)) where
  toFun a i := (a.1 i, (a.2.1 i, a.2.2 i))
  invFun a := (fun i => (a i).1, (fun i => (a i).2.1, fun i => (a i).2.2))
  left_inv a := by cases a; rfl
  right_inv a := by funext i; rfl

/-- Regrouping three independent complete streams gives the full product
of independent triples, including arbitrary whole-tuple events. -/
theorem triple_iid_pushes (α : PositiveRationalLaw A)
    (β : PositiveRationalLaw B) (γ : PositiveRationalLaw C) (w : ℕ) :
    ((α.iid w).prod ((β.iid w).prod (γ.iid w))).toFiniteLaw.PushesTo
      ((α.prod (β.prod γ)).iid w).toFiniteLaw (tripleEquiv w) := by
  classical
  intro E
  unfold FiniteLaw.prob
  apply Fintype.sum_equiv (tripleEquiv w)
  intro a
  have hw :
      (((α.iid w).prod ((β.iid w).prod (γ.iid w))).weight a : ℝ) =
      (((α.prod (β.prod γ)).iid w).weight (tripleEquiv w a) : ℝ) := by
    simp [PositiveRationalLaw.prod, PositiveRationalLaw.iid, tripleEquiv,
      Finset.prod_mul_distrib]
  change (if E (tripleEquiv w a) then _ else 0) =
    (if E (tripleEquiv w a) then _ else 0)
  simpa only [PositiveRationalLaw.toFiniteLaw] using
    congrArg (fun t : ℝ => if E (tripleEquiv w a) then t else 0) hw

theorem iid_map_pushes (α : PositiveRationalLaw A)
    (β : PositiveRationalLaw B) (f : A → B)
    (hf : α.toFiniteLaw.PushesTo β.toFiniteLaw f) (w : ℕ) :
    (α.iid w).toFiniteLaw.PushesTo (β.iid w).toFiniteLaw
      (fun a i => f (a i)) := by
  classical
  intro E
  apply FiniteLaw.prob_preimage_eq_of_fibres
  intro y
  have hev : (fun a : Fin w → A => (fun i => f (a i)) = y) =
      (fun a => ∀ i, f (a i) = y i) := by
    funext a
    exact propext funext_iff
  rw [hev, PositiveRationalLaw.toFiniteLaw_iid]
  rw [FiniteLaw.iid_prob_coordinatewise α.toFiniteLaw w
    (fun i a => f a = y i)]
  change (∏ i, α.toFiniteLaw.prob (fun a => f a = y i)) = _
  have hweight (i : Fin w) : α.toFiniteLaw.prob (fun a => f a = y i) =
      β.toFiniteLaw.weight (y i) := by
    rw [hf (fun b => b = y i), FiniteLaw.prob_singleton]
  simp_rw [hweight]
  simp [PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.iid,
    FiniteLaw.iid]

/-- Whole metadata and base streams are fixed before the retained selector
section is conditioned. The ambient selector law is unchanged. -/
theorem fixed_complete_streams (α : PositiveRationalLaw A)
    (β : PositiveRationalLaw B) (γ : PositiveRationalLaw C)
    (a : A) (b : B) (E : C → Prop) :
    (α.prod (β.prod γ)).toFiniteLaw.prob
        (fun z => z.1 = a ∧ z.2.1 = b ∧ E z.2.2) /
      (α.prod (β.prod γ)).toFiniteLaw.prob
        (fun z => z.1 = a ∧ z.2.1 = b) = γ.toFiniteLaw.prob E := by
  rw [PositiveRationalLaw.toFiniteLaw_prod,
    PositiveRationalLaw.toFiniteLaw_prod]
  rw [FiniteLaw.prod_prob_fixed_fst α.toFiniteLaw
      (β.toFiniteLaw.prod γ.toFiniteLaw) a (fun t => t.1 = b ∧ E t.2),
    FiniteLaw.prod_prob_fixed_fst β.toFiniteLaw γ.toFiniteLaw b E,
    FiniteLaw.prod_prob_fixed_fst α.toFiniteLaw
      (β.toFiniteLaw.prod γ.toFiniteLaw) a (fun t => t.1 = b)]
  have hb : (β.toFiniteLaw.prod γ.toFiniteLaw).prob
      (fun z => z.1 = b) = β.toFiniteLaw.weight b := by
    simpa using FiniteLaw.prod_prob_fixed_fst β.toFiniteLaw γ.toFiniteLaw b
      (fun _ => True)
  rw [hb]
  have ha : α.toFiniteLaw.weight a ≠ 0 := by
    change (α.weight a : ℝ) ≠ 0
    exact_mod_cast ne_of_gt (α.positive a)
  have hb' : β.toFiniteLaw.weight b ≠ 0 := by
    change (β.weight b : ℝ) ≠ 0
    exact_mod_cast ne_of_gt (β.positive b)
  field_simp

end General

section Source

variable {X V A : Type*} [Fintype X] [Fintype V] [Fintype A]
  [Nonempty V] [Nonempty A] {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero s]

abbrev Metadata (s : ℕ) (V A : Type*) := Fin s ⊕ (V ⊕ A)

/-- The metadata has the literal 255/256, 1/512, 1/512 source masses. -/
noncomputable def metadataLaw : PositiveRationalLaw (Metadata s V A) where
  weight
    | .inl p => (255/256) * (PositiveRationalLaw.uniform (Fin s)).weight p
    | .inr (.inl v) => (1/512) * (PositiveRationalLaw.uniform V).weight v
    | .inr (.inr a) => (1/512) * (PositiveRationalLaw.uniform A).weight a
  positive a := by
    rcases a with p | (v | a) <;>
      exact mul_pos (by norm_num) (PositiveRationalLaw.uniform _ |>.positive _)
  total := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [← Finset.mul_sum, PositiveRationalLaw.total, mul_one]
    norm_num

def decodeTriple : Metadata s V A × (X × Template q₁ q₂ X) →
    RawRow q₁ q₂ s X (V ⊕ A)
  | (.inl p, _, z) => .inl (p,z)
  | (.inr i, u, _) => .inr (i,u)

/-- One complete metadata/base/selector triple decodes with exactly the
actual raw K law; ignored values are integrated out. -/
theorem decode_triple_pushes (μ : PositiveRationalLaw X) :
    ((metadataLaw (s := s) (V := V) (A := A)).prod
      (μ.prod (SourceLaws.templateLaw μ q₁ q₂))).toFiniteLaw.PushesTo
      (SourceLaws.rowLaw (V := V) (A := A) μ q₁ q₂ s).toFiniteLaw decodeTriple := by
  classical
  intro E
  apply FiniteLaw.prob_preimage_eq_of_fibres
  intro k
  rw [PositiveRationalLaw.toFiniteLaw_prod, PositiveRationalLaw.toFiniteLaw_prod]
  rcases k with ⟨p,z⟩ | ⟨v | a,u⟩
  · have he : (fun t : Metadata s V A × (X × Template q₁ q₂ X) =>
        decodeTriple t = Sum.inl (p,z)) =
        (fun t => t.1 = Sum.inl p ∧ t.2.2 = z) := by
      funext t
      rcases t with ⟨m,u,z'⟩
      rcases m with p' | (v | a) <;> simp [decodeTriple, Prod.mk.injEq]
    rw [he, FiniteLaw.prod_prob_fixed_fst
      (metadataLaw (s := s) (V := V) (A := A)).toFiniteLaw
      (μ.toFiniteLaw.prod (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw)
      (.inl p) (fun t => t.2 = z),
      FiniteLaw.prod_prob_snd μ.toFiniteLaw
        (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw (fun zz => zz = z),
      FiniteLaw.prob_singleton]
    simp [PositiveRationalLaw.toFiniteLaw, metadataLaw, SourceLaws.rowLaw,
      SourceLaws.templateRowLaw, PositiveRationalLaw.prod]
    ring
  · have he : (fun t : Metadata s V A × (X × Template q₁ q₂ X) =>
        decodeTriple t = Sum.inr (Sum.inl v,u)) =
        (fun t => t.1 = Sum.inr (Sum.inl v) ∧ t.2.1 = u) := by
      funext t
      rcases t with ⟨m,u',z⟩
      rcases m with p | (v' | a) <;> simp [decodeTriple, Prod.mk.injEq]
    rw [he, FiniteLaw.prod_prob_fixed_fst
      (metadataLaw (s := s) (V := V) (A := A)).toFiniteLaw
      (μ.toFiniteLaw.prod (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw)
      (.inr (.inl v)) (fun t => t.1 = u)]
    have hb : (μ.toFiniteLaw.prod (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw).prob
        (fun t => t.1 = u) = μ.toFiniteLaw.weight u := by
      simpa using FiniteLaw.prod_prob_fixed_fst μ.toFiniteLaw
        (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw u (fun _ => True)
    rw [hb]
    simp [PositiveRationalLaw.toFiniteLaw, metadataLaw, SourceLaws.rowLaw,
      SourceLaws.itemRowLaw, PositiveRationalLaw.prod]
    ring
  · have he : (fun t : Metadata s V A × (X × Template q₁ q₂ X) =>
        decodeTriple t = Sum.inr (Sum.inr a,u)) =
        (fun t => t.1 = Sum.inr (Sum.inr a) ∧ t.2.1 = u) := by
      funext t
      rcases t with ⟨m,u',z⟩
      rcases m with p | (v | a') <;> simp [decodeTriple, Prod.mk.injEq]
    rw [he, FiniteLaw.prod_prob_fixed_fst
      (metadataLaw (s := s) (V := V) (A := A)).toFiniteLaw
      (μ.toFiniteLaw.prod (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw)
      (.inr (.inr a)) (fun t => t.1 = u)]
    have hb : (μ.toFiniteLaw.prod (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw).prob
        (fun t => t.1 = u) = μ.toFiniteLaw.weight u := by
      simpa using FiniteLaw.prod_prob_fixed_fst μ.toFiniteLaw
        (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw u (fun _ => True)
    rw [hb]
    simp [PositiveRationalLaw.toFiniteLaw, metadataLaw, SourceLaws.rowLaw,
      SourceLaws.itemRowLaw, PositiveRationalLaw.prod]
    ring

abbrev Label (w : ℕ) :=
  (Fin w → Metadata s V A) × ((Fin w → X) × (Fin w → Template q₁ q₂ X))

noncomputable def law (μ : PositiveRationalLaw X) (w : ℕ) :
    PositiveRationalLaw (Label (X := X) (V := V) (A := A) (q₁ := q₁) (q₂ := q₂) (s := s) w) :=
  ((metadataLaw (s := s) (V := V) (A := A)).iid w).prod
    ((μ.iid w).prod ((SourceLaws.templateLaw μ q₁ q₂).iid w))

def decode {w : ℕ}
    (a : Label (X := X) (V := V) (A := A) (q₁ := q₁) (q₂ := q₂) (s := s) w) :=
  fun i => decodeTriple (a.1 i, (a.2.1 i, a.2.2 i))

/-- The auxiliary full streams push to the original complete K^w law. -/
theorem decode_full_pushes (μ : PositiveRationalLaw X) (w : ℕ) :
    (law (V := V) (A := A) (s := s) (q₁ := q₁) (q₂ := q₂) μ w).toFiniteLaw.PushesTo
      ((SourceLaws.rowLaw (V := V) (A := A) μ q₁ q₂ s).iid w).toFiniteLaw decode := by
  intro E
  calc
    _ = (((metadataLaw (s := s) (V := V) (A := A)).prod
        (μ.prod (SourceLaws.templateLaw μ q₁ q₂))).iid w).toFiniteLaw.prob
        (fun a => E (fun i => decodeTriple (a i))) :=
      triple_iid_pushes _ _ _ w (fun a => E (fun i => decodeTriple (a i)))
    _ = _ := iid_map_pushes _ _ decodeTriple (decode_triple_pushes μ) w E

/-- Pulling back the actual retained event preserves its mass exactly. -/
theorem retained_event_mass (μ : PositiveRationalLaw X) (w : ℕ)
    (Y : Set (Fin w → RawRow q₁ q₂ s X (V ⊕ A))) :
    (law (V := V) (A := A) (s := s) (q₁ := q₁) (q₂ := q₂) μ w).toFiniteLaw.prob
        (fun a => decode a ∈ Y) =
      ((SourceLaws.rowLaw (V := V) (A := A) μ q₁ q₂ s).iid w).toFiniteLaw.prob
        (· ∈ Y) := decode_full_pushes μ w (· ∈ Y)

end Source

end CurrentAdditive.V39CompleteStreams

#print axioms CurrentAdditive.V39CompleteStreams.decode_full_pushes
#print axioms CurrentAdditive.V39CompleteStreams.retained_event_mass
#print axioms CurrentAdditive.V39CompleteStreams.fixed_complete_streams
