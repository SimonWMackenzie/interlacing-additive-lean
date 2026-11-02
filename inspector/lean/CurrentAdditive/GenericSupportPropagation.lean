import CurrentAdditive.CompactSupportShape
import Paper2.FullSupport

/-! Structural output support of recursive generator codes. This file starts
with the generic tuple and ticket closures; later modules can use them to
separate exact sampling weights from physical navigation support. -/

namespace Paper2.GenericSupportPropagation

open Paper2.GeneratorCode Paper2.GeneratorSource
open Paper2.RecursiveRequestCodeShape
open Paper2.RecursiveLabelCodecScratch

theorem ticket_index (n : ℕ) (i : Fin n) :
    Produces (meaning (.ticket n)) ((finCodec n).encode i) :=
  (produces_ticket n _).mpr (Or.inr ⟨i, rfl⟩)

theorem append_words (a b : Code) (x y : List Bool)
    (hx : Produces (meaning a) x)
    (hy : Produces (meaning b) y) :
    Produces (meaning (.append a b)) (x ++ y) :=
  (produces_concat _ _).mpr ⟨x, y, hx, hy, rfl⟩

theorem copies_typed {A : Type} (n : ℕ) (c : Code)
    (ca : PrefixCodec A)
    (h : ∀ a, Produces (meaning c) (ca.encode a))
    (xs : Fin n → A) :
    Produces (meaning (copies n c)) ((piCodec ca n).encode xs) := by
  induction n with
  | zero =>
      change Produces (meaning (.emit [])) []
      exact (produces_emit [] []).mpr rfl
  | succ n ih =>
      change Produces (meaning (.append c (copies n c)))
        (ca.encode (xs 0) ++ (piCodec ca n).encode (Fin.tail xs))
      exact append_words c (copies n c) _ _ (h _) (ih (Fin.tail xs))

theorem outer_typed {Y : Type} (q₁ q₂ s : ℕ) (c : Code)
    (cy : PrefixCodec Y)
    (h : ∀ y, Produces (meaning c) (cy.encode y))
    (o : Paper2.SourceMatrix.OuterColumn q₁ q₂ s Y) :
    Produces (meaning (outerCode q₁ q₂ s c))
      ((outerColumnCodec q₁ q₂ s cy).encode o) := by
  change Produces (meaning (.append (.ticket q₂) (copies (q₁ + s + 1) c)))
    ((finCodec q₂).encode o.1 ++
      (piCodec cy (q₁ + s + 1)).encode o.2)
  exact append_words _ _ _ _ (ticket_index q₂ o.1)
    (copies_typed _ c cy h o.2)

theorem raw_typed {Y : Type} (q₁ q₂ s : ℕ) (c : Code)
    (cy : PrefixCodec Y)
    (h : ∀ y, Produces (meaning c) (cy.encode y))
    (r : Paper2.SourceMatrix.RawColumn q₁ q₂ s Y) :
    Produces (meaning (rawCode q₁ q₂ s c))
      ((rawColumnCodec q₁ q₂ s cy).encode r) := by
  change Produces
    (meaning (.append (copies (s + 1) c)
      (copies s (outerCode q₁ q₂ s c))))
    ((piCodec cy (s + 1)).encode r.1 ++
      (piCodec (outerColumnCodec q₁ q₂ s cy) s).encode r.2)
  exact append_words _ _ _ _
    (copies_typed _ c cy h r.1)
    (copies_typed _ (outerCode q₁ q₂ s c)
      (outerColumnCodec q₁ q₂ s cy)
      (outer_typed q₁ q₂ s c cy h) r.2)

theorem fixedTail_typed {Y : Type} (q₁ q₂ s : ℕ) (c : Code)
    (cy : PrefixCodec Y)
    (h : ∀ y, Produces (meaning c) (cy.encode y))
    (js : Fin s → Paper2.SourceMatrix.OuterColumn q₁ q₂ s Y) :
    Produces (meaning (fixedTailCode q₁ q₂ s c))
      ((piCodec (outerColumnCodec q₁ q₂ s cy) s).encode js) := by
  exact copies_typed _ _ _ (outer_typed q₁ q₂ s c cy h) js

theorem tagged_typed {Y : Type} (q₁ q₂ s : ℕ) (c : Code)
    (cy : PrefixCodec Y)
    (h : ∀ y, Produces (meaning c) (cy.encode y))
    (z : Paper2.SourceMatrix.TaggedColumn q₁ q₂ s Y) :
    Produces (meaning (taggedCode q₁ q₂ s c))
      ((taggedColumnCodec q₁ q₂ s cy).encode z) := by
  cases z with
  | unrestricted r =>
      apply (produces_branch3 (n := 256) (a := 254) (b := 255)
        (by decide) _ _ _ _).mpr
      refine ⟨⟨0, by decide⟩, ?_⟩
      simpa [taggedCode, taggedColumnCodec, taggedEquiv] using
        append_words (.emit [false]) (rawCode q₁ q₂ s c)
          [false] ((rawColumnCodec q₁ q₂ s cy).encode r)
          ((produces_emit _ _).mpr rfl) (raw_typed q₁ q₂ s c cy h r)
  | fixedTail js =>
      apply (produces_branch3 (n := 256) (a := 254) (b := 255)
        (by decide) _ _ _ _).mpr
      refine ⟨⟨254, by decide⟩, ?_⟩
      simpa [taggedCode, taggedColumnCodec, taggedEquiv] using
        append_words (.emit [true, false]) (fixedTailCode q₁ q₂ s c)
          [true, false] ((piCodec (outerColumnCodec q₁ q₂ s cy) s).encode js)
          ((produces_emit _ _).mpr rfl) (fixedTail_typed q₁ q₂ s c cy h js)
  | diagonal o =>
      apply (produces_branch3 (n := 256) (a := 254) (b := 255)
        (by decide) _ _ _ _).mpr
      refine ⟨⟨255, by decide⟩, ?_⟩
      simpa [taggedCode, taggedColumnCodec, taggedEquiv] using
        append_words (.emit [true, true]) (outerCode q₁ q₂ s c)
          [true, true] ((outerColumnCodec q₁ q₂ s cy).encode o)
          ((produces_emit _ _).mpr rfl) (outer_typed q₁ q₂ s c cy h o)

theorem ticket_pair {A : Type} (n : ℕ) (c : Code)
    (ca : PrefixCodec A)
    (h : ∀ a, Produces (meaning c) (ca.encode a))
    (z : Fin n × A) :
    Produces (meaning (.append (.ticket n) c))
      ((prodCodec (finCodec n) ca).encode z) := by
  change Produces (meaning (.append (.ticket n) c))
    ((finCodec n).encode z.1 ++ ca.encode z.2)
  exact append_words _ _ _ _ (ticket_index n z.1) (h z.2)

theorem template_typed {X : Type} (q₁ q₂ : ℕ) (c : Code)
    (cx : PrefixCodec X)
    (h : ∀ x, Produces (meaning c) (cx.encode x))
    (z : Fin q₂ → Fin q₁ × X) :
    Produces (meaning (templateCode q₁ q₂ c))
      ((piCodec (prodCodec (finCodec q₁) cx) q₂).encode z) := by
  exact copies_typed q₂ _ _ (ticket_pair q₁ c cx h) z

theorem templateRow_typed {X : Type} (q₁ q₂ s : ℕ) (c : Code)
    (cx : PrefixCodec X)
    (h : ∀ x, Produces (meaning c) (cx.encode x))
    (z : Fin s × (Fin q₂ → Fin q₁ × X)) :
    Produces (meaning (templateRowCode q₁ q₂ s c))
      ((prodCodec (finCodec s)
        (piCodec (prodCodec (finCodec q₁) cx) q₂)).encode z) := by
  change Produces (meaning (.append (.ticket s) (templateCode q₁ q₂ c)))
    ((finCodec s).encode z.1 ++
      (piCodec (prodCodec (finCodec q₁) cx) q₂).encode z.2)
  exact append_words _ _ _ _ (ticket_index s z.1)
    (template_typed q₁ q₂ c cx h z.2)

theorem vertex_item (n s : ℕ) (g : Fin (4 * s)) (v : Fin n) :
    Produces (meaning (vertexLabelsCode (V := Fin n) s))
      ((defaultItemCodec n s).encode (g, .inl v)) := by
  simp only [vertexLabelsCode, Fintype.card_fin, defaultItemCodec,
    prodCodec, sumCodec]
  change Produces
    (meaning (.append (.ticket (4 * s))
      (.append (.emit [false]) (.ticket n))))
    ((finCodec (4 * s)).encode g ++ false :: (finCodec n).encode v)
  exact append_words _ _ _ _ (ticket_index (4 * s) g)
    (append_words _ _ _ _ ((produces_emit _ _).mpr rfl)
      (ticket_index n v))

theorem auxiliary_item (n s : ℕ) (g : Fin (4 * s))
    (a : Fin (s - 3)) :
    Produces (meaning (auxiliaryLabelsCode s))
      ((defaultItemCodec n s).encode (g, .inr a)) := by
  simp only [auxiliaryLabelsCode, defaultItemCodec, prodCodec, sumCodec]
  change Produces
    (meaning (.append (.ticket (4 * s))
      (.append (.emit [true]) (.ticket (s - 3)))))
    ((finCodec (4 * s)).encode g ++ true ::
      (finCodec (s - 3)).encode a)
  exact append_words _ _ _ _ (ticket_index (4 * s) g)
    (append_words _ _ _ _ ((produces_emit _ _).mpr rfl)
      (ticket_index (s - 3) a))

theorem graphRows_typed {X : Type} (n q₁ q₂ s : ℕ) (c : Code)
    (cx : PrefixCodec X)
    (h : ∀ x, Produces (meaning c) (cx.encode x))
    (r : Paper2.SourceMatrix.RawRow q₁ q₂ s X
      (Paper2.SourceConstruction.Items s (Fin n))) :
    Produces (meaning (graphRowsCode (V := Fin n) q₁ q₂ s c))
      ((rawRowCodec q₁ q₂ s cx (defaultItemCodec n s)).encode r) := by
  cases r with
  | inl z =>
      apply (produces_branch3 (n := 512) (a := 510) (b := 511)
        (by decide) _ _ _ _).mpr
      refine ⟨⟨0, by decide⟩, ?_⟩
      simpa [graphRowsCode, rowsCode, rawRowCodec] using
        append_words (.emit [false]) (templateRowCode q₁ q₂ s c)
          [false] ((prodCodec (finCodec s)
            (piCodec (prodCodec (finCodec q₁) cx) q₂)).encode z)
          ((produces_emit _ _).mpr rfl)
          (templateRow_typed q₁ q₂ s c cx h z)
  | inr z =>
      rcases z with ⟨item, x⟩
      rcases item with ⟨g, choice⟩
      cases choice with
      | inl v =>
          apply (produces_branch3 (n := 512) (a := 510) (b := 511)
            (by decide) _ _ _ _).mpr
          refine ⟨⟨510, by decide⟩, ?_⟩
          simpa [graphRowsCode, rowsCode, rawRowCodec] using
            append_words (.emit [true])
              (.append (vertexLabelsCode (V := Fin n) s) c)
              [true] ((defaultItemCodec n s).encode (g, .inl v) ++ cx.encode x)
              ((produces_emit _ _).mpr rfl)
              (append_words _ _ _ _ (vertex_item n s g v) (h x))
      | inr a =>
          apply (produces_branch3 (n := 512) (a := 510) (b := 511)
            (by decide) _ _ _ _).mpr
          refine ⟨⟨511, by decide⟩, ?_⟩
          simpa [graphRowsCode, rowsCode, rawRowCodec] using
            append_words (.emit [true])
              (.append (auxiliaryLabelsCode s) c)
              [true] ((defaultItemCodec n s).encode (g, .inr a) ++ cx.encode x)
              ((produces_emit _ _).mpr rfl)
              (append_words _ _ _ _ (auxiliary_item n s g a) (h x))

#print axioms ticket_index
#print axioms copies_typed
#print axioms tagged_typed
#print axioms templateRow_typed
#print axioms graphRows_typed

end Paper2.GenericSupportPropagation
