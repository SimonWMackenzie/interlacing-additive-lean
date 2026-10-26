import CurrentAdditive.V39RoundedSample
import Paper2.GeneratorSource
import Paper2.GeneratorSerialization

set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

namespace CurrentAdditive.V39GeneratorCode

open Paper2 Paper2.RecursiveSamplingProgram Paper2.RecursiveSamplingLaws
open Paper2.RecursiveLabelCodecScratch Paper2.EncodedSamplerAlgebra
open Paper2.GeneratorCode Paper2.GeneratorSource
open CurrentAdditive.V38OneStep CurrentAdditive.V39RecursiveGenerator

/-- Coordinate-order concatenation for an arbitrary (possibly redundant)
representation function. No carrier enumeration occurs. -/
def tupleWord {A : Type} (f : A → List Bool) : (m : ℕ) → (Fin m → A) → List Bool
  | 0, _ => []
  | m + 1, x => f (x 0) ++ tupleWord f m (Fin.tail x)

theorem tupleWord_cons {A : Type} (f : A → List Bool) (m : ℕ) (a : A) (x : Fin m → A) :
    tupleWord f (m + 1) (Fin.cons a x) = f a ++ tupleWord f m x := by
  simp [tupleWord, Fin.tail_cons]

theorem encoded_tuple {A : Type} (f : A → List Bool) (p : Program A) (m : ℕ) :
    Program.map (tupleWord f m) (iid p m) = repeatedConcat (Program.map f p) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iid, repeatedConcat, Program.map_bind, Program.bind_map]
    congr 1
    funext a
    rw [Program.map_map, ← ih, Program.map_map]
    congr 1

theorem copies_word_exact {A : Type} (f : A → List Bool) (p : Program A)
    (c : Code) (hc : meaning c = Program.map f p) (m : ℕ) :
    meaning (copies m c) = Program.map (tupleWord f m) (iid p m) := by
  rw [meaning_copies, hc, encoded_tuple]

def outerWord {Y : Type} (q₁ q₂ s : ℕ) (f : Y → List Bool)
    (z : SourceMatrix.OuterColumn q₁ q₂ s Y) : List Bool :=
  (finCodec q₂).encode z.1 ++ tupleWord f (q₁ + s + 1) z.2

def rawWord {Y : Type} (q₁ q₂ s : ℕ) (f : Y → List Bool)
    (z : SourceMatrix.RawColumn q₁ q₂ s Y) : List Bool :=
  tupleWord f (s + 1) z.1 ++ tupleWord (outerWord q₁ q₂ s f) s z.2

def tagWord {Y : Type} (q₁ q₂ s : ℕ) (f : Y → List Bool) :
    V38Matrix.TaggedColumn q₁ q₂ s Y → List Bool
  | .inl z => [false] ++ rawWord q₁ q₂ s f z
  | .inr z => [true, true] ++ outerWord q₁ q₂ s f z

def currentTaggedCode (q₁ q₂ s : ℕ) (c : Code) : Code :=
  .branch3 256 255 255
    (.append (.emit [false]) (rawCode q₁ q₂ s c))
    (.append (.emit [true, true]) (outerCode q₁ q₂ s c))
    (.append (.emit [true, true]) (outerCode q₁ q₂ s c))

theorem outer_word_exact {Y : Type} {q₁ q₂ s : ℕ} [NeZero q₂]
    (f : Y → List Bool) (p : Program Y) (c : Code)
    (hc : meaning c = Program.map f p) :
    meaning (outerCode q₁ q₂ s c) =
      Program.map (outerWord q₁ q₂ s f) (Paper2.RecursiveSampling.outer p) := by
  rw [outerCode, meaning_append, meaning_copies, hc,
    ← encoded_tuple, meaning_ticket q₂ (Nat.pos_of_ne_zero (NeZero.ne q₂))]
  exact (encoded_pair (finCodec q₂).encode (tupleWord f (q₁ + s + 1))
    (Paper2.RecursiveSampling.uniform q₂) (iid p (q₁ + s + 1))).symm

theorem raw_word_exact {Y : Type} {q₁ q₂ s : ℕ} [NeZero q₂]
    (f : Y → List Bool) (p : Program Y) (c : Code)
    (hc : meaning c = Program.map f p) :
    meaning (rawCode q₁ q₂ s c) =
      Program.map (rawWord q₁ q₂ s f) (Paper2.RecursiveSampling.raw p) := by
  exact pairCode_exact (tupleWord f (s + 1)) (tupleWord (outerWord q₁ q₂ s f) s)
    (iid p (s + 1)) (iid (Paper2.RecursiveSampling.outer p) s)
    (copies (s + 1) c) (copies s (outerCode q₁ q₂ s c))
    (copies_word_exact f p c hc _) (copies_word_exact _ _ _ (outer_word_exact f p c hc) _)

/-- Exactly the current 255/256 and 1/256 generator, encoded in the
physical parser's layout. The middle branch has an empty ticket interval. -/
theorem currentTagged_exact {Y : Type} {q₁ q₂ s : ℕ} [NeZero q₂]
    (f : Y → List Bool) (p : Program Y) (c : Code)
    (hc : meaning c = Program.map f p) :
    meaning (currentTaggedCode q₁ q₂ s c) =
      Program.map (tagWord q₁ q₂ s f) (V38OneStep.tagged p) := by
  change (Program.draw 256 (by decide) fun t =>
    if t.val < 255 then meaning (.append (.emit [false]) (rawCode q₁ q₂ s c))
    else if t.val < 255 then meaning (.append (.emit [true, true]) (outerCode q₁ q₂ s c))
    else meaning (.append (.emit [true, true]) (outerCode q₁ q₂ s c))) = _
  simp only [V38OneStep.tagged, Program.map_draw]
  congr 1
  funext t
  by_cases ht : t.val < 255
  · simp only [ht, ↓reduceIte]
    rw [meaning_prefix, raw_word_exact f p c hc]
    simp only [Program.map_map]
    rfl
  · simp only [ht, ↓reduceIte]
    rw [meaning_prefix, outer_word_exact f p c hc]
    simp only [Program.map_map]
    rfl

theorem tupleWord_eq_piCodec {A B : Type} (c : PrefixCodec B) (f : A → B)
    (m : ℕ) (x : Fin m → A) :
    tupleWord (fun a => c.encode (f a)) m x =
      (piCodec c m).encode (fun i => f (x i)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change c.encode (f (x 0)) ++ tupleWord (fun a => c.encode (f a)) m (Fin.tail x) = _
    rw [ih]
    rfl

def templateWord {X : Type} (q₁ q₂ s : ℕ) (f : X → List Bool)
    (z : Fin s × SourceMatrix.Template q₁ q₂ X) : List Bool :=
  (finCodec s).encode z.1 ++
    tupleWord (fun a => (finCodec q₁).encode a.1 ++ f a.2) q₂ z.2

def rawRowWord {X : Type} (n q₁ q₂ s : ℕ) (f : X → List Bool) :
    SourceMatrix.RawRow q₁ q₂ s X (EdgeSourceMatrix.Items s (Fin n)) → List Bool
  | .inl z => [false] ++ templateWord q₁ q₂ s f z
  | .inr z => [true] ++ (defaultItemCodec n s).encode z.1 ++ f z.2

def vertexWord (n s : ℕ) (z : Fin (4 * s) × Fin n) : List Bool :=
  (defaultItemCodec n s).encode (z.1, .inl z.2)

def auxiliaryWord (n s : ℕ) (z : Fin (4 * s) × Fin (s - 3)) : List Bool :=
  (defaultItemCodec n s).encode (z.1, .inr z.2)

theorem template_word_exact {X : Type} {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero s]
    (f : X → List Bool) (p : Program X) (c : Code)
    (hc : meaning c = Program.map f p) :
    meaning (templateRowCode q₁ q₂ s c) =
      Program.map (templateWord q₁ q₂ s f) (Paper2.RecursiveSampling.templateRow p) := by
  have hpair := pairCode_exact (finCodec q₁).encode f
    (Paper2.RecursiveSampling.uniform q₁) p (.ticket q₁) c
    (meaning_ticket q₁ (Nat.pos_of_ne_zero (NeZero.ne q₁))) hc
  have htuple := copies_word_exact _ _ _ hpair q₂
  exact pairCode_exact (finCodec s).encode
    (tupleWord (fun a : Fin q₁ × X => (finCodec q₁).encode a.1 ++ f a.2) q₂)
    (Paper2.RecursiveSampling.uniform s)
    (iid (prod (Paper2.RecursiveSampling.uniform q₁) p) q₂)
    (.ticket s) (templateCode q₁ q₂ c)
    (meaning_ticket s (Nat.pos_of_ne_zero (NeZero.ne s))) htuple

theorem vertex_word_exact {n s : ℕ} [NeZero n] [NeZero (4 * s)] :
    meaning (vertexLabelsCode (V := Fin n) s) =
      Program.map (vertexWord n s) (vertexItems (s := s) (Paper2.RecursiveSampling.uniform n)) := by
  have hn : meaning (.append (.emit [false]) (.ticket n)) =
      Program.map (fun a => [false] ++ (finCodec n).encode a)
        (Paper2.RecursiveSampling.uniform n) := by
    rw [meaning_prefix, meaning_ticket n (Nat.pos_of_ne_zero (NeZero.ne n)), Program.map_map]
    rfl
  simpa only [vertexLabelsCode, Fintype.card_fin] using
    pairCode_exact (finCodec (4 * s)).encode (fun a => [false] ++ (finCodec n).encode a)
      (Paper2.RecursiveSampling.uniform (4 * s)) (Paper2.RecursiveSampling.uniform n)
      (.ticket (4 * s)) (.append (.emit [false]) (.ticket n))
      (meaning_ticket (4 * s) (Nat.pos_of_ne_zero (NeZero.ne (4 * s)))) hn

theorem auxiliary_word_exact {n s : ℕ} [NeZero (4 * s)] [NeZero (s - 3)] :
    meaning (auxiliaryLabelsCode s) =
      Program.map (auxiliaryWord n s) (auxiliaryItems (s := s)) := by
  have hn : meaning (.append (.emit [true]) (.ticket (s - 3))) =
      Program.map (fun a => [true] ++ (finCodec (s - 3)).encode a)
        (Paper2.RecursiveSampling.uniform (s - 3)) := by
    rw [meaning_prefix, meaning_ticket (s - 3) (Nat.pos_of_ne_zero (NeZero.ne (s - 3))), Program.map_map]
    rfl
  exact pairCode_exact (finCodec (4 * s)).encode (fun a => [true] ++ (finCodec (s - 3)).encode a)
    (Paper2.RecursiveSampling.uniform (4 * s)) (Paper2.RecursiveSampling.uniform (s - 3))
    (.ticket (4 * s)) (.append (.emit [true]) (.ticket (s - 3)))
    (meaning_ticket (4 * s) (Nat.pos_of_ne_zero (NeZero.ne (4 * s)))) hn

theorem currentRows_exact {X : Type} {n q₁ q₂ s : ℕ}
    [NeZero n] [NeZero q₁] [NeZero s] [NeZero (4 * s)] [NeZero (s - 3)]
    (f : X → List Bool) (p : Program X) (c : Code)
    (hc : meaning c = Program.map f p) :
    meaning (graphRowsCode (V := Fin n) q₁ q₂ s c) =
      Program.map (rawRowWord n q₁ q₂ s f)
        (rawRows (q₁ := q₁) (q₂ := q₂) (s := s) (Paper2.RecursiveSampling.uniform n) p) := by
  change (Program.draw 512 (by decide) fun t =>
    if t.val < 510 then meaning (.append (.emit [false]) (templateRowCode q₁ q₂ s c))
    else if t.val < 511 then meaning (.append (.emit [true]) (.append (vertexLabelsCode (V := Fin n) s) c))
    else meaning (.append (.emit [true]) (.append (auxiliaryLabelsCode s) c))) = _
  simp only [rawRows, Paper2.RecursiveSampling.rows, Program.map_draw]
  congr 1
  funext t
  by_cases ht : t.val < 510
  · simp only [ht, ↓reduceIte]
    rw [meaning_prefix, template_word_exact f p c hc]
    simp only [Program.map_map]
    rfl
  · by_cases he : t.val = 510
    · simp only [he, show ¬ (510 : ℕ) < 510 by decide, show (510 : ℕ) < 511 by decide,
        ↓reduceIte]
      rw [meaning_prefix, pairCode_exact (vertexWord n s) f _ _ _ _ vertex_word_exact hc]
      simp only [Program.map_map]
      congr 1
    · have hlt : ¬ t.val < 511 := by omega
      simp only [ht, he, hlt, ↓reduceIte]
      rw [meaning_prefix, pairCode_exact (auxiliaryWord n s) f _ _ _ _ auxiliary_word_exact hc]
      simp only [Program.map_map]
      congr 1

def words (n p₀ q₁ q₂ s w Q : ℕ) : (k : ℕ) →
    (Row n p₀ q₁ q₂ s w Q k → List Bool) × (Column n p₀ q₁ q₂ s w Q k → List Bool)
  | 0 => (tupleWord boolCodec.encode p₀, (finCodec p₀).encode)
  | k + 1 =>
    let previous := words n p₀ q₁ q₂ s w Q k
    (tupleWord (fun z => (finCodec w).encode z.1 ++ tagWord q₁ q₂ s previous.2 z.2) Q,
      fun z => (finCodec Q).encode z.1 ++ tupleWord (rawRowWord n q₁ q₂ s previous.1) w z.2)

def currentCodes (n p₀ q₁ q₂ s w Q : ℕ) : ℕ → Code × Code
  | 0 => (copies p₀ .bit, .ticket p₀)
  | k + 1 =>
    let previous := currentCodes n p₀ q₁ q₂ s w Q k
    (copies Q (.append (.ticket w) (currentTaggedCode q₁ q₂ s previous.2)),
      .append (.ticket Q) (copies w (graphRowsCode (V := Fin n) q₁ q₂ s previous.1)))

theorem currentCodes_exact (n p₀ q₁ q₂ s w Q : ℕ)
    [NeZero n] [NeZero p₀] [NeZero q₁] [NeZero q₂]
    [NeZero s] [NeZero (4 * s)] [NeZero (s - 3)] [NeZero w] [NeZero Q] (k : ℕ) :
    meaning (currentCodes n p₀ q₁ q₂ s w Q k).1 =
        Program.map (words n p₀ q₁ q₂ s w Q k).1 (V39RecursiveGenerator.programs n p₀ q₁ q₂ s w Q k).1 ∧
    meaning (currentCodes n p₀ q₁ q₂ s w Q k).2 =
        Program.map (words n p₀ q₁ q₂ s w Q k).2 (V39RecursiveGenerator.programs n p₀ q₁ q₂ s w Q k).2 := by
  induction k with
  | zero =>
    constructor
    · exact copies_word_exact boolCodec.encode _ .bit rfl p₀
    · exact meaning_ticket p₀ (Nat.pos_of_ne_zero (NeZero.ne p₀))
  | succ k ih =>
    have htag := currentTagged_exact (q₁ := q₁) (q₂ := q₂) (s := s) _ _ _ ih.2
    have hrowUnit := pairCode_exact (finCodec w).encode _
      (Paper2.RecursiveSampling.uniform w) _ (.ticket w) _
      (meaning_ticket w (Nat.pos_of_ne_zero (NeZero.ne w))) htag
    have hrow := copies_word_exact _ _ _ hrowUnit Q
    have hraw := currentRows_exact (n := n) (q₁ := q₁) (q₂ := q₂) (s := s) _ _ _ ih.1
    have hcolUnit := copies_word_exact _ _ _ hraw w
    have hcol := pairCode_exact (finCodec Q).encode _
      (Paper2.RecursiveSampling.uniform Q) _ (.ticket Q) _
      (meaning_ticket Q (Nat.pos_of_ne_zero (NeZero.ne Q))) hcolUnit
    exact ⟨hrow, hcol⟩

#print axioms currentTagged_exact
#print axioms currentRows_exact
#print axioms currentCodes_exact

end CurrentAdditive.V39GeneratorCode
