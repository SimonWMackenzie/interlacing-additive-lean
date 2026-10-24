import CurrentAdditive.V39PhysicalSelect
import CurrentAdditive.V39GeneratorCode

/-! The first-order current sampler's emitted bytes are exactly the bytes
consumed by the physical selector. No old sampler law is substituted. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace CurrentAdditive.V39GeneratorEncodingBridge

open Paper2 Paper2.SourceMatrix Paper2.RecursiveLabelCodecScratch
open CurrentAdditive.V39RecursiveGenerator CurrentAdditive.V39PhysicalSelect
open CurrentAdditive.V39GeneratorCode

variable {n p₀ q₁ q₂ s w Q : ℕ}

theorem outer_word_matches {A B : Type} (c : PrefixCodec B) (f : A → B)
    (j : OuterColumn q₁ q₂ s A) :
    outerWord q₁ q₂ s (fun a => c.encode (f a)) j =
      (outerColumnCodec q₁ q₂ s c).encode (outerMap f j) := by
  unfold outerWord outerColumnCodec outerMap prodCodec
  rw [tupleWord_eq_piCodec c f]

theorem raw_word_matches {A B : Type} (c : PrefixCodec B) (f : A → B)
    (Z : RawColumn q₁ q₂ s A) :
    rawWord q₁ q₂ s (fun a => c.encode (f a)) Z =
      (rawColumnCodec q₁ q₂ s c).encode (rawColumnMap f Z) := by
  unfold rawWord
  rw [tupleWord_eq_piCodec c f]
  have houter : outerWord q₁ q₂ s (fun a => c.encode (f a)) =
      fun a => (outerColumnCodec q₁ q₂ s c).encode (outerMap f a) :=
    funext (outer_word_matches c f)
  rw [houter, tupleWord_eq_piCodec]
  rfl

theorem tag_word_matches {A B : Type} (c : PrefixCodec B) (f : A → B)
    (Z : V38Matrix.TaggedColumn q₁ q₂ s A) :
    tagWord q₁ q₂ s (fun a => c.encode (f a)) Z =
      (taggedColumnCodec q₁ q₂ s c).encode (tagMap f Z) := by
  cases Z with
  | inl Z =>
    change [false] ++ rawWord q₁ q₂ s (fun a => c.encode (f a)) Z =
      [false] ++ (rawColumnCodec q₁ q₂ s c).encode (rawColumnMap f Z)
    rw [raw_word_matches]
  | inr j =>
    change [true, true] ++ outerWord q₁ q₂ s (fun a => c.encode (f a)) j =
      [true, true] ++ (outerColumnCodec q₁ q₂ s c).encode (outerMap f j)
    rw [outer_word_matches]

theorem raw_row_word_matches {A B : Type} (c : PrefixCodec B) (f : A → B)
    (z : RawRow q₁ q₂ s A (EdgeSourceMatrix.Items s (Fin n))) :
    rawRowWord n q₁ q₂ s (fun a => c.encode (f a)) z =
      (rawRowCodec q₁ q₂ s c (defaultItemCodec n s)).encode (rawRowMap f z) := by
  cases z with
  | inl z =>
    change [false] ++ ((finCodec s).encode z.1 ++
      tupleWord (fun a => (finCodec q₁).encode a.1 ++ c.encode (f a.2)) q₂ z.2) = _
    have h := tupleWord_eq_piCodec (prodCodec (finCodec q₁) c)
      (fun a : Fin q₁ × A => (a.1, f a.2)) q₂ z.2
    change tupleWord (fun a => (finCodec q₁).encode a.1 ++ c.encode (f a.2)) q₂ z.2 =
      (piCodec (prodCodec (finCodec q₁) c) q₂).encode (fun i => ((z.2 i).1, f (z.2 i).2)) at h
    rw [h]
    rfl
  | inr z => rfl

/-- This is equality of complete encoded words, including every unused
coordinate, rather than equality of an entry-only projection. -/
theorem words_match (n p₀ q₁ q₂ s w Q k : ℕ) :
    (∀ x : Row n p₀ q₁ q₂ s w Q k,
      (words n p₀ q₁ q₂ s w Q k).1 x = rowWord k x) ∧
    (∀ y : Column n p₀ q₁ q₂ s w Q k,
      (words n p₀ q₁ q₂ s w Q k).2 y = columnWord k y) := by
  induction k with
  | zero =>
    constructor
    · intro x
      simpa only [rowWord, embedding, defaultCarrierCodecs, carrierCodecs, id_eq]
        using tupleWord_eq_piCodec boolCodec id p₀ x
    · intro y; rfl
  | succ k ih =>
    let C := defaultCarrierCodecs n p₀ s q₁ q₂ w Q k
    let e := embedding n p₀ q₁ q₂ s w Q k
    have hx : (words n p₀ q₁ q₂ s w Q k).1 = fun x => C.1.encode (e.1 x) := funext ih.1
    have hy : (words n p₀ q₁ q₂ s w Q k).2 = fun y => C.2.encode (e.2 y) := funext ih.2
    constructor
    · intro x
      change tupleWord (fun z => (finCodec w).encode z.1 ++
        tagWord q₁ q₂ s (words n p₀ q₁ q₂ s w Q k).2 z.2) Q x = _
      rw [hy]
      have hunit : (fun z : Fin w × V38Matrix.TaggedColumn q₁ q₂ s (Column n p₀ q₁ q₂ s w Q k) =>
          (finCodec w).encode z.1 ++ tagWord q₁ q₂ s (fun y => C.2.encode (e.2 y)) z.2) =
          fun z => (prodCodec (finCodec w) (taggedColumnCodec q₁ q₂ s C.2)).encode
            (z.1, tagMap e.2 z.2) := by
        funext z
        exact congrArg ((finCodec w).encode z.1 ++ ·) (tag_word_matches C.2 e.2 z.2)
      rw [hunit, tupleWord_eq_piCodec]
      rfl
    · intro y
      change (finCodec Q).encode y.1 ++
        tupleWord (rawRowWord n q₁ q₂ s (words n p₀ q₁ q₂ s w Q k).1) w y.2 = _
      rw [hx]
      have hunit : rawRowWord n q₁ q₂ s (fun x => C.1.encode (e.1 x)) =
          fun z => (rawRowCodec q₁ q₂ s C.1 (defaultItemCodec n s)).encode (rawRowMap e.1 z) :=
        funext (raw_row_word_matches C.1 e.1)
      rw [hunit, tupleWord_eq_piCodec]
      rfl

#print axioms words_match

end CurrentAdditive.V39GeneratorEncodingBridge
