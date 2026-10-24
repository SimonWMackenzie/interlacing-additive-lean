import CurrentAdditive.DeterministicIndexedRows

/-! Appendix I `det:construction`: actual labels and entries through the
internal and final restricted interlaces. Complete metadata, base and selector
streams are independently indexed; their product is a literal source law. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2 Paper2.SourceMatrix

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]

/-- Metadata chooses either a template bin or one of the source items. -/
noncomputable def metadataLaw (μI : PositiveRationalLaw I) :
    PositiveRationalLaw (Fin s ⊕ I) where
  weight
    | .inl p => (255 / 256) *
        (PositiveRationalLaw.uniform (Fin s)).weight p
    | .inr i => (1 / 256) * μI.weight i
  positive x := by
    cases x with
    | inl p =>
        exact mul_pos (by norm_num)
          ((PositiveRationalLaw.uniform (Fin s)).positive p)
    | inr i => exact mul_pos (by norm_num) (μI.positive i)
  total := by
    rw [Fintype.sum_sum_type]
    simp only [← Finset.mul_sum,
      (PositiveRationalLaw.uniform (Fin s)).total, μI.total, mul_one]
    norm_num

namespace Sources

variable {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- Three whole source indices, not one source conditioned after metadata is
fixed. This is the independence distinction needed in `det:construction`. -/
structure InternalStreams (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (μI : PositiveRationalLaw I) (w : ℕ) where
  metadataStream : CodeSource D w (Fin s ⊕ I) (metadataLaw μI)
  baseStream : CodeSource D w X μX
  selectorStream : CodeSource D w src.inner.Label src.inner.law

namespace InternalStreams

variable {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

noncomputable def law (streams : InternalStreams src μI w) :
    PositiveRationalLaw (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)) :=
  streams.metadataStream.law.prod (streams.baseStream.law.prod streams.selectorStream.law)

/-- The actual K-valued tuple decoded from independent complete streams. -/
def decode (streams : InternalStreams src μI w)
    (a : streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label))
    (p : Fin w) : Row (I := I) src :=
  match streams.metadataStream.decode a.1 p with
  | .inl bin => .inl (bin, streams.selectorStream.decode a.2.2 p)
  | .inr i => .inr (i, streams.baseStream.decode a.2.1 p)

end InternalStreams

noncomputable def chosenInternal (μI : PositiveRationalLaw I) (w : ℕ) :
    InternalStreams src μI w :=
  ⟨chooseCodeSource D w (metadataLaw μI),
   chooseCodeSource D w μX,
   chooseCodeSource D w src.inner.law⟩

noncomputable instance : DecidableEq (Column src) := Classical.decEq _

/-- The final indexed Q-tuple source has the actual W-column alphabet:
a bin together with a tagged N-row label. -/
noncomputable def chosenFinal (w Q : ℕ) [NeZero w] :
    CodeSource D Q (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)) :=
  chooseCodeSource D Q
    ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src))

/-- The internal transpose W. Its input `t` is an actual generated tuple
index, so two identical decoded tuples remain separate columns of U. -/
def W {μI : PositiveRationalLaw I} {w : ℕ}
    (streams : InternalStreams src μI w)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) :
    (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)) →
        (Fin w × Column src) → Bool :=
  fun t pc => B src R activity ξ₀ (InternalStreams.decode src streams t pc.1) pc.2

/-- The final transposed restricted interlace R⁺, on the very same indexed
matrix used by all later cost and profile arguments. -/
def successor {μI : PositiveRationalLaw I} {w Q : ℕ} [NeZero w]
    (streams : InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) :
    final.Label → (Fin Q ×
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label))) → Bool :=
  fun seed a => W src streams R activity ξ₀ a.2 (final.decode seed a.1)

@[simp] theorem successor_entry {μI : PositiveRationalLaw I} {w Q : ℕ}
    [NeZero w] (streams : InternalStreams src μI w)
    (final : CodeSource D Q (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (seed : final.Label)
    (a : Fin Q × (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label))) :
    successor src streams final R activity ξ₀ seed a =
      B src R activity ξ₀
        (InternalStreams.decode src streams a.2 (final.decode seed a.1).1)
        (final.decode seed a.1).2 := rfl

end Sources

end CurrentAdditive.DeterministicIndexedMatrix
