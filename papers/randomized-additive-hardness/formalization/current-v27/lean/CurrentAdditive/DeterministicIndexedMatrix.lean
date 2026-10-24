import CurrentAdditive.CylinderSource
import Paper2.SourceProtocols

/-!
Appendix I, `det:construction`, `det:entries`, `det:raw-entries`.
This module builds the finite indexed input alphabets and their Boolean entries.
The source objects are concrete finite positive rational lists with exact decoded
D-wise laws. The executable Code_D algorithm and its bit cost are separate.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2 Paper2.SourceMatrix

universe u

/-- A finite rational source with its own index labels. The decoder need not be
injective: two labels with the same visible word remain different inputs. -/
structure CodeSource (D q : ℕ) (Y : Type u) [Fintype Y] [DecidableEq Y]
    (μ : PositiveRationalLaw Y) where
  Label : Type u
  finite : Fintype Label
  decEq : DecidableEq Label
  law : PositiveRationalLaw Label
  decode : Label → Fin q → Y
  exactLaw : IsDWise D law.toFiniteLaw decode μ.toFiniteLaw

attribute [instance] CodeSource.finite
attribute [instance] CodeSource.decEq

/-- Finite existence from the checked cylinder-source theorem. This choice is
proof-only; it does not implement the polynomial-time Code_D algorithm. -/
noncomputable def chooseCodeSource {Y : Type*} [Fintype Y] [DecidableEq Y]
    (D q : ℕ) (μ : PositiveRationalLaw Y) : CodeSource D q Y μ :=
  let h := exists_rational_dwise_source q D μ
  let t := Classical.choose h
  let ν := Classical.choose (Classical.choose_spec h)
  let hexact := (Classical.choose_spec (Classical.choose_spec h)).2
  {
    Label := ↥t
    finite := inferInstance
    decEq := Classical.decEq (↥t)
    law := ν
    decode := fun x => x.1
    exactLaw := hexact
  }

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]

/-- The three complete source calls used by the finite matrix. The outer
alphabet contains the index of Γ, not just its decoded word. -/
structure Sources (μX : PositiveRationalLaw X) (μY : PositiveRationalLaw Y) where
  gamma : CodeSource D (q₁ + s + 1) Y μY
  inner : CodeSource D q₂ (Fin q₁ × X)
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μX)
  outer : CodeSource D s (Fin q₂ × gamma.Label)
    ((PositiveRationalLaw.uniform (Fin q₂)).prod gamma.law)

namespace Sources

variable {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

abbrev Gamma := src.gamma.Label
abbrev S := src.inner.Label
abbrev J := Fin q₂ × src.gamma.Label
abbrev CalJ := src.outer.Label

/-- Every tagged column is a distinct legal input, even if decoded raw
columns coincide. The ordinary tail is sampled independently of CalJ. -/
inductive Column where
  | ordinary : src.outer.Label × src.gamma.Label → Column
  | fixedTail : src.outer.Label → Column
  | diagonal : (Fin q₂ × src.gamma.Label) → Column
  deriving Fintype

abbrev Row := (Fin s × src.inner.Label) ⊕ (I × X)

def gammaWord (γ : src.gamma.Label) : Word q₁ s Y := src.gamma.decode γ
def innerWord (z : src.inner.Label) : Template q₁ q₂ X := src.inner.decode z
def outerWord (j : J src) : OuterColumn q₁ q₂ s Y :=
  (j.1, gammaWord src j.2)

def decodeRow : Row (I := I) src → RawRow q₁ q₂ s X I
  | .inl (p, z) => .inl (p, innerWord src z)
  | .inr iu => .inr iu

def decodeColumn (ξ₀ : Tail s Y) : Column src → RawColumn q₁ q₂ s Y
  | .ordinary (js, γ) =>
      (tail (gammaWord src γ), fun p => outerWord src (src.outer.decode js p))
  | .fixedTail js =>
      (ξ₀, fun p => outerWord src (src.outer.decode js p))
  | .diagonal j =>
      (tail (gammaWord src j.2), fun _ => outerWord src j)

/-- The actual finite raw matrix. Neither a colouring nor a protocol occurs
in its definition. -/
def B (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) : Row (I := I) src → Column src → Bool :=
  fun k Z => raw R activity (decodeRow src k) (decodeColumn src ξ₀ Z)

def N (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) : Column src → Row (I := I) src → Bool :=
  fun Z k => B src R activity ξ₀ k Z

@[simp] theorem template_entry (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (p : Fin s) (z : src.inner.Label) (Z : Column src) :
    B src R activity ξ₀ (.inl (p, z)) Z =
      R (src.inner.decode z ((decodeColumn src ξ₀ Z).2 p).1).2
        (head ((decodeColumn src ξ₀ Z).2 p).2
          (src.inner.decode z ((decodeColumn src ξ₀ Z).2 p).1).1) := by
  rfl

@[simp] theorem source_entry (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (i : I) (u : X) (Z : Column src) :
    B src R activity ξ₀ (.inr (i, u)) Z =
      R u (sourceColumn activity i (decodeColumn src ξ₀ Z)) := rfl

end Sources

end CurrentAdditive.DeterministicIndexedMatrix
