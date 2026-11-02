import Paper2.SourceProjection

/-!
# Two literal selectors and their tagged coordinate matrix

Frozen v12 Section 5, `res:paired`. False is the ordinary selector and
true the foreign selector. The tags remain distinct even when values
coincide. The selector law is the literal product of its two iid laws.
-/

namespace Paper2.PairedSelectorMatrix

abbrev Selector (q : ℕ) (J : Type*) := (Fin q → J) × (Fin q → J)
abbrev Block (q : ℕ) := Bool × Fin q
abbrev Column (q : ℕ) (W : Type*) := Block q × W

variable {J W : Type*} {q n : ℕ}

/-- One tagged coordinate of the original selector pair. -/
def coordinate (z : Selector q J) (b : Block q) : J :=
  if b.1 then z.2 b.2 else z.1 b.2

@[simp] theorem coordinate_false (z : Selector q J) (i : Fin q) :
    coordinate z (false, i) = z.1 i := rfl

@[simp] theorem coordinate_true (z : Selector q J) (i : Fin q) :
    coordinate z (true, i) = z.2 i := rfl

/-- The matrix in its selector-row, tagged-word-column orientation. -/
def matrix (R : W → J → Bool) : Selector q J → Column q W → Bool :=
  fun z c => R c.2 (coordinate z c.1)

/-- A joint projection of a whole selector pair, not independent images. -/
def projection (e : Fin n → Block q) (z : Selector q J) : Fin n → J :=
  fun i => coordinate z (e i)

noncomputable def selectorLaw [Fintype J] (ν : PositiveRationalLaw J) (q : ℕ) :
    PositiveRationalLaw (Selector q J) :=
  (ν.iid q).prod (ν.iid q)

end Paper2.PairedSelectorMatrix
