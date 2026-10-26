import CurrentAdditive.V39GeneratedTable
import CurrentAdditive.IndexedConstructor

/-! Concrete instantiation of all seven generated-support calls by the actual
zero-filtered, independent-stopping Code D array algorithm. No source supplier
or desired-profile record is a parameter of executableStep/executableIterate.
The remaining physical-machine/runtime and NO-profile obligations are not
hidden in this functional constructor. -/

namespace CurrentAdditive.V39GeneratedConstruction

open Paper2 Workspace.Types.CommComplexity

def executableCodeD (D : ℕ) : CodeD D where
  run q n μ := {
    size := (IndexedLaw.construct D μ.weight q).size
    law := (IndexedLaw.codeSource D q μ).law
    decode := (IndexedLaw.codeSource D q μ).decode
    exactLaw := (IndexedLaw.codeSource D q μ).exactLaw
  }

theorem executable_size (D q n : ℕ) (μ : PositiveRationalLaw (Fin n)) :
    ((executableCodeD D).run q n μ).size ≤ (1+q*n)^D :=
  IndexedLaw.construct_size D μ.weight μ.total q

@[simp] theorem executable_weight (D q n : ℕ) (μ : PositiveRationalLaw (Fin n))
    (j : Fin ((executableCodeD D).run q n μ).size) :
    ((executableCodeD D).run q n μ).law.weight j =
      (IndexedLaw.construct D μ.weight q)[j].2 := rfl

@[simp] theorem executable_decode (D q n : ℕ) (μ : PositiveRationalLaw (Fin n))
    (j : Fin ((executableCodeD D).run q n μ).size) (i : Fin q) :
    (((executableCodeD D).run q n μ).decode j i).val =
      (IndexedLaw.construct D μ.weight q)[j].1 i := rfl

theorem executable_call_size {A : Type} [Fintype A] [DecidableEq A]
    (D q n : ℕ) (e : A ≃ Fin n) (μ : PositiveRationalLaw A) :
    ((executableCodeD D).call q e μ).size ≤ (1+q*n)^D :=
  executable_size D q n (reindex e μ)

variable {q₁ q₂ s w Q ni : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]

def executableStep (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : NumberedMatrix) :
    NumberedMatrix :=
  NumberedMatrix.step (q₁ := q₁) (s := s) (w := w) (Q := Q)
    (executableCodeD 8192) μI activity R

def executableIterate (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (k : ℕ) (R : NumberedMatrix) :
    NumberedMatrix :=
  NumberedMatrix.iterate (q₁ := q₁) (s := s) (w := w) (Q := Q)
    (executableCodeD 8192) μI activity k R

def executableRectangle (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (k : ℕ)
    (R : NumberedMatrix) (b : ℕ) :=
  (executableIterate (q₁ := q₁) (s := s) (w := w) (Q := Q)
    μI activity k R).rectangle b

theorem executable_yes (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (k : ℕ)
    (R : NumberedMatrix) (assign : Fin ni → Fin s)
    (hc : Paper2.SourceMatrix.CollisionFree assign activity) :
    Workspace.Types.CommComplexity.D
      (executableIterate (q₁ := q₁) (s := s) (w := w) (Q := Q) μI activity k R).entry ≤
        Workspace.Types.CommComplexity.D R.entry +
          k*(Nat.clog 2 s+Nat.clog 2 q₂+Nat.clog 2 (q₁+2)+
            Nat.clog 2 w+Nat.clog 2 Q) :=
  NumberedMatrix.iterate_yes (executableCodeD 8192) μI activity R assign hc k

theorem executableRectangle_valid (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (k : ℕ)
    (R : NumberedMatrix) (b : ℕ) :
    (executableRectangle (q₁ := q₁) (s := s) (w := w) (Q := Q)
      μI activity k R b).Valid := NumberedMatrix.rectangle_valid _ b

end CurrentAdditive.V39GeneratedConstruction
