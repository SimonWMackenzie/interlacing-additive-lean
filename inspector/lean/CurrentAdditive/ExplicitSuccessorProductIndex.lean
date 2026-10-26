import CurrentAdditive.CodeDExplicitLabelNumbering

/-! The successor column is a nested product of one public coordinate and
three indexed Code D labels.  The following arithmetic bijection gives its
row-major numeric order once each source's array-position decoder is known. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

universe u v w

def nestedFinProduct (Q a b c : ℕ) :
    Fin (Q * (a * (b * c))) ≃
      Fin Q × (Fin a × (Fin b × Fin c)) :=
  finProdFinEquiv.symm |>.trans
    ((Equiv.refl (Fin Q)).prodCongr
      (finProdFinEquiv.symm |>.trans
        ((Equiv.refl (Fin a)).prodCongr finProdFinEquiv.symm)))

def successorColumnNumbering {A : Type u} {B : Type v} {C : Type w}
    (Q a b c : ℕ) (eA : Fin a ≃ A) (eB : Fin b ≃ B)
    (eC : Fin c ≃ C) :
    Fin (Q * (a * (b * c))) ≃ Fin Q × (A × (B × C)) :=
  (nestedFinProduct Q a b c).trans
    ((Equiv.refl (Fin Q)).prodCongr
      (eA.prodCongr (eB.prodCongr eC)))

theorem successorColumnNumbering_at {A : Type u} {B : Type v}
    {C : Type w} (Q a b c : ℕ) (eA : Fin a ≃ A)
    (eB : Fin b ≃ B) (eC : Fin c ≃ C)
    (q : Fin Q) (i : Fin a) (j : Fin b) (k : Fin c) :
    successorColumnNumbering Q a b c eA eB eC
      (finProdFinEquiv
        (q, finProdFinEquiv (i, finProdFinEquiv (j, k)))) =
      (q, eA i, eB j, eC k) := by
  simp [successorColumnNumbering, nestedFinProduct]

#print axioms successorColumnNumbering_at

end CurrentAdditive.IndexedExecutableStepRecovery
