import CurrentAdditive.V42FullConstruction
import CurrentAdditive.V42FullIteration

/-! Same-object link from the v42 graph-ordered full iteration to its actual
complete recursive labels, original rational laws and entry evaluator. -/
namespace CurrentAdditive.V42FullActualLabels
noncomputable section

open Paper2 V42Schedule V42PublicSchedule V42FullSuccessor
open CurrentAdditive.EdgeSourceMatrix

variable (n : ℕ) [NeZero n] (hn : 0<n) (L : ℕ)
variable {E : Type} [Fintype E] [DecidableEq E]
variable (order : Items (fullS L) (Fin n) ≃ Fin (Fintype.card (Items (fullS L) (Fin n))))
variable (edge : E → Bool → Fin n) (rep : ℕ)
variable (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep)

def ownerActivity : Items (fullS L) (Fin n) → Fin (fullQ₂ L) → Option (Fin (fullS L)) :=
  EdgeSourceMatrix.activity order edge (by have h:=fullS_ge_256 L; omega) rep hq

private theorem exponent_large (L : ℕ) : 2≤fullExponent L := by unfold fullExponent; omega

include hn
theorem next_eq_generic (R : V39FullIteration.State) :
    V42FullIteration.next L order edge rep hq R =
      V42FullConstruction.next (fullExponent L) L (exponent_large L) n hn
        (ownerActivity n L order edge rep hq) R := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  letI : NeZero (s (fullExponent L)) := ⟨(s_pos _).ne'⟩
  unfold V42FullIteration.next V42FullConstruction.next
  congr 1
  funext x y
  change V42FullSuccessor.successor L order edge rep hq _ _ x y = _
  unfold V42FullSuccessor.successor V42FullSuccessor.internal V38Matrix.matrix
  change SourceMatrix.raw _ _ _ (V38Matrix.forgetTag _ _) =
    SourceMatrix.raw _ _ _ (V39RecursiveTable.eraseTag _)
  generalize (x y.1).2=Z
  cases Z <;> rfl

theorem iterate_eq_generic (rounds : ℕ) :
    V42FullIteration.iterate L order edge rep hq rounds =
      V42FullConstruction.iterate (fullExponent L) L (exponent_large L) n hn
        (ownerActivity n L order edge rep hq) L rounds := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
    rw [V42FullIteration.iterate,V42FullConstruction.iterate,←ih]
    exact next_eq_generic n hn L order edge rep hq _

theorem iterate_eq_actualState (rounds : ℕ) :
    V42FullIteration.iterate L order edge rep hq rounds =
      V42FullConstruction.actualState (fullExponent L) L (exponent_large L) n hn
        (ownerActivity n L order edge rep hq) L rounds := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  exact (iterate_eq_generic n hn L order edge rep hq rounds).trans
    (V42FullConstruction.iterate_eq_actualState _ _ _ _ _ _ _ _)

#print axioms next_eq_generic
#print axioms iterate_eq_actualState

end
end CurrentAdditive.V42FullActualLabels
