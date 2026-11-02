import CurrentAdditive.IndexedStagePresentation
import Paper2.RestrictionProfiles

/-!
An exact, chosen order for printing each indexed stage.  The equivalences here
are semantic certificates for a producer's explicit finite numbering; the
physical decoder and its clock remain separate obligations.  No equality is
claimed with the arbitrary `Fintype.equivFin` table used in the earlier
endpoint packet.
-/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open Paper2
open Workspace.Types.CommComplexity
open CurrentAdditive.IndexedStagePresentation

universe u v

def numberedLaw {A : Type v} {B : Type u} [Fintype A] [Fintype B]
    (μ : PositiveRationalLaw B) (e : A ≃ B) : PositiveRationalLaw A where
  weight a := μ.weight (e a)
  positive a := μ.positive (e a)
  total := by
    simpa using (Fintype.sum_equiv e (fun a : A => μ.weight (e a)) μ.weight
      (fun _ => rfl)).trans μ.total

theorem numberedLaw_pushesTo {A : Type v} {B : Type u} [Fintype A] [Fintype B]
    (μ : PositiveRationalLaw B) (e : A ≃ B) :
    (numberedLaw μ e).toFiniteLaw.PushesTo μ.toFiniteLaw e := by
  classical
  intro E
  simp only [FiniteLaw.prob, PositiveRationalLaw.toFiniteLaw, numberedLaw]
  exact Fintype.sum_equiv e
    (fun a : A => if E (e a) then (μ.weight (e a) : ℝ) else 0)
    (fun b : B => if E b then (μ.weight b : ℝ) else 0)
    (fun _ => rfl)

structure ExplicitNumberings {N : ℕ} (R : Stage.{u} N) where
  row : Fin (rows R) ≃ R.Row
  col : Fin (cols R) ≃ R.Col

def numberedTable {N : ℕ} (R : Stage.{u} N)
    (e : ExplicitNumberings R) :
    Fin (rows R) → Fin (cols R) → Bool :=
  fun i j => R.matrix (e.row i) (e.col j)

noncomputable def numberedRowLaw {N : ℕ} (R : Stage.{u} N)
    (e : ExplicitNumberings R) : PositiveRationalLaw (Fin (rows R)) :=
  numberedLaw R.rowLaw e.row

noncomputable def numberedColLaw {N : ℕ} (R : Stage.{u} N)
    (e : ExplicitNumberings R) : PositiveRationalLaw (Fin (cols R)) :=
  numberedLaw R.colLaw e.col

theorem numberedTable_cost {N : ℕ} (R : Stage.{u} N)
    (e : ExplicitNumberings R) :
    D (numberedTable R e) = D R.matrix := by
  exact NPCC.D_equiv_invariance R.matrix e.row e.col

theorem numberedTable_profile_iff {N : ℕ} (R : Stage.{u} N)
    (e : ExplicitNumberings R) (ρ : ℝ) (d : ℤ) :
    RestrictionProfile (numberedTable R e)
      (numberedRowLaw R e).toFiniteLaw
      (numberedColLaw R e).toFiniteLaw ρ d ↔
    RestrictionProfile R.matrix R.rowLaw.toFiniteLaw
      R.colLaw.toFiniteLaw ρ d := by
  exact restrictionProfile_pullback_iff R.matrix
    R.rowLaw.toFiniteLaw R.colLaw.toFiniteLaw
    (numberedRowLaw R e).toFiniteLaw
    (numberedColLaw R e).toFiniteLaw e.row e.col
    (numberedLaw_pushesTo R.rowLaw e.row)
    (numberedLaw_pushesTo R.colLaw e.col)
    e.row.surjective e.col.surjective ρ d

#print axioms numberedLaw_pushesTo
#print axioms numberedTable_cost
#print axioms numberedTable_profile_iff

end CurrentAdditive.IndexedExecutableStepRecovery
