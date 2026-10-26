import CurrentAdditive.V39BudgetPrintedLaw
import CurrentAdditive.V39FullIteration
import CurrentAdditive.V39FullSampleResources

set_option autoImplicit false

/-! The owner-activity iteration has exactly the complete labels and laws
used by the current sampler. Literal selector numbering is a separate
conjugacy; no owner/literal activity equality is assumed here. -/

set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384

namespace CurrentAdditive.V39ActualIterationBridge
noncomputable section
open Paper2 V38Schedule V39PublicSchedule V39FullSampleResources
open V39RecursiveGenerator

private instance seedWidthNeZero (L : ℕ) : NeZero (seedWidth L) :=
  ⟨ne_of_gt (full_positive_widths L).1⟩
private instance fullQ₁NeZero (L : ℕ) : NeZero (fullQ₁ L) :=
  ⟨ne_of_gt (full_positive_widths L).2.1⟩
private instance fullQ₂NeZero (L : ℕ) : NeZero (fullQ₂ L) :=
  ⟨ne_of_gt (full_positive_widths L).2.2.1⟩
private instance fullSNeZero (L : ℕ) : NeZero (fullS L) :=
  ⟨ne_of_gt (full_positive_widths L).2.2.2.1⟩
private instance fourFullSNeZero (L : ℕ) : NeZero (4*fullS L) :=
  ⟨ne_of_gt (full_positive_widths L).2.2.2.2.1⟩
private instance fullSMinusThreeNeZero (L : ℕ) : NeZero (fullS L-3) :=
  ⟨ne_of_gt (full_positive_widths L).2.2.2.2.2.1⟩
private instance fullWNeZero (L : ℕ) : NeZero (fullW L) :=
  ⟨ne_of_gt (full_positive_widths L).2.2.2.2.2.2.1⟩
private instance fullQNeZero (L : ℕ) : NeZero (fullQ L) :=
  ⟨ne_of_gt (full_positive_widths L).2.2.2.2.2.2.2⟩

theorem lookup_rowLaw_eq (p : ℕ) :
    LookupSeed.rowLaw p=(PositiveRationalLaw.uniform Bool).iid p := by
  have hh : (LookupSeed.rowLaw p).weight=((PositiveRationalLaw.uniform Bool).iid p).weight := by
    funext x
    simp [LookupSeed.rowLaw,LookupSeed.uniformRational,PositiveRationalLaw.uniform,
      PositiveRationalLaw.iid,Fintype.card_fun,inv_pow]
  cases h₁ : LookupSeed.rowLaw p
  cases h₂ : (PositiveRationalLaw.uniform Bool).iid p
  simp only [h₁,h₂] at hh
  cases hh
  rfl

theorem lookup_columnLaw_eq (p : ℕ) [NeZero p] :
    LookupSeed.columnLaw p (NeZero.pos p)=PositiveRationalLaw.uniform (Fin p) := by
  rfl

def actualState (n : ℕ) [NeZero n] (L : ℕ)
    (activity : EdgeSourceMatrix.Items (fullS L) (Fin n) → Fin (fullQ₂ L) → Option (Fin (fullS L)))
    (k : ℕ) : V39FullIteration.State where
  Row := V39RecursiveGenerator.Row n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L) k
  Col := V39RecursiveGenerator.Column n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L) k
  rowFinite := inferInstance
  colFinite := inferInstance
  rowLaw := (laws n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L) k).1
  colLaw := (laws n (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L) k).2
  matrix := V39RecursiveTable.matrix activity k

theorem seed_eq_actualState (n : ℕ) [NeZero n] (L : ℕ)
    (activity : EdgeSourceMatrix.Items (fullS L) (Fin n) → Fin (fullQ₂ L) → Option (Fin (fullS L))) :
    V39FullIteration.seed L=actualState n L activity 0 := by
  unfold V39FullIteration.seed actualState
  simp only [laws]
  congr 1
  exact lookup_rowLaw_eq _

variable (n : ℕ) [NeZero n] (L : ℕ)
variable {E : Type} [Fintype E] [DecidableEq E]
variable (order : EdgeSourceMatrix.Items (fullS L) (Fin n) ≃
  Fin (Fintype.card (EdgeSourceMatrix.Items (fullS L) (Fin n))))
variable (edge : E → Bool → Fin n) (rep : ℕ)
variable (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep)

def ownerActivity := EdgeSourceMatrix.activity order edge
  (by have h:=fullS_ge_256 L; omega) rep hq

theorem next_actualState (k : ℕ) :
    V39FullIteration.next L order edge rep hq
      (actualState n L (ownerActivity n L order edge rep hq) k)=
      actualState n L (ownerActivity n L order edge rep hq) (k+1) := by
  unfold V39FullIteration.next actualState
  simp only [laws]
  congr 1
  funext x y
  change V39FullAmplifier.successor L order edge rep hq _ _ x y = _
  unfold V39FullAmplifier.successor V39FullScheduleAlignment.matrix
    V39FullProductSources.fullW
  change SourceMatrix.raw _ _ _ (V38Matrix.forgetTag _ _) =
    SourceMatrix.raw _ _ _ (V39RecursiveTable.eraseTag _)
  generalize (x y.1).2=Z
  cases Z <;> rfl

theorem iterate_eq_actualState (k : ℕ) :
    V39FullIteration.iterate L order edge rep hq k=
      actualState n L (ownerActivity n L order edge rep hq) k := by
  induction k with
  | zero => exact seed_eq_actualState n L _
  | succ k ih =>
    rw [V39FullIteration.iterate,ih]
    exact next_actualState n L order edge rep hq k

#print axioms lookup_rowLaw_eq
#print axioms seed_eq_actualState
#print axioms next_actualState
#print axioms iterate_eq_actualState
end
end CurrentAdditive.V39ActualIterationBridge
