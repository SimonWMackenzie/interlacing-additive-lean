import CurrentAdditive.IndexedSuccessorRestoration
import CurrentAdditive.DeterministicETHConcreteIterationProd

/-!
One remaining mathematical input for the NO induction: exact cost and
near-full restrictions of the actual internal W.  These are the alignment
theorem's target, not assumed successor conclusions.  This file turns that
input into `NoContract` for the same literal seed and step already used by
the universal and YES contracts.
-/

namespace CurrentAdditive.IndexedSemanticIteration

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.DeterministicIteration
open CurrentAdditive.DeterministicETHConcreteIteration

variable (v e L : ℕ) [NeZero v] [NeZero (s L)] [NeZero (s L-3)]
  [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]

/-- The exact pending `det:alignment` conclusion for one predecessor stage.
Both claims refer to its original indexed W laws and the source's public
retention thresholds. -/
def FullWAt (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : Graph (Fin v) (Fin e)) (Δ : ℕ) (γ : ℚ)
    (R : Stage (N L)) : Prop :=
  let i := inputs R
  let activity := Paper2.SourceConstruction.activity T.order G
    (by have hh := s_ge_64 L (by have := T.large; omega : 24 ≤ L); omega)
    T.rep T.repetition
  let C := D R.matrix + 2*((L+3)/4) + 6*L + 1
  D (Sources.W i.src i.streams R.matrix activity i.tail) = C ∧
  ∀ A : Set (i.streams.metadataStream.Label ×
      (i.streams.baseStream.Label × i.streams.selectorStream.Label)),
    ∀ B : Set (Fin (w L) × Sources.Column i.src),
    (θ L : ℝ) ≤ i.streams.law.toFiniteLaw.prob (· ∈ A) →
    1 - (δU L Δ γ : ℝ) ≤
      (((PositiveRationalLaw.uniform (Fin (w L))).prod
        (Sources.columnLaw i.src)).toFiniteLaw).prob (· ∈ B) →
    C ≤ Paper2.Compression.restrictionD
      (Sources.W i.src i.streams R.matrix activity i.tail) A B

/-- The source's actual seed has communication cost at least three. -/
theorem actual_seed_cost_ge_three :
    3 ≤ Paper2.LookupSeed.exponent L + 1 := by
  have hwidth := Paper2.LookupSeed.width_admissible L
  have h64 : 64 ≤ 2 ^ Paper2.LookupSeed.exponent L := by
    dsimp [Paper2.LookupSeed.width] at hwidth
    have hm : 64 ≤ 64 * (L + 1) := by omega
    omega
  have hexp : 6 ≤ Paper2.LookupSeed.exponent L := by
    by_contra hn
    have he : Paper2.LookupSeed.exponent L ≤ 5 := by omega
    have hp : 2 ^ Paper2.LookupSeed.exponent L ≤ 2 ^ 5 :=
      Nat.pow_le_pow_right (by decide : (0:ℕ) < 2) he
    norm_num at hp
    omega
  omega

/-- The NO contract is now reduced exactly to the internal-W alignment
statement at every valid predecessor.  No NO premise appears in the YES or
universal contracts, and the full-W input does not mention the successor's
cost or profile. -/
theorem actual_no_of_full_W
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : Graph (Fin v) (Fin e))
    (Δ Caux : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hadm : Admissible L Δ v e Caux γ)
    (hfull : ∀ R : Stage (N L),
      3 ≤ D R.matrix →
      RestrictionProfile R.matrix R.rowLaw.toFiniteLaw
        R.colLaw.toFiniteLaw (ρ L : ℝ) (D R.matrix : ℤ) →
      FullWAt v e L T inputs G Δ γ R) :
    NoContract (actualConstruction v e L T inputs) G
      (Paper2.LookupSeed.exponent L + 1) (h L) := by
  refine {
    seed_exact := actual_seed_cost v e L T inputs G
    seed_profile := actual_seed_profile v e L T inputs G
    seed_cost_ge := actual_seed_cost_ge_three L
    step_exact_profile := ?_
  }
  intro R _ hcost hp
  have hRprofile : RestrictionProfile R.matrix R.rowLaw.toFiniteLaw
      R.colLaw.toFiniteLaw (ρ L : ℝ) (D R.matrix : ℤ) := by
    simpa only [actualConstruction, construction] using hp
  obtain ⟨hWcost, hWnear⟩ := hfull R hcost hRprofile
  have hadm' : Admissible L Δ (Fintype.card (Fin v))
      (Fintype.card (Fin e)) Caux γ := by
    simpa only [Fintype.card_fin] using hadm
  have hr := next_restored_from_full_W L T inputs G R Δ Caux γ
    hΔ hγ hadm' (D R.matrix) hcost rfl hRprofile
    (by simpa only [FullWAt] using hWcost)
    (by simpa only [FullWAt] using hWnear)
  constructor
  · simpa only [actualConstruction, construction] using hr.1
  · have hcost' := hr.1
    rw [← hcost'] at hr
    simpa only [actualConstruction, construction] using hr.2

#print axioms actual_seed_cost_ge_three
#print axioms actual_no_of_full_W

end CurrentAdditive.IndexedSemanticIteration
