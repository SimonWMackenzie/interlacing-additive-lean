import CurrentAdditive.V42FullSuccessor
import CurrentAdditive.V39FullIteration
import CurrentAdditive.V39IterationArithmetic
import Paper2.LookupSeed

/-! Semantic iteration of the actual full-product double interlace. The
state stores only finite carriers, their original rational laws and Boolean
entries. It contains no cost/profile assertion, encoding or running time
certificate. The lookup seed and literal successor below determine every
stage without access to the graph promise. -/

namespace CurrentAdditive.V42FullIteration

open Paper2 Workspace.Types.CommComplexity
open V42PublicSchedule
open CurrentAdditive.EdgeSourceMatrix
open CurrentAdditive.V42FullSuccessor

set_option maxHeartbeats 2000000

abbrev State := V39FullIteration.State
noncomputable abbrev seed (L : ℕ) : State := V39FullIteration.seed L

theorem seed_cost_profile (L : ℕ) :
    D (seed L).matrix=V42PublicSchedule.seedCost L ∧
    V38RestrictionProfiles.TwoThresholdProfile (seed L).matrix
      (seed L).rowLaw.toFiniteLaw (seed L).colLaw.toFiniteLaw
      ((V42Schedule.rho L:ℚ):ℝ) (V42PublicSchedule.seedCost L:ℤ) := by
  simpa only [seed,V42PublicSchedule.seedCost,V42PublicSchedule.ell,V42Schedule.rho,
    V39PublicSchedule.seedCost,V38Schedule.ell,V38Schedule.fullRho] using
    V39FullIteration.seed_cost_profile L

variable {V E : Type} [Fintype V] [Nonempty V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

noncomputable def next (L : ℕ)
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (rep : ℕ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep) (R : State) : State := by
  classical
  exact {
    Row := Fin (fullQ L) → Fin (fullW L) × V38Matrix.TaggedColumn (fullQ₁ L) (fullQ₂ L) (fullS L) R.Col
    Col := Fin (fullQ L) × (Fin (fullW L) → SourceMatrix.RawRow (fullQ₁ L) (fullQ₂ L) (fullS L) R.Row (Items (fullS L) V))
    rowFinite := inferInstance
    colFinite := inferInstance
    rowLaw := V42FullSuccessor.rowLaw R.colLaw L
    colLaw := V42FullSuccessor.columnLaw (V := V) R.rowLaw L
    matrix := V42FullSuccessor.successor L order edge rep hq R.matrix
      (fun _ => Classical.choice (inferInstance : Nonempty R.Col))
  }

noncomputable def iterate (L : ℕ)
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (rep : ℕ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep) : ℕ → State
  | 0 => seed L
  | k+1 => next L order edge rep hq (iterate L order edge rep hq k)

/-- The universal and YES protocol bounds are for the identical promise-free
constructor used in the NO theorem. -/
theorem upper_iteration
    (L : ℕ)
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (rep : ℕ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep) (k : ℕ) :
    D (iterate L order edge rep hq k).matrix≤V42PublicSchedule.H L k ∧
    (∀ colour : V → Fin 3, (∀ e, colour (edge e false)≠colour (edge e true)) →
      D (iterate L order edge rep hq k).matrix≤V42PublicSchedule.B L k) := by
  classical
  induction k with
  | zero =>
    have hh := (seed_cost_profile L).1
    simp only [iterate,V42PublicSchedule.H,V42PublicSchedule.B,Nat.zero_mul,add_zero]
    exact ⟨hh.le,fun _ _ => hh.le⟩
  | succ k ih =>
    let R := iterate L order edge rep hq k
    have hh := V42FullSuccessor.upper L order edge rep hq R.matrix
      (fun _ => Classical.choice (inferInstance : Nonempty R.Col))
    constructor
    · change D (next L order edge rep hq R).matrix≤_
      apply hh.1.trans
      rw [V42PublicSchedule.H_succ]
      exact Nat.add_le_add_right (Nat.add_le_add_right ih.1 _) _
    · intro colour proper
      change D (next L order edge rep hq R).matrix≤_
      apply (hh.2 colour proper).trans
      rw [V42PublicSchedule.B_succ]
      exact Nat.add_le_add_right (ih.2 colour proper) _

theorem rankBound_zero (L : ℕ) : V42PublicSchedule.rankBound L 0=V42PublicSchedule.seedWidth L := by
  rw [V42PublicSchedule.seedWidth_exact]
  unfold V42PublicSchedule.rankBound V42PublicSchedule.B V42PublicSchedule.seedCost
  simp only [Nat.zero_mul,Nat.add_zero]
  congr 1
  omega

theorem rank_iteration
    (L : ℕ) (hn : Fintype.card V≤2^L)
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (rep : ℕ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep) (k : ℕ) :
    (RankLeaves.realMatrix (iterate L order edge rep hq k).matrix).rank≤V42PublicSchedule.rankBound L k := by
  classical
  induction k with
  | zero =>
    rw [rankBound_zero]
    exact (LookupSeed.rank_matrix (V42PublicSchedule.seedWidth L)).le
  | succ k ih =>
    let R := iterate L order edge rep hq k
    have hh := V42FullSuccessor.rank_le L hn order edge rep hq R.matrix
      (fun _ => Classical.choice (inferInstance : Nonempty R.Col))
    change (RankLeaves.realMatrix (next L order edge rep hq R).matrix).rank≤_
    apply hh.trans
    rw [V42PublicSchedule.rankBound_succ]
    exact Nat.mul_le_mul_left _ ih

#print axioms seed_cost_profile
#print axioms upper_iteration
#print axioms rank_iteration

end CurrentAdditive.V42FullIteration
