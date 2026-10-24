import CurrentAdditive.V39FullAmplifier
import CurrentAdditive.V39IterationArithmetic
import Paper2.LookupSeed

/-! Semantic iteration of the actual full-product double interlace. The
state stores only finite carriers, their original rational laws and Boolean
entries. It contains no cost/profile assertion, encoding or running time
certificate. The lookup seed and literal successor below determine every
stage without access to the graph promise. -/

namespace CurrentAdditive.V39FullIteration

open Paper2 Workspace.Types.CommComplexity V38Schedule
open CurrentAdditive.EdgeSourceMatrix
open CurrentAdditive.V39FullAmplifier

set_option maxHeartbeats 2000000

structure State where
  Row : Type
  Col : Type
  rowFinite : Fintype Row
  colFinite : Fintype Col
  rowLaw : @PositiveRationalLaw Row rowFinite
  colLaw : @PositiveRationalLaw Col colFinite
  matrix : Row → Col → Bool

attribute [instance] State.rowFinite State.colFinite

instance (R : State) : Nonempty R.Row := R.rowLaw.nonempty
instance (R : State) : Nonempty R.Col := R.colLaw.nonempty

noncomputable def seed (L : ℕ) : State where
  Row := Fin (V39PublicSchedule.seedWidth L) → Bool
  Col := Fin (V39PublicSchedule.seedWidth L)
  rowFinite := inferInstance
  colFinite := inferInstance
  rowLaw := LookupSeed.rowLaw _
  colLaw := LookupSeed.columnLaw _ (by rw [V39PublicSchedule.seedWidth_exact]; positivity)
  matrix := LookupSeed.matrix _

private theorem seed_at_width (p a L : ℕ) (hp : 0<p) (heq : p=2^a)
    (hwidth : 64*(L+1)≤2^a) :
    D (LookupSeed.matrix p)=a+1 ∧
    RestrictionProfile (LookupSeed.matrix p) (LookupSeed.rowLaw p).toFiniteLaw
      (LookupSeed.columnLaw p hp).toFiniteLaw ((1/2:ℝ)^L) ((a:ℤ)+1) := by
  subst p
  exact ⟨(LookupSeed.seed_finite a L hwidth).1,(LookupSeed.seed_finite a L hwidth).2.1⟩

theorem seed_cost_profile (L : ℕ) :
    D (seed L).matrix=V39PublicSchedule.seedCost L ∧
    V38RestrictionProfiles.TwoThresholdProfile (seed L).matrix
      (seed L).rowLaw.toFiniteLaw (seed L).colLaw.toFiniteLaw
      ((fullRho L:ℚ):ℝ) (V39PublicSchedule.seedCost L:ℤ) := by
  have hwidth : 64*(L+1)≤2^(6+ell L) := by
    have h := Nat.le_pow_clog (by decide : 1<2) (L+1)
    change L+1≤2^ell L at h
    calc 64*(L+1)≤64*2^ell L := Nat.mul_le_mul_left 64 h
         _=2^(6+ell L) := by rw [pow_add]; norm_num
  have hh := seed_at_width (V39PublicSchedule.seedWidth L) (6+ell L) L
    (by rw [V39PublicSchedule.seedWidth_exact]; positivity)
    (V39PublicSchedule.seedWidth_exact L) hwidth
  have hheight : 6+ell L+1=V39PublicSchedule.seedCost L := by
    unfold V39PublicSchedule.seedCost
    omega
  constructor
  · exact hh.1.trans hheight
  · intro j
    have hj := hh.2 ⟨j.val,by omega⟩
    have hr : ((fullRho L:ℚ):ℝ)=(1/2:ℝ)^L := by simp [fullRho]
    have hheightZ : ((6+ell L:ℕ):ℤ)+1=(V39PublicSchedule.seedCost L:ℤ) := by exact_mod_cast hheight
    rw [hheightZ] at hj
    simpa only [seed,hr] using hj

variable {V E : Type} [Fintype V] [Nonempty V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

noncomputable def next (L : ℕ)
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (rep : ℕ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep) (R : State) : State := by
  classical
  exact {
    Row := Fin (fullQ L) → Fin (V38Schedule.fullW L) × V38Matrix.TaggedColumn (fullQ₁ L) (fullQ₂ L) (fullS L) R.Col
    Col := Fin (fullQ L) × (Fin (V38Schedule.fullW L) → SourceMatrix.RawRow (fullQ₁ L) (fullQ₂ L) (fullS L) R.Row (Items (fullS L) V))
    rowFinite := inferInstance
    colFinite := inferInstance
    rowLaw := V39FullAmplifier.rowLaw R.colLaw L
    colLaw := V39FullAmplifier.columnLaw (V := V) R.rowLaw L
    matrix := V39FullAmplifier.successor L order edge rep hq R.matrix
      (fun _ => Classical.choice (inferInstance : Nonempty R.Col))
  }

noncomputable def iterate (L : ℕ)
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (rep : ℕ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep) : ℕ → State
  | 0 => seed L
  | k+1 => next L order edge rep hq (iterate L order edge rep hq k)

theorem no_iteration
    (L : ℕ) (hL : L=Nat.clog 2 (Fintype.card V))
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (rep Δ : ℕ) (hΔ : 0 < Δ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℚ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (hnm : Fintype.card V ≤ 2*Fintype.card E)
    (hdeg : 2*Fintype.card E ≤ Δ*Fintype.card V)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ ≤ Fintype.card V)
    (gap : ∀ colour : V → Fin 3, (γ : ℝ)*Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card : ℝ))
    (k : ℕ) :
    D (iterate L order edge rep hq k).matrix=V39PublicSchedule.H L k ∧
    V38RestrictionProfiles.TwoThresholdProfile (iterate L order edge rep hq k).matrix
      (iterate L order edge rep hq k).rowLaw.toFiniteLaw
      (iterate L order edge rep hq k).colLaw.toFiniteLaw
      ((fullRho L:ℚ):ℝ) (V39PublicSchedule.H L k:ℤ) := by
  classical
  induction k with
  | zero => simpa [iterate,V39PublicSchedule.H,V39PublicSchedule.B] using seed_cost_profile L
  | succ k ih =>
    let R := iterate L order edge rep hq k
    have hd : 3≤V39PublicSchedule.H L k := by
      unfold V39PublicSchedule.H V39PublicSchedule.B V39PublicSchedule.seedCost
      omega
    have hh := V39FullAmplifier.amplifier L hL order edge loopless rep Δ hΔ hq hdegree
      γ hγ hE hnm hdeg hlarge gap R.rowLaw R.colLaw R.matrix
      (fun _ => Classical.choice (inferInstance : Nonempty R.Col))
      (V39PublicSchedule.H L k) hd ih.2 ih.1
    simpa only [iterate,next,V39PublicSchedule.H_succ,V39PublicSchedule.fullOverhead,
      V39FullAmplifier.overhead] using hh

/-- The universal and YES protocol bounds are for the identical promise-free
constructor used in the NO theorem. -/
theorem upper_iteration
    (L : ℕ)
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (rep : ℕ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep) (k : ℕ) :
    D (iterate L order edge rep hq k).matrix≤V39PublicSchedule.H L k ∧
    (∀ colour : V → Fin 3, (∀ e, colour (edge e false)≠colour (edge e true)) →
      D (iterate L order edge rep hq k).matrix≤V39PublicSchedule.B L k) := by
  classical
  induction k with
  | zero =>
    have hh := (seed_cost_profile L).1
    simp only [iterate,V39PublicSchedule.H,V39PublicSchedule.B,Nat.zero_mul,add_zero]
    exact ⟨hh.le,fun _ _ => hh.le⟩
  | succ k ih =>
    let R := iterate L order edge rep hq k
    have hh := V39FullAmplifier.upper L order edge rep hq R.matrix
      (fun _ => Classical.choice (inferInstance : Nonempty R.Col))
    constructor
    · change D (next L order edge rep hq R).matrix≤_
      apply hh.1.trans
      rw [V39PublicSchedule.H_succ]
      exact Nat.add_le_add_right (Nat.add_le_add_right ih.1 _) _
    · intro colour proper
      change D (next L order edge rep hq R).matrix≤_
      apply (hh.2 colour proper).trans
      rw [V39PublicSchedule.B_succ]
      exact Nat.add_le_add_right (ih.2 colour proper) _

theorem rank_iteration
    (L : ℕ) (hn : Fintype.card V≤2^L)
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (rep : ℕ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep) (k : ℕ) :
    (RankLeaves.realMatrix (iterate L order edge rep hq k).matrix).rank≤V39PublicSchedule.rankBound L k := by
  classical
  induction k with
  | zero =>
    rw [V39PublicSchedule.rankBound_zero]
    exact (LookupSeed.rank_matrix (V39PublicSchedule.seedWidth L)).le
  | succ k ih =>
    let R := iterate L order edge rep hq k
    have hh := V39FullAmplifier.rank_le L hn order edge rep hq R.matrix
      (fun _ => Classical.choice (inferInstance : Nonempty R.Col))
    change (RankLeaves.realMatrix (next L order edge rep hq R).matrix).rank≤_
    apply hh.trans
    rw [V39PublicSchedule.rankBound_succ]
    exact Nat.mul_le_mul_left _ ih

#print axioms seed_cost_profile
#print axioms no_iteration
#print axioms upper_iteration
#print axioms rank_iteration

end CurrentAdditive.V39FullIteration
