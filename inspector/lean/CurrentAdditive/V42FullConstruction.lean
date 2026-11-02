import CurrentAdditive.V42GeneratedConstruction
import CurrentAdditive.V39ActualIterationBridge

/-! The literal v42 full-product matrices with their complete recursive
labels, rational input laws and evaluator. All widths are taken from the
new unified recipe. The old full-schedule iteration is not called. -/

set_option maxHeartbeats 2500000

namespace CurrentAdditive.V42FullConstruction
noncomputable section

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open V42Schedule V39GeneratedConstruction V39RecursiveGenerator

abbrev State := V39FullIteration.State

private abbrev q₁NZ (k : ℕ) (hk : 2≤k) : NeZero (q₁ k) := ⟨by
  have hs := V42GeneratedConstruction.s_ge_four k hk
  unfold q₁
  omega⟩

private theorem widths_positive (k : ℕ) (hk : 2≤k) :
    NeZero (4*s k) ∧ NeZero (s k-3) := by
  have hs := V42GeneratedConstruction.s_ge_four k hk
  exact ⟨⟨by omega⟩,⟨by omega⟩⟩

variable (k b : ℕ) (hk : 2≤k) (n : ℕ) (hn : 0<n)
local instance sNZ : NeZero (s k) := ⟨(s_pos k).ne'⟩
local instance q₂NZ : NeZero (q₂ k b) := ⟨(q₂_pos k b).ne'⟩
local instance wNZ : NeZero (w k) := ⟨(w_pos k).ne'⟩
local instance QNZ : NeZero (Q k) := ⟨(Q_pos k).ne'⟩

include hk hn

def next (activity : EdgeSourceMatrix.Items (s k) (Fin n) →
    Fin (q₂ k b) → Option (Fin (s k))) (R : State) : State := by
  letI := q₁NZ k hk
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  exact {
    Row := Fin (Q k) → Fin (w k) × V38Matrix.TaggedColumn (q₁ k) (q₂ k b) (s k) R.Col
    Col := Fin (Q k) × (Fin (w k) → RawRow (q₁ k) (q₂ k b) (s k) R.Row
      (EdgeSourceMatrix.Items (s k) (Fin n)))
    rowFinite := inferInstance
    colFinite := inferInstance
    rowLaw := V38OneStep.successorRowLaw R.colLaw
    colLaw := V38OneStep.successorColumnLaw R.rowLaw
      (V42GeneratedConstruction.s_ge_four k hk)
    matrix := fun z a =>
      let p := z a.1
      raw R.matrix activity (a.2 p.1) (V39RecursiveTable.eraseTag p.2)
  }

def iterate (activity : EdgeSourceMatrix.Items (s k) (Fin n) →
    Fin (q₂ k b) → Option (Fin (s k))) (seedLog : ℕ) : ℕ → State
  | 0 => V39FullIteration.seed seedLog
  | rounds+1 => next k b hk n hn activity (iterate activity seedLog rounds)

theorem next_upper (activity : EdgeSourceMatrix.Items (s k) (Fin n) →
    Fin (q₂ k b) → Option (Fin (s k))) (R : State) :
    D (next k b hk n hn activity R).matrix ≤
      D R.matrix+V42GeneratedConstruction.overhead k b+1 := by
  letI := q₁NZ k hk
  let B := fun (a : RawRow (q₁ k) (q₂ k b) (s k) R.Row
      (EdgeSourceMatrix.Items (s k) (Fin n)))
    (Z : V38Matrix.TaggedColumn (q₁ k) (q₂ k b) (s k) R.Col) =>
    raw R.matrix activity a (V39RecursiveTable.eraseTag Z)
  let N := fun Z a => B a Z
  let W := fun (z : Fin (w k) → RawRow (q₁ k) (q₂ k b) (s k) R.Row
      (EdgeSourceMatrix.Items (s k) (Fin n)))
    (a : Fin (w k) × V38Matrix.TaggedColumn (q₁ k) (q₂ k b) (s k) R.Col) => B (z a.1) a.2
  have hB := (Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (raw (q₁ := q₁ k) R.matrix activity) id V39RecursiveTable.eraseTag).trans
      (raw_D_le (q₁ := q₁ k) activity R.matrix)
  change D B ≤ _ at hB
  have hN : D N=D B := transpose_D B
  have hW := Paper2.indexedInterlace_transpose_D_le N (w_pos k) id
  change D W≤Nat.clog 2 (w k)+D N at hW
  have hnext := Paper2.indexedInterlace_transpose_D_le W (Q_pos k) id
  change D (next k b hk n hn activity R).matrix≤Nat.clog 2 (Q k)+D W at hnext
  have he := V42GeneratedConstruction.universal_overhead_exact k b hk
  omega

theorem next_yes (activity : EdgeSourceMatrix.Items (s k) (Fin n) →
    Fin (q₂ k b) → Option (Fin (s k))) (R : State)
    (assign : EdgeSourceMatrix.Items (s k) (Fin n) → Fin (s k))
    (hc : CollisionFree assign activity) :
    D (next k b hk n hn activity R).matrix ≤
      D R.matrix+V42GeneratedConstruction.overhead k b := by
  letI := q₁NZ k hk
  let B := fun (a : RawRow (q₁ k) (q₂ k b) (s k) R.Row
      (EdgeSourceMatrix.Items (s k) (Fin n)))
    (Z : V38Matrix.TaggedColumn (q₁ k) (q₂ k b) (s k) R.Col) =>
    raw R.matrix activity a (V39RecursiveTable.eraseTag Z)
  let N := fun Z a => B a Z
  let W := fun (z : Fin (w k) → RawRow (q₁ k) (q₂ k b) (s k) R.Row
      (EdgeSourceMatrix.Items (s k) (Fin n)))
    (a : Fin (w k) × V38Matrix.TaggedColumn (q₁ k) (q₂ k b) (s k) R.Col) => B (z a.1) a.2
  have hB := (Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (raw (q₁ := q₁ k) R.matrix activity) id V39RecursiveTable.eraseTag).trans
      (raw_D_le_of_collisionFree (q₁ := q₁ k) assign activity hc R.matrix)
  change D B ≤ _ at hB
  have hN : D N=D B := transpose_D B
  have hW := Paper2.indexedInterlace_transpose_D_le N (w_pos k) id
  change D W≤Nat.clog 2 (w k)+D N at hW
  have hnext := Paper2.indexedInterlace_transpose_D_le W (Q_pos k) id
  change D (next k b hk n hn activity R).matrix≤Nat.clog 2 (Q k)+D W at hnext
  have he := V42GeneratedConstruction.overhead_exact k b hk
  omega

theorem iterate_yes (activity : EdgeSourceMatrix.Items (s k) (Fin n) →
    Fin (q₂ k b) → Option (Fin (s k))) (seedLog rounds : ℕ)
    (assign : EdgeSourceMatrix.Items (s k) (Fin n) → Fin (s k))
    (hc : CollisionFree assign activity) :
    D (iterate k b hk n hn activity seedLog rounds).matrix ≤
      V42PublicSchedule.seedCost seedLog+rounds*V42GeneratedConstruction.overhead k b := by
  induction rounds with
  | zero =>
    have h := (V39FullIteration.seed_cost_profile seedLog).1
    simpa only [iterate,Nat.zero_mul,Nat.add_zero,V42PublicSchedule.seedCost,
      V42PublicSchedule.ell,V39PublicSchedule.seedCost,V38Schedule.ell] using h.le
  | succ rounds ih =>
    have h := next_yes k b hk n hn activity
      (iterate k b hk n hn activity seedLog rounds) assign hc
    exact h.trans (by simpa only [Nat.succ_mul,Nat.add_assoc] using
      Nat.add_le_add_right ih (V42GeneratedConstruction.overhead k b))

def actualState (activity : EdgeSourceMatrix.Items (s k) (Fin n) →
    Fin (q₂ k b) → Option (Fin (s k))) (seedLog rounds : ℕ) : State := by
  letI := q₁NZ k hk
  letI : NeZero n := ⟨hn.ne'⟩
  letI := (widths_positive k hk).1
  letI := (widths_positive k hk).2
  letI : NeZero (V42PublicSchedule.seedWidth seedLog) :=
    ⟨by rw [V42PublicSchedule.seedWidth_exact]; positivity⟩
  exact {
    Row := Row n (V42PublicSchedule.seedWidth seedLog) (q₁ k) (q₂ k b) (s k) (w k) (Q k) rounds
    Col := Column n (V42PublicSchedule.seedWidth seedLog) (q₁ k) (q₂ k b) (s k) (w k) (Q k) rounds
    rowFinite := inferInstance
    colFinite := inferInstance
    rowLaw := (laws n (V42PublicSchedule.seedWidth seedLog) (q₁ k) (q₂ k b) (s k) (w k) (Q k) rounds).1
    colLaw := (laws n (V42PublicSchedule.seedWidth seedLog) (q₁ k) (q₂ k b) (s k) (w k) (Q k) rounds).2
    matrix := V39RecursiveTable.matrix activity rounds
  }

theorem seed_eq_actualState (activity : EdgeSourceMatrix.Items (s k) (Fin n) →
    Fin (q₂ k b) → Option (Fin (s k))) (seedLog : ℕ) :
    V39FullIteration.seed seedLog=actualState k b hk n hn activity seedLog 0 := by
  unfold V39FullIteration.seed actualState
  simp only [laws]
  congr 1
  exact V39ActualIterationBridge.lookup_rowLaw_eq _

theorem next_actualState (activity : EdgeSourceMatrix.Items (s k) (Fin n) →
    Fin (q₂ k b) → Option (Fin (s k))) (seedLog rounds : ℕ) :
    next k b hk n hn activity (actualState k b hk n hn activity seedLog rounds)=
      actualState k b hk n hn activity seedLog (rounds+1) := by
  unfold next actualState
  simp only [laws]
  rfl

theorem iterate_eq_actualState (activity : EdgeSourceMatrix.Items (s k) (Fin n) →
    Fin (q₂ k b) → Option (Fin (s k))) (seedLog rounds : ℕ) :
    iterate k b hk n hn activity seedLog rounds=
      actualState k b hk n hn activity seedLog rounds := by
  induction rounds with
  | zero => exact seed_eq_actualState k b hk n hn activity seedLog
  | succ rounds ih =>
    rw [iterate,ih]
    exact next_actualState k b hk n hn activity seedLog rounds

#print axioms next_upper
#print axioms iterate_yes
#print axioms iterate_eq_actualState

end
end CurrentAdditive.V42FullConstruction
