import CurrentAdditive.V42Schedule
import CurrentAdditive.V42PublicSchedule
import CurrentAdditive.V39GraphGenerated
import CurrentAdditive.V39NumberedProfile

/-! Actual v42 generated matrices. These definitions instantiate the generic
seven-call constructor at the new literal widths. No cost, profile, graph
promise, machine or running-time certificate occurs in the constructor. -/

namespace CurrentAdditive.V42GeneratedConstruction

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open V42Schedule V39GeneratedConstruction

theorem s_ge_four (k : ℕ) (hk : 2 ≤ k) : 4 ≤ s k := by
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk
  simpa [s] using hp

section Parameters

variable (k b : ℕ) (hk : 2 ≤ k)

local instance sNZ : NeZero (s k) := ⟨(s_pos k).ne'⟩
private def q₁NZ : NeZero (q₁ k) := ⟨by
  have hs := s_ge_four k hk
  unfold q₁
  omega⟩
local instance q₂NZ : NeZero (q₂ k b) := ⟨(q₂_pos k b).ne'⟩
local instance wNZ : NeZero (w k) := ⟨(w_pos k).ne'⟩
local instance QNZ : NeZero (Q k) := ⟨(Q_pos k).ne'⟩

include hk

def source {nx ny : ℕ} (μX : PositiveRationalLaw (Fin nx))
    (μY : PositiveRationalLaw (Fin ny)) := by
  letI := q₁NZ k hk
  exact sourceData (q₁ := q₁ k) (q₂ := q₂ k b) (s := s k)
    (executableCodeD 8192) μX μY

def numberedStep {ni : ℕ} (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin (q₂ k b) → Option (Fin (s k)))
    (R : NumberedMatrix) : NumberedMatrix := by
  letI := q₁NZ k hk
  exact executableStep (q₁ := q₁ k) (s := s k) (w := w k) (Q := Q k) μI activity R

def numberedIterate {ni : ℕ} (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin (q₂ k b) → Option (Fin (s k)))
    (rounds : ℕ) (R : NumberedMatrix) : NumberedMatrix := by
  letI := q₁NZ k hk
  exact executableIterate (q₁ := q₁ k) (s := s k) (w := w k) (Q := Q k)
    μI activity rounds R

def storedStep {ni : ℕ} (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin (q₂ k b) → Option (Fin (s k)))
    (R : StoredMatrix) : StoredMatrix := by
  letI := q₁NZ k hk
  exact StoredMatrix.step (q₁ := q₁ k) (s := s k) (w := w k) (Q := Q k) μI activity R

def storedIterate {ni : ℕ} (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin (q₂ k b) → Option (Fin (s k)))
    (rounds : ℕ) (R : StoredMatrix) : StoredMatrix := by
  letI := q₁NZ k hk
  exact StoredMatrix.iterate (q₁ := q₁ k) (s := s k) (w := w k) (Q := Q k)
    μI activity rounds R

def overhead : ℕ := 36*k+b

theorem overhead_exact :
    Nat.clog 2 (s k) + Nat.clog 2 (q₂ k b) + Nat.clog 2 (q₁ k+2) +
      Nat.clog 2 (w k) + Nat.clog 2 (Q k) = overhead k b := by
  have hs := s_ge_four k hk
  have he : q₁ k+2=s k := by unfold q₁; omega
  rw [he]
  simp only [s,q₂,w,Q,Nat.clog_pow 2 _ (by decide)]
  unfold overhead
  omega

theorem universal_overhead_exact :
    Nat.clog 2 (s k) + Nat.clog 2 (q₂ k b) + Nat.clog 2 (q₁ k+s k+1) +
      Nat.clog 2 (w k) + Nat.clog 2 (Q k) = overhead k b+1 := by
  have hs := s_ge_four k hk
  have he : q₁ k+s k+1=2*s k-1 := by unfold q₁; omega
  have hc : Nat.clog 2 (2*s k-1)=k+1 := by
    rw [Nat.clog_of_two_le (by decide : 1<2) (by omega : 2≤2*s k-1)]
    have hdiv : (2*s k-1+2-1)/2=s k := by omega
    rw [hdiv]
    simp only [s,Nat.clog_pow 2 _ (by decide)]
  rw [he,hc]
  simp only [s,q₂,w,Q,Nat.clog_pow 2 _ (by decide)]
  unfold overhead
  omega

theorem source_call_widths {nx ny : ℕ} (μX : PositiveRationalLaw (Fin nx))
    (μY : PositiveRationalLaw (Fin ny)) :
    q₁ k+s k+1=2*s k-1 ∧ q₂ k b=2^(b+2*k) ∧
      w k=2^(8*k) ∧ Q k=2^(24*k) := by
  have hs := s_ge_four k hk
  exact ⟨by unfold q₁; omega,rfl,rfl,rfl⟩

theorem numberedStep_upper {ni : ℕ} (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin (q₂ k b) → Option (Fin (s k)))
    (R : NumberedMatrix) :
    D (numberedStep k b hk μI activity R).entry ≤ D R.entry+overhead k b+1 := by
  letI := q₁NZ k hk
  have h := NumberedMatrix.step_upper (q₁ := q₁ k) (s := s k)
    (w := w k) (Q := Q k) (executableCodeD 8192) μI activity R
  rw [universal_overhead_exact k b hk] at h
  exact h

theorem numberedIterate_yes {ni : ℕ} (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin (q₂ k b) → Option (Fin (s k)))
    (rounds : ℕ) (R : NumberedMatrix) (assign : Fin ni → Fin (s k))
    (hc : CollisionFree assign activity) :
    D (numberedIterate k b hk μI activity rounds R).entry ≤
      D R.entry+rounds*overhead k b := by
  letI := q₁NZ k hk
  have h := executable_yes (q₁ := q₁ k) (s := s k) (w := w k) (Q := Q k)
    μI activity rounds R assign hc
  rw [overhead_exact k b hk] at h
  exact h

theorem storedStep_numbered {ni : ℕ} (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin (q₂ k b) → Option (Fin (s k))) (R : StoredMatrix) :
    (storedStep k b hk μI activity R).numbered=numberedStep k b hk μI activity R.numbered := by
  letI := q₁NZ k hk
  exact StoredMatrix.ofNumbered_numbered _

theorem storedIterate_numbered {ni : ℕ} (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin (q₂ k b) → Option (Fin (s k)))
    (rounds : ℕ) (R : StoredMatrix) :
    (storedIterate k b hk μI activity rounds R).numbered=
      numberedIterate k b hk μI activity rounds R.numbered := by
  letI := q₁NZ k hk
  exact StoredMatrix.iterate_numbered μI activity rounds R

theorem storedIterate_yes {ni : ℕ} (μI : PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin (q₂ k b) → Option (Fin (s k)))
    (rounds : ℕ) (R : StoredMatrix) (assign : Fin ni → Fin (s k))
    (hc : CollisionFree assign activity) :
    D (storedIterate k b hk μI activity rounds R).entry ≤
      D R.entry+rounds*overhead k b := by
  letI := q₁NZ k hk
  have h := StoredMatrix.iterate_yes (q₁ := q₁ k) (s := s k) (w := w k) (Q := Q k)
    μI activity rounds R assign hc
  rw [overhead_exact k b hk] at h
  exact h

def graphRun {n m rep : ℕ} (hn : 0<n)
    (hwidth : q₂ k b=LiteralEdgeEncoder.Width (s k) m rep)
    (edge : Fin m → Bool → Fin n) (seedLog rounds : ℕ) : StoredMatrix :=
  V39GeneratedConstruction.graphRun (w := w k) (Q := Q k)
    (s_ge_four k hk) hn hwidth edge seedLog rounds

theorem graphRun_yes {n m rep : ℕ} (hn : 0<n)
    (hwidth : q₂ k b=LiteralEdgeEncoder.Width (s k) m rep)
    (edge : Fin m → Bool → Fin n) (seedLog rounds : ℕ)
    (colour : Fin n → Fin 3) (proper : ∀ e, colour (edge e false)≠colour (edge e true)) :
    D (graphRun k b hk hn hwidth edge seedLog rounds).entry ≤
      LookupSeed.exponent seedLog+1+rounds*overhead k b := by
  have h := V39GeneratedConstruction.graphRun_yes (w := w k) (Q := Q k)
    (s_ge_four k hk) hn hwidth edge seedLog rounds colour proper
  have he : graphIncrement (s k) (q₂ k b) (w k) (Q k)=overhead k b := by
    unfold graphIncrement
    simp only [s,q₂,w,Q,Nat.clog_pow 2 _ (by decide)]
    unfold overhead
    omega
  simpa only [graphThreshold,he] using h

def graphRectangle {n m rep : ℕ} (hn : 0<n)
    (hwidth : q₂ k b=LiteralEdgeEncoder.Width (s k) m rep)
    (edge : Fin m → Bool → Fin n) (seedLog rounds : ℕ) :=
  (graphRun k b hk hn hwidth edge seedLog rounds).rectangle
    (LookupSeed.exponent seedLog+1+rounds*overhead k b)

theorem graphRectangle_valid {n m rep : ℕ} (hn : 0<n)
    (hwidth : q₂ k b=LiteralEdgeEncoder.Width (s k) m rep)
    (edge : Fin m → Bool → Fin n) (seedLog rounds : ℕ) :
    (graphRectangle k b hk hn hwidth edge seedLog rounds).Valid :=
  StoredMatrix.rectangle_valid _ _

end Parameters

theorem generated_overhead (k : ℕ) : overhead k (4*k)=40*k := by unfold overhead; omega
theorem full_overhead (L : ℕ) :
    overhead (V42PublicSchedule.fullExponent L) L=V42PublicSchedule.fullOverhead L := by
  unfold overhead V42PublicSchedule.fullOverhead
  omega

#print axioms numberedIterate_yes
#print axioms storedIterate_numbered
#print axioms storedIterate_yes
#print axioms graphRun_yes
#print axioms graphRectangle_valid

end CurrentAdditive.V42GeneratedConstruction

