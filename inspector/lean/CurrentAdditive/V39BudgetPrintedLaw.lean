import CurrentAdditive.V39PhysicalSampleBudget
import CurrentAdditive.RankCountV38
import Paper2.IndexedMatrices

set_option autoImplicit false

/-! Whole encoded-table observables of the exact physically emitted current
label pair. The reservation is any proved cap; the precision uses literal A.
The generic compression facts below are helpers, not the final source theorem. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V39BudgetPrintedLaw
noncomputable section
open Paper2 Workspace.Types.CommComplexity
open EthInapproximability.CurrentPaper.EncodedCommunication
open V39RecursiveGenerator V39RecursiveTable V38OneStep

theorem prod_prob_swap {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteLaw A) (ν : FiniteLaw B) (E : A → B → Prop) :
    (μ.prod ν).prob (fun z => E z.1 z.2) =
      (ν.prod μ).prob (fun z => E z.2 z.1) := by
  classical
  simp only [FiniteLaw.prob,FiniteLaw.prod,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp [mul_comm]

theorem prob_not {A : Type*} [Fintype A] (μ : FiniteLaw A) (E : A → Prop) :
    μ.prob (fun a => ¬E a) = 1-μ.prob E := by
  classical
  have h : μ.prob (fun a => ¬E a)+μ.prob E=1 := by
    rw [FiniteLaw.prob,FiniteLaw.prob,←Finset.sum_add_distrib]
    calc
      _ = ∑ a, μ.weight a := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : E a <;> simp [ha]
      _ = 1 := μ.total
  linarith

theorem row_first_compression {X Y : Type*} [Fintype X] [Fintype Y]
    (F : X → Y → Bool) (μX : PositiveRationalLaw X) (μY : PositiveRationalLaw Y)
    (r H : ℕ) (hH : 1≤H) (hrank : (RankLeaves.realMatrix F).rank≤r)
    (hrobust : ∀ U V, (3/5:ℝ)≤μX.toFiniteLaw.prob (·∈U) →
      (3/5:ℝ)≤μY.toFiniteLaw.prob (·∈V) → H≤Compression.restrictionD F U V) :
    let m := V38RankCount.squareDrawsV38 r H
    ((μX.iid m).prod (μY.iid m)).toFiniteLaw.prob
      (fun z => D (sampleMatrix F z.1 z.2)<H)<(1:ℝ)/100 := by
  intro m
  rw [PositiveRationalLaw.toFiniteLaw_prod,
    PositiveRationalLaw.toFiniteLaw_iid,PositiveRationalLaw.toFiniteLaw_iid]
  rw [prod_prob_swap (μX.toFiniteLaw.iid m) (μY.toFiniteLaw.iid m)
    (fun xs ys => D (sampleMatrix F xs ys)<H)]
  exact V38RankCount.square_compression_failure_v38 F μX.toFiniteLaw μY.toFiniteLaw
    r H hH hrank hrobust

variable (n p q₁ q₂ s w Q : ℕ)
variable [NeZero n] [NeZero p] [NeZero q₁] [NeZero q₂]
  [NeZero s] [NeZero (4*s)] [NeZero (s-3)] [NeZero w] [NeZero Q]

def printedWord (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (hs : 4 ≤ s) (hq₁ : q₁ = s-2) (k m B N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.blockLength n p q₂ s w Q N) N) : List Bool :=
  outputWord activity k m B
    (V39PhysicalSample.sampleAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits)

theorem printedWord_event_error (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (hs : 4 ≤ s) (hq₁ : q₁ = s-2) (k m B N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N) (E : List Bool → Prop) :
    |(RoundedDraw.bitBlocksLaw (V39PhysicalSample.blockLength n p q₂ s w Q N) N).prob
       (fun bits => E (printedWord n p q₁ q₂ s w Q activity hs hq₁ k m B N hN bits))-
      (sampleLaw n p q₁ q₂ s w Q k m).toFiniteLaw.prob
       (fun z => E (outputWord activity k m B z))|≤(1:ℝ)/200 :=
  V39PhysicalSample.budget_labels_event_error_200 n p q₁ q₂ s w Q hs hq₁ k m N hN
    (fun z => E (outputWord activity k m B z))

theorem every_tape_exact (activity : EdgeSourceMatrix.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (hs : 4 ≤ s) (hq₁ : q₁ = s-2) (k m B N : ℕ) (hm : 0 < m)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.blockLength n p q₂ s w Q N) N) :
    let z := V39PhysicalSample.sampleAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits
    let out := tableInstance activity k m B z
    decodeInstance (printedWord n p q₁ q₂ s w Q activity hs hq₁ k m B N hN bits)=some out ∧
      out.rows=m ∧ out.cols=m ∧ out.threshold=B ∧ out.table.length=m*m ∧
      (∀ i j : Fin m, (sampledTable activity k m z).matrix i j=
        matrix activity k (z.1 i) (z.2 j)) := by
  intro z out
  exact ⟨decode_outputWord activity k m B hm z,rfl,rfl,rfl,
    (sampledTable activity k m z).length,sampledTable_entry activity k m z⟩

#print axioms row_first_compression
#print axioms printedWord_event_error
#print axioms every_tape_exact
end
end CurrentAdditive.V39BudgetPrintedLaw
