import EthInapproximability.CurrentPaper.SourceCSPRowLoopAll
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-!
# Input-derived cost of clearing a yielded source-row bank

The generic finite-program stack-growth theorem bounds each actually reached
query/work stack by its initial cap length plus the charged number of row-loop
transitions times a fixed program-syntax push constant. Summing over the
q*5+4 physically cleared stacks removes the existential yielded bank from
the row-loop runtime bound.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopCost

open Turing BitMachineEncoding
open SourceCSPRowLoopController SourceCSPRowLoopAll

variable {n a q : Nat}

def pushConstant (q a : Nat) : Nat :=
  BitMachineStackGrowth.perStep (program q (a ^ q))

theorem initial_scratch_le (q : Nat) (input cap : List Bool)
    (E : Fin 4 → List Bool) (i : Fin (q * 5 + 4)) :
    (Sum.elim (SourceCSPRowQueryFrame.initial (q := q) input cap) E
      (SourceCSPRowLoopClear.scratch q i)).length ≤ cap.length := by
  cases h : SourceCSPRowLoopClear.scratchEquiv q i with
  | inl p =>
      simp [SourceCSPRowLoopClear.scratch,
        SourceCSPRowLoopClear.scratchSlot, h,
        SourceCSPRowQueryFrame.initial]
  | inr k =>
      fin_cases k <;>
        simp [SourceCSPRowLoopClear.scratch,
          SourceCSPRowLoopClear.scratchSlot, h,
          SourceCSPRowQueryFrame.initial]

def resetBound (row : Row (n := n) (a := a) (q := q))
    (rest : List Bool) : Nat :=
  let cap := List.replicate (n - 1) true
  (q * 5 + 4) * (cap.length + pushConstant q a * queryCost row rest n) +
    (q * 5 + 4) + 2 + (2 * cap.length + 2) + 1

theorem produced_reset_bound
    (row : Row (n := n) (a := a) (q := q))
    (rest count : List Bool)
    (U : SourceCSPRowQueryFrame.Stack q → List Bool)
    (hp : Produced row rest count U) :
    frameResetCost q U (List.replicate (n - 1) true) ≤
      resetBound row rest := by
  obtain ⟨ty, v, E, hcount, hcap, hscratch, hty, hrun⟩ := hp
  let cap := List.replicate (n - 1) true
  let S₀ : Stack q → List Bool :=
    Sum.elim (SourceCSPRowQueryFrame.initial
      (SourceCSPCodec.rowFields row ++ rest) cap) E
  have hcell (i : Fin (q * 5 + 4)) :
      (Sum.elim U (Function.update E 0 count)
        (SourceCSPRowLoopClear.scratch q i)).length ≤
        cap.length + pushConstant q a * queryCost row rest n := by
    have hg := BitMachineStackGrowth.run_growth (program q (a ^ q))
      (⟨some (adminLabel .check), initialControl, S₀⟩ : Config q (a ^ q))
      ty (SourceCSPRowLoopClear.scratch q i)
    rw [hrun] at hg
    have hi := initial_scratch_le q
      (SourceCSPCodec.rowFields row ++ rest) cap E i
    change (Sum.elim U (Function.update E 0 count)
      (SourceCSPRowLoopClear.scratch q i)).length ≤
      (S₀ (SourceCSPRowLoopClear.scratch q i)).length +
        pushConstant q a * ty at hg
    have hi' : (S₀ (SourceCSPRowLoopClear.scratch q i)).length ≤
        cap.length := by simpa only [S₀] using hi
    have hm := Nat.mul_le_mul_left (pushConstant q a) hty
    exact hg.trans (Nat.add_le_add hi' hm)
  have hsum : (∑ i : Fin (q * 5 + 4),
      (Sum.elim U (Function.update E 0 count)
        (SourceCSPRowLoopClear.scratch q i)).length) ≤
      ∑ _i : Fin (q * 5 + 4),
        (cap.length + pushConstant q a * queryCost row rest n) := by
    apply Finset.sum_le_sum
    intro i _
    exact hcell i
  have hsums : (∑ i : Fin (q * 5 + 4),
      (Sum.elim U (Function.update E 0 count)
        (SourceCSPRowLoopClear.scratch q i)).length) ≤
      (q * 5 + 4) *
        (cap.length + pushConstant q a * queryCost row rest n) := by
    simpa only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] using hsum
  rw [← resetCost_elim q U (Function.update E 0 count) cap]
  change (∑ i : Fin (q * 5 + 4),
      (Sum.elim U (Function.update E 0 count)
        (SourceCSPRowLoopClear.scratch q i)).length) +
      (q * 5 + 4) + 2 + (2 * cap.length + 2) + 1 ≤
    (q * 5 + 4) *
      (cap.length + pushConstant q a * queryCost row rest n) +
      (q * 5 + 4) + 2 + (2 * cap.length + 2) + 1
  omega

end EthInapproximability.CurrentPaper.SourceCSPRowLoopCost
