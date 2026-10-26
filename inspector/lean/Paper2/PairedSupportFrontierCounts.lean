import Paper2.PairedSupportFrontier
import Paper2.PairedSupportStepCounts

/-!
# Conservation along the generated paired-support tree

Frozen v12, Section 5, `res:paired`. Every singleton of either tag counts
in `h`, while an unseparated pair counts once in `h` and once in `z`.
The global equations below are consequences of the actual transitions.
-/

namespace Paper2.PairedSupportFrontier

open Workspace.Types.Protocol SourceSupportFrontier
open scoped BigOperators

variable {A C I W : Type*} [Fintype W]

theorem run_counts (μ : FiniteLaw W) (input : (Bool × I) → W → C)
    (fuel : ℕ) (s : State A C I W) (hs : s.Valid) :
    (∑ v : (run μ input fuel s).Leaves, ((run μ input fuel s).state v).h) =
      s.h + (run μ input fuel s).totalSplits ∧
    (∑ v : (run μ input fuel s).Leaves, ((run μ input fuel s).state v).z) +
      (run μ input fuel s).totalSplits = s.z := by
  induction fuel generalizing s with
  | zero => simp [run, Tree.Leaves]
  | succ fuel ih =>
    rcases s with ⟨P, U, S, Z, F⟩
    cases P with
    | leaf value => simp [run, Tree.Leaves]
    | aNode query left right => simp [run, Tree.Leaves]
    | bNode query left right =>
      have hl := ih
        (child μ input ⟨.bNode query left right, U, S, Z, F⟩ query left false)
        (PairedSupportStep.child_valid μ S Z F _ false hs)
      have hr := ih
        (child μ input ⟨.bNode query left right, U, S, Z, F⟩ query right true)
        (PairedSupportStep.child_valid μ S Z F _ true hs)
      have hQ := PairedSupportStep.h_conservation μ S Z F (fun a w => query (input a w)) hs
      have hZ := PairedSupportStep.z_conservation μ Z F (fun a w => query (input a w))
      let sl := child μ input (State.mk (.bNode query left right) U S Z F) query left false
      let sr := child μ input (State.mk (.bNode query left right) U S Z F) query right true
      let tl := run μ input fuel sl
      let tr := run μ input fuel sr
      let n := (PairedSupportStep.splitPairs μ Z F (fun a w => query (input a w))).card
      change (∑ v : (Tree.fork n tl tr).Leaves, ((Tree.fork n tl tr).state v).h) =
          S.card + Z.card + (Tree.fork n tl tr).totalSplits ∧
        (∑ v : (Tree.fork n tl tr).Leaves, ((Tree.fork n tl tr).state v).z) +
          (Tree.fork n tl tr).totalSplits = Z.card
      rw [Tree.sum_state_fork n tl tr (fun t : State A C I W => t.h),
        Tree.sum_state_fork n tl tr (fun t : State A C I W => t.z)]
      simp only [Tree.totalSplits]
      dsimp only [tl, tr, sl, sr, n, child, State.h, State.z] at hl hr ⊢
      omega

end Paper2.PairedSupportFrontier
