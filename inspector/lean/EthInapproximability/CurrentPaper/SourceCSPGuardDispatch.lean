import EthInapproximability.CurrentPaper.SourceCSPGuardStatusSequence

/-!
# Literal reject, zero-vertex, and positive-vertex dispatch

After the all-input header and count guard, this finite controller reads the
new status bit. Failure rejects. Success with nonempty parsed vertex word
enters the positive branch; an empty vertex word enters the zero branch only
if unary `m` and the unread source suffix are both empty.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPGuardDispatch

open Turing TM2.Stmt BitMachineEncoding

abbrev Stack := SourceCSPInputFrame.Stack

inductive Outcome where
  | reject | zero | positive
  deriving DecidableEq, Fintype

inductive Label where
  | status | vertex | zeroCount | zeroEof | reject | zero | positive
  deriving DecidableEq, Fintype

abbrev Control := (Option Bool × Option Bool × Option Bool) × Option Outcome
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def statusSlot : Stack := SourceCSPGuardStatus.statusSlot
def vertexSlot : Stack := .inl (.inl (.inl 0))
def countSlot : Stack := SourceCSPGuardStatus.guardSlot
def sourceSlot : Stack := .inl (.inl (.inr 0))

def initialControl : Control := ((none, none, none), none)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .status =>
      pop statusSlot (fun _ b => ((b, none, none), none))
        (branch (fun v => v.1.1 == some true)
          (goto (fun _ => .vertex)) (goto (fun _ => .reject)))
  | .vertex =>
      peek vertexSlot (fun v b => ((v.1.1, b, none), none))
        (branch (fun v => v.1.2.1.isSome)
          (goto (fun _ => .positive)) (goto (fun _ => .zeroCount)))
  | .zeroCount =>
      peek countSlot (fun v b => ((v.1.1, v.1.2.1, b), none))
        (branch (fun v => v.1.2.2.isSome)
          (goto (fun _ => .reject)) (goto (fun _ => .zeroEof)))
  | .zeroEof =>
      peek sourceSlot (fun v b => ((v.1.1, v.1.2.1, b), none))
        (branch (fun v => v.1.2.2.isSome)
          (goto (fun _ => .reject)) (goto (fun _ => .zero)))
  | .reject => load (fun v => (v.1, some .reject)) halt
  | .zero => load (fun v => (v.1, some .zero)) halt
  | .positive => load (fun v => (v.1, some .positive)) halt

def run (t : Nat) (S : Stack → List Bool) : Config :=
  ((advance program)^[t]) ⟨some .status, initialControl, S⟩

theorem reject_on_bad_status (S : Stack → List Bool) (tail : List Bool)
    (hs : S statusSlot = false :: tail) :
    (run 2 S).l = none ∧ (run 2 S).var.2 = some .reject := by
  change S SourceCSPGuardStatus.statusSlot = false :: tail at hs
  simp [run, Function.iterate_succ_apply', advance, TM2.step,
    TM2.stepAux, program, statusSlot, hs, initialControl]

theorem positive_on_vertex (S : Stack → List Bool) (tail : List Bool)
    (hs : S statusSlot = true :: tail)
    (b : Bool) (nTail : List Bool)
    (hn : S vertexSlot = b :: nTail) :
    (run 3 S).l = none ∧ (run 3 S).var.2 = some .positive := by
  change S SourceCSPGuardStatus.statusSlot = true :: tail at hs
  change S (.inl (.inl (.inl 0))) = b :: nTail at hn
  have hvertex : (Function.update S SourceCSPGuardStatus.statusSlot tail)
      (.inl (.inl (.inl 0))) = b :: nTail := by
    rw [Function.update_of_ne (by simp [SourceCSPGuardStatus.statusSlot] :
      (.inl (.inl (.inl 0)) : Stack) ≠ SourceCSPGuardStatus.statusSlot)]
    exact hn
  simp [run, Function.iterate_succ_apply', advance, TM2.step,
    TM2.stepAux, program, statusSlot, vertexSlot,
    hs, hvertex, initialControl]

theorem reject_on_zero_count (S : Stack → List Bool) (tail : List Bool)
    (hs : S statusSlot = true :: tail)
    (hn : S vertexSlot = [])
    (b : Bool) (mTail : List Bool)
    (hm : S countSlot = b :: mTail) :
    (run 4 S).l = none ∧ (run 4 S).var.2 = some .reject := by
  change S SourceCSPGuardStatus.statusSlot = true :: tail at hs
  change S (.inl (.inl (.inl 0))) = [] at hn
  change S SourceCSPGuardStatus.guardSlot = b :: mTail at hm
  have hvertex : (Function.update S SourceCSPGuardStatus.statusSlot tail)
      (.inl (.inl (.inl 0))) = [] := by
    rw [Function.update_of_ne (by simp [SourceCSPGuardStatus.statusSlot] :
      (.inl (.inl (.inl 0)) : Stack) ≠ SourceCSPGuardStatus.statusSlot)]
    exact hn
  have hcount : (Function.update S SourceCSPGuardStatus.statusSlot tail)
      SourceCSPGuardStatus.guardSlot = b :: mTail := by
    rw [Function.update_of_ne (by simp [SourceCSPGuardStatus.statusSlot,
      SourceCSPGuardStatus.guardSlot] :
      SourceCSPGuardStatus.guardSlot ≠ SourceCSPGuardStatus.statusSlot)]
    exact hm
  simp [run, Function.iterate_succ_apply', advance, TM2.step,
    TM2.stepAux, program, statusSlot, vertexSlot, countSlot,
    hs, hvertex, hcount, initialControl]

theorem reject_on_zero_suffix (S : Stack → List Bool) (tail : List Bool)
    (hs : S statusSlot = true :: tail)
    (hn : S vertexSlot = [])
    (hm : S countSlot = [])
    (b : Bool) (sourceTail : List Bool)
    (heof : S sourceSlot = b :: sourceTail) :
    (run 5 S).l = none ∧ (run 5 S).var.2 = some .reject := by
  change S SourceCSPGuardStatus.statusSlot = true :: tail at hs
  change S (.inl (.inl (.inl 0))) = [] at hn
  change S SourceCSPGuardStatus.guardSlot = [] at hm
  change S (.inl (.inl (.inr 0))) = b :: sourceTail at heof
  have hvertex : (Function.update S SourceCSPGuardStatus.statusSlot tail)
      (.inl (.inl (.inl 0))) = [] := by
    rw [Function.update_of_ne (by simp [SourceCSPGuardStatus.statusSlot] :
      (.inl (.inl (.inl 0)) : Stack) ≠ SourceCSPGuardStatus.statusSlot)]
    exact hn
  have hcount : (Function.update S SourceCSPGuardStatus.statusSlot tail)
      SourceCSPGuardStatus.guardSlot = [] := by
    rw [Function.update_of_ne (by simp [SourceCSPGuardStatus.statusSlot,
      SourceCSPGuardStatus.guardSlot] :
      SourceCSPGuardStatus.guardSlot ≠ SourceCSPGuardStatus.statusSlot)]
    exact hm
  have hsource : (Function.update S SourceCSPGuardStatus.statusSlot tail)
      (.inl (.inl (.inr 0))) = b :: sourceTail := by
    rw [Function.update_of_ne (by simp [SourceCSPGuardStatus.statusSlot] :
      (.inl (.inl (.inr 0)) : Stack) ≠ SourceCSPGuardStatus.statusSlot)]
    exact heof
  simp [run, Function.iterate_succ_apply', advance, TM2.step,
    TM2.stepAux, program, statusSlot, vertexSlot, countSlot, sourceSlot,
    hs, hvertex, hcount, hsource, initialControl]

theorem zero_on_empty (S : Stack → List Bool) (tail : List Bool)
    (hs : S statusSlot = true :: tail)
    (hn : S vertexSlot = [])
    (hm : S countSlot = [])
    (heof : S sourceSlot = []) :
    (run 5 S).l = none ∧ (run 5 S).var.2 = some .zero := by
  change S SourceCSPGuardStatus.statusSlot = true :: tail at hs
  change S (.inl (.inl (.inl 0))) = [] at hn
  change S SourceCSPGuardStatus.guardSlot = [] at hm
  change S (.inl (.inl (.inr 0))) = [] at heof
  have hvertex : (Function.update S SourceCSPGuardStatus.statusSlot tail)
      (.inl (.inl (.inl 0))) = [] := by
    rw [Function.update_of_ne (by simp [SourceCSPGuardStatus.statusSlot] :
      (.inl (.inl (.inl 0)) : Stack) ≠ SourceCSPGuardStatus.statusSlot)]
    exact hn
  have hcount : (Function.update S SourceCSPGuardStatus.statusSlot tail)
      SourceCSPGuardStatus.guardSlot = [] := by
    rw [Function.update_of_ne (by simp [SourceCSPGuardStatus.statusSlot,
      SourceCSPGuardStatus.guardSlot] :
      SourceCSPGuardStatus.guardSlot ≠ SourceCSPGuardStatus.statusSlot)]
    exact hm
  have hsource : (Function.update S SourceCSPGuardStatus.statusSlot tail)
      (.inl (.inl (.inr 0))) = [] := by
    rw [Function.update_of_ne (by simp [SourceCSPGuardStatus.statusSlot] :
      (.inl (.inl (.inr 0)) : Stack) ≠ SourceCSPGuardStatus.statusSlot)]
    exact heof
  simp [run, Function.iterate_succ_apply', advance, TM2.step,
    TM2.stepAux, program, statusSlot, vertexSlot, countSlot, sourceSlot,
    hs, hvertex, hcount, hsource, initialControl]

def classify (good : Bool) (vertex count source : List Bool) : Outcome :=
  if !good then .reject
  else if vertex.isEmpty then
    if count.isEmpty && source.isEmpty then .zero else .reject
  else .positive

/-- Every physical status bit leads to one of three terminal branch tags in
at most five transitions, even when the remaining bank is malformed. -/
theorem total (S : Stack → List Bool) (good : Bool) (tail : List Bool)
    (hs : S statusSlot = good :: tail) :
    ∃ t ≤ 5, (run t S).l = none ∧
      (run t S).var.2 =
        some (classify good (S vertexSlot) (S countSlot) (S sourceSlot)) := by
  cases good with
  | false =>
      obtain ⟨hh, ho⟩ := reject_on_bad_status S tail hs
      refine ⟨2, by decide, hh, ?_⟩
      simpa only [classify, Bool.not_false, Bool.cond_true] using ho
  | true =>
      cases hn : S vertexSlot with
      | cons b nTail =>
          obtain ⟨hh, ho⟩ := positive_on_vertex S tail hs b nTail hn
          refine ⟨3, by decide, hh, ?_⟩
          simpa [classify, hn] using ho
      | nil =>
          cases hm : S countSlot with
          | cons b mTail =>
              obtain ⟨hh, ho⟩ := reject_on_zero_count S tail hs hn b mTail hm
              refine ⟨4, by decide, hh, ?_⟩
              simpa [classify, hn, hm] using ho
          | nil =>
              cases heof : S sourceSlot with
              | cons b sourceTail =>
                  obtain ⟨hh, ho⟩ :=
                    reject_on_zero_suffix S tail hs hn hm b sourceTail heof
                  refine ⟨5, by decide, hh, ?_⟩
                  simpa [classify, hn, hm, heof] using ho
              | nil =>
                  obtain ⟨hh, ho⟩ := zero_on_empty S tail hs hn hm heof
                  refine ⟨5, by decide, hh, ?_⟩
                  simpa [classify, hn, hm, heof] using ho

end EthInapproximability.CurrentPaper.SourceCSPGuardDispatch
