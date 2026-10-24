import Paper2.AFrontTransducer
import EthInapproximability.CurrentPaper.EncodedComplexity

/-! A physical finite-state transducer keeps the first framed field and
removes only the framing of the second field. It lets the fixed comparator
consume the header and estimator result produced by the split/PairMap chain. -/

namespace CurrentAdditive.DeterministicETHPairUnframe

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open AFront.Transducer

inductive Phase
  | firstTag | firstBit | secondTag | secondBit | done
  deriving DecidableEq, Fintype

def spec : Spec Phase where
  step s b _ := match s with
    | .firstTag => if b then .firstBit else .secondTag
    | .firstBit => .firstTag
    | .secondTag => if b then .secondBit else .done
    | .secondBit => .secondTag
    | .done => .done
  emit s b := match s with
    | .firstTag | .firstBit => [b]
    | .secondBit => [b]
    | _ => []
  op _ _ := .keep
  fin _ := []
  incBy := 0
  bound := 1
  emit_le s b := by cases s <;> simp
  fin_le _ := by simp

def unframe (w : List Bool) : List Bool := spec.out .firstTag 0 w

theorem done_out (w : List Bool) : spec.out .done 0 w = [] := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [Spec.out_cons]; simpa [spec, Spec.next] using ih

theorem second_field (b t : List Bool) :
    spec.out .secondTag 0 (field b ++ t) = b := by
  induction b with
  | nil =>
      rw [field, List.singleton_append, Spec.out_cons]
      simpa [spec, Spec.next] using done_out t
  | cons x xs ih =>
      simp only [field, List.cons_append]
      rw [Spec.out_cons]
      simp only [spec, Spec.next]
      rw [Spec.out_cons]
      simpa [spec, Spec.next] using congrArg (List.cons x) ih

theorem first_field (a rest : List Bool) :
    spec.out .firstTag 0 (field a ++ rest) =
      field a ++ spec.out .secondTag 0 rest := by
  induction a with
  | nil =>
      rw [field, List.singleton_append, Spec.out_cons]
      simp [spec, Spec.next]
  | cons x xs ih =>
      simp only [field, List.cons_append]
      rw [Spec.out_cons]
      simp only [spec, Spec.next]
      rw [Spec.out_cons]
      simpa [spec, Spec.next, List.cons_append] using congrArg (fun t => true :: x :: t) ih

theorem unframe_pair (a b t : List Bool) :
    unframe (EncodedComplexity.pair a (EncodedComplexity.pair b t)) =
      EncodedComplexity.pair a b := by
  unfold unframe EncodedComplexity.pair
  rw [first_field, second_field]

noncomputable def machine : BitMachine.Machine :=
  AFront.Transducer.machine spec Phase.firstTag

theorem outputs (w : List Bool) :
    machine.OutputsWithin w (unframe w) (3 * (w.length + 1)) :=
  AFront.Transducer.machine_outputs_linear spec Phase.firstTag w

theorem outputs_pair (a b t : List Bool) :
    machine.OutputsWithin
      (EncodedComplexity.pair a (EncodedComplexity.pair b t))
      (EncodedComplexity.pair a b)
      (3 * ((EncodedComplexity.pair a (EncodedComplexity.pair b t)).length + 1)) := by
  simpa only [unframe_pair] using outputs
    (EncodedComplexity.pair a (EncodedComplexity.pair b t))

#print axioms outputs_pair

end CurrentAdditive.DeterministicETHPairUnframe
