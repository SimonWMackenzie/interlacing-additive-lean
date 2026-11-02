import CurrentAdditive.YaoEndpointPhysical
import Paper2.AFrontTransducer
import Paper2.AModelEstimator

/-! Private continuation: physically project a threshold header from a comparator
input `pair w out`. The output is `pair (natField m) out` whenever
`w = natField m ++ rest`. This isolates the table suffix from the rational
threshold code while preserving the original estimator input. -/

namespace CurrentAdditive.ModelEndpointReview.RationalCodeAdapter

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity
open AFront.Transducer

inductive Phase
  | start | innerTagOuterTag | innerTagOuterPayload
  | innerBitOuterTag | innerBitOuterPayload
  | skipTag | skipPayload | copy
  deriving DecidableEq, Fintype

def spec : Spec Phase where
  step s b _ := match s with
    | .start => if b then .innerTagOuterPayload else .copy
    | .innerTagOuterTag => if b then .innerTagOuterPayload else .copy
    | .innerTagOuterPayload => if b then .innerBitOuterTag else .skipTag
    | .innerBitOuterTag => if b then .innerBitOuterPayload else .copy
    | .innerBitOuterPayload => .innerTagOuterTag
    | .skipTag => if b then .skipPayload else .copy
    | .skipPayload => .skipTag
    | .copy => .copy
  emit s b := match s with
    | .start => [true, false, b]
    | .innerTagOuterTag => [b]
    | .innerTagOuterPayload => if b then [true] else [false, false]
    | .innerBitOuterTag => [b]
    | .innerBitOuterPayload => [b]
    | .skipTag | .skipPayload => []
    | .copy => [b]
  op _ _ := .keep
  fin _ := []
  incBy := 0
  bound := 3
  emit_le s b := by cases s <;> cases b <;> decide
  fin_le _ := by simp

def adapt (input : List Bool) : List Bool := spec.out .start 0 input

noncomputable def machine : BitMachine.Machine :=
  AFront.Transducer.machine spec Phase.start

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (adapt input) (5 * (input.length + 1)) := by
  exact AFront.Transducer.machine_outputs_linear spec Phase.start input

theorem polytime : BitMachine.Polytime adapt := by
  exact ⟨machine, 5, 1, by simpa only [pow_one] using outputs⟩

private theorem start_cons (b : Bool) (input : List Bool) :
    spec.out .start 0 (b :: input) =
      [true, false] ++ spec.out .innerTagOuterTag 0 (b :: input) := by
  rw [Spec.out_cons, Spec.out_cons]
  simp [spec, Spec.next]

private theorem start_nonempty (input : List Bool) (h : input ≠ []) :
    spec.out .start 0 input =
      [true, false] ++ spec.out .innerTagOuterTag 0 input := by
  cases input with
  | nil => contradiction
  | cons b rest => exact start_cons b rest

private theorem copy (input : List Bool) : spec.out .copy 0 input = input := by
  induction input with
  | nil => rfl
  | cons b rest ih =>
    rw [Spec.out_cons]
    simpa [spec, Spec.next] using congrArg (List.cons b) ih

private theorem skip (bs suffix : List Bool) :
    spec.out .skipTag 0 (field bs ++ suffix) = suffix := by
  induction bs with
  | nil =>
    simp only [field, List.singleton_append]
    rw [Spec.out_cons]
    simpa [spec, Spec.next] using copy suffix
  | cons b bs ih =>
    simp only [field, List.cons_append]
    rw [Spec.out_cons]
    rw [Spec.out_cons]
    simpa [spec, Spec.next] using ih

/-- The adapter is a charged first-header projection, not an uncharged
semantic rewrite. It works for arbitrary suffix and output words. -/
theorem adapt_header (m : ℕ) (rest out : List Bool) :
    adapt (pair (natField m ++ rest) out) = pair (false :: natField m) out := by
  have hfield (bs rest out : List Bool) :
      spec.out .innerTagOuterTag 0 (field (field bs ++ rest) ++ out) =
        field (field bs) ++ out := by
    induction bs with
    | nil =>
      simp only [field, List.nil_append, List.cons_append]
      rw [Spec.out_cons]
      rw [Spec.out_cons]
      simpa [spec, Spec.next] using skip rest out
    | cons b bs ih =>
      simp only [field, List.cons_append]
      rw [Spec.out_cons]
      rw [Spec.out_cons]
      rw [Spec.out_cons]
      rw [Spec.out_cons]
      simpa [spec, Spec.next] using ih
  have h := hfield m.bits rest out
  unfold adapt pair
  have hne : field (natField m ++ rest) ++ out ≠ [] := by
    cases (natField m ++ rest) <;> simp [field]
  rw [start_nonempty _ hne]
  simpa [natField, field] using congrArg (List.append [true, false]) h

#print axioms adapt_header
#print axioms polytime

end CurrentAdditive.ModelEndpointReview.RationalCodeAdapter
