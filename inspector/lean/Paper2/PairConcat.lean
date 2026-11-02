import Paper2.AFrontTransducer
import EthInapproximability.CurrentPaper.EncodedComplexity

/-!
# Physical concatenation of two framed Boolean words

On `pair h (pair matrix [])` this fixed four-stack transducer prints exactly
`h ++ matrix`, within a linear transition clock. It is total on all Boolean
words; malformed input is not assigned a special mathematical meaning.
-/

namespace Paper2.PairConcat

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
    | .firstBit | .secondBit => [b]
    | _ => []
  op _ _ := .keep
  fin _ := []
  incBy := 0
  bound := 1
  emit_le s b := by cases s <;> simp
  fin_le _ := by simp

def concat (w : List Bool) : List Bool := spec.out .firstTag 0 w

theorem done_out (rest : List Bool) : spec.out .done 0 rest = [] := by
  induction rest with
  | nil => rfl
  | cons b rest ih =>
      rw [Spec.out_cons]
      simpa [spec, Spec.next] using ih

theorem first_field (bs rest : List Bool) :
    spec.out .firstTag 0 (field bs ++ rest) = bs ++ spec.out .secondTag 0 rest := by
  induction bs with
  | nil =>
      rw [field, List.singleton_append, Spec.out_cons]
      simp [spec, Spec.next]
  | cons b bs ih =>
      simp only [field, List.cons_append]
      rw [Spec.out_cons]
      simp only [spec, Spec.next, List.nil_append]
      rw [Spec.out_cons]
      simpa [spec, Spec.next] using congrArg (List.cons b) ih

theorem second_field (bs rest : List Bool) :
    spec.out .secondTag 0 (field bs ++ rest) = bs := by
  induction bs with
  | nil =>
      rw [field, List.singleton_append, Spec.out_cons]
      change [] ++ spec.out .done 0 rest = []
      simp [done_out]
  | cons b bs ih =>
      simp only [field, List.cons_append]
      rw [Spec.out_cons]
      simp only [spec, Spec.next, List.nil_append]
      rw [Spec.out_cons]
      simpa [spec, Spec.next] using congrArg (List.cons b) ih

theorem concat_pair (h matrix : List Bool) :
    concat (EncodedComplexity.pair h (EncodedComplexity.pair matrix [])) =
      h ++ matrix := by
  unfold concat EncodedComplexity.pair
  rw [first_field, second_field]

noncomputable def machine : BitMachine.Machine :=
  AFront.Transducer.machine spec Phase.firstTag

theorem outputs (w : List Bool) :
    machine.OutputsWithin w (concat w) (3 * (w.length + 1)) :=
  AFront.Transducer.machine_outputs_linear spec Phase.firstTag w

theorem polytime : BitMachine.Polytime concat := by
  exact ⟨machine, 3, 1, by simpa only [pow_one] using outputs⟩

#print axioms concat_pair
#print axioms outputs
#print axioms polytime

end Paper2.PairConcat
