import Paper2.AFrontTransducer
import EthInapproximability.CurrentPaper.EncodedCommunication

/-!
# Physical removal of one self-delimiting natural-number field

The fixed four-stack transducer discards the first `field` and emits every bit
after its delimiter.  It runs on every Boolean word, including malformed words;
there is no promise-dependent program or uncharged list operation.
-/

namespace Paper2.HeaderStrip

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open AFront.Transducer

inductive Phase
  | tag | payload | body
  deriving DecidableEq, Fintype

def spec : Spec Phase where
  step s b _ := match s with
    | .tag => if b then .payload else .body
    | .payload => .tag
    | .body => .body
  emit s b := match s with
    | .body => [b]
    | _ => []
  op _ _ := .keep
  fin _ := []
  incBy := 0
  bound := 1
  emit_le s b := by cases s <;> simp
  fin_le _ := by simp

def strip (w : List Bool) : List Bool := spec.out .tag 0 w

theorem body (w : List Bool) : spec.out .body 0 w = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      rw [Spec.out_cons]
      simpa [spec, Spec.next] using congrArg (List.cons b) ih

theorem field (bs rest : List Bool) :
    spec.out .tag 0 (EncodedCommunication.field bs ++ rest) =
      spec.out .body 0 rest := by
  induction bs with
  | nil =>
      rw [EncodedCommunication.field, List.singleton_append, Spec.out_cons]
      simp [spec, Spec.next]
  | cons b bs ih =>
      simp only [EncodedCommunication.field, List.cons_append]
      rw [Spec.out_cons]
      simp only [spec, Spec.next, List.nil_append]
      rw [Spec.out_cons]
      simpa [spec, Spec.next] using ih

theorem strip_natField (n : ℕ) (rest : List Bool) :
    strip (natField n ++ rest) = rest := by
  simpa [strip, natField, body] using field n.bits rest

/-- One fixed finite four-stack machine physically discards the first field. -/
noncomputable def machine : BitMachine.Machine := AFront.Transducer.machine spec Phase.tag

theorem outputs (w : List Bool) :
    machine.OutputsWithin w (strip w) (3 * (w.length + 1)) :=
  AFront.Transducer.machine_outputs_linear spec Phase.tag w

theorem polytime : BitMachine.Polytime strip := by
  exact ⟨machine, 3, 1, by simpa only [pow_one] using outputs⟩

#print axioms strip_natField
#print axioms outputs
#print axioms polytime

end Paper2.HeaderStrip
