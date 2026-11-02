import CurrentAdditive.GaussPivotPrepBank

/-! One fixed Fin32 TM2 controller for the five charged preparation stages.
Each administrative transition only changes finite control and label; all
unbounded work is performed by the embedded physical subprograms. -/

namespace CurrentAdditive.GaussPivotPrepController32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack := Fin 32
noncomputable abbrev M := GaussPivotCount32.M

inductive Control where
  | copy (v : GaussPivotInputCopy32.Control)
  | count (v : GaussPivotCount32.Control)
  | extract (v : GaussPivotCountExtract32.Control)
  | parse (v : GaussPivotParser32.Control)
  | fields (v : GaussPivotFields32.Control)
  deriving DecidableEq, Fintype

inductive Label where
  | copy (l : GaussPivotInputCopy32.Label)
  | count (l : GaussPivotCount32.Label)
  | extract (l : GaussPivotCountExtract32.Label)
  | parse (l : GaussPivotParser32.Label)
  | fields (l : GaussPivotFields32.Label)
  | toCount | toExtract | toParse | toFields | done
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def readCopy : Control → GaussPivotInputCopy32.Control
  | .copy v => v
  | _ => ((), none)
def readCount : Control → GaussPivotCount32.Control
  | .count v => v
  | _ => M.initial
def readExtract : Control → GaussPivotCountExtract32.Control
  | .extract v => v
  | _ => ((), none)
def readParse : Control → GaussPivotParser32.Control
  | .parse v => v
  | _ => none
def readFields : Control → GaussPivotFields32.Control
  | .fields v => v
  | _ => ((), none)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .copy l => BitMachineInline.stmt Label.copy Control.copy readCopy
      (some .toCount) (GaussPivotInputCopy32.program l)
  | .count l => BitMachineInline.stmt Label.count Control.count readCount
      (some .toExtract) (GaussPivotCount32.program l)
  | .extract l => BitMachineInline.stmt Label.extract Control.extract readExtract
      (some .toParse) (GaussPivotCountExtract32.program l)
  | .parse l => BitMachineInline.stmt Label.parse Control.parse readParse
      (some .toFields) (GaussPivotParser32.program l)
  | .fields l => BitMachineInline.stmt Label.fields Control.fields readFields
      (some .done) (GaussPivotFields32.program l)
  | .toCount => .load (fun _ => .count M.initial)
      (.goto (fun _ => .count (.inl M.start)))
  | .toExtract => .load (fun _ => .extract ((), none))
      (.goto (fun _ => .extract (.copy .scan)))
  | .toParse => .load (fun _ => .parse none)
      (.goto (fun _ => .parse (.inl (.scan 0))))
  | .toFields => .load (fun _ => .fields ((), none))
      (.goto (fun _ => .fields (.copy 0 .scan)))
  | .done => .halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

def initial (word : List Bool) : Config :=
  ⟨some (.copy .scan), .copy ((), none),
    GaussPivotInputCopy32.startBank word⟩

theorem finite_program : Finite Stack ∧ Finite Label ∧ Finite Control :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem run_add {c c' : Config} {t : Nat} (h : run t c = c') (u : Nat) :
    run (t + u) c = run u c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run u) h

theorem to_count_step (S : Stack → List Bool) (v : Control) :
    run 1 ⟨some .toCount, v, S⟩ =
      ⟨some (.count (.inl M.start)), .count M.initial, S⟩ := rfl

theorem to_extract_step (S : Stack → List Bool) (v : Control) :
    run 1 ⟨some .toExtract, v, S⟩ =
      ⟨some (.extract (.copy .scan)), .extract ((), none), S⟩ := rfl

theorem to_parse_step (S : Stack → List Bool) (v : Control) :
    run 1 ⟨some .toParse, v, S⟩ =
      ⟨some (.parse (.inl (.scan 0))), .parse none, S⟩ := rfl

theorem to_fields_step (S : Stack → List Bool) (v : Control) :
    run 1 ⟨some .toFields, v, S⟩ =
      ⟨some (.fields (.copy 0 .scan)), .fields ((), none), S⟩ := rfl

end
end CurrentAdditive.GaussPivotPrepController32
