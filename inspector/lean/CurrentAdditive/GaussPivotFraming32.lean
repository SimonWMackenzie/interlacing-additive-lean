import CurrentAdditive.GaussPivotAppend32
import EthInapproximability.CurrentPaper.SourceListMachineWriter

/-!
The inherited eight-stack length-framing worker runs in ambient banks 8--15.
Its input is a physically serialized pivot pair and its output is the literal
length field followed by that pair.  Banks 4--7 and 16--31 remain outside
the worker embedding.
-/

namespace CurrentAdditive.GaussPivotFraming32

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

private noncomputable abbrev W := SourceListMachineWriter.framingMachine true

abbrev Stack := Fin 32
abbrev Label := Fin W.labelCount ⊕ Unit
abbrev Control := Fin W.controlCount
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

private theorem count_eight : W.stackCount = 8 := rfl

noncomputable def locate : Fin W.stackCount ↪ Stack where
  toFun j := ⟨j.val + 8, by
    have hj : j.val < 8 := by simpa only [count_eight] using j.isLt
    omega⟩
  inj' := by
    intro a b h
    have hh := congrArg Fin.val h
    change a.val + 8 = b.val + 8 at hh
    exact Fin.ext (Nat.add_right_cancel hh)

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt locate Sum.inl id id
      (some (.inr ())) (W.program l)
  | .inr () => .halt

noncomputable def run (t : Nat) (c : Config) : Config :=
  ((advance program)^[t]) c

noncomputable def frame (foreign : Stack → List Bool)
    (c : W.Config) : Config :=
  BitMachineStackEmbedding.cfg locate foreign Sum.inl id
    (some (.inr ())) c

theorem physical_frame {m k : Nat} (p : Fin m × Fin k)
    (foreign : Stack → List Bool) :
    ∃ t ≤ (UnaryBinaryEncoding.coefficient + 7) *
        ((CurrentAdditive.GaussControlTrace.pivotPacket p).length + 1)^2,
      ∃ u ≤ t,
        run u (frame foreign
          (W.init (CurrentAdditive.GaussControlTrace.pivotPacket p))) =
          frame foreign
            (W.run t (W.init
              (CurrentAdditive.GaussControlTrace.pivotPacket p))) ∧
        (W.run t (W.init
          (CurrentAdditive.GaussControlTrace.pivotPacket p))).stk W.output =
          CurrentAdditive.GaussPivotFieldsAppend.payload p := by
  let pair := CurrentAdditive.GaussControlTrace.pivotPacket p
  obtain ⟨t, ht, hhalt, hout, _⟩ :=
    BitMachineCompositionArithmetic.first_halt W
      (SourceListMachineWriter.outputs true pair)
  have he := BitMachineStackEmbedding.outputs locate foreign Sum.inl id id
    (by intro v; rfl) (some (.inr ())) W.program program
    (by intro l; rfl) (W.init pair) t hhalt
  obtain ⟨u, hu, hr⟩ := he
  refine ⟨t, ht, u, hu, ?_, ?_⟩
  · simpa only [run, frame] using hr
  · simpa [pair, CurrentAdditive.GaussPivotFieldsAppend.payload,
      SourceListMachineWriter.result] using hout

theorem framed_at_output {m k : Nat} (p : Fin m × Fin k)
    (foreign : Stack → List Bool) (t : Nat)
    (hout : (W.run t (W.init
      (CurrentAdditive.GaussControlTrace.pivotPacket p))).stk W.output =
        CurrentAdditive.GaussPivotFieldsAppend.payload p) :
    (frame foreign (W.run t (W.init
      (CurrentAdditive.GaussControlTrace.pivotPacket p)))).stk
      (locate W.output) =
        CurrentAdditive.GaussPivotFieldsAppend.payload p := by
  exact (BitMachineStackEmbedding.bank_at locate foreign _ W.output).trans hout

#print axioms physical_frame
#print axioms framed_at_output

end CurrentAdditive.GaussPivotFraming32
