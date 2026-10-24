import CurrentAdditive.CodeDCanonicalSourceV2
import CurrentAdditive.CylinderRowSerializer

/-! The empty cylinder is first in every generated feature list and matches
every retained source item.  This literal machine writes its complete row
directly from the actual indexed source packet, retaining duplicate entries. -/

namespace CurrentAdditive.CylinderEmptyRowMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.CodeDCodec
open CurrentAdditive.CylinderFeatureCodec

inductive Label where
  | write
  deriving DecidableEq, Fintype

def emit (bits : List Bool) :
    TM2.Stmt (fun _ : Fin 2 => Bool) Label Unit :=
  bits.reverse.foldr (fun bit next => push 1 (fun _ => bit) next) halt

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label Unit
  | .write => emit (encodeRawRat oneRat)

def cfg (l : Option Label) (input output : List Bool) :
    TM2.Cfg (fun _ : Fin 2 => Bool) Label Unit :=
  ⟨l, (), fun k => if k = 0 then input else output⟩

noncomputable def oneMachine : Machine :=
  ofFinite (0 : Fin 2) 1 .write () program

theorem one_outputs (input : List Bool) :
    oneMachine.OutputsWithin input (encodeRawRat oneRat) 1 := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 .write () program
    input (encodeRawRat oneRat) 1 1 le_rfl
  · change (((advance program)^[1]) (cfg (some .write) input [])).l = none
    simp [cfg, program, emit, advance, TM2.step, TM2.stepAux,
      encodeRawRat, oneRat, CurrentAdditive.CodeDCodec.rawRatBank,
      BitMachineBankCodec.encode, BitMachineBankCodec.encodeFrom,
      EncodedCommunication.field, List.foldr]
  · change (((advance program)^[1]) (cfg (some .write) input [])).stk 1 =
      encodeRawRat oneRat
    simp [cfg, program, emit, advance, TM2.step, TM2.stepAux,
      encodeRawRat, oneRat, CurrentAdditive.CodeDCodec.rawRatBank,
      BitMachineBankCodec.encode, BitMachineBankCodec.encodeFrom,
      EncodedCommunication.field, List.foldr]

noncomputable def rowMachine : Machine :=
  SourceListMachineOuterFramed.machine oneMachine

noncomputable def rowClock (items : List (List Bool)) : Nat :=
  SourceListMachineOuter.canonicalBound
    (SourceListMachineOuterFramed.itemMachine oneMachine) items
    (SourceListMachineOuterFramed.framedOutput (fun _ => encodeRawRat oneRat))
    (SourceListMachineOuterFramed.framedBound
      (fun _ => encodeRawRat oneRat) (fun _ => 1))

theorem source_empty_row (q : Nat)
    (source : Array ((Fin q → Nat) × ℚ)) :
    rowMachine.OutputsWithin
      (CodeDCanonicalSourceV2.encodedSource source)
      (SourceListEncoding.encode
        (List.replicate source.size (encodeRawRat oneRat)))
      (rowClock ((CodeDCanonicalSourceV2.canonicalSource source).map
        CodeDSourceCodecV2.encodeEntry)) := by
  let items := (CodeDCanonicalSourceV2.canonicalSource source).map
    CodeDSourceCodecV2.encodeEntry
  have hitem : ∀ x ∈ items,
      oneMachine.OutputsWithin x (encodeRawRat oneRat) 1 := by
    intro x _
    exact one_outputs x
  have h := SourceListMachineOuterFramed.outputsWithin oneMachine items
    (fun _ => encodeRawRat oneRat) (fun _ => 1) hitem
  have hmap : items.map (fun _ => encodeRawRat oneRat) =
      List.replicate source.size (encodeRawRat oneRat) := by
    have hconst : ∀ xs : List (List Bool),
        xs.map (fun _ => encodeRawRat oneRat) =
          List.replicate xs.length (encodeRawRat oneRat) := by
      intro xs
      induction xs with
      | nil => rfl
      | cons x xs ih => simp [ih, List.replicate_succ]
    rw [hconst]
    simp [items, CodeDCanonicalSourceV2.canonicalSource]
  rw [hmap] at h
  simpa only [rowMachine, rowClock, CodeDCanonicalSourceV2.encodedSource,
    CodeDSourceCodecV2.encodeSource, CodeDCodecV2.encodeItems, items] using h

#print axioms source_empty_row

end CurrentAdditive.CylinderEmptyRowMachine
