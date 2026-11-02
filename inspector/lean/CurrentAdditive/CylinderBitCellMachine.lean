import CurrentAdditive.CylinderFeatureCodec
import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! Fixed finite-stack writer for one already evaluated cylinder bit.  The
output is exactly the agreed RawRat Bank3 encoding of zero or one.  The program
contains both fixed byte patterns in its finite statement table. -/

namespace CurrentAdditive.CylinderBitCellMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.CodeDCodec
open CurrentAdditive.CylinderFeatureCodec

inductive Label where
  | write
  deriving DecidableEq, Fintype

def emit (bits : List Bool) :
    TM2.Stmt (fun _ : Fin 2 => Bool) Label (Option Bool) :=
  bits.reverse.foldr (fun bit next => push 1 (fun _ => bit) next) halt

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label (Option Bool)
  | .write => pop 0 (fun _ bit => bit)
      (branch Option.isSome
        (branch (fun bit => bit.getD false)
          (emit (encodeRawRat oneRat))
          (emit (encodeRawRat zeroRat)))
        halt)

def bank (input output : List Bool) : Fin 2 → List Bool :=
  fun k => if k = 0 then input else output

def cfg (l : Option Label) (v : Option Bool)
    (input output : List Bool) : TM2.Cfg (fun _ : Fin 2 => Bool) Label (Option Bool) :=
  ⟨l, v, bank input output⟩

def run (t : Nat) (c : TM2.Cfg (fun _ : Fin 2 => Bool) Label (Option Bool)) :=
  ((advance program)^[t]) c

theorem run_cell (b : Bool) :
    run 1 (cfg (some .write) none [b] []) =
      cfg none (some b) [] (encodeRawRat (if b then oneRat else zeroRat)) := by
  cases b <;>
    simp [run, advance, TM2.step, TM2.stepAux, program, emit,
      cfg, bank, encodeRawRat, zeroRat, oneRat,
      CurrentAdditive.CodeDCodec.rawRatBank,
      EthInapproximability.CurrentPaper.BitMachineBankCodec.encode,
      EthInapproximability.CurrentPaper.BitMachineBankCodec.encodeFrom,
      EthInapproximability.CurrentPaper.EncodedCommunication.field,
      List.foldr]
  all_goals
    funext k
    fin_cases k <;> rfl

#print axioms run_cell

end CurrentAdditive.CylinderBitCellMachine
