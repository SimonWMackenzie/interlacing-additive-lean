import EthInapproximability.CurrentPaper.MatrixWeightedRowOrderSplit
import EthInapproximability.CurrentPaper.MatrixAddressMachine
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! # Physical item-order translation to a raw Stage--4 row ordinal

The explicit table codec is `MatrixWeightedRowOrderLookup.orderWord`.
For a vertex label, `aux=false`; for an auxiliary label, `aux=true`.
The latter physically copies `nv` into the offset cell before adding it to
the quotient. The table producer is outside this component.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedRowOrderMachine

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := Fin 23

def globalSlots : Stack ↪ Fin 64 where
  toFun := ![54,17,18,16,60,25,7,8,9,10,11,12,13,14,23,55,56,57,58,59,61,62,63]
  inj' := by decide

def splitSlots : MatrixWeightedRowOrderSplit.Stack ↪ Stack where
  toFun := ![0,1,6,7,8,9,10,11]
  inj' := by decide

def offsetCopySlots : Fin 3 ↪ Stack where
  toFun := ![2,14,6]
  inj' := by decide

def offsetAddressSlots : Fin 6 ↪ Stack where
  toFun := ![10,12,14,15,16,13]
  inj' := by decide

def lookupSlots : MatrixWeightedRowOrderLookup.Stack ↪ Stack where
  toFun := ![13,4,17,18,19]
  inj' := by decide

def sourceCopySlots : Fin 3 ↪ Stack where
  toFun := ![3,5,20]
  inj' := by decide

def rowAddressSlots : Fin 6 ↪ Stack where
  toFun := ![19,1,9,21,22,5]
  inj' := by decide

inductive Label where
  | split (aux : Bool) (l : MatrixWeightedRowOrderSplit.Label)
  | afterSplit (aux : Bool)
  | offsetCopy (l : BitMachineCopy.Label)
  | afterOffset
  | offsetAddress (l : MatrixAddressMachine.Label)
  | afterAddress
  | lookup (l : MatrixWeightedRowOrderLookup.Label)
  | afterLookup
  | sourceCopy (l : BitMachineCopy.Label)
  | afterSource
  | rowAddress (l : MatrixAddressMachine.Label)
  deriving DecidableEq, Fintype

inductive State where
  | split (v : MatrixWeightedRowOrderSplit.Control)
  | copy (v : Option Bool)
  | address (v : Bool)
  | lookup (v : MatrixWeightedRowOrderLookup.Control)
  deriving DecidableEq, Fintype

def splitState : State → MatrixWeightedRowOrderSplit.Control
  | .split v => v
  | _ => (none,false)

def copyState : State → Option Bool
  | .copy v => v
  | _ => none

def addressState : State → Bool
  | .address v => v
  | _ => false

def lookupState : State → MatrixWeightedRowOrderLookup.Control
  | .lookup v => v
  | _ => none

def start (aux : Bool) : Label := .split aux (.inl .scan)
def initial : State := .split (none,false)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label State
  | .split aux l => stmt splitSlots (Label.split aux)
      State.split splitState (some (.afterSplit aux))
      (MatrixWeightedRowOrderSplit.program l)
  | .afterSplit aux => .push 12 (fun _ => true)
      (.load (fun _ => if aux then .copy none else .address false)
        (.goto (fun _ => if aux then .offsetCopy .scan else .offsetAddress .outer)))
  | .offsetCopy l => stmt offsetCopySlots Label.offsetCopy
      State.copy copyState (some .afterOffset) (BitMachineCopy.program l)
  | .afterOffset => .load (fun _ => .address false)
      (.goto (fun _ => .offsetAddress .outer))
  | .offsetAddress l => stmt offsetAddressSlots Label.offsetAddress
      State.address addressState (some .afterAddress)
      (MatrixAddressMachine.program l)
  | .afterAddress => .load (fun _ => .lookup none)
      (.goto (fun _ => .lookup .select))
  | .lookup l => stmt lookupSlots Label.lookup
      State.lookup lookupState (some .afterLookup)
      (MatrixWeightedRowOrderLookup.program l)
  | .afterLookup => .load (fun _ => .copy none)
      (.goto (fun _ => .sourceCopy .scan))
  | .sourceCopy l => stmt sourceCopySlots Label.sourceCopy
      State.copy copyState (some .afterSource) (BitMachineCopy.program l)
  | .afterSource => .load (fun _ => .address false)
      (.goto (fun _ => .rowAddress .outer))
  | .rowAddress l => stmt rowAddressSlots Label.rowAddress
      State.address addressState none (MatrixAddressMachine.program l)

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label State
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

end EthInapproximability.CurrentPaper.MatrixWeightedRowOrderMachine
