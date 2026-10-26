import EthInapproximability.CurrentPaper.BitMachineBinaryMultiply
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
Two literal binary multiplications on disjoint banks. This is a private
candidate for the rational-product part of the locked `det:code` source.
The left factor of each multiplication is little-endian, and the right factor
is MSB-first, exactly as in `BitMachineBinaryMultiply.standard_value`.
-/

namespace EthInapproximability.CurrentPaper.RationalProductCore

open Turing BitMachineEncoding BitMachineComposition

abbrev Stack := Fin 12
abbrev HalfLabel := BitMachineBinaryMultiply.Label ⊕ Unit
abbrev HalfControl := BitMachineBinaryMultiply.Control × Unit
abbrev Label := BitMachineRawSequence.Label HalfLabel HalfLabel
abbrev Control := BitMachineRawSequence.Control HalfControl HalfControl
abbrev Bank := Stack → List Bool

def firstStacks : (Fin 6 ⊕ Fin 6) ≃ Stack := finSumFinEquiv

def swapHalves : (Fin 6 ⊕ Fin 6) ≃ (Fin 6 ⊕ Fin 6) where
  toFun := Sum.swap
  invFun := Sum.swap
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x <;> rfl

def secondStacks : (Fin 6 ⊕ Fin 6) ≃ Stack := swapHalves.trans firstStacks

def firstProgram : HalfLabel →
    TM2.Stmt (fun _ : Stack => Bool) HalfLabel HalfControl
  | .inl l => renameStmt firstStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt none (BitMachineBinaryMultiply.finProgram l))
  | .inr () => .halt

def secondProgram : HalfLabel →
    TM2.Stmt (fun _ : Stack => Bool) HalfLabel HalfControl
  | .inl l => renameStmt secondStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt none (BitMachineBinaryMultiply.finProgram l))
  | .inr () => .halt

def mulStart : BitMachineBinaryMultiply.Label := .inr (.inr ())
def halfStart : HalfLabel := .inl mulStart
def halfInitial : HalfControl := (BitMachineBinaryMultiply.initial, ())

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineRawSequence.program firstProgram secondProgram
    halfStart halfInitial halfInitial

def firstBank (source multiplier : List Bool) : Fin 6 → List Bool :=
  BitMachineBinaryMultiply.initialBank source multiplier
def firstFinal (source multiplier : List Bool) : Fin 6 → List Bool :=
  BitMachineBinaryMultiply.finalBank source multiplier

def inputBank (a b c d : List Bool) : Bank :=
  fun k => (Sum.elim (firstBank a c) (firstBank b d)) (firstStacks.symm k)

def outputBank (a b c d : List Bool) : Bank :=
  fun k => (Sum.elim (firstFinal a c) (firstFinal b d)) (firstStacks.symm k)

def middleBank (a b c d : List Bool) : Bank :=
  fun k => (Sum.elim (firstFinal a c) (firstBank b d)) (firstStacks.symm k)

theorem first_run (a b c d : List Bool) :
    ∃ t ≤ (c.length + 1) * (4 * (a.length + 2 * c.length) + 7),
      ((advance firstProgram)^[t])
        (⟨some halfStart, halfInitial, inputBank a b c d⟩ :
          TM2.Cfg (fun _ : Stack => Bool) HalfLabel HalfControl) =
        ⟨none, halfInitial, middleBank a b c d⟩ := by
  obtain ⟨t, ht, hr⟩ := BitMachineBinaryMultiply.fin_run a c
  have hr' : ((advance BitMachineBinaryMultiply.finProgram)^[t]
      (⟨some mulStart, BitMachineBinaryMultiply.initial,
        BitMachineBinaryMultiply.initialBank a c⟩ :
        TM2.Cfg (fun _ : Fin 6 => Bool) BitMachineBinaryMultiply.Label
          BitMachineBinaryMultiply.Control)) =
      ⟨none, BitMachineBinaryMultiply.initial,
        BitMachineBinaryMultiply.finalBank a c⟩ := by
    simpa only [mulStart] using hr
  have hh : (((advance BitMachineBinaryMultiply.finProgram)^[t])
      (⟨some mulStart, BitMachineBinaryMultiply.initial, BitMachineBinaryMultiply.initialBank a c⟩ :
        TM2.Cfg (fun _ : Fin 6 => Bool) BitMachineBinaryMultiply.Label BitMachineBinaryMultiply.Control)).l = none := by
    rw [hr']
  have hQ : ∀ l, firstProgram (.inl l) =
      renameStmt firstStacks (Equiv.refl _) (Equiv.refl _)
        (liftStmt none (BitMachineBinaryMultiply.finProgram l)) := by intro l; rfl
  obtain ⟨u, hu, hrun⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    firstStacks (Equiv.refl _) (Equiv.refl _)
    BitMachineBinaryMultiply.finProgram firstProgram none hQ () (firstBank b d)
    (⟨some mulStart, BitMachineBinaryMultiply.initial, BitMachineBinaryMultiply.initialBank a c⟩ :
      TM2.Cfg (fun _ : Fin 6 => Bool) BitMachineBinaryMultiply.Label BitMachineBinaryMultiply.Control) t hh
  refine ⟨u, hu.trans ht, ?_⟩
  rw [hr'] at hrun
  simpa only [renameCfg, liftCfg, inputBank, middleBank, firstBank, firstFinal,
    firstStacks, halfStart, halfInitial] using hrun

theorem second_run (a b c d : List Bool) :
    ∃ t ≤ (d.length + 1) * (4 * (b.length + 2 * d.length) + 7),
      ((advance secondProgram)^[t])
        (⟨some halfStart, halfInitial, middleBank a b c d⟩ :
          TM2.Cfg (fun _ : Stack => Bool) HalfLabel HalfControl) =
        ⟨none, halfInitial, outputBank a b c d⟩ := by
  obtain ⟨t, ht, hr⟩ := BitMachineBinaryMultiply.fin_run b d
  have hr' : ((advance BitMachineBinaryMultiply.finProgram)^[t]
      (⟨some mulStart, BitMachineBinaryMultiply.initial,
        BitMachineBinaryMultiply.initialBank b d⟩ :
        TM2.Cfg (fun _ : Fin 6 => Bool) BitMachineBinaryMultiply.Label
          BitMachineBinaryMultiply.Control)) =
      ⟨none, BitMachineBinaryMultiply.initial,
        BitMachineBinaryMultiply.finalBank b d⟩ := by
    simpa only [mulStart] using hr
  have hh : (((advance BitMachineBinaryMultiply.finProgram)^[t])
      (⟨some mulStart, BitMachineBinaryMultiply.initial, BitMachineBinaryMultiply.initialBank b d⟩ :
        TM2.Cfg (fun _ : Fin 6 => Bool) BitMachineBinaryMultiply.Label BitMachineBinaryMultiply.Control)).l = none := by
    rw [hr']
  have hQ : ∀ l, secondProgram (.inl l) =
      renameStmt secondStacks (Equiv.refl _) (Equiv.refl _)
        (liftStmt none (BitMachineBinaryMultiply.finProgram l)) := by intro l; rfl
  obtain ⟨u, hu, hrun⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    secondStacks (Equiv.refl _) (Equiv.refl _)
    BitMachineBinaryMultiply.finProgram secondProgram none hQ () (firstFinal a c)
    (⟨some mulStart, BitMachineBinaryMultiply.initial, BitMachineBinaryMultiply.initialBank b d⟩ :
      TM2.Cfg (fun _ : Fin 6 => Bool) BitMachineBinaryMultiply.Label BitMachineBinaryMultiply.Control) t hh
  refine ⟨u, hu.trans ht, ?_⟩
  rw [hr'] at hrun
  have hstart :
      renameCfg secondStacks (Equiv.refl HalfLabel) (Equiv.refl HalfControl)
        (liftCfg (none : Option Unit) () (firstFinal a c)
          (⟨some mulStart, BitMachineBinaryMultiply.initial,
            BitMachineBinaryMultiply.initialBank b d⟩ :
            TM2.Cfg (fun _ : Fin 6 => Bool) BitMachineBinaryMultiply.Label
              BitMachineBinaryMultiply.Control)) =
      ⟨some halfStart, halfInitial, middleBank a b c d⟩ := by
    unfold renameCfg liftCfg middleBank firstFinal firstBank halfStart halfInitial
    congr 1
    funext k
    fin_cases k <;> rfl
  have hend :
      renameCfg secondStacks (Equiv.refl HalfLabel) (Equiv.refl HalfControl)
        (liftCfg (none : Option Unit) () (firstFinal a c)
          (⟨none, BitMachineBinaryMultiply.initial,
            BitMachineBinaryMultiply.finalBank b d⟩ :
            TM2.Cfg (fun _ : Fin 6 => Bool) BitMachineBinaryMultiply.Label
              BitMachineBinaryMultiply.Control)) =
      ⟨none, halfInitial, outputBank a b c d⟩ := by
    unfold renameCfg liftCfg outputBank firstFinal halfInitial
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [← hstart, ← hend]
  exact hrun

theorem local_run (a b c d : List Bool) :
    ∃ t ≤ (c.length + 1) * (4 * (a.length + 2 * c.length) + 7) +
      (d.length + 1) * (4 * (b.length + 2 * d.length) + 7) + 1,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel halfStart),
          (halfInitial, halfInitial), inputBank a b c d⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none, (halfInitial, halfInitial), outputBank a b c d⟩ := by
  obtain ⟨ta, hta, ha⟩ := first_run a b c d
  obtain ⟨tb, htb, hb⟩ := second_run a b c d
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    firstProgram secondProgram halfStart halfStart halfInitial halfInitial
    halfInitial halfInitial (inputBank a b c d) (middleBank a b c d)
    (outputBank a b c d) ta tb ha hb
  exact ⟨t, by omega, hr⟩

theorem numerator_value (a b c d : List Bool) :
    EncodedCommunication.bitsValue (outputBank a b c d 0) =
      EncodedCommunication.bitsValue a * BitMachineBinaryMultiply.msbValue c := by
  simpa [outputBank, firstFinal, BitMachineBinaryMultiply.finalBank, BitMachineBinaryMultiply.finBank, BitMachineBinaryMultiply.finStack,
    BitMachineBinaryMultiply.cfg, BitMachineBinaryMultiply.rightBank, firstStacks, finSumFinEquiv,
    BitMachineBinaryAddAny.bank, BitMachineBinaryAdd.bank, Fin.addCases]
    using BitMachineBinaryMultiply.standard_value a c

theorem denominator_value (a b c d : List Bool) :
    EncodedCommunication.bitsValue (outputBank a b c d 6) =
      EncodedCommunication.bitsValue b * BitMachineBinaryMultiply.msbValue d := by
  simpa [outputBank, firstFinal, BitMachineBinaryMultiply.finalBank, BitMachineBinaryMultiply.finBank, BitMachineBinaryMultiply.finStack,
    BitMachineBinaryMultiply.cfg, BitMachineBinaryMultiply.rightBank, firstStacks, finSumFinEquiv,
    BitMachineBinaryAddAny.bank, BitMachineBinaryAdd.bank, Fin.addCases]
    using BitMachineBinaryMultiply.standard_value b d

theorem denominator_pos (a b c d : List Bool)
    (hb : 0 < EncodedCommunication.bitsValue b) (hd : 0 < BitMachineBinaryMultiply.msbValue d) :
    0 < EncodedCommunication.bitsValue (outputBank a b c d 6) := by
  rw [denominator_value]
  exact Nat.mul_pos hb hd

end EthInapproximability.CurrentPaper.RationalProductCore
