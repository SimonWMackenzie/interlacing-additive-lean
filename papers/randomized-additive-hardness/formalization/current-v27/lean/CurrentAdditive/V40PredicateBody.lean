import CurrentAdditive.V40ThreeFieldPacket
import CurrentAdditive.MachineInvokeFull

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace CurrentAdditive.V40PredicateBody

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

variable (M : BitMachine.Machine)

abbrev Stack := MachineInvokeCore.StackN M.stackCount
abbrev Bank := Stack M → List Bool

def low (i : Fin 32) : Stack M := ⟨i.val, by omega⟩

def packSlots : Fin 9 ↪ Stack M where
  toFun i := ⟨i.val, by omega⟩
  inj' := by intro i j h; exact Fin.ext (congrArg (fun k : Stack M => k.val) h)

def callSlots : MachineInvokeCore.Slots M M.stackCount where
  machine := ⟨fun i => ⟨32 + i.val, by omega⟩, by
    intro i j h
    have hh := congrArg Fin.val h
    exact Fin.ext (by dsimp at hh; omega)⟩
  source := low M 8
  target := low M 9
  scratch := low M 31
  source_target := by intro h; have hh := congrArg Fin.val h; change (8 : Nat) = 9 at hh; omega
  source_scratch := by intro h; have hh := congrArg Fin.val h; change (8 : Nat) = 31 at hh; omega
  target_scratch := by intro h; have hh := congrArg Fin.val h; change (9 : Nat) = 31 at hh; omega
  source_machine := by intro i h; have hh := congrArg Fin.val h; change 8 = 32 + i.val at hh; omega
  target_machine := by intro i h; have hh := congrArg Fin.val h; change 9 = 32 + i.val at hh; omega
  scratch_machine := by intro i h; have hh := congrArg Fin.val h; change 31 = 32 + i.val at hh; omega

def packProgram (l : V40ThreeFieldPacket.Label) :=
  BitMachineStackEmbedding.stackStmt (packSlots M) (V40ThreeFieldPacket.program l)

def clearProgram : Bool → TM2.Stmt (fun _ : Stack M => Bool) Bool (Unit × Option Bool)
  | false => BitMachineClearBank.clearStep (low M 8) false true
  | true => .halt

def packCallProgram := BitMachineRawSequence.program (packProgram M)
  (MachineInvokeFull.program (callSlots M)) (MachineInvokeFull.start (callSlots M))
  V40ThreeFieldPacket.initial (MachineInvokeFull.control (callSlots M))

def program := BitMachineRawSequence.program (packCallProgram M) (clearProgram M) false
  (V40ThreeFieldPacket.initial, MachineInvokeFull.control (callSlots M)) (((), none) : Unit × Option Bool)

def entry := BitMachineRawSequence.leftLabel
  (LA := BitMachineRawSequence.Label V40ThreeFieldPacket.Label (MachineInvokeFull.LabelFull M))
  (LB := Bool) (BitMachineRawSequence.leftLabel V40ThreeFieldPacket.entry)

def initial := ((V40ThreeFieldPacket.initial, MachineInvokeFull.control (callSlots M)),
  (((), none) : Unit × Option Bool))

theorem pack_run (S : Bank M) (x y z : List Bool)
    (h0 : S (low M 0) = x) (h1 : S (low M 1) = y) (h2 : S (low M 2) = z)
    (hblank : ∀ i : Fin 6, S ⟨i.val + 3, by omega⟩ = []) :
    ∃ t ≤ 3 * (V40ThreeFieldPacket.bytes x y z).length + 8,
      ((advance (packProgram M))^[t])
        (⟨some V40ThreeFieldPacket.entry, V40ThreeFieldPacket.initial, S⟩ : TM2.Cfg (fun _ : Stack M => Bool) _ _) =
        ⟨none, V40ThreeFieldPacket.initial,
          Function.update S (low M 8) (V40ThreeFieldPacket.bytes x y z)⟩ := by
  let R : V40ThreeFieldPacket.Bank := fun i => S (packSlots M i)
  obtain ⟨t, ht, hr⟩ := V40ThreeFieldPacket.run R x y z h0 h1 h2 hblank
  have hs := BitMachineStackRun.run (packSlots M) S V40ThreeFieldPacket.program
    (⟨some V40ThreeFieldPacket.entry, V40ThreeFieldPacket.initial, R⟩ : TM2.Cfg (fun _ : Fin 9 => Bool) _ _) t
  rw [hr] at hs
  have hbank : BitMachineStackEmbedding.bank (packSlots M) S R = S :=
    BitMachineStackEmbedding.bank_restrict (packSlots M) S
  have hout : BitMachineStackEmbedding.bank (packSlots M) S
      (Function.update R 8 (V40ThreeFieldPacket.bytes x y z)) =
      Function.update S (low M 8) (V40ThreeFieldPacket.bytes x y z) := by
    rw [BitMachineStackEmbedding.bank_update, hbank]
    rfl
  refine ⟨t, ht, ?_⟩
  simpa only [packProgram, BitMachineStackEmbedding.stackCfg, hbank, hout] using hs

theorem clear_run (S : Bank M) :
    ((advance (clearProgram M))^[(S (low M 8)).length + 2])
      (⟨some false, ((), none), S⟩ : TM2.Cfg (fun _ : Stack M => Bool) Bool (Unit × Option Bool)) =
      ⟨none, ((), none), Function.update S (low M 8) []⟩ := by
  have h := BitMachineClearBank.clear_one_run (clearProgram M) (low M 8)
    false true rfl () S
  rw [show (S (low M 8)).length + 2 = (S (low M 8)).length + 1 + 1 by omega,
    Function.iterate_succ_apply']
  rw [h]
  rfl

/-- A real preserving request builder, machine invocation, and packet cleanup.
The sole supplier premise is the raw test machine's own output theorem. -/
theorem run (S : Bank M) (x y z : List Bool) (bit : Bool) (T : Nat)
    (h0 : S (low M 0) = x) (h1 : S (low M 1) = y) (h2 : S (low M 2) = z)
    (hblank : ∀ i : Fin 6, S ⟨i.val + 3, by omega⟩ = [])
    (hflag : S (low M 9) = []) (hscratch : S (low M 31) = [])
    (hhigh : ∀ i, S ((callSlots M).machine i) = [])
    (hM : M.OutputsWithin (V40ThreeFieldPacket.bytes x y z) [bit] T) :
    ∃ t ≤ 4 * (V40ThreeFieldPacket.bytes x y z).length +
        MachineInvokeFull.uniformBound M (V40ThreeFieldPacket.bytes x y z) T + 12,
      ((advance (program M))^[t])
        (⟨some (entry M), initial M, S⟩ : TM2.Cfg (fun _ : Stack M => Bool) _ _) =
        ⟨none, initial M, Function.update S (low M 9) [bit]⟩ := by
  let bytes := V40ThreeFieldPacket.bytes x y z
  let S1 := Function.update S (low M 8) bytes
  let S2 := Function.update S1 (low M 9) [bit]
  obtain ⟨a, ha, hpack⟩ := pack_run M S x y z h0 h1 h2 hblank
  obtain ⟨b, hb, hcall⟩ := MachineInvokeFull.invoke_run_uniform (callSlots M) S1 bytes [bit] T
    (by simp [S1, callSlots])
    (by simpa [S1, callSlots, low, Fin.ext_iff] using hflag)
    (by simpa [S1, callSlots, low, Fin.ext_iff] using hscratch)
    (by
      intro i
      have hh := hhigh i
      have hne : 32 + i.val ≠ 8 := by omega
      simpa [S1, callSlots, low, Function.update_apply, Fin.ext_iff, hne] using hh) hM
  have hclear := clear_run M S2
  have hlen : (S2 (low M 8)).length = bytes.length := by
    simp [S2, S1, low, Fin.ext_iff]
  have hout : Function.update S2 (low M 8) [] = Function.update S (low M 9) [bit] := by
    have h8 : S (low M 8) = [] := hblank 5
    have h89 : low M 8 ≠ low M 9 := by
      intro h
      have hh := congrArg Fin.val h
      change (8 : Nat) = 9 at hh
      omega
    funext i
    by_cases h8i : i = low M 8
    · subst i
      rw [Function.update_self, Function.update_of_ne h89]
      exact h8.symm
    · by_cases h9i : i = low M 9
      · subst i
        simp [S2, S1, low, Fin.ext_iff]
      · simp [S2, S1, Function.update_apply, h8i, h9i]
  rw [hout] at hclear
  obtain ⟨ab, hab, hrab⟩ := BitMachineRawSequence.runs (packProgram M)
    (MachineInvokeFull.program (callSlots M)) V40ThreeFieldPacket.entry
    (MachineInvokeFull.start (callSlots M)) V40ThreeFieldPacket.initial V40ThreeFieldPacket.initial
    (MachineInvokeFull.control (callSlots M)) (MachineInvokeFull.control (callSlots M))
    S S1 S2 a b hpack hcall
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs (packCallProgram M) (clearProgram M)
    (BitMachineRawSequence.leftLabel V40ThreeFieldPacket.entry) false
    (V40ThreeFieldPacket.initial, MachineInvokeFull.control (callSlots M))
    (V40ThreeFieldPacket.initial, MachineInvokeFull.control (callSlots M)) ((), none) ((), none)
    S S2 (Function.update S (low M 9) [bit]) ab ((S2 (low M 8)).length + 2) hrab hclear
  exact ⟨t, by rw [hlen] at ht; dsimp only [bytes] at *; omega,
    by simpa only [program, entry, initial, packCallProgram] using hr⟩

end CurrentAdditive.V40PredicateBody
