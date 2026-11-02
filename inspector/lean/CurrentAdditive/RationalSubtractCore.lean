import CurrentAdditive.SignedMagnitudeSubtract
import CurrentAdditive.RationalProductPacket
import CurrentAdditive.RationalProductAdapter
import CurrentAdditive.CodeDCodec
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-!
A fixed physical bank program for unreduced rational subtraction.  The input
bank has two multiplication workspaces, two signs, and five subtraction
scratch/output stacks.  The three products are computed by the two-product
packet program; the signed difference is then computed by the nine-stack
subtractor.  A separate parser/router must turn two nested RawRat records into
this bank layout.
-/

namespace EthInapproximability.CurrentPaper.RationalSubtractCore

open Turing BitMachineEncoding BitMachineStackEmbedding
open CurrentAdditive.CodeDCodec

abbrev Bank := Fin 32 → List Bool

def crossSlots : Fin 12 ↪ Fin 32 := ⟨![0,1,2,3,4,5,6,7,8,9,10,11], by decide⟩
def denSlots : Fin 12 ↪ Fin 32 := ⟨![12,13,14,15,16,17,18,19,20,21,22,23], by decide⟩
def subSlots : Fin 9 ↪ Fin 32 := ⟨![24,25,0,6,27,28,29,30,31], by decide⟩

def crossProgram : RationalProductPacket.Label →
    TM2.Stmt (fun _ : Fin 32 => Bool) RationalProductPacket.Label
      RationalProductPacket.Control :=
  fun l => stackStmt crossSlots (RationalProductPacket.program l)

def denProgram : RationalProductPacket.Label →
    TM2.Stmt (fun _ : Fin 32 => Bool) RationalProductPacket.Label
      RationalProductPacket.Control :=
  fun l => stackStmt denSlots (RationalProductPacket.program l)

def subProgram : SignedMagnitudeSubtract.Label →
    TM2.Stmt (fun _ : Fin 32 => Bool) SignedMagnitudeSubtract.Label
      SignedMagnitudeSubtract.Control :=
  fun l => stackStmt subSlots (SignedMagnitudeSubtract.program l)

abbrev ProductLabel := BitMachineRawSequence.Label
  RationalProductPacket.Label RationalProductPacket.Label
abbrev ProductControl := BitMachineRawSequence.Control
  RationalProductPacket.Control RationalProductPacket.Control

def products : ProductLabel →
    TM2.Stmt (fun _ : Fin 32 => Bool) ProductLabel ProductControl :=
  BitMachineRawSequence.program crossProgram denProgram
    (.inr 0) RationalProductPacket.initial RationalProductPacket.initial

abbrev Label := BitMachineRawSequence.Label ProductLabel SignedMagnitudeSubtract.Label
abbrev Control := BitMachineRawSequence.Control ProductControl
  SignedMagnitudeSubtract.Control

def start : Label :=
  BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inr 0))
def initial : Control :=
  ((RationalProductPacket.initial, RationalProductPacket.initial),
    SignedMagnitudeSubtract.initial)

def program : Label → TM2.Stmt (fun _ : Fin 32 => Bool) Label Control :=
  BitMachineRawSequence.program products subProgram .signA
    (RationalProductPacket.initial, RationalProductPacket.initial)
    SignedMagnitudeSubtract.initial

def restricted (ι : Fin 12 ↪ Fin 32) (S : Bank) : Fin 12 → List Bool :=
  fun i => S (ι i)

noncomputable def crossBank (S : Bank) : Bank :=
  bank crossSlots S (RationalProductPacket.resultBank (restricted crossSlots S))

noncomputable def denBank (S : Bank) : Bank :=
  bank denSlots S (RationalProductPacket.resultBank (restricted denSlots S))

noncomputable def productBank (S : Bank) : Bank := denBank (crossBank S)

def subInput (S : Bank) : Fin 9 → List Bool := fun i => S (subSlots i)

noncomputable def finalBank (S : Bank) : Bank :=
  bank subSlots (productBank S)
    (SignedMagnitudeSubtract.finalBank (subInput (productBank S)))

theorem cross_run (S : Bank) :
    ∃ t ≤ RationalProductPacket.clearTime (restricted crossSlots S) +
        RationalProductPacket.rawTime (restricted crossSlots S),
      ((advance crossProgram)^[t])
        (⟨some (.inr 0), RationalProductPacket.initial, S⟩ :
          TM2.Cfg (fun _ : Fin 32 => Bool) RationalProductPacket.Label
            RationalProductPacket.Control) =
        ⟨none, RationalProductPacket.initial, crossBank S⟩ := by
  obtain ⟨t, ht, hr⟩ := RationalProductPacket.local_run (restricted crossSlots S)
  refine ⟨t, ht, ?_⟩
  have he := BitMachineStackRun.run crossSlots S RationalProductPacket.program
    (⟨some (.inr 0), RationalProductPacket.initial, restricted crossSlots S⟩ :
      TM2.Cfg (fun _ : Fin 12 => Bool) RationalProductPacket.Label
        RationalProductPacket.Control) t
  rw [hr] at he
  have hi : bank crossSlots S (restricted crossSlots S) = S :=
    bank_restrict crossSlots S
  simpa only [crossProgram, BitMachineStackEmbedding.stackCfg, hi,
    crossBank] using he

theorem den_run (S : Bank) :
    ∃ t ≤ RationalProductPacket.clearTime (restricted denSlots S) +
        RationalProductPacket.rawTime (restricted denSlots S),
      ((advance denProgram)^[t])
        (⟨some (.inr 0), RationalProductPacket.initial, S⟩ :
          TM2.Cfg (fun _ : Fin 32 => Bool) RationalProductPacket.Label
            RationalProductPacket.Control) =
        ⟨none, RationalProductPacket.initial, denBank S⟩ := by
  obtain ⟨t, ht, hr⟩ := RationalProductPacket.local_run (restricted denSlots S)
  refine ⟨t, ht, ?_⟩
  have he := BitMachineStackRun.run denSlots S RationalProductPacket.program
    (⟨some (.inr 0), RationalProductPacket.initial, restricted denSlots S⟩ :
      TM2.Cfg (fun _ : Fin 12 => Bool) RationalProductPacket.Label
        RationalProductPacket.Control) t
  rw [hr] at he
  have hi : bank denSlots S (restricted denSlots S) = S :=
    bank_restrict denSlots S
  simpa only [denProgram, BitMachineStackEmbedding.stackCfg, hi,
    denBank] using he

theorem subtract_run (S : Bank) :
    ((advance subProgram)^[SignedMagnitudeSubtract.localTime (subInput S)])
      (⟨some .signA, SignedMagnitudeSubtract.initial, S⟩ :
        TM2.Cfg (fun _ : Fin 32 => Bool) SignedMagnitudeSubtract.Label
          SignedMagnitudeSubtract.Control) =
      ⟨none, SignedMagnitudeSubtract.initial,
        bank subSlots S (SignedMagnitudeSubtract.finalBank (subInput S))⟩ := by
  have he := BitMachineStackRun.run subSlots S SignedMagnitudeSubtract.program
    (⟨some .signA, SignedMagnitudeSubtract.initial, subInput S⟩ :
      TM2.Cfg (fun _ : Fin 9 => Bool) SignedMagnitudeSubtract.Label
        SignedMagnitudeSubtract.Control)
    (SignedMagnitudeSubtract.localTime (subInput S))
  have hr : ((advance SignedMagnitudeSubtract.program)^[
      SignedMagnitudeSubtract.localTime (subInput S)])
      (⟨some .signA, SignedMagnitudeSubtract.initial, subInput S⟩ :
        TM2.Cfg (fun _ : Fin 9 => Bool) SignedMagnitudeSubtract.Label
          SignedMagnitudeSubtract.Control) =
      ⟨none, SignedMagnitudeSubtract.initial,
        SignedMagnitudeSubtract.finalBank (subInput S)⟩ := by
    simpa only [SignedMagnitudeSubtract.run] using
      SignedMagnitudeSubtract.local_run (subInput S)
  rw [hr] at he
  have hi : bank subSlots S (subInput S) = S := bank_restrict subSlots S
  simpa only [subProgram, BitMachineStackEmbedding.stackCfg, hi] using he

theorem local_run (S : Bank) :
    ∃ t ≤
        RationalProductPacket.clearTime (restricted crossSlots S) +
        RationalProductPacket.rawTime (restricted crossSlots S) +
        RationalProductPacket.clearTime (restricted denSlots (crossBank S)) +
        RationalProductPacket.rawTime (restricted denSlots (crossBank S)) +
        SignedMagnitudeSubtract.localTime (subInput (productBank S)) + 2,
      ((advance program)^[t])
        (⟨some start, initial, S⟩ :
          TM2.Cfg (fun _ : Fin 32 => Bool) Label Control) =
        ⟨none, initial, finalBank S⟩ := by
  obtain ⟨t₁, ht₁, h₁⟩ := cross_run S
  obtain ⟨t₂, ht₂, h₂⟩ := den_run (crossBank S)
  obtain ⟨tp, htp, hp⟩ := BitMachineRawSequence.runs
    crossProgram denProgram (.inr 0) (.inr 0)
    RationalProductPacket.initial RationalProductPacket.initial
    RationalProductPacket.initial RationalProductPacket.initial
    S (crossBank S) (productBank S) t₁ t₂ h₁ h₂
  have hs := subtract_run (productBank S)
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    products subProgram
    (BitMachineRawSequence.leftLabel (.inr 0)) .signA
    (RationalProductPacket.initial, RationalProductPacket.initial)
    (RationalProductPacket.initial, RationalProductPacket.initial)
    SignedMagnitudeSubtract.initial SignedMagnitudeSubtract.initial
    S (productBank S) (finalBank S) tp
    (SignedMagnitudeSubtract.localTime (subInput (productBank S))) hp hs
  refine ⟨t, ?_, ?_⟩
  · omega
  · simpa only [program, start, initial] using hr

end EthInapproximability.CurrentPaper.RationalSubtractCore
