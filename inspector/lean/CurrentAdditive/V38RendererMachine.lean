import CurrentAdditive.V38RendererClock
import EthInapproximability.CurrentPaper.BitMachineEncoding

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option synthInstance.maxSize 65536

namespace CurrentAdditive.V38PhysicalRenderer

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
open Paper2.YaoSourceCodec Paper2.YaoMachine Paper2.HeaderA

def inputCell (t : ℕ) : Cell t 16 := .source (sN 0)
def outputCell (t : ℕ) : Cell t 16 := .header outH

def machine (t : ℕ) : BitMachine.Machine :=
  ofFinite (P:=program t) (inputCell t) (outputCell t)
    (BitMachineRawSequence.leftLabel (prefixStart t))
    (prefixControl t,printerControl t)

theorem initial_bank (t : ℕ) (x : YaoSource t) :
    bank (sourceEmbed t 16) (blank t 16) (initBank 0 x []) =
      fun j : Cell t 16 => if j=inputCell t then encode x else [] := by
  have hlocal : initBank 0 x [] = Function.update (fun _ => []) (sN 0) (encode x) := by
    funext j
    simp [initBank, Function.update]
  have hblank : bank (sourceEmbed t 16) (blank t 16) (fun _ => []) = blank t 16 := by
    apply bank_eq_self
    intro k
    rfl
  rw [hlocal, bank_update, hblank]
  funext j
  simp [blank,inputCell,sourceEmbed,Function.update]

theorem outputs (t : ℕ) (ht : 4 ≤ t) (x : YaoSource t) :
    (machine t).OutputsWithin (encode x) (word x) (clock x) := by
  obtain ⟨steps,hs,hhalt,hout⟩ := raw_run t ht x
  unfold machine
  apply outputsWithin_of_raw_run (inputCell t) (outputCell t)
    (BitMachineRawSequence.leftLabel (prefixStart t))
    (prefixControl t,printerControl t) (program t)
    (encode x) (word x) steps (clock x) hs
  · change (((advance (program t))^[steps])
      ⟨some _,_,fun j => if j=inputCell t then encode x else []⟩).l=none
    rw [←initial_bank t x]
    exact hhalt
  · change (((advance (program t))^[steps])
      ⟨some _,_,fun j => if j=inputCell t then encode x else []⟩).stk (outputCell t)=word x
    rw [←initial_bank t x]
    exact hout

#print axioms machine
#print axioms outputs
end CurrentAdditive.V38PhysicalRenderer
