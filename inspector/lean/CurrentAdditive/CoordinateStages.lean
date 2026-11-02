import CurrentAdditive.CanonicalPhysicalSelectorDigitFull
import CurrentAdditive.CanonicalPhysicalPosition
import CurrentAdditive.CanonicalPhysicalPayloadIndex
import EthInapproximability.CurrentPaper.CopyFill
import EthInapproximability.CurrentPaper.RegionClear

namespace CurrentAdditive.FiniteFieldCoordinate

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.BitMachineStackRun
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable

abbrev Stack := Fin 40

-- The seven public cells are copied once to their private working cells.
def jobs : List (Stack × List Stack) :=
  [(0, [8]), (1, [10]), (2, [9]), (3, [21]),
   (4, [23]), (5, [20]), (6, [22, 33])]

def staged (S : Stack → List Bool) : Stack → List Bool :=
  EthInapproximability.CurrentPaper.CopyFill.fill jobs S

def selectorSlots : Fin 12 ↪ Stack :=
  ⟨![8,11,12,13,14,15,9,16,17,18,19,10], by decide⟩

def positionSlots : Fin 13 ↪ Stack :=
  ⟨![20,21,22,23,24,25,26,27,28,29,30,31,32], by decide⟩

def payloadSlots : Fin 6 ↪ Stack :=
  ⟨![33,17,7,34,29,35], by decide⟩

def scratchSlots : Fin 32 ↪ Stack :=
  Fin.natAddEmb 8

theorem scratchSlots_val (i : Fin 32) : (scratchSlots i).val = i.val + 8 := by
  simp [scratchSlots, Fin.natAddEmb, Nat.add_comm]

theorem staged_at_public (S : Stack → List Bool) (k : Fin 7) :
    staged S ⟨k.val, by omega⟩ = S ⟨k.val, by omega⟩ := by
  fin_cases k <;> simp [staged, jobs, EthInapproximability.CurrentPaper.CopyFill.fill]

theorem staged_at_target (S : Stack → List Bool) :
    staged S 8 = S 0 ∧ staged S 10 = S 1 ∧ staged S 9 = S 2 ∧
    staged S 21 = S 3 ∧ staged S 23 = S 4 ∧ staged S 20 = S 5 ∧
    staged S 22 = S 6 ∧ staged S 33 = S 6 := by
  simp [staged, jobs, EthInapproximability.CurrentPaper.CopyFill.fill]

theorem stage_run (S : Stack → List Bool)
    (hblank : ∀ k : Stack, 7 ≤ k.val → S k = []) :
    ((advance (EthInapproximability.CurrentPaper.MultiMove.program
        (jobs.map EthInapproximability.CurrentPaper.CopyFill.toJob) 36))^[
        EthInapproximability.CurrentPaper.CopyFill.fillCost jobs S + 1])
      (⟨some (EthInapproximability.CurrentPaper.MultiMove.startLabel
        (jobs.map EthInapproximability.CurrentPaper.CopyFill.toJob)),
        EthInapproximability.CurrentPaper.MultiMove.initial, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, EthInapproximability.CurrentPaper.MultiMove.initial, staged S⟩ := by
  apply EthInapproximability.CurrentPaper.CopyFill.run 36 jobs
  · constructor
    · decide
    · decide
    · decide
    · decide
  · exact hblank 36 (by decide)
  · intro j hj d hd
    have hgood : ∀ j ∈ jobs, ∀ d ∈ j.2, 7 ≤ d.val := by decide
    exact hblank d (hgood j hj d hd)

end CurrentAdditive.FiniteFieldCoordinate
