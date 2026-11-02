import EthInapproximability.CurrentPaper.ChosenPrimeRaw
import EthInapproximability.CurrentPaper.ColumnInputStaging
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import Mathlib.Data.Fin.VecNotation

/-! Physical chosen-prime power suffix with a retained unary t source. -/

namespace EthInapproximability.CurrentPaper.ChosenSizeSuffix

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding

noncomputable section

abbrev Stack := ChosenPrimeRaw.Stack ⊕ (Fin 64 ⊕ Fin 8)

def primeCell : Stack := .inl (.inr 3)
def writerL : Stack := .inr (.inl 57)
def tCell : Stack := .inr (.inr 0)
def fuelCell : Stack := .inr (.inr 1)

def copySlots : Fin 3 ↪ Stack :=
  ⟨![tCell,fuelCell,.inr (.inr 2)], by decide⟩

def powerSlots : MatrixWeightedPower.Stack ↪ Stack :=
  ⟨Sum.elim ![writerL,primeCell,.inr (.inr 3),.inr (.inr 4),
      .inr (.inr 5),.inr (.inr 6)] ![fuelCell], by decide⟩

def copyProgram := MatrixStage4ScalarPreparationOps.copyProgram copySlots

def accProgram : Unit → TM2.Stmt (fun _ : Stack => Bool) Unit Unit
  | () => push writerL (fun _ => true) halt

def powerProgram := MatrixStage4ScalarPreparationOps.weightedPowerProgram powerSlots

private theorem acc_run (S : Stack → List Bool) (hblank : S writerL = []) :
    advance accProgram
      (⟨some (),(),S⟩ : TM2.Cfg (fun _ : Stack => Bool) Unit Unit) =
      ⟨none,(),Function.update S writerL [true]⟩ := by
  simp [advance, accProgram, TM2.step, TM2.stepAux, hblank]

def P12 := BitMachineRawSequence.program copyProgram accProgram
  () (none : Option Bool) ()
def program := BitMachineRawSequence.program P12 powerProgram
  (.inr MatrixWeightedPower.Admin.test) ((none : Option Bool),()) (false,false)

abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label BitMachineCopy.Label Unit) MatrixWeightedPower.Label
abbrev Control := ((Option Bool × Unit) × MatrixWeightedPower.Control)

def start : Label := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
def initialControl : Control := ((none,()),(false,false))

def bound (p t : ℕ) : ℕ :=
  (2*t+2) + 1 + 1 + MatrixWeightedPower.powerBound p t + 1

/-- The prime word is on the actual search output stack, not an arbitrary
newly supplied operand. Only the t source word is staged separately. The
suffix copies t, initializes the output accumulator physically, then runs
the checked preserving unary-power machine. -/
theorem size_suffix_run (S : Stack → List Bool) (p t : ℕ)
    (hp : S primeCell = List.replicate p true)
    (ht : S tCell = List.replicate t true)
    (hL : S writerL = [])
    (hf : S fuelCell = [])
    (hc : S (.inr (.inr 2)) = [])
    (h3 : S (.inr (.inr 3)) = [])
    (h4 : S (.inr (.inr 4)) = [])
    (h5 : S (.inr (.inr 5)) = [])
    (h6 : S (.inr (.inr 6)) = []) :
    ∃ u ≤ bound p t,
      ((advance program)^[u])
        (⟨some start,initialControl,S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none,initialControl,
          Function.update S writerL (List.replicate (p^t) true)⟩ := by
  let S1 := Function.update S fuelCell (List.replicate t true)
  let S2 := Function.update S1 writerL [true]
  have hcopy : ((advance copyProgram)^[2*t+2])
      (⟨some BitMachineCopy.Label.scan,none,S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none,none,S1⟩ := by
    have he := MatrixStage4ScalarPreparationOps.copy_run copySlots S hc
    simpa [copyProgram, copySlots, S1, ht, hf] using he
  have hacc : ((advance accProgram)^[1])
      (⟨some (),(),S1⟩ : TM2.Cfg (fun _ : Stack => Bool) Unit Unit) =
      ⟨none,(),S2⟩ := by
    have hb : S1 writerL = [] := by
      change Function.update S fuelCell (List.replicate t true) writerL = []
      rw [Function.update_of_ne (by decide : writerL ≠ fuelCell)]
      exact hL
    simpa only [Function.iterate_one, S2] using acc_run S1 hb
  obtain ⟨u12,hu12,h12⟩ := BitMachineRawSequence.runs
    copyProgram accProgram BitMachineCopy.Label.scan ()
    (none : Option Bool) none () () S S1 S2 (2*t+2) 1 hcopy hacc
  have hpower := MatrixStage4ScalarPreparationOps.weighted_power_run powerSlots
    S2 p t
    (by change S2 writerL = [true]; simp [S2])
    (by change S2 primeCell = List.replicate p true;
        simpa [S2, S1, writerL, fuelCell, primeCell] using hp)
    (by change S2 (.inr (.inr 3)) = [];
        simpa [S2, S1, writerL, fuelCell] using h3)
    (by change S2 (.inr (.inr 4)) = [];
        simpa [S2, S1, writerL, fuelCell] using h4)
    (by change S2 (.inr (.inr 5)) = [];
        simpa [S2, S1, writerL, fuelCell] using h5)
    (by change S2 (.inr (.inr 6)) = [];
        simpa [S2, S1, writerL, fuelCell] using h6)
    (by change S2 fuelCell = List.replicate t true;
        simp [S2, S1, fuelCell, writerL])
  obtain ⟨up,hup,hpwr⟩ := hpower
  have hfinal : Function.update
      (Function.update S2 writerL (List.replicate (p^t) true)) fuelCell [] =
      Function.update S writerL (List.replicate (p^t) true) := by
    funext k
    by_cases hw : k = writerL
    · subst k; simp [S2, S1, writerL, fuelCell]
    · by_cases hfu : k = fuelCell
      · subst k
        simp [S2, S1, writerL, fuelCell]
        exact hf
      · simp [S2, S1, hw, hfu]
  change ((advance powerProgram)^[up])
    (⟨some (.inr MatrixWeightedPower.Admin.test),(false,false),S2⟩ :
      TM2.Cfg (fun _ : Stack => Bool) MatrixWeightedPower.Label MatrixWeightedPower.Control) =
    ⟨none,(false,false),Function.update
      (Function.update S2 writerL (List.replicate (p^t) true)) fuelCell []⟩ at hpwr
  rw [hfinal] at hpwr
  obtain ⟨u,hu,hr⟩ := BitMachineRawSequence.runs
    P12 powerProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (.inr MatrixWeightedPower.Admin.test)
    ((none : Option Bool),()) ((none : Option Bool),())
    (false,false) (false,false)
    S S2 (Function.update S writerL (List.replicate (p^t) true))
    u12 up h12 hpwr
  exact ⟨u, by unfold bound; omega, by simpa only [program, start, initialControl] using hr⟩

#print axioms size_suffix_run

end
end EthInapproximability.CurrentPaper.ChosenSizeSuffix
