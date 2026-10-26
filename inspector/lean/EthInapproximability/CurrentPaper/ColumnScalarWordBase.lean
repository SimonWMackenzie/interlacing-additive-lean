import EthInapproximability.CurrentPaper.ColumnScalarPrefix

/-! Physical variable-base power for the first Stage--4 column radix. -/

namespace EthInapproximability.CurrentPaper.ColumnScalarWordBase

open Turing BitMachineEncoding MatrixStage4ScalarPreparationOps
open ColumnScalarPrefix

def fuelSlots : Fin 3 ↪ Stack := ⟨![7,32,33], by decide⟩
def fuelProgram := copyProgram fuelSlots

def sourceBank (a s q L rx cy : ℕ) : Stack → List Bool :=
  lengthBank (qoneBank (inputBank a s q L rx cy) a) a s

def fuelBank (S : Stack → List Bool) (a s : ℕ) : Stack → List Bool :=
  Function.update S 32 (List.replicate (Construction.firstLength a s) true)

theorem fuel_run (a s q L rx cy : ℕ) :
    ((advance fuelProgram)^[2 * Construction.firstLength a s + 2])
      (⟨some .scan, none, sourceBank a s q L rx cy⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, fuelBank (sourceBank a s q L rx cy) a s⟩ := by
  have hr := copy_run fuelSlots (sourceBank a s q L rx cy)
    (by simp [fuelSlots, sourceBank, lengthBank, qoneBank, inputBank])
  have hs : (sourceBank a s q L rx cy) (fuelSlots 0) =
      List.replicate (Construction.firstLength a s) true := by
    simp [sourceBank, fuelSlots, lengthBank]
  rw [hs] at hr
  have h32 : sourceBank a s q L rx cy 32 = [] := by
    simp [sourceBank, lengthBank, qoneBank, inputBank]
  simpa [fuelProgram, fuelSlots, fuelBank, h32] using hr

inductive SeedLabel where | push
  deriving DecidableEq, Fintype

def seedProgram : SeedLabel → TM2.Stmt (fun _ : Stack => Bool) SeedLabel Unit
  | .push => .push 8 (fun _ => true) .halt

def seedBank (S : Stack → List Bool) : Stack → List Bool :=
  Function.update S 8 [true]

theorem seed_run (a s q L rx cy : ℕ) :
    advance seedProgram
      (⟨some .push, (), fuelBank (sourceBank a s q L rx cy) a s⟩ :
        TM2.Cfg (fun _ : Stack => Bool) SeedLabel Unit) =
      ⟨none, (), seedBank (fuelBank (sourceBank a s q L rx cy) a s)⟩ := by
  simp [advance, TM2.step, TM2.stepAux, seedProgram, seedBank,
    fuelBank, sourceBank, lengthBank, qoneBank, inputBank]

def setupProgram := BitMachineRawSequence.program fuelProgram seedProgram
  SeedLabel.push none ()

theorem setup_run (a s q L rx cy : ℕ) :
    ∃ t ≤ 2 * Construction.firstLength a s + 4,
      ((advance setupProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none,()), sourceBank a s q L rx cy⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label BitMachineCopy.Label SeedLabel)
            (Option Bool × Unit)) =
        ⟨none, (none,()),
          seedBank (fuelBank (sourceBank a s q L rx cy) a s)⟩ := by
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    fuelProgram seedProgram BitMachineCopy.Label.scan SeedLabel.push
    none none () ()
    (sourceBank a s q L rx cy)
    (fuelBank (sourceBank a s q L rx cy) a s)
    (seedBank (fuelBank (sourceBank a s q L rx cy) a s))
    (2 * Construction.firstLength a s + 2) 1
    (fuel_run a s q L rx cy)
    (by simpa only [Function.iterate_one] using seed_run a s q L rx cy)
  exact ⟨t, by omega, by simpa only [setupProgram] using hr⟩

def powerSlots : MatrixWeightedPower.Stack ↪ Stack :=
  ⟨fun k => match k with
    | .inl 0 => 8
    | .inl 1 => 5
    | .inl 2 => 34
    | .inl 3 => 35
    | .inl 4 => 36
    | .inl _ => 37
    | .inr 0 => 32,
    by decide⟩

def powerProgram := weightedPowerProgram powerSlots

def outputBank (S : Stack → List Bool) (a s cy : ℕ) : Stack → List Bool :=
  Function.update S 8
    (List.replicate (MatrixStage4Digits.wordBase a s cy) true)

theorem physical_power_run (a s q L rx cy : ℕ) :
    ∃ t ≤ MatrixWeightedPower.powerBound cy
        (Construction.firstLength a s),
      ((advance powerProgram)^[t])
        (⟨some (.inr .test), (false,false),
          seedBank (fuelBank (sourceBank a s q L rx cy) a s)⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            MatrixWeightedPower.Label MatrixWeightedPower.Control) =
        ⟨none, (false,false),
          outputBank (sourceBank a s q L rx cy) a s cy⟩ := by
  let S := seedBank (fuelBank (sourceBank a s q L rx cy) a s)
  obtain ⟨t,ht,hr⟩ := weighted_power_run powerSlots S cy
    (Construction.firstLength a s)
    (by simp [S, powerSlots, seedBank])
    (by simp [S, powerSlots, seedBank, fuelBank, sourceBank,
      lengthBank, qoneBank, inputBank])
    (by simp [S, powerSlots, seedBank, fuelBank, sourceBank,
      lengthBank, qoneBank, inputBank])
    (by simp [S, powerSlots, seedBank, fuelBank, sourceBank,
      lengthBank, qoneBank, inputBank])
    (by simp [S, powerSlots, seedBank, fuelBank, sourceBank,
      lengthBank, qoneBank, inputBank])
    (by simp [S, powerSlots, seedBank, fuelBank, sourceBank,
      lengthBank, qoneBank, inputBank])
    (by simp [S, powerSlots, seedBank, fuelBank, sourceBank,
      lengthBank, qoneBank, inputBank])
  have hbank : Function.update
      (Function.update S (powerSlots (.inl 0))
        (List.replicate (cy ^ Construction.firstLength a s) true))
      (powerSlots (.inr 0)) [] =
      outputBank (sourceBank a s q L rx cy) a s cy := by
    funext j
    by_cases hj8 : j = 8
    · subst j
      simp [S, powerSlots, outputBank, MatrixStage4Digits.wordBase]
    · by_cases hj32 : j = 32
      · subst j
        simp [S, powerSlots, outputBank, seedBank, fuelBank,
          Function.update_of_ne hj8, sourceBank, lengthBank,
          qoneBank, inputBank]
      · simp [S, powerSlots, outputBank, seedBank, fuelBank,
          Function.update_of_ne hj8, Function.update_of_ne hj32]
  exact ⟨t,ht, by simpa only [powerProgram, hbank] using hr⟩

def wordBaseProgram := BitMachineRawSequence.program setupProgram powerProgram
  (.inr .test) (none,()) (false,false)

theorem wordBase_run (a s q L rx cy : ℕ) :
    ∃ t ≤ 2 * Construction.firstLength a s + 5 +
        MatrixWeightedPower.powerBound cy (Construction.firstLength a s),
      ((advance wordBaseProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          ((none,()),(false,false)), sourceBank a s q L rx cy⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label BitMachineCopy.Label SeedLabel)
              MatrixWeightedPower.Label)
            ((Option Bool × Unit) × MatrixWeightedPower.Control)) =
        ⟨none, ((none,()),(false,false)),
          outputBank (sourceBank a s q L rx cy) a s cy⟩ := by
  obtain ⟨ts,hts,hs⟩ := setup_run a s q L rx cy
  obtain ⟨tp,htp,hp⟩ := physical_power_run a s q L rx cy
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    setupProgram powerProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (.inr .test) (none,()) (none,()) (false,false) (false,false)
    (sourceBank a s q L rx cy)
    (seedBank (fuelBank (sourceBank a s q L rx cy) a s))
    (outputBank (sourceBank a s q L rx cy) a s cy)
    ts tp hs hp
  exact ⟨t, by omega, by simpa only [wordBaseProgram] using hr⟩

#print axioms wordBase_run

end EthInapproximability.CurrentPaper.ColumnScalarWordBase
