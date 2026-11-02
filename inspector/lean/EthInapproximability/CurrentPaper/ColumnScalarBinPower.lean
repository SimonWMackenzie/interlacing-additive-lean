import EthInapproximability.CurrentPaper.ColumnScalarTailPower

/-! Physical `binBase^s` factor of the variable-bin column width. -/

namespace EthInapproximability.CurrentPaper.ColumnScalarBinPower

open Turing BitMachineEncoding MatrixStage4ScalarPreparationOps
open ColumnScalarPrefix

def sourceBank (a s q L rx cy : ℕ) : Stack → List Bool :=
  ColumnScalarTailPower.outputBank
    (ColumnScalarTailPower.sourceBank a s q L rx cy) cy s

def fuelSlots : Fin 3 ↪ Stack := ⟨![1,32,33], by decide⟩
def fuelProgram := copyProgram fuelSlots

def fuelBank (S : Stack → List Bool) (s : ℕ) : Stack → List Bool :=
  Function.update S 32 (List.replicate s true)

theorem fuel_run (a s q L rx cy : ℕ) :
    ((advance fuelProgram)^[2*s+2])
      (⟨some .scan, none, sourceBank a s q L rx cy⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, fuelBank (sourceBank a s q L rx cy) s⟩ := by
  let S := sourceBank a s q L rx cy
  have hr := MatrixStage4ScalarPreparationOps.copy_run fuelSlots S
    (by simp [S, fuelSlots, sourceBank, ColumnScalarTailPower.outputBank,
      ColumnScalarTailPower.sourceBank, ColumnScalarBinBase.outputBank,
      ColumnScalarBinBase.sourceBank, ColumnScalarWordBase.outputBank,
      ColumnScalarWordBase.sourceBank, ColumnScalarPrefix.lengthBank,
      ColumnScalarPrefix.qoneBank, ColumnScalarPrefix.inputBank])
  have hs : S (fuelSlots 0) = List.replicate s true := by
    simp [S, fuelSlots, sourceBank, ColumnScalarTailPower.outputBank,
      ColumnScalarTailPower.sourceBank, ColumnScalarBinBase.outputBank,
      ColumnScalarBinBase.sourceBank, ColumnScalarWordBase.outputBank,
      ColumnScalarWordBase.sourceBank, ColumnScalarPrefix.lengthBank,
      ColumnScalarPrefix.qoneBank, ColumnScalarPrefix.inputBank]
  have h32 : S 32 = [] := by
    simp [S, sourceBank, ColumnScalarTailPower.outputBank,
      ColumnScalarTailPower.sourceBank, ColumnScalarBinBase.outputBank,
      ColumnScalarBinBase.sourceBank, ColumnScalarWordBase.outputBank,
      ColumnScalarWordBase.sourceBank, ColumnScalarPrefix.lengthBank,
      ColumnScalarPrefix.qoneBank, ColumnScalarPrefix.inputBank]
  rw [hs] at hr
  simpa [fuelProgram, fuelSlots, fuelBank, h32] using hr

inductive SeedLabel where | push
  deriving DecidableEq, Fintype

def seedProgram : SeedLabel → TM2.Stmt (fun _ : Stack => Bool) SeedLabel Unit
  | .push => .push 11 (fun _ => true) .halt

def readyBank (S : Stack → List Bool) (s : ℕ) : Stack → List Bool :=
  Function.update (fuelBank S s) 11 [true]

theorem seed_run (a s q L rx cy : ℕ) :
    advance seedProgram
      (⟨some .push, (), fuelBank (sourceBank a s q L rx cy) s⟩ :
        TM2.Cfg (fun _ : Stack => Bool) SeedLabel Unit) =
      ⟨none, (), readyBank (sourceBank a s q L rx cy) s⟩ := by
  simp [advance, TM2.step, TM2.stepAux, seedProgram, readyBank,
    fuelBank, sourceBank, ColumnScalarTailPower.outputBank,
    ColumnScalarTailPower.sourceBank, ColumnScalarBinBase.outputBank,
    ColumnScalarBinBase.sourceBank, ColumnScalarWordBase.outputBank,
    ColumnScalarWordBase.sourceBank, ColumnScalarPrefix.lengthBank,
    ColumnScalarPrefix.qoneBank, ColumnScalarPrefix.inputBank]

def setupProgram := BitMachineRawSequence.program fuelProgram seedProgram
  SeedLabel.push none ()

theorem setup_run (a s q L rx cy : ℕ) :
    ∃ t ≤ 2*s+4,
      ((advance setupProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none,()), sourceBank a s q L rx cy⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label BitMachineCopy.Label SeedLabel)
            (Option Bool × Unit)) =
        ⟨none, (none,()), readyBank (sourceBank a s q L rx cy) s⟩ := by
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    fuelProgram seedProgram BitMachineCopy.Label.scan SeedLabel.push
    none none () ()
    (sourceBank a s q L rx cy)
    (fuelBank (sourceBank a s q L rx cy) s)
    (readyBank (sourceBank a s q L rx cy) s)
    (2*s+2) 1 (fuel_run a s q L rx cy)
    (by simpa only [Function.iterate_one] using seed_run a s q L rx cy)
  exact ⟨t, by omega, by simpa only [setupProgram] using hr⟩

def powerSlots : MatrixWeightedPower.Stack ↪ Stack :=
  ⟨fun k => match k with
    | .inl 0 => 11
    | .inl 1 => 9
    | .inl 2 => 34
    | .inl 3 => 35
    | .inl 4 => 36
    | .inl _ => 37
    | .inr 0 => 32,
    by decide⟩

def powerProgram := weightedPowerProgram powerSlots

def outputBank (S : Stack → List Bool) (a s q cy : ℕ) : Stack → List Bool :=
  Function.update S 11
    (List.replicate ((MatrixStage4Digits.binBase a s q cy)^s) true)

theorem power_run (a s q L rx cy : ℕ) :
    ∃ t ≤ MatrixWeightedPower.powerBound
        (MatrixStage4Digits.binBase a s q cy) s,
      ((advance powerProgram)^[t])
        (⟨some (.inr .test), (false,false),
          readyBank (sourceBank a s q L rx cy) s⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            MatrixWeightedPower.Label MatrixWeightedPower.Control) =
        ⟨none, (false,false),
          outputBank (sourceBank a s q L rx cy) a s q cy⟩ := by
  let S := readyBank (sourceBank a s q L rx cy) s
  obtain ⟨t,ht,hr⟩ := weighted_power_run powerSlots S
    (MatrixStage4Digits.binBase a s q cy) s
    (by simp [S, powerSlots, readyBank])
    (by simp [S, powerSlots, readyBank, fuelBank, sourceBank,
      ColumnScalarTailPower.outputBank, ColumnScalarTailPower.sourceBank,
      ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
      ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
      ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
      ColumnScalarPrefix.inputBank, MatrixStage4Digits.binBase])
    (by simp [S, powerSlots, readyBank, fuelBank, sourceBank,
      ColumnScalarTailPower.outputBank, ColumnScalarTailPower.sourceBank,
      ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
      ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
      ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
      ColumnScalarPrefix.inputBank])
    (by simp [S, powerSlots, readyBank, fuelBank, sourceBank,
      ColumnScalarTailPower.outputBank, ColumnScalarTailPower.sourceBank,
      ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
      ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
      ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
      ColumnScalarPrefix.inputBank])
    (by simp [S, powerSlots, readyBank, fuelBank, sourceBank,
      ColumnScalarTailPower.outputBank, ColumnScalarTailPower.sourceBank,
      ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
      ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
      ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
      ColumnScalarPrefix.inputBank])
    (by simp [S, powerSlots, readyBank, fuelBank, sourceBank,
      ColumnScalarTailPower.outputBank, ColumnScalarTailPower.sourceBank,
      ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
      ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
      ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
      ColumnScalarPrefix.inputBank])
    (by simp [S, powerSlots, readyBank, fuelBank])
  have hbank : Function.update
      (Function.update S (powerSlots (.inl 0))
        (List.replicate ((MatrixStage4Digits.binBase a s q cy)^s) true))
      (powerSlots (.inr 0)) [] =
      outputBank (sourceBank a s q L rx cy) a s q cy := by
    funext j
    by_cases hj11 : j = 11
    · subst j
      simp [S, powerSlots, outputBank]
    · by_cases hj32 : j = 32
      · subst j
        simp [S, powerSlots, outputBank, readyBank, fuelBank, sourceBank,
          ColumnScalarTailPower.outputBank, ColumnScalarTailPower.sourceBank,
          ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
          ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
          ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
          ColumnScalarPrefix.inputBank]
      · simp [S, powerSlots, outputBank, readyBank, fuelBank,
          Function.update_of_ne hj11, Function.update_of_ne hj32]
  exact ⟨t,ht, by simpa only [powerProgram, hbank] using hr⟩

def binPowerProgram := BitMachineRawSequence.program setupProgram powerProgram
  (.inr .test) (none,()) (false,false)

theorem binPower_run (a s q L rx cy : ℕ) :
    ∃ t ≤ 2*s+5 + MatrixWeightedPower.powerBound
        (MatrixStage4Digits.binBase a s q cy) s,
      ((advance binPowerProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          ((none,()),(false,false)), sourceBank a s q L rx cy⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label BitMachineCopy.Label SeedLabel)
              MatrixWeightedPower.Label)
            ((Option Bool × Unit) × MatrixWeightedPower.Control)) =
        ⟨none, ((none,()),(false,false)),
          outputBank (sourceBank a s q L rx cy) a s q cy⟩ := by
  obtain ⟨ts,hts,hs⟩ := setup_run a s q L rx cy
  obtain ⟨tp,htp,hp⟩ := power_run a s q L rx cy
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    setupProgram powerProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (.inr .test) (none,()) (none,()) (false,false) (false,false)
    (sourceBank a s q L rx cy)
    (readyBank (sourceBank a s q L rx cy) s)
    (outputBank (sourceBank a s q L rx cy) a s q cy)
    ts tp hs hp
  exact ⟨t, by omega, by simpa only [binPowerProgram] using hr⟩

#print axioms binPower_run

end EthInapproximability.CurrentPaper.ColumnScalarBinPower
