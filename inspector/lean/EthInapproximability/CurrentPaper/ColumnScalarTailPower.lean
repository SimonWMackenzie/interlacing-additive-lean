import EthInapproximability.CurrentPaper.ColumnScalarBinBase

/-! Physical `cy^(s+1)` factor of the variable-bin column width. -/

namespace EthInapproximability.CurrentPaper.ColumnScalarTailPower

open Turing BitMachineEncoding MatrixStage4ScalarPreparationOps
open ColumnScalarPrefix

def sourceBank (a s q L rx cy : ℕ) : Stack → List Bool :=
  ColumnScalarBinBase.outputBank
    (ColumnScalarBinBase.sourceBank a s q L rx cy) a s q cy

def fuelSlots : Fin 3 ↪ Stack := ⟨![1,32,33], by decide⟩
def fuelProgram := copyProgram fuelSlots

def copiedBank (S : Stack → List Bool) (s : ℕ) : Stack → List Bool :=
  Function.update S 32 (List.replicate s true)

theorem copy_run (a s q L rx cy : ℕ) :
    ((advance fuelProgram)^[2*s+2])
      (⟨some .scan, none, sourceBank a s q L rx cy⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, copiedBank (sourceBank a s q L rx cy) s⟩ := by
  let S := sourceBank a s q L rx cy
  have hr := MatrixStage4ScalarPreparationOps.copy_run fuelSlots S
    (by simp [S, sourceBank, ColumnScalarBinBase.outputBank,
      ColumnScalarBinBase.sourceBank, ColumnScalarWordBase.outputBank,
      ColumnScalarWordBase.sourceBank, ColumnScalarPrefix.lengthBank,
      ColumnScalarPrefix.qoneBank, ColumnScalarPrefix.inputBank, fuelSlots])
  have hs : S (fuelSlots 0) = List.replicate s true := by
    simp [S, sourceBank, ColumnScalarBinBase.outputBank,
      ColumnScalarBinBase.sourceBank, ColumnScalarWordBase.outputBank,
      ColumnScalarWordBase.sourceBank, ColumnScalarPrefix.lengthBank,
      ColumnScalarPrefix.qoneBank, ColumnScalarPrefix.inputBank, fuelSlots]
  have h32 : S 32 = [] := by
    simp [S, sourceBank, ColumnScalarBinBase.outputBank,
      ColumnScalarBinBase.sourceBank, ColumnScalarWordBase.outputBank,
      ColumnScalarWordBase.sourceBank, ColumnScalarPrefix.lengthBank,
      ColumnScalarPrefix.qoneBank, ColumnScalarPrefix.inputBank]
  rw [hs] at hr
  simpa [fuelProgram, fuelSlots, copiedBank, h32] using hr

inductive Admin where | plus | seed
  deriving DecidableEq, Fintype

def adminProgram : Admin → TM2.Stmt (fun _ : Stack => Bool) Admin Unit
  | .plus => .push 32 (fun _ => true) (.goto (fun _ => .seed))
  | .seed => .push 10 (fun _ => true) .halt

def readyBank (S : Stack → List Bool) (s : ℕ) : Stack → List Bool :=
  Function.update (Function.update S 32 (List.replicate (s+1) true)) 10 [true]

theorem admin_run (a s q L rx cy : ℕ) :
    ((advance adminProgram)^[2])
      (⟨some .plus, (), copiedBank (sourceBank a s q L rx cy) s⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Admin Unit) =
      ⟨none, (), readyBank (sourceBank a s q L rx cy) s⟩ := by
  change advance adminProgram (advance adminProgram
    (⟨some .plus, (), copiedBank (sourceBank a s q L rx cy) s⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Admin Unit)) = _
  simp only [advance, TM2.step, TM2.stepAux, adminProgram,
    Option.getD_some]
  congr 1
  funext j
  by_cases hj32 : j = 32
  · subst j
    simp [readyBank, copiedBank, List.replicate_succ]
  · by_cases hj10 : j = 10
    · subst j
      simp [readyBank, copiedBank, sourceBank,
        ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
        ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
        ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
        ColumnScalarPrefix.inputBank]
    · simp [readyBank, copiedBank,
        Function.update_of_ne hj32, Function.update_of_ne hj10]

def setupProgram := BitMachineRawSequence.program fuelProgram adminProgram
  Admin.plus none ()

theorem setup_run (a s q L rx cy : ℕ) :
    ∃ t ≤ 2*s+5,
      ((advance setupProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none,()), sourceBank a s q L rx cy⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label BitMachineCopy.Label Admin)
            (Option Bool × Unit)) =
        ⟨none, (none,()), readyBank (sourceBank a s q L rx cy) s⟩ := by
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    fuelProgram adminProgram BitMachineCopy.Label.scan Admin.plus
    none none () ()
    (sourceBank a s q L rx cy)
    (copiedBank (sourceBank a s q L rx cy) s)
    (readyBank (sourceBank a s q L rx cy) s)
    (2*s+2) 2 (copy_run a s q L rx cy) (admin_run a s q L rx cy)
  exact ⟨t, by omega, by simpa only [setupProgram] using hr⟩

def powerSlots : MatrixWeightedPower.Stack ↪ Stack :=
  ⟨fun k => match k with
    | .inl 0 => 10
    | .inl 1 => 5
    | .inl 2 => 34
    | .inl 3 => 35
    | .inl 4 => 36
    | .inl _ => 37
    | .inr 0 => 32,
    by decide⟩

def powerProgram := weightedPowerProgram powerSlots

def outputBank (S : Stack → List Bool) (cy s : ℕ) : Stack → List Bool :=
  Function.update S 10 (List.replicate (cy^(s+1)) true)

theorem power_run (a s q L rx cy : ℕ) :
    ∃ t ≤ MatrixWeightedPower.powerBound cy (s+1),
      ((advance powerProgram)^[t])
        (⟨some (.inr .test), (false,false),
          readyBank (sourceBank a s q L rx cy) s⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            MatrixWeightedPower.Label MatrixWeightedPower.Control) =
        ⟨none, (false,false), outputBank (sourceBank a s q L rx cy) cy s⟩ := by
  let S := readyBank (sourceBank a s q L rx cy) s
  obtain ⟨t,ht,hr⟩ := weighted_power_run powerSlots S cy (s+1)
    (by simp [S, powerSlots, readyBank])
    (by simp [S, powerSlots, readyBank, sourceBank,
      ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
      ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
      ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
      ColumnScalarPrefix.inputBank])
    (by simp [S, powerSlots, readyBank, sourceBank,
      ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
      ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
      ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
      ColumnScalarPrefix.inputBank])
    (by simp [S, powerSlots, readyBank, sourceBank,
      ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
      ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
      ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
      ColumnScalarPrefix.inputBank])
    (by simp [S, powerSlots, readyBank, sourceBank,
      ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
      ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
      ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
      ColumnScalarPrefix.inputBank])
    (by simp [S, powerSlots, readyBank, sourceBank,
      ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
      ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
      ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
      ColumnScalarPrefix.inputBank])
    (by simp [S, powerSlots, readyBank])
  have hbank : Function.update
      (Function.update S (powerSlots (.inl 0))
        (List.replicate (cy^(s+1)) true)) (powerSlots (.inr 0)) [] =
      outputBank (sourceBank a s q L rx cy) cy s := by
    funext j
    by_cases hj10 : j = 10
    · subst j
      simp [S, powerSlots, outputBank]
    · by_cases hj32 : j = 32
      · subst j
        simp [S, powerSlots, outputBank, readyBank, sourceBank,
          ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
          ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
          ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
          ColumnScalarPrefix.inputBank]
      · simp [S, powerSlots, outputBank, readyBank,
          Function.update_of_ne hj10, Function.update_of_ne hj32]
  exact ⟨t,ht, by simpa only [powerProgram, hbank] using hr⟩

def tailProgram := BitMachineRawSequence.program setupProgram powerProgram
  (.inr .test) (none,()) (false,false)

theorem tail_run (a s q L rx cy : ℕ) :
    ∃ t ≤ 2*s+6 + MatrixWeightedPower.powerBound cy (s+1),
      ((advance tailProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          ((none,()),(false,false)), sourceBank a s q L rx cy⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label BitMachineCopy.Label Admin)
              MatrixWeightedPower.Label)
            ((Option Bool × Unit) × MatrixWeightedPower.Control)) =
        ⟨none, ((none,()),(false,false)),
          outputBank (sourceBank a s q L rx cy) cy s⟩ := by
  obtain ⟨ts,hts,hs⟩ := setup_run a s q L rx cy
  obtain ⟨tp,htp,hp⟩ := power_run a s q L rx cy
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    setupProgram powerProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (.inr .test) (none,()) (none,()) (false,false) (false,false)
    (sourceBank a s q L rx cy)
    (readyBank (sourceBank a s q L rx cy) s)
    (outputBank (sourceBank a s q L rx cy) cy s)
    ts tp hs hp
  exact ⟨t, by omega, by simpa only [tailProgram] using hr⟩

#print axioms tail_run

end EthInapproximability.CurrentPaper.ColumnScalarTailPower
