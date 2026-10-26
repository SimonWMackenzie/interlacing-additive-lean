import EthInapproximability.CurrentPaper.ColumnScalarWidth

/-! One fixed physical program composes all Stage--4 column-scalar stages. -/

namespace EthInapproximability.CurrentPaper.ColumnScalarJoin

open Turing BitMachineEncoding
open ColumnScalarPrefix

namespace Raw
abbrev Label := BitMachineRawSequence.Label
abbrev leftLabel := @BitMachineRawSequence.leftLabel
abbrev program := @BitMachineRawSequence.program
abbrev runs := @BitMachineRawSequence.runs
end Raw

def qStart : Raw.Label MatrixUnaryPower.Label ColumnScalarPrefix.PopLabel :=
  Raw.leftLabel (.inr false)
def qControl : MatrixUnaryPower.Control × Unit :=
  (((false,false),none),())

def lStart : Raw.Label
    (Raw.Label BitMachineCopy.Label BitMachineCopy.Label)
    ColumnScalarPrefix.PushLabel :=
  Raw.leftLabel (Raw.leftLabel .scan)
def lControl : ((Option Bool × Option Bool) × Unit) := ((none,none),())

def wStart : Raw.Label
    (Raw.Label BitMachineCopy.Label ColumnScalarWordBase.SeedLabel)
    MatrixWeightedPower.Label :=
  Raw.leftLabel (Raw.leftLabel .scan)
def wControl : ((Option Bool × Unit) × MatrixWeightedPower.Control) :=
  ((none,()),(false,false))

def tStart : Raw.Label
    (Raw.Label BitMachineCopy.Label ColumnScalarTailPower.Admin)
    MatrixWeightedPower.Label :=
  Raw.leftLabel (Raw.leftLabel .scan)
def tControl : ((Option Bool × Unit) × MatrixWeightedPower.Control) :=
  ((none,()),(false,false))

def bStart : Raw.Label
    (Raw.Label BitMachineCopy.Label ColumnScalarBinPower.SeedLabel)
    MatrixWeightedPower.Label :=
  Raw.leftLabel (Raw.leftLabel .scan)
def bControl : ((Option Bool × Unit) × MatrixWeightedPower.Control) :=
  ((none,()),(false,false))

def c₀ (a : ℕ) := 4*2^a+5*a+10
def c₁ (a s : ℕ) := 2*Construction.qOne a+2*s+7
def c₂ (a s cy : ℕ) := 2*Construction.firstLength a s+5+
  MatrixWeightedPower.powerBound cy (Construction.firstLength a s)
def c₃ (a s q cy : ℕ) := MatrixAddressMachine.exactTime q
  (MatrixStage4Digits.wordBase a s cy) 0
def c₄ (s cy : ℕ) := 2*s+6+MatrixWeightedPower.powerBound cy (s+1)
def c₅ (a s q cy : ℕ) := 2*s+5+
  MatrixWeightedPower.powerBound (MatrixStage4Digits.binBase a s q cy) s
def c₆ (a s q cy : ℕ) := MatrixAddressMachine.exactTime
  (cy^(s+1)) ((MatrixStage4Digits.binBase a s q cy)^s) 0

def P₁ := Raw.program ColumnScalarPrefix.qoneProgram
  ColumnScalarPrefix.lengthProgram lStart qControl lControl
def start₁ : Raw.Label
    (Raw.Label MatrixUnaryPower.Label ColumnScalarPrefix.PopLabel)
    (Raw.Label (Raw.Label BitMachineCopy.Label BitMachineCopy.Label)
      ColumnScalarPrefix.PushLabel) := Raw.leftLabel qStart
def control₁ := (qControl,lControl)
def cost₁ (a s : ℕ) := c₀ a+c₁ a s+1

theorem run₁ (a s q L rx cy : ℕ) :
    ∃ t ≤ cost₁ a s,
      ((advance P₁)^[t])
        ⟨some start₁, control₁, inputBank a s q L rx cy⟩ =
      ⟨none, control₁, ColumnScalarWordBase.sourceBank a s q L rx cy⟩ := by
  obtain ⟨u,hu,hru⟩ := ColumnScalarPrefix.qone_run a s q L rx cy
  obtain ⟨v,hv,hrv⟩ := ColumnScalarPrefix.length_run a s q L rx cy
  obtain ⟨t,ht,hr⟩ := Raw.runs
    ColumnScalarPrefix.qoneProgram ColumnScalarPrefix.lengthProgram
    qStart lStart qControl qControl lControl lControl
    (inputBank a s q L rx cy)
    (qoneBank (inputBank a s q L rx cy) a)
    (ColumnScalarWordBase.sourceBank a s q L rx cy)
    u v hru (by simpa only [ColumnScalarWordBase.sourceBank] using hrv)
  exact ⟨t, by dsimp [cost₁,c₀,c₁]; omega,
    by simpa only [P₁,start₁,control₁] using hr⟩

def P₂ := Raw.program P₁ ColumnScalarWordBase.wordBaseProgram
  wStart control₁ wControl
def start₂ : Raw.Label (Raw.Label
    (Raw.Label MatrixUnaryPower.Label ColumnScalarPrefix.PopLabel)
    (Raw.Label (Raw.Label BitMachineCopy.Label BitMachineCopy.Label)
      ColumnScalarPrefix.PushLabel))
    (Raw.Label (Raw.Label BitMachineCopy.Label ColumnScalarWordBase.SeedLabel)
      MatrixWeightedPower.Label) := Raw.leftLabel start₁
def control₂ := (control₁,wControl)
def cost₂ (a s cy : ℕ) := cost₁ a s+c₂ a s cy+1

theorem run₂ (a s q L rx cy : ℕ) :
    ∃ t ≤ cost₂ a s cy,
      ((advance P₂)^[t])
        ⟨some start₂, control₂, inputBank a s q L rx cy⟩ =
      ⟨none, control₂, ColumnScalarBinBase.sourceBank a s q L rx cy⟩ := by
  obtain ⟨u,hu,hru⟩ := run₁ a s q L rx cy
  obtain ⟨v,hv,hrv⟩ := ColumnScalarWordBase.wordBase_run a s q L rx cy
  obtain ⟨t,ht,hr⟩ := Raw.runs P₁ ColumnScalarWordBase.wordBaseProgram
    start₁ wStart control₁ control₁ wControl wControl
    (inputBank a s q L rx cy)
    (ColumnScalarWordBase.sourceBank a s q L rx cy)
    (ColumnScalarBinBase.sourceBank a s q L rx cy)
    u v hru (by simpa only [ColumnScalarBinBase.sourceBank] using hrv)
  exact ⟨t, by dsimp [cost₂,c₂] at *; omega,
    by simpa only [P₂,start₂,control₂] using hr⟩

def P₃ := Raw.program P₂ ColumnScalarBinBase.productProgram
  MatrixAddressMachine.Label.outer control₂ false
def start₃ : Raw.Label (Raw.Label (Raw.Label
    (Raw.Label MatrixUnaryPower.Label ColumnScalarPrefix.PopLabel)
    (Raw.Label (Raw.Label BitMachineCopy.Label BitMachineCopy.Label)
      ColumnScalarPrefix.PushLabel))
    (Raw.Label (Raw.Label BitMachineCopy.Label ColumnScalarWordBase.SeedLabel)
      MatrixWeightedPower.Label)) MatrixAddressMachine.Label :=
  Raw.leftLabel start₂
def control₃ := (control₂,false)
def cost₃ (a s q cy : ℕ) := cost₂ a s cy+c₃ a s q cy+1

theorem run₃ (a s q L rx cy : ℕ) :
    ∃ t ≤ cost₃ a s q cy,
      ((advance P₃)^[t])
        ⟨some start₃, control₃, inputBank a s q L rx cy⟩ =
      ⟨none, control₃, ColumnScalarTailPower.sourceBank a s q L rx cy⟩ := by
  obtain ⟨u,hu,hru⟩ := run₂ a s q L rx cy
  have hrv := ColumnScalarBinBase.binBase_run a s q L rx cy
  obtain ⟨t,ht,hr⟩ := Raw.runs P₂ ColumnScalarBinBase.productProgram
    start₂ MatrixAddressMachine.Label.outer control₂ control₂ false false
    (inputBank a s q L rx cy)
    (ColumnScalarBinBase.sourceBank a s q L rx cy)
    (ColumnScalarTailPower.sourceBank a s q L rx cy)
    u (c₃ a s q cy) hru
    (by simpa only [c₃,ColumnScalarTailPower.sourceBank] using hrv)
  exact ⟨t, by dsimp [cost₃]; omega,
    by simpa only [P₃,start₃,control₃] using hr⟩

def P₄ := Raw.program P₃ ColumnScalarTailPower.tailProgram
  tStart control₃ tControl
def start₄ : Raw.Label (Raw.Label (Raw.Label (Raw.Label
    (Raw.Label MatrixUnaryPower.Label ColumnScalarPrefix.PopLabel)
    (Raw.Label (Raw.Label BitMachineCopy.Label BitMachineCopy.Label)
      ColumnScalarPrefix.PushLabel))
    (Raw.Label (Raw.Label BitMachineCopy.Label ColumnScalarWordBase.SeedLabel)
      MatrixWeightedPower.Label)) MatrixAddressMachine.Label)
    (Raw.Label (Raw.Label BitMachineCopy.Label ColumnScalarTailPower.Admin)
      MatrixWeightedPower.Label) := Raw.leftLabel start₃
def control₄ := (control₃,tControl)
def cost₄ (a s q cy : ℕ) := cost₃ a s q cy+c₄ s cy+1

theorem run₄ (a s q L rx cy : ℕ) :
    ∃ t ≤ cost₄ a s q cy,
      ((advance P₄)^[t])
        ⟨some start₄, control₄, inputBank a s q L rx cy⟩ =
      ⟨none, control₄, ColumnScalarBinPower.sourceBank a s q L rx cy⟩ := by
  obtain ⟨u,hu,hru⟩ := run₃ a s q L rx cy
  obtain ⟨v,hv,hrv⟩ := ColumnScalarTailPower.tail_run a s q L rx cy
  obtain ⟨t,ht,hr⟩ := Raw.runs P₃ ColumnScalarTailPower.tailProgram
    start₃ tStart control₃ control₃ tControl tControl
    (inputBank a s q L rx cy)
    (ColumnScalarTailPower.sourceBank a s q L rx cy)
    (ColumnScalarBinPower.sourceBank a s q L rx cy)
    u v hru (by simpa only [ColumnScalarBinPower.sourceBank] using hrv)
  exact ⟨t, by dsimp [cost₄,c₄] at *; omega,
    by simpa only [P₄,start₄,control₄] using hr⟩

def P₅ := Raw.program P₄ ColumnScalarBinPower.binPowerProgram
  bStart control₄ bControl
def start₅ : Raw.Label (Raw.Label (Raw.Label (Raw.Label (Raw.Label
    (Raw.Label MatrixUnaryPower.Label ColumnScalarPrefix.PopLabel)
    (Raw.Label (Raw.Label BitMachineCopy.Label BitMachineCopy.Label)
      ColumnScalarPrefix.PushLabel))
    (Raw.Label (Raw.Label BitMachineCopy.Label ColumnScalarWordBase.SeedLabel)
      MatrixWeightedPower.Label)) MatrixAddressMachine.Label)
    (Raw.Label (Raw.Label BitMachineCopy.Label ColumnScalarTailPower.Admin)
      MatrixWeightedPower.Label))
    (Raw.Label (Raw.Label BitMachineCopy.Label ColumnScalarBinPower.SeedLabel)
      MatrixWeightedPower.Label) := Raw.leftLabel start₄
def control₅ := (control₄,bControl)
def cost₅ (a s q cy : ℕ) := cost₄ a s q cy+c₅ a s q cy+1

theorem run₅ (a s q L rx cy : ℕ) :
    ∃ t ≤ cost₅ a s q cy,
      ((advance P₅)^[t])
        ⟨some start₅, control₅, inputBank a s q L rx cy⟩ =
      ⟨none, control₅, ColumnScalarWidth.sourceBank a s q L rx cy⟩ := by
  obtain ⟨u,hu,hru⟩ := run₄ a s q L rx cy
  obtain ⟨v,hv,hrv⟩ := ColumnScalarBinPower.binPower_run a s q L rx cy
  obtain ⟨t,ht,hr⟩ := Raw.runs P₄ ColumnScalarBinPower.binPowerProgram
    start₄ bStart control₄ control₄ bControl bControl
    (inputBank a s q L rx cy)
    (ColumnScalarBinPower.sourceBank a s q L rx cy)
    (ColumnScalarWidth.sourceBank a s q L rx cy)
    u v hru (by simpa only [ColumnScalarWidth.sourceBank] using hrv)
  exact ⟨t, by dsimp [cost₅,c₅] at *; omega,
    by simpa only [P₅,start₅,control₅] using hr⟩

def program := Raw.program P₅ ColumnScalarWidth.productProgram
  MatrixAddressMachine.Label.outer control₅ false
def start : Raw.Label (Raw.Label (Raw.Label (Raw.Label (Raw.Label (Raw.Label
    (Raw.Label MatrixUnaryPower.Label ColumnScalarPrefix.PopLabel)
    (Raw.Label (Raw.Label BitMachineCopy.Label BitMachineCopy.Label)
      ColumnScalarPrefix.PushLabel))
    (Raw.Label (Raw.Label BitMachineCopy.Label ColumnScalarWordBase.SeedLabel)
      MatrixWeightedPower.Label)) MatrixAddressMachine.Label)
    (Raw.Label (Raw.Label BitMachineCopy.Label ColumnScalarTailPower.Admin)
      MatrixWeightedPower.Label))
    (Raw.Label (Raw.Label BitMachineCopy.Label ColumnScalarBinPower.SeedLabel)
      MatrixWeightedPower.Label)) MatrixAddressMachine.Label := Raw.leftLabel start₅
def control := (control₅,false)
def cost (a s q cy : ℕ) := cost₅ a s q cy+c₆ a s q cy+1

theorem run (a s q L rx cy : ℕ) :
    ∃ t ≤ cost a s q cy,
      ((advance program)^[t])
        ⟨some start, control, inputBank a s q L rx cy⟩ =
      ⟨none, control,
        ColumnScalarWidth.outputBank
          (ColumnScalarWidth.sourceBank a s q L rx cy) a s q cy⟩ := by
  obtain ⟨u,hu,hru⟩ := run₅ a s q L rx cy
  have hrv := ColumnScalarWidth.width_run a s q L rx cy
  obtain ⟨t,ht,hr⟩ := Raw.runs P₅ ColumnScalarWidth.productProgram
    start₅ MatrixAddressMachine.Label.outer control₅ control₅ false false
    (inputBank a s q L rx cy)
    (ColumnScalarWidth.sourceBank a s q L rx cy)
    (ColumnScalarWidth.outputBank
      (ColumnScalarWidth.sourceBank a s q L rx cy) a s q cy)
    u (c₆ a s q cy) hru (by simpa only [c₆] using hrv)
  exact ⟨t, by dsimp [cost]; omega,
    by simpa only [program,start,control] using hr⟩

#print axioms run

end EthInapproximability.CurrentPaper.ColumnScalarJoin
