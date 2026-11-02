import EthInapproximability.CurrentPaper.PrimeSamplerBinaryDigitStream
import EthInapproximability.CurrentPaper.PrimeSamplerBinaryHornerStream
import EthInapproximability.CurrentPaper.BitMachineBankWrapper

/-!
# Fixed-bank binary balanced-family query machine

The phase program embeds the physically proved significant-digit decoder,
framed Horner evaluator, and final binary division by the alphabet size in
twenty-three Boolean banks. The controller is finite. The initial packet
contains binary label, prime, coordinate, and alphabet words; the degree is
only a semantic guard (`label < prime^degree`) and is never expanded or used
as an iteration count.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerBinaryQueryMachine

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition

abbrev Stack := Fin 23
abbrev Label := PrimeSamplerBinaryDigitStream.Label ⊕
  (PrimeSamplerBinaryHornerStream.Label ⊕ BitMachineBinaryDivision.Label)
abbrev Control := PrimeSamplerBinaryDigitStream.Control ×
  (PrimeSamplerBinaryHornerStream.Control × BitMachineBinaryDivision.Control)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control :=
  (PrimeSamplerBinaryDigitStream.initial,
    (PrimeSamplerBinaryModularStep.initial, some false, none),
    BitMachineBinaryDivision.initial)

def digitStacks : (Fin 9 ⊕ Fin 14) ≃ Stack := finSumFinEquiv

def hornerPermutation : Stack ≃ Stack where
  toFun i := ![11,12,13,9,14,15,16,17,1,18,19,20,21,22,8,
    0,2,3,4,5,6,7,10] i
  invFun i := ![15,8,16,17,18,19,20,21,14,3,22,0,1,2,4,
    5,6,7,9,10,11,12,13] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def hornerStacks : (Fin 15 ⊕ Fin 8) ≃ Stack :=
  finSumFinEquiv.trans hornerPermutation

def divisionPermutation : Stack ≃ Stack where
  toFun i := ![14,10,18,19,20,21,22,0,1,2,3,4,5,6,7,8,
    9,11,12,13,15,16,17] i
  invFun i := ![7,8,9,10,11,12,13,14,15,16,1,17,18,19,
    0,20,21,22,2,3,4,5,6] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def divisionStacks : (Fin 7 ⊕ Fin 16) ≃ Stack :=
  finSumFinEquiv.trans divisionPermutation

def hornerLabels :
    (PrimeSamplerBinaryHornerStream.Label ⊕
      (PrimeSamplerBinaryDigitStream.Label ⊕
        BitMachineBinaryDivision.Label)) ≃ Label where
  toFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inr l)
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inr l)
  left_inv l := by rcases l with l | (l | l) <;> rfl
  right_inv l := by rcases l with l | (l | l) <;> rfl

def divisionLabels :
    (BitMachineBinaryDivision.Label ⊕
      (PrimeSamplerBinaryDigitStream.Label ⊕
        PrimeSamplerBinaryHornerStream.Label)) ≃ Label where
  toFun
    | .inl l => .inr (.inr l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inl l)
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inr (.inr l)
    | .inr (.inr l) => .inl l
  left_inv l := by rcases l with l | (l | l) <;> rfl
  right_inv l := by rcases l with l | (l | l) <;> rfl

def hornerControl :
    (PrimeSamplerBinaryHornerStream.Control ×
      (PrimeSamplerBinaryDigitStream.Control ×
        BitMachineBinaryDivision.Control)) ≃ Control where
  toFun s := (s.2.1,s.1,s.2.2)
  invFun s := (s.2.1,s.1,s.2.2)
  left_inv s := by rcases s with ⟨a,b,c⟩; rfl
  right_inv s := by rcases s with ⟨a,b,c⟩; rfl

def divisionControl :
    (BitMachineBinaryDivision.Control ×
      (PrimeSamplerBinaryDigitStream.Control ×
        PrimeSamplerBinaryHornerStream.Control)) ≃ Control where
  toFun s := (s.2.1,s.2.2,s.1)
  invFun s := (s.2.2,s.1,s.2.1)
  left_inv s := by rcases s with ⟨a,b,c⟩; rfl
  right_inv s := by rcases s with ⟨a,b,c⟩; rfl

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt digitStacks (Equiv.refl Label) (Equiv.refl Control)
      (liftStmt (some (.inl (.inr (.inr .choose))))
        (PrimeSamplerBinaryDigitStream.program l))
  | .inr (.inl l) => renameStmt hornerStacks hornerLabels hornerControl
      (liftStmt (some (.inr .outer))
        (PrimeSamplerBinaryHornerStream.program l))
  | .inr (.inr l) => renameStmt divisionStacks divisionLabels divisionControl
      (liftStmt none (BitMachineBinaryDivision.program l))

def bank (label prime drem dquot dold dsaved ddiff dscratch stream coordinate
    alphabet hprod hoperand hscratch accumulator hcopy digit hinput hrem hquot
    hold hsaved hdiff : List Bool) : Stack → List Bool :=
  ![label,prime,drem,dquot,dold,dsaved,ddiff,dscratch,stream,coordinate,
    alphabet,hprod,hoperand,hscratch,accumulator,hcopy,digit,hinput,
    hrem,hquot,hold,hsaved,hdiff]

def cfg (l : Option Label) (s : Control)
    (label prime drem dquot dold dsaved ddiff dscratch stream coordinate
      alphabet hprod hoperand hscratch accumulator hcopy digit hinput hrem hquot
      hold hsaved hdiff : List Bool) : Config :=
  ⟨l,s,bank label prime drem dquot dold dsaved ddiff dscratch stream coordinate
    alphabet hprod hoperand hscratch accumulator hcopy digit hinput hrem hquot
    hold hsaved hdiff⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d)
    (u : ℕ) : run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def digitFrame (coordinate alphabet : List Bool)
    (c : PrimeSamplerBinaryDigitStream.Config) : Config :=
  renameCfg digitStacks (Equiv.refl Label) (Equiv.refl Control)
    (liftCfg (some (.inl (.inr (.inr .choose))))
      ((PrimeSamplerBinaryModularStep.initial, some false, none),
        BitMachineBinaryDivision.initial)
      (fun i : Fin 14 => ![coordinate,alphabet,[],[],[],[],[],[],[],[],[],[],[],[]] i) c)

theorem digitFrame_start
    (labelBits prime coordinate alphabet : List Bool) :
    digitFrame coordinate alphabet
      (PrimeSamplerBinaryDigitStream.cfg (some (.inl .outer))
        PrimeSamplerBinaryDigitStream.initial
        labelBits.reverse prime [] [] [] [] [] [] []) =
    cfg (some (.inl (.inl .outer))) initial
      labelBits.reverse prime [] [] [] [] [] [] [] coordinate alphabet
      [] [] [] [] [] [] [] [] [] [] [] [] := by
  unfold digitFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [digitStacks, PrimeSamplerBinaryDigitStream.cfg,
      PrimeSamplerBinaryDigitStream.bank, finSumFinEquiv, Fin.addCases]

theorem digitFrame_end
    (labelBits prime coordinate alphabet : List Bool) :
    digitFrame coordinate alphabet
      (PrimeSamplerBinaryDigitStream.cfg none
        (BitMachineBinaryDivision.initial, none, ⟨false, none⟩)
        [] prime [] [] [] [] [] []
        (PrimeSamplerBinaryDigitStream.streamFuel prime
          (labelBits.length + 1) labelBits.reverse [])) =
    cfg (some (.inr (.inl (.inr (.inr .choose))))) initial
      [] prime [] [] [] [] [] []
      (PrimeSamplerBinaryDigitStream.streamFuel prime
        (labelBits.length + 1) labelBits.reverse [])
      coordinate alphabet [] [] [] [] [] [] [] [] [] [] [] [] := by
  unfold digitFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [digitStacks, PrimeSamplerBinaryDigitStream.cfg,
      PrimeSamplerBinaryDigitStream.bank, finSumFinEquiv, Fin.addCases]

theorem digit_call
    (labelBits prime coordinate alphabet : List Bool)
    (hp : 2 ≤ EncodedCommunication.bitsValue prime) :
    ∃ n ≤ (labelBits.length + 1) *
        PrimeSamplerBinaryDigitStream.cycleBound labelBits.length prime.length,
      run n (cfg (some (.inl (.inl .outer))) initial
        labelBits.reverse prime [] [] [] [] [] [] [] coordinate alphabet
        [] [] [] [] [] [] [] [] [] [] [] [] ) =
      cfg (some (.inr (.inl (.inr (.inr .choose))))) initial
        [] prime [] [] [] [] [] []
        (PrimeSamplerBinaryDigitStream.streamFuel prime
          (labelBits.length + 1) labelBits.reverse [])
        coordinate alphabet [] [] [] [] [] [] [] [] [] [] [] [] := by
  have hQ : ∀ l, program (.inl l) =
      renameStmt digitStacks (Equiv.refl Label) (Equiv.refl Control)
        (liftStmt (some (.inl (.inr (.inr .choose))))
          (PrimeSamplerBinaryDigitStream.program l)) := by
    intro l
    rfl
  obtain ⟨u, hu, hr⟩ := PrimeSamplerBinaryDigitStream.run_label_stream
    labelBits prime hp
  have hhalt : (((advance PrimeSamplerBinaryDigitStream.program)^[u])
      (PrimeSamplerBinaryDigitStream.cfg (some (.inl .outer))
        PrimeSamplerBinaryDigitStream.initial
        labelBits.reverse prime [] [] [] [] [] [] [])).l = none := by
    change (PrimeSamplerBinaryDigitStream.run u
      (PrimeSamplerBinaryDigitStream.cfg (some (.inl .outer))
        PrimeSamplerBinaryDigitStream.initial
        labelBits.reverse prime [] [] [] [] [] [] [])).l = none
    rw [hr]
    rfl
  obtain ⟨n, hn, hglobal⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    digitStacks (Equiv.refl Label) (Equiv.refl Control)
    PrimeSamplerBinaryDigitStream.program program
    (some (.inl (.inr (.inr .choose)))) hQ
    ((PrimeSamplerBinaryModularStep.initial, some false, none),
      BitMachineBinaryDivision.initial)
    (fun i : Fin 14 => ![coordinate,alphabet,[],[],[],[],[],[],[],[],[],[],[],[]] i)
    (PrimeSamplerBinaryDigitStream.cfg (some (.inl .outer))
      PrimeSamplerBinaryDigitStream.initial
      labelBits.reverse prime [] [] [] [] [] [] []) u hhalt
  refine ⟨n, hn.trans hu, ?_⟩
  change run n (digitFrame coordinate alphabet _) =
    digitFrame coordinate alphabet _ at hglobal
  rw [show ((advance PrimeSamplerBinaryDigitStream.program)^[u]) _ =
    PrimeSamplerBinaryDigitStream.run u _ from rfl, hr] at hglobal
  simpa only [digitFrame_start, digitFrame_end] using hglobal

def hornerFrame (alphabet : List Bool)
    (c : PrimeSamplerBinaryHornerStream.Config) : Config :=
  renameCfg hornerStacks hornerLabels hornerControl
    (liftCfg (some (.inr .outer))
      (PrimeSamplerBinaryDigitStream.initial, BitMachineBinaryDivision.initial)
      (fun i : Fin 8 => ![[],[],[],[],[],[],[],alphabet] i) c)

theorem hornerFrame_start
    (labelBits prime coordinate alphabet : List Bool) :
    let words := PrimeSamplerBinaryDigitStream.streamWords prime
      (labelBits.length + 1) labelBits.reverse
    hornerFrame alphabet
      (PrimeSamplerBinaryHornerStream.phaseCfg .choose none
        coordinate [] prime [] []
        (PrimeSamplerBinaryDigitStream.encodeWords words [])) =
    cfg (some (.inr (.inl (.inr (.inr .choose))))) initial
      [] prime [] [] [] [] [] []
      (PrimeSamplerBinaryDigitStream.encodeWords words [])
      coordinate alphabet [] [] [] [] [] [] [] [] [] [] [] [] := by
  dsimp
  unfold hornerFrame PrimeSamplerBinaryHornerStream.phaseCfg cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [hornerStacks, hornerPermutation,
      PrimeSamplerBinaryHornerStream.cfg,
      PrimeSamplerBinaryHornerStream.bank,
      finSumFinEquiv, Fin.addCases]

theorem hornerFrame_end
    (labelBits prime coordinate alphabet : List Bool) :
    let words := PrimeSamplerBinaryDigitStream.streamWords prime
      (labelBits.length + 1) labelBits.reverse
    hornerFrame alphabet
      (PrimeSamplerBinaryHornerStream.cfg none
        (PrimeSamplerBinaryModularStep.initial, some false, none)
        [] [] [] coordinate
        (PrimeSamplerBinaryHornerStream.evaluateWords coordinate prime words [])
        [] [] [] prime [] [] [] [] [] []) =
    cfg (some (.inr (.inr .outer))) initial
      [] prime [] [] [] [] [] [] [] coordinate alphabet
      [] [] []
      (PrimeSamplerBinaryHornerStream.evaluateWords coordinate prime words [])
      [] [] [] [] [] [] [] [] := by
  dsimp
  unfold hornerFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [hornerStacks, hornerPermutation,
      PrimeSamplerBinaryHornerStream.cfg,
      PrimeSamplerBinaryHornerStream.bank,
      finSumFinEquiv, Fin.addCases]

theorem horner_call
    (labelBits prime coordinate alphabet : List Bool)
    (hp : 0 < EncodedCommunication.bitsValue prime) :
    let words := PrimeSamplerBinaryDigitStream.streamWords prime
      (labelBits.length + 1) labelBits.reverse
    ∃ n ≤ (labelBits.length + 1) *
        PrimeSamplerBinaryHornerStream.wordCostBound coordinate prime
          (labelBits.length + prime.length) + 1,
      run n (cfg (some (.inr (.inl (.inr (.inr .choose))))) initial
        [] prime [] [] [] [] [] []
        (PrimeSamplerBinaryDigitStream.encodeWords words [])
        coordinate alphabet [] [] [] [] [] [] [] [] [] [] [] [] ) =
      cfg (some (.inr (.inr .outer))) initial
        [] prime [] [] [] [] [] [] [] coordinate alphabet
        [] [] []
        (PrimeSamplerBinaryHornerStream.evaluateWords coordinate prime words [])
        [] [] [] [] [] [] [] [] := by
  dsimp
  have hQ : ∀ l, program (hornerLabels (.inl l)) =
      renameStmt hornerStacks hornerLabels hornerControl
        (liftStmt (some (.inr .outer))
          (PrimeSamplerBinaryHornerStream.program l)) := by
    intro l
    rfl
  obtain ⟨u, hu, hr⟩ := PrimeSamplerBinaryHornerStream.run_label_horner
    labelBits coordinate prime hp
  have hhalt : (((advance PrimeSamplerBinaryHornerStream.program)^[u])
      (PrimeSamplerBinaryHornerStream.phaseCfg .choose none
        coordinate [] prime [] []
        (PrimeSamplerBinaryDigitStream.encodeWords
          (PrimeSamplerBinaryDigitStream.streamWords prime
            (labelBits.length + 1) labelBits.reverse) []))).l = none := by
    change (PrimeSamplerBinaryHornerStream.run u
      (PrimeSamplerBinaryHornerStream.phaseCfg .choose none
        coordinate [] prime [] []
        (PrimeSamplerBinaryDigitStream.encodeWords
          (PrimeSamplerBinaryDigitStream.streamWords prime
            (labelBits.length + 1) labelBits.reverse) []))).l = none
    rw [hr]
    rfl
  obtain ⟨n, hn, hglobal⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    hornerStacks hornerLabels hornerControl
    PrimeSamplerBinaryHornerStream.program program
    (some (.inr .outer)) hQ
    (PrimeSamplerBinaryDigitStream.initial, BitMachineBinaryDivision.initial)
    (fun i : Fin 8 => ![[],[],[],[],[],[],[],alphabet] i)
    (PrimeSamplerBinaryHornerStream.phaseCfg .choose none
      coordinate [] prime [] []
      (PrimeSamplerBinaryDigitStream.encodeWords
        (PrimeSamplerBinaryDigitStream.streamWords prime
          (labelBits.length + 1) labelBits.reverse) [])) u hhalt
  refine ⟨n, hn.trans hu, ?_⟩
  change run n (hornerFrame alphabet _) = hornerFrame alphabet _ at hglobal
  rw [show ((advance PrimeSamplerBinaryHornerStream.program)^[u]) _ =
    PrimeSamplerBinaryHornerStream.run u _ from rfl, hr] at hglobal
  simpa only [hornerFrame_start, hornerFrame_end] using hglobal

def divisionFrame (prime coordinate : List Bool)
    (c : BitMachineBinaryDivision.Config) : Config :=
  renameCfg divisionStacks divisionLabels divisionControl
    (liftCfg none
      (PrimeSamplerBinaryDigitStream.initial,
        (PrimeSamplerBinaryModularStep.initial, some false, none))
      (fun i : Fin 16 => ![[],prime,[],[],[],[],[],[],[],coordinate,
        [],[],[],[],[],[]] i) c)

theorem divisionFrame_start
    (prime coordinate alphabet accumulator : List Bool) :
    divisionFrame prime coordinate
      (BitMachineBinaryDivision.cfg (some .outer)
        BitMachineBinaryDivision.initial
        accumulator alphabet [] [] [] [] []) =
    cfg (some (.inr (.inr .outer))) initial
      [] prime [] [] [] [] [] [] [] coordinate alphabet
      [] [] [] accumulator [] [] [] [] [] [] [] [] := by
  unfold divisionFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [divisionStacks, divisionPermutation,
      BitMachineBinaryDivision.cfg, BitMachineBinaryDivision.bank,
      finSumFinEquiv, Fin.addCases]

theorem divisionFrame_end
    (prime coordinate alphabet accumulator : List Bool) :
    divisionFrame prime coordinate
      (BitMachineBinaryDivision.cfg none BitMachineBinaryDivision.initial
        [] alphabet
        (BitMachineBinaryDivision.divideFrom accumulator alphabet [] []).1
        (BitMachineBinaryDivision.divideFrom accumulator alphabet [] []).2
        [] [] []) =
    cfg none initial
      [] prime [] [] [] [] [] [] [] coordinate alphabet
      [] [] [] [] [] [] []
      (BitMachineBinaryDivision.divideFrom accumulator alphabet [] []).1
      (BitMachineBinaryDivision.divideFrom accumulator alphabet [] []).2
      [] [] [] := by
  unfold divisionFrame cfg bank
  simp only [renameCfg, liftCfg]
  congr 1
  funext k
  fin_cases k <;>
    simp [divisionStacks, divisionPermutation,
      BitMachineBinaryDivision.cfg, BitMachineBinaryDivision.bank,
      finSumFinEquiv, Fin.addCases]

theorem division_call
    (prime coordinate alphabet accumulator : List Bool) :
    ∃ n ≤ (accumulator.length + 1) *
        (4 * (accumulator.length + alphabet.length + 1) + 5),
      run n (cfg (some (.inr (.inr .outer))) initial
        [] prime [] [] [] [] [] [] [] coordinate alphabet
        [] [] [] accumulator [] [] [] [] [] [] [] [] ) =
      cfg none initial
        [] prime [] [] [] [] [] [] [] coordinate alphabet
        [] [] [] [] [] [] []
        (BitMachineBinaryDivision.divideFrom accumulator alphabet [] []).1
        (BitMachineBinaryDivision.divideFrom accumulator alphabet [] []).2
        [] [] [] := by
  have hQ : ∀ l, program (divisionLabels (.inl l)) =
      renameStmt divisionStacks divisionLabels divisionControl
        (liftStmt none (BitMachineBinaryDivision.program l)) := by
    intro l
    rfl
  have hr := BitMachineBinaryDivision.total_run accumulator alphabet [] []
  have ht := BitMachineBinaryDivision.standard_time_bound accumulator alphabet
  have hhalt : (((advance BitMachineBinaryDivision.program)^[
      BitMachineBinaryDivision.totalTime accumulator alphabet []])
      (BitMachineBinaryDivision.cfg (some .outer)
        BitMachineBinaryDivision.initial
        accumulator alphabet [] [] [] [] [])).l = none := by
    change (BitMachineBinaryDivision.run
      (BitMachineBinaryDivision.totalTime accumulator alphabet [])
      (BitMachineBinaryDivision.cfg (some .outer)
        BitMachineBinaryDivision.initial
        accumulator alphabet [] [] [] [] [])).l = none
    rw [hr]
    rfl
  obtain ⟨n, hn, hglobal⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    divisionStacks divisionLabels divisionControl
    BitMachineBinaryDivision.program program none hQ
    (PrimeSamplerBinaryDigitStream.initial,
      (PrimeSamplerBinaryModularStep.initial, some false, none))
    (fun i : Fin 16 => ![[],prime,[],[],[],[],[],[],[],coordinate,
      [],[],[],[],[],[]] i)
    (BitMachineBinaryDivision.cfg (some .outer)
      BitMachineBinaryDivision.initial
      accumulator alphabet [] [] [] [] [])
    (BitMachineBinaryDivision.totalTime accumulator alphabet []) hhalt
  refine ⟨n, hn.trans ht, ?_⟩
  change run n (divisionFrame prime coordinate _) =
    divisionFrame prime coordinate _ at hglobal
  rw [show ((advance BitMachineBinaryDivision.program)^[
    BitMachineBinaryDivision.totalTime accumulator alphabet []]) _ =
    BitMachineBinaryDivision.run
      (BitMachineBinaryDivision.totalTime accumulator alphabet []) _ from rfl,
      hr] at hglobal
  simpa only [divisionFrame_start, divisionFrame_end] using hglobal

def words (labelBits prime : List Bool) : List (List Bool) :=
  PrimeSamplerBinaryDigitStream.streamWords prime
    (labelBits.length + 1) labelBits.reverse

def accumulatorWord (labelBits prime coordinate : List Bool) : List Bool :=
  PrimeSamplerBinaryHornerStream.evaluateWords coordinate prime
    (words labelBits prime) []

def resultWord (labelBits prime coordinate alphabet : List Bool) : List Bool :=
  (BitMachineBinaryDivision.divideFrom
    (accumulatorWord labelBits prime coordinate) alphabet [] []).1

def inputCfg (labelBits prime coordinate alphabet : List Bool) : Config :=
  cfg (some (.inl (.inl .outer))) initial
    labelBits.reverse prime [] [] [] [] [] [] [] coordinate alphabet
    [] [] [] [] [] [] [] [] [] [] [] []

def outputCfg (labelBits prime coordinate alphabet : List Bool) : Config :=
  cfg none initial
    [] prime [] [] [] [] [] [] [] coordinate alphabet
    [] [] [] [] [] [] []
    (BitMachineBinaryDivision.divideFrom
      (accumulatorWord labelBits prime coordinate) alphabet [] []).1
    (BitMachineBinaryDivision.divideFrom
      (accumulatorWord labelBits prime coordinate) alphabet [] []).2
    [] [] []

def queryCost (labelBits prime coordinate alphabet : List Bool) : ℕ :=
  (labelBits.length + 1) *
      PrimeSamplerBinaryDigitStream.cycleBound labelBits.length prime.length +
    ((labelBits.length + 1) *
      PrimeSamplerBinaryHornerStream.wordCostBound coordinate prime
        (labelBits.length + prime.length) + 1) +
    ((prime.length + 1) *
      (4 * (prime.length + alphabet.length + 1) + 5))

/-- The one fixed twenty-three-bank controller executes digit extraction,
Horner evaluation, and the final alphabet division. This is a physical
bitword-length cost, with no factor depending on numerical `degree` or
numerical label value. -/
theorem query_run (labelBits prime coordinate alphabet : List Bool)
    (hp : 2 ≤ EncodedCommunication.bitsValue prime) :
    ∃ t ≤ queryCost labelBits prime coordinate alphabet,
      run t (inputCfg labelBits prime coordinate alphabet) =
        outputCfg labelBits prime coordinate alphabet := by
  obtain ⟨n₁, hn₁, hd⟩ := digit_call labelBits prime coordinate alphabet hp
  rw [PrimeSamplerBinaryDigitStream.streamFuel_eq_encodeWords] at hd
  obtain ⟨n₂, hn₂, hh⟩ := horner_call labelBits prime coordinate alphabet
    (by omega)
  let acc := accumulatorWord labelBits prime coordinate
  obtain ⟨n₃, hn₃, hm⟩ := division_call prime coordinate alphabet acc
  have hacc : acc.length ≤ prime.length := by
    exact PrimeSamplerBinaryHornerStream.evaluateWords_length
      coordinate prime (by omega) (words labelBits prime) [] (by simp)
  have h₁₂ := (run_add hd n₂).trans hh
  have h₁₂₃ := (run_add h₁₂ n₃).trans hm
  refine ⟨n₁ + n₂ + n₃, ?_, ?_⟩
  · dsimp [queryCost, acc] at *
    nlinarith
  · simpa only [inputCfg, outputCfg, accumulatorWord, words]
      using h₁₂₃

theorem query_value (labelBits prime coordinate alphabet : List Bool)
    (hp : 2 ≤ EncodedCommunication.bitsValue prime)
    (hm : 0 < EncodedCommunication.bitsValue alphabet)
    (degree : ℕ)
    (hlabel : EncodedCommunication.bitsValue labelBits <
      EncodedCommunication.bitsValue prime ^ degree) :
    EncodedCommunication.bitsValue
      (resultWord labelBits prime coordinate alphabet) =
      PrimeSamplerEntryAlgorithm.entry
        (EncodedCommunication.bitsValue prime) degree
        (EncodedCommunication.bitsValue alphabet)
        (EncodedCommunication.bitsValue labelBits)
        (EncodedCommunication.bitsValue coordinate) := by
  have hdiv := (BitMachineBinaryDivision.standard_division_spec
    (accumulatorWord labelBits prime coordinate) alphabet hm).2
  have hhorner := PrimeSamplerBinaryHornerStream.label_horner_value
    labelBits coordinate prime hp degree hlabel
  change BitMachineBinaryDivision.msbValue
    (accumulatorWord labelBits prime coordinate) = _ at hhorner
  simpa [resultWord, PrimeSamplerEntryAlgorithm.entry, hhorner] using hdiv

/-- A cubic upper bound in the four binary operand lengths, independent of
the numerical degree and label. -/
theorem queryCost_poly (labelBits prime coordinate alphabet : List Bool) :
    let N := labelBits.length + prime.length + coordinate.length + alphabet.length
    queryCost labelBits prime coordinate alphabet ≤ 3000 * (N + 1) ^ 3 := by
  let L := labelBits.length
  let P := prime.length
  let J := coordinate.length
  let M := alphabet.length
  let N := L + P + J + M
  have hL : L + 1 ≤ N + 1 := by dsimp [N,L,P,J,M]; omega
  have hcycle : PrimeSamplerBinaryDigitStream.cycleBound L P ≤
      20 * (N + 1) ^ 2 := by
    dsimp [PrimeSamplerBinaryDigitStream.cycleBound]
    have hfactor : 4 * (L + P + 1) + 5 ≤ 9 * (N + 1) := by
      dsimp [N,L,P,J,M]
      omega
    have hprod := Nat.mul_le_mul hL hfactor
    have hlin : (L + P + 2) + (3 * L + 3) + 1 ≤ 6 * (N + 1) := by
      dsimp [N,L,P,J,M]
      omega
    nlinarith [sq_nonneg (N + 1)]
  have hword : PrimeSamplerBinaryHornerStream.wordCostBound
      coordinate prime (L + P) ≤ 2000 * (N + 1) ^ 2 := by
    dsimp [PrimeSamplerBinaryHornerStream.wordCostBound]
    have hbase : 2 * P + J + (L + P) + 1 ≤ 3 * (N + 1) := by
      dsimp [N,L,P,J,M]
      omega
    nlinarith [sq_nonneg (N + 1)]
  have hfinal : (P + 1) * (4 * (P + M + 1) + 5) ≤
      10 * (N + 1) ^ 2 := by
    have hfactor : 4 * (P + M + 1) + 5 ≤ 9 * (N + 1) := by
      dsimp [N,L,P,J,M]
      omega
    have hp : P + 1 ≤ N + 1 := by dsimp [N,L,P,J,M]; omega
    have hprod := Nat.mul_le_mul hp hfactor
    nlinarith [sq_nonneg (N + 1)]
  have hdigit := Nat.mul_le_mul hL hcycle
  have hhorner := Nat.mul_le_mul hL hword
  have hcube : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := by
    nlinarith [sq_nonneg N]
  change (L + 1) * PrimeSamplerBinaryDigitStream.cycleBound L P +
    ((L + 1) * PrimeSamplerBinaryHornerStream.wordCostBound coordinate prime
      (L + P) + 1) +
    (P + 1) * (4 * (P + M + 1) + 5) ≤ 3000 * (N + 1) ^ 3
  nlinarith [sq_nonneg (N + 1)]

def initialBank (labelBits prime coordinate alphabet : List Bool) : Stack → List Bool :=
  bank labelBits.reverse prime [] [] [] [] [] [] [] coordinate alphabet
    [] [] [] [] [] [] [] [] [] [] [] []

def finalBank (labelBits prime coordinate alphabet : List Bool) : Stack → List Bool :=
  bank [] prime [] [] [] [] [] [] [] coordinate alphabet
    [] [] [] [] [] [] []
    (BitMachineBinaryDivision.divideFrom
      (accumulatorWord labelBits prime coordinate) alphabet [] []).1
    (BitMachineBinaryDivision.divideFrom
      (accumulatorWord labelBits prime coordinate) alphabet [] []).2
    [] [] []

def packedInput (labelBits prime coordinate alphabet : List Bool) : List Bool :=
  BitMachineBankCodec.encode (initialBank labelBits prime coordinate alphabet)

theorem initialBank_code_length (labelBits prime coordinate alphabet : List Bool) :
    let N := labelBits.length + prime.length + coordinate.length + alphabet.length
    (packedInput labelBits prime coordinate alphabet).length = 2 * N + 23 := by
  rw [packedInput, BitMachineBankCodec.encode_length]
  simp [initialBank, bank, Fin.sum_univ_succ]
  omega

theorem finalBank_code_length_le (labelBits prime coordinate alphabet : List Bool)
    (hp : 2 ≤ EncodedCommunication.bitsValue prime) :
    let N := labelBits.length + prime.length + coordinate.length + alphabet.length
    (BitMachineBankCodec.encode
      (finalBank labelBits prime coordinate alphabet)).length ≤ 20 * (N + 1) := by
  let acc := accumulatorWord labelBits prime coordinate
  have hacc : acc.length ≤ prime.length :=
    PrimeSamplerBinaryHornerStream.evaluateWords_length coordinate prime
      (by omega) (words labelBits prime) [] (by simp)
  have hq := BitMachineBinaryDivision.divideFrom_quotient_length
    acc alphabet [] []
  simp only [List.length_nil, Nat.add_zero] at hq
  have hr := BitMachineBinaryDivision.divideFrom_remainder_length
    acc alphabet [] [] acc.length (by simp) le_rfl
  dsimp [acc] at hacc hq hr
  have hpLen : 0 < prime.length := by
    cases prime with
    | nil => simp [EncodedCommunication.bitsValue] at hp
    | cons b bs => simp
  rw [BitMachineBankCodec.encode_length]
  simp [finalBank, bank, Fin.sum_univ_succ] at hq hr ⊢
  omega

theorem packed_run (labelBits prime coordinate alphabet : List Bool)
    (hp : 2 ≤ EncodedCommunication.bitsValue prime) :
    ∃ (u : ℕ) (S' : Stack → List Bool),
      u ≤ 10000 * ((packedInput labelBits prime coordinate alphabet).length + 1) ^ 3 ∧
      BitMachineBankWrapper.run program (.inl (.inl .outer)) initial u
        (BitMachineBankWrapper.cfg
          (some (.inr (.parse (.scan 0)))) (initial, none)
          (fun _ : Stack => [])
          (packedInput labelBits prime coordinate alphabet) [] []) =
        BitMachineBankWrapper.cfg none (initial, none) S' [] []
          (BitMachineBankCodec.encode
            (finalBank labelBits prime coordinate alphabet)) := by
  have hd : BitMachineBankCodec.decode 23
      (packedInput labelBits prime coordinate alphabet) =
      some (initialBank labelBits prime coordinate alphabet) := by
    simp [packedInput]
  obtain ⟨n, hn, hr⟩ := query_run labelBits prime coordinate alphabet hp
  let c : Config := ⟨none, initial,
    finalBank labelBits prime coordinate alphabet⟩
  have hc : ((advance program)^[n])
      (⟨some (.inl (.inl .outer)), initial,
        initialBank labelBits prime coordinate alphabet⟩ : Config) = c := by
    simpa [run, inputCfg, outputCfg, initialBank, finalBank, c]
      using hr
  have hhalt : c.l = none := rfl
  obtain ⟨u, S', hu, hrun⟩ := BitMachineBankWrapper.packed_run
    program (.inl (.inl .outer)) initial
    (packedInput labelBits prime coordinate alphabet)
    (initialBank labelBits prime coordinate alphabet) hd n c hc hhalt
  have he : BitMachineBankSerialize.encode
      (List.ofFn (finalBank labelBits prime coordinate alphabet)) =
      BitMachineBankCodec.encode
        (finalBank labelBits prime coordinate alphabet) := by
    rw [BitMachineBankCodec.encode_eq_list]
    rfl
  rw [he] at hu hrun
  refine ⟨u, S', ?_, hrun⟩
  have hi := initialBank_code_length labelBits prime coordinate alphabet
  have ho := finalBank_code_length_le labelBits prime coordinate alphabet hp
  have hnpoly := queryCost_poly labelBits prime coordinate alphabet
  let N := labelBits.length + prime.length + coordinate.length + alphabet.length
  change (packedInput labelBits prime coordinate alphabet).length = 2 * N + 23 at hi
  change (BitMachineBankCodec.encode
    (finalBank labelBits prime coordinate alphabet)).length ≤
    20 * (N + 1) at ho
  change queryCost labelBits prime coordinate alphabet ≤
    3000 * (N + 1) ^ 3 at hnpoly
  have hn' : n ≤ 3000 * (N + 1) ^ 3 := hn.trans hnpoly
  rw [hi] at hu ⊢
  nlinarith [Nat.zero_le N]

noncomputable def packedMachine : BitMachine.Machine :=
  BitMachineBankWrapper.machine program (.inl (.inl .outer)) initial

/-- Canonical four-word packets have a single fixed-machine execution in
cubic packet bitlength. The semantic theorem separately guards positive
alphabet and the frozen label domain; malformed packets are not asserted to
encode valid prime-family entries. -/
theorem packed_outputs (labelBits prime coordinate alphabet : List Bool)
    (hp : 2 ≤ EncodedCommunication.bitsValue prime) :
    packedMachine.OutputsWithin
      (packedInput labelBits prime coordinate alphabet)
      (BitMachineBankCodec.encode
        (finalBank labelBits prime coordinate alphabet))
      (10000 * ((packedInput labelBits prime coordinate alphabet).length + 1) ^ 3) := by
  obtain ⟨u, S', hu, hr⟩ := packed_run labelBits prime coordinate alphabet hp
  change (BitMachineBankWrapper.machine program (.inl (.inl .outer)) initial).OutputsWithin
    (packedInput labelBits prime coordinate alphabet)
    (BitMachineBankCodec.encode
      (finalBank labelBits prime coordinate alphabet))
    (10000 * ((packedInput labelBits prime coordinate alphabet).length + 1) ^ 3)
  apply outputsWithin_of_raw_run (.inr 0) (.inr 2)
    (.inr (.parse (.scan 0))) (initial, none)
    (BitMachineBankWrapper.program program (.inl (.inl .outer)) initial)
    (packedInput labelBits prime coordinate alphabet)
    (BitMachineBankCodec.encode
      (finalBank labelBits prime coordinate alphabet)) u _ hu
  · rw [BitMachineBankWrapper.initial_cfg]
    change (BitMachineBankWrapper.run program (.inl (.inl .outer)) initial u _).l = none
    rw [hr]
    rfl
  · rw [BitMachineBankWrapper.initial_cfg]
    change (BitMachineBankWrapper.run program (.inl (.inl .outer)) initial u _).stk
      (.inr 2) = _
    rw [hr]
    rfl

theorem answer_decodes (labelBits prime coordinate alphabet : List Bool) :
    BitMachineBankCodec.decode 23
      (BitMachineBankCodec.encode
        (finalBank labelBits prime coordinate alphabet)) =
      some (finalBank labelBits prime coordinate alphabet) := by
  simp

theorem answer_entry_value (labelBits prime coordinate alphabet : List Bool)
    (hp : 2 ≤ EncodedCommunication.bitsValue prime)
    (hm : 0 < EncodedCommunication.bitsValue alphabet)
    (degree : ℕ)
    (hlabel : EncodedCommunication.bitsValue labelBits <
      EncodedCommunication.bitsValue prime ^ degree) :
    EncodedCommunication.bitsValue
      ((finalBank labelBits prime coordinate alphabet) 18) =
      PrimeSampler.entry
        (EncodedCommunication.bitsValue prime) degree
        (EncodedCommunication.bitsValue alphabet)
        (EncodedCommunication.bitsValue labelBits)
        (EncodedCommunication.bitsValue coordinate) := by
  have hv := query_value labelBits prime coordinate alphabet hp hm degree hlabel
  rw [PrimeSamplerEntryAlgorithm.entry_eq] at hv
  simpa [finalBank, bank, resultWord] using hv
end EthInapproximability.CurrentPaper.PrimeSamplerBinaryQueryMachine
