import EthInapproximability.CurrentPaper.SamplerWriterFinalCleanup
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.ExecutableExactReduction

/-!
# One physical first/middle/second/reverse/cleanup sampler controller

All five fixed instruction tables are inlined on one shared Boolean-stack
bank. The four handoff transitions are charged explicitly.
-/

namespace EthInapproximability.CurrentPaper.SamplerWriterFullSequence

open Turing BitMachineEncoding
open SamplerWriterPhysicalSequence

abbrev Stack := SamplerWriterPhysicalSequence.Stack

abbrev FirstLabel := SamplerMachineFieldTable.Label
abbrev FirstControl := SamplerMachineFieldTable.Control
abbrev MiddleLabel := SamplerWriterSecondSequence.Label
abbrev MiddleControl := SamplerWriterSecondSequence.Control
abbrev SecondLabel := SamplerMachineFieldTable.Label
abbrev SecondControl := SamplerMachineFieldTable.Control
abbrev ReverseLabel := SamplerMachineBlockReverse.Label
abbrev ReverseControl := SamplerMachineBlockReverse.Control
abbrev ClearLabel := SamplerWriterFinalCleanup.Label
abbrev ClearControl := SamplerWriterFinalCleanup.Control

def firstStart : FirstLabel := .inl (.inr .scan)
def firstIdle : FirstControl := .inl SamplerMachineChosenWord.initial
def middleStart : MiddleLabel := .inl (.inl (.inl 0))
def middleIdle : MiddleControl := (((((), none), none), none), none)
def secondStart : SecondLabel := .inl (.inr .scan)
def secondIdle : SecondControl := .inl SamplerMachineChosenWord.initial
def reverseStart : ReverseLabel := .check
def reverseIdle : ReverseControl := SamplerMachineBlockReverse.initial
def clearStart : ClearLabel := 0
def clearIdle : ClearControl := ((), none)

abbrev PairLabel := BitMachineRawSequence.Label FirstLabel MiddleLabel
abbrev PairControl := BitMachineRawSequence.Control FirstControl MiddleControl
abbrev TripleLabel := BitMachineRawSequence.Label PairLabel SecondLabel
abbrev TripleControl := BitMachineRawSequence.Control PairControl SecondControl
abbrev QuadLabel := BitMachineRawSequence.Label TripleLabel ReverseLabel
abbrev QuadControl := BitMachineRawSequence.Control TripleControl ReverseControl
abbrev Label := BitMachineRawSequence.Label QuadLabel ClearLabel
abbrev Control := BitMachineRawSequence.Control QuadControl ClearControl

def pairProgram : PairLabel → TM2.Stmt (fun _ : Stack => Bool) PairLabel PairControl :=
  BitMachineRawSequence.program firstProgram SamplerWriterSecondSequence.program
    middleStart firstIdle middleIdle

def tripleProgram : TripleLabel → TM2.Stmt (fun _ : Stack => Bool)
    TripleLabel TripleControl :=
  BitMachineRawSequence.program pairProgram secondProgram
    secondStart (firstIdle, middleIdle) secondIdle

def quadProgram : QuadLabel → TM2.Stmt (fun _ : Stack => Bool)
    QuadLabel QuadControl :=
  BitMachineRawSequence.program tripleProgram reverseProgram
    reverseStart ((firstIdle, middleIdle), secondIdle) reverseIdle

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineRawSequence.program quadProgram SamplerWriterFinalCleanup.program
    clearStart (((firstIdle, middleIdle), secondIdle), reverseIdle) clearIdle

def startLabel : Label := .inl (.inl (.inl (.inl firstStart)))
def startControl : Control :=
  ((((firstIdle, middleIdle), secondIdle), reverseIdle), clearIdle)

def firstLength (a : ℕ) : ℕ := ExactConstruction.prefixLength a + 3
def firstDegree (a t₁ d : ℕ) : ℕ :=
  SmallBiasSampler.fieldExponent (firstLength a)
    (SmallBiasSampler.exactDenominator d * (2 ^ 1) ^ t₁)
def secondDegree (a t₂ d : ℕ) : ℕ :=
  SmallBiasSampler.fieldExponent (d * a)
    (SmallBiasSampler.exactDenominator d * (2 ^ a) ^ t₂)

def firstBank (a d N₁ N₂ n : ℕ) (source secondBits : List Bool)
    (secondLength t₁ : ℕ) : Stack → List Bool :=
  afterFirst a d N₁ N₂ n source secondBits secondLength
    (firstDegree a t₁ d) (firstLength a)

def middleBank (a d N₁ N₂ n : ℕ) (source secondBits : List Bool)
    (secondLength t₁ : ℕ) : Stack → List Bool :=
  afterMiddle a d N₁ N₂ n (firstDegree a t₁ d) (firstLength a)
    secondLength source secondBits

def secondBank (a d N₁ N₂ n : ℕ) (source secondBits : List Bool)
    (secondLength t₁ : ℕ) : Stack → List Bool :=
  afterSecond a d N₁ N₂ n (firstDegree a t₁ d) (firstLength a)
    secondLength source secondBits

def reverseBank (a t₁ t₂ d N₁ N₂ n : ℕ) (source secondBits : List Bool)
    (v : Fin n → Fin d → Bool) : Stack → List Bool :=
  afterReverse a t₁ t₂ d N₁ N₂ n (firstDegree a t₁ d)
    (firstLength a) source secondBits v

def middleCost (a d N₁ N₂ n : ℕ) (source secondBits : List Bool)
    (t₁ : ℕ) : ℕ :=
  ((firstBank a d N₁ N₂ n source secondBits (d * a) t₁)
      SamplerWriterSecondInit.degreeCell).length +
  ((firstBank a d N₁ N₂ n source secondBits (d * a) t₁)
      SamplerWriterSecondInit.lengthCell).length + 4 +
  (2 * secondBits.length + 2) +
  (2 * (List.replicate (d * a) true).length + 2) +
  (2 * (List.replicate a true).length + 2) + 3

def reverseCost (a t₂ d : ℕ) : ℕ :=
  (SamplerExactPayloadArrays.secondBlocks a t₂ d).length *
      SamplerMachineBlockReverse.blockStep a +
    ((SamplerExactPayloadArrays.secondBlocks a t₂ d).reverse.flatten).length + 2

def clearCost (a t₁ t₂ d N₁ N₂ n : ℕ) (source secondBits : List Bool)
    (v : Fin n → Fin d → Bool) : ℕ :=
  (∑ i : Fin 21,
    ((reverseBank a t₁ t₂ d N₁ N₂ n source secondBits v)
      (SamplerWriterFinalCleanup.clearing i)).length) + 23

def totalCost (a t₁ t₂ d N₁ N₂ n : ℕ) (source firstBits secondBits : List Bool)
    (v : Fin n → Fin d → Bool) : ℕ :=
  SamplerMachineFieldTable.timeBound firstBits.length (firstLength a) +
  middleCost a d N₁ N₂ n source secondBits t₁ +
  SamplerMachineFieldTable.timeBound secondBits.length (d * a) +
  reverseCost a t₂ d +
  clearCost a t₁ t₂ d N₁ N₂ n source secondBits v + 4

theorem run_exact (a t₁ t₂ d N₁ N₂ n : ℕ) (ha : 0 < a)
    (v : Fin n → Fin d → Bool) (source firstBits secondBits : List Bool)
    (hsource : source =
      (SamplerWriterFinalCleanup.exactData a t₁ t₂ d n v).source)
    (hfirst : firstBits.length = firstDegree a t₁ d)
    (hsecond : secondBits.length = secondDegree a t₂ d) :
    ∃ t ≤ totalCost a t₁ t₂ d N₁ N₂ n source firstBits secondBits v,
      ((advance program)^[t])
        (⟨some startLabel, startControl,
          initial a d N₁ N₂ n source firstBits secondBits
            (firstLength a) (d * a)⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none, startControl,
          SamplerWriterFinalCleanup.expected a t₁ t₂ d N₁ N₂ n v⟩ := by
  obtain ⟨tf, htf, hrf⟩ := run_first a d N₁ N₂ n source firstBits secondBits
    (firstLength a) (d * a)
  have hf : ((advance firstProgram)^[tf])
      (⟨some firstStart, firstIdle,
        initial a d N₁ N₂ n source firstBits secondBits
          (firstLength a) (d * a)⟩ :
        TM2.Cfg (fun _ : Stack => Bool) FirstLabel FirstControl) =
      ⟨none, .inr SamplerMachineTable.initial,
        firstBank a d N₁ N₂ n source secondBits (d * a) t₁⟩ := by
    simpa only [firstStart, firstIdle, firstBank, hfirst] using hrf
  obtain ⟨tm, htm, hrm⟩ := run_middle a d N₁ N₂ n
    (firstDegree a t₁ d) (firstLength a) (d * a) source secondBits
  have hm : ((advance SamplerWriterSecondSequence.program)^[tm])
      (⟨some middleStart, middleIdle,
        firstBank a d N₁ N₂ n source secondBits (d * a) t₁⟩ :
        TM2.Cfg (fun _ : Stack => Bool) MiddleLabel MiddleControl) =
      ⟨none, middleIdle,
        middleBank a d N₁ N₂ n source secondBits (d * a) t₁⟩ := by
    simpa only [middleStart, middleIdle, firstBank, middleBank,
      afterMiddle] using hrm
  obtain ⟨ts, hts, hrs⟩ := run_second a d N₁ N₂ n
    (firstDegree a t₁ d) (firstLength a) (d * a) source secondBits
  have hs : ((advance secondProgram)^[ts])
      (⟨some secondStart, secondIdle,
        middleBank a d N₁ N₂ n source secondBits (d * a) t₁⟩ :
        TM2.Cfg (fun _ : Stack => Bool) SecondLabel SecondControl) =
      ⟨none, .inr SamplerMachineTable.initial,
        secondBank a d N₁ N₂ n source secondBits (d * a) t₁⟩ := by
    simpa only [secondStart, secondIdle, middleBank, secondBank,
      afterMiddle, afterSecond] using hrs
  obtain ⟨tr, htr, hrr⟩ := run_reverse a t₁ t₂ d N₁ N₂ n
    (firstDegree a t₁ d) (firstLength a) ha source secondBits
    hsecond v
  have hr : ((advance reverseProgram)^[tr])
      (⟨some reverseStart, reverseIdle,
        secondBank a d N₁ N₂ n source secondBits (d * a) t₁⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ReverseLabel ReverseControl) =
      ⟨none, reverseIdle,
        reverseBank a t₁ t₂ d N₁ N₂ n source secondBits v⟩ := by
    simpa only [reverseStart, reverseIdle, secondBank, reverseBank,
      reverseInput] using hrr
  have hc : ((advance SamplerWriterFinalCleanup.program)^[(clearCost
      a t₁ t₂ d N₁ N₂ n source secondBits v)])
      (⟨some clearStart, clearIdle,
        reverseBank a t₁ t₂ d N₁ N₂ n source secondBits v⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ClearLabel ClearControl) =
      ⟨none, clearIdle,
        SamplerWriterFinalCleanup.expected a t₁ t₂ d N₁ N₂ n v⟩ := by
    have hh := SamplerWriterFinalCleanup.run_halt
      (reverseBank a t₁ t₂ d N₁ N₂ n source secondBits v)
    rw [show BitMachineClearBank.cleared SamplerWriterFinalCleanup.clearing
      (reverseBank a t₁ t₂ d N₁ N₂ n source secondBits v) =
        SamplerWriterFinalCleanup.expected a t₁ t₂ d N₁ N₂ n v by
          exact SamplerWriterFinalCleanup.afterReverse_cleared_exact
            a t₁ t₂ d N₁ N₂ n v source secondBits hsource] at hh
    simpa only [clearCost, clearStart, clearIdle] using hh
  obtain ⟨tp, htp, hrp⟩ := BitMachineRawSequence.runs
    firstProgram SamplerWriterSecondSequence.program
    firstStart middleStart firstIdle (.inr SamplerMachineTable.initial)
    middleIdle middleIdle
    (initial a d N₁ N₂ n source firstBits secondBits (firstLength a) (d * a))
    (firstBank a d N₁ N₂ n source secondBits (d * a) t₁)
    (middleBank a d N₁ N₂ n source secondBits (d * a) t₁)
    tf tm hf hm
  obtain ⟨tq, htq, hrq⟩ := BitMachineRawSequence.runs
    pairProgram secondProgram
    (.inl firstStart) secondStart
    (firstIdle, middleIdle) (firstIdle, middleIdle)
    secondIdle (.inr SamplerMachineTable.initial)
    (initial a d N₁ N₂ n source firstBits secondBits (firstLength a) (d * a))
    (middleBank a d N₁ N₂ n source secondBits (d * a) t₁)
    (secondBank a d N₁ N₂ n source secondBits (d * a) t₁)
    tp ts hrp hs
  obtain ⟨tu, htu, hru⟩ := BitMachineRawSequence.runs
    tripleProgram reverseProgram
    (.inl (.inl firstStart)) reverseStart
    ((firstIdle, middleIdle), secondIdle)
    ((firstIdle, middleIdle), (.inr SamplerMachineTable.initial))
    reverseIdle reverseIdle
    (initial a d N₁ N₂ n source firstBits secondBits (firstLength a) (d * a))
    (secondBank a d N₁ N₂ n source secondBits (d * a) t₁)
    (reverseBank a t₁ t₂ d N₁ N₂ n source secondBits v)
    tq tr hrq hr
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    quadProgram SamplerWriterFinalCleanup.program
    (.inl (.inl (.inl firstStart))) clearStart
    (((firstIdle, middleIdle), secondIdle), reverseIdle)
    (((firstIdle, middleIdle), secondIdle), reverseIdle)
    clearIdle clearIdle
    (initial a d N₁ N₂ n source firstBits secondBits (firstLength a) (d * a))
    (reverseBank a t₁ t₂ d N₁ N₂ n source secondBits v)
    (SamplerWriterFinalCleanup.expected a t₁ t₂ d N₁ N₂ n v)
    tu (clearCost a t₁ t₂ d N₁ N₂ n source secondBits v) hru hc
  refine ⟨t, ?_, ?_⟩
  · unfold totalCost
    have hmiddle : tm ≤ middleCost a d N₁ N₂ n source secondBits t₁ := by
      simpa only [middleCost, firstBank] using htm
    have hreverse : tr ≤ reverseCost a t₂ d := by
      simpa only [reverseCost] using htr
    omega
  · simpa only [program, pairProgram, tripleProgram, quadProgram,
      startLabel, startControl] using hrun

def exactFirstBits (s : ℕ) : List Bool :=
  List.replicate
    (firstDegree (ExactParameters.firstExponent s) (ExactParameters.firstOrder s)
      (ExactParameters.dimension s)) false

def exactSecondBits (s : ℕ) : List Bool :=
  List.replicate
    (secondDegree (ExactParameters.firstExponent s) (ExactParameters.secondOrder s)
      (ExactParameters.dimension s)) false

def exactStart (s : ℕ) {n d : ℕ} (e : Fin d → Fin 2 → Fin n) :
    Stack → List Bool :=
  initial (ExactParameters.firstExponent s) (ExactParameters.dimension s)
    (ExactParameters.firstListSize s) (ExactParameters.secondListSize s) (5 * n)
    (ExecutableExactReduction.payload s e).source
    (exactFirstBits s) (exactSecondBits s)
    (firstLength (ExactParameters.firstExponent s))
    (ExactParameters.dimension s * ExactParameters.firstExponent s)

def exactReady (s : ℕ) {n d : ℕ} (e : Fin d → Fin 2 → Fin n) :
    Stack → List Bool :=
  Sum.elim (MatrixScalarWriterFrame.rawInput
    (ExactParameters.firstExponent s) (ExactParameters.dimension s)
    (ExactParameters.firstListSize s) (ExactParameters.secondListSize s) (5 * n)
    (ExecutableExactReduction.payload s e)) (fun _ => [])

theorem run_payload (s : ℕ) {n d : ℕ} (e : Fin d → Fin 2 → Fin n) :
    ∃ t ≤ totalCost
      (ExactParameters.firstExponent s) (ExactParameters.firstOrder s)
      (ExactParameters.secondOrder s) (ExactParameters.dimension s)
      (ExactParameters.firstListSize s) (ExactParameters.secondListSize s) (5 * n)
      (ExecutableExactReduction.payload s e).source
      (exactFirstBits s) (exactSecondBits s)
      (ExactConstruction.sourceVectors (ExactParameters.dimension s) e),
      ((advance program)^[t])
        (⟨some startLabel, startControl, exactStart s e⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none, startControl, exactReady s e⟩ := by
  have ha : 0 < ExactParameters.firstExponent s := by
    unfold ExactParameters.firstExponent
    omega
  have hs : (ExecutableExactReduction.payload s e).source =
      (SamplerWriterFinalCleanup.exactData
        (ExactParameters.firstExponent s) (ExactParameters.firstOrder s)
        (ExactParameters.secondOrder s) (ExactParameters.dimension s)
        (5 * n) (ExactConstruction.sourceVectors (ExactParameters.dimension s) e)).source :=
    rfl
  have hf : (exactFirstBits s).length =
      firstDegree (ExactParameters.firstExponent s) (ExactParameters.firstOrder s)
        (ExactParameters.dimension s) := by simp [exactFirstBits]
  have ht : (exactSecondBits s).length =
      secondDegree (ExactParameters.firstExponent s) (ExactParameters.secondOrder s)
        (ExactParameters.dimension s) := by simp [exactSecondBits]
  simpa only [exactStart, exactReady, SamplerWriterFinalCleanup.expected,
    SamplerWriterFinalCleanup.exactData,
    ExecutableExactReduction.payload, ExecutableExactReduction.firstFamily,
    ExecutableExactReduction.secondFamily]
    using run_exact (ExactParameters.firstExponent s) (ExactParameters.firstOrder s)
      (ExactParameters.secondOrder s) (ExactParameters.dimension s)
      (ExactParameters.firstListSize s) (ExactParameters.secondListSize s)
      (5 * n) ha (ExactConstruction.sourceVectors (ExactParameters.dimension s) e)
      (ExecutableExactReduction.payload s e).source
      (exactFirstBits s) (exactSecondBits s) hs hf ht

end EthInapproximability.CurrentPaper.SamplerWriterFullSequence
