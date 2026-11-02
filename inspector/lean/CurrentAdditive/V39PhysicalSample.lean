import CurrentAdditive.V39ConstructorTransport
import CurrentAdditive.V39CurrentCodeConstructorBounds
import CurrentAdditive.V39DeadRecursiveCode
import CurrentAdditive.V39GeneratorEncodingBridge
import CurrentAdditive.RoundedCodeResources

/-! The actual public-count constructor and actual fixed-bit interpreter run
on one fixed shared bank. The complete output is the same current row-first
sample word consumed by the entry parser. No table evaluator is assumed. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384

namespace CurrentAdditive.V39PhysicalSample
noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2 Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorPositive Paper2.RecursiveSamplingProgram
open V39DeadTaggedCompiler V39GeneratorCode V39RecursiveGenerator V38OneStep

abbrev ConstructorStack := V39CurrentCodeConstructor.Stack
abbrev Stack := RoundedCodeOutput.SharedBank ConstructorStack
def source : ConstructorStack := CodeGeneratorSampleTransfer.sample 10
def constructorSlots : ConstructorStack ↪ Stack := Function.Embedding.inl
def constructorProgram (l : V39CurrentCodeConstructor.Label) :=
  stackStmt constructorSlots (V39DeadSampleJoin.program l)
def interpreterProgram := RoundedCodeOutput.embeddedProgram (RoundedCodeOutput.sharedSlots source)
def interpreterStart : RoundedCodeOutput.Label :=
  BitMachineRawSequence.leftLabel (.inl RoundedCodeLoop.entry)
def program := BitMachineRawSequence.program constructorProgram interpreterProgram
  interpreterStart V39CurrentCodeConstructor.control RoundedCodeOutput.initial
abbrev Label := BitMachineRawSequence.Label V39CurrentCodeConstructor.Label RoundedCodeOutput.Label
abbrev Control := V39CurrentCodeConstructor.Control × RoundedCodeOutput.Control
def start : Label := BitMachineRawSequence.leftLabel V39CurrentCodeConstructor.start
def control : Control := (V39CurrentCodeConstructor.control, RoundedCodeOutput.initial)

def initial (n p q₁ q₂ s w Q k m : ℕ) (tape : List Bool) (b : ℕ) : Stack → List Bool :=
  RoundedCodeOutput.sharedInitial (V39DeadSampleJoin.initial n p s q₁ q₂ w Q k m m) tape b

def afterConstructor (n p q₁ q₂ s w Q k m : ℕ) (tape : List Bool) (b : ℕ) : Stack → List Bool :=
  RoundedCodeOutput.sharedInitial (V39CurrentCodeConstructor.finalBank n p q₁ q₂ s w Q k m) tape b

theorem constructor_bank (n p q₁ q₂ s w Q k m : ℕ) (tape : List Bool) (b : ℕ) :
    bank constructorSlots (initial n p q₁ q₂ s w Q k m tape b)
      (V39CurrentCodeConstructor.finalBank n p q₁ q₂ s w Q k m) =
      afterConstructor n p q₁ q₂ s w Q k m tape b := by
  funext j
  rcases j with j | j
  · change bank constructorSlots _ _ (constructorSlots j) = _
    rw [bank_at]
    rfl
  · rw [bank_outside]
    · rfl
    · rintro ⟨j, h⟩
      cases h

theorem physical_construct (n p q₁ q₂ s w Q k m : ℕ) (hs : 3 ≤ s)
    (tape : List Bool) (b : ℕ) :
    ∃ t ≤ V39DeadSampleJoin.clock n p s q₁ q₂ w Q k m m,
      ((advance constructorProgram)^[t])
        (⟨some V39CurrentCodeConstructor.start,V39CurrentCodeConstructor.control,
          initial n p q₁ q₂ s w Q k m tape b⟩ :
          TM2.Cfg (fun _ : Stack => Bool) V39CurrentCodeConstructor.Label V39CurrentCodeConstructor.Control) =
        ⟨none,V39CurrentCodeConstructor.control,afterConstructor n p q₁ q₂ s w Q k m tape b⟩ := by
  obtain ⟨t,ht,hr⟩ := V39ConstructorTransport.physical_from_bank constructorSlots
    (initial n p q₁ q₂ s w Q k m tape b) n p q₁ q₂ s w Q k m hs (fun _ => rfl)
  exact ⟨t,ht,by simpa only [constructorProgram,constructor_bank] using hr⟩

theorem positive_deadTagged (q₁ q₂ s : ℕ) (c : Code) (hq₂ : 0 < q₂) (hc : Positive c) :
    Positive (deadTaggedCode q₁ q₂ s c) := by
  exact ⟨by decide, ⟨trivial,positive_raw q₁ q₂ s c hq₂ hc⟩,
    ⟨trivial,positive_fixedTail q₁ q₂ s c hq₂ hc⟩,
    ⟨trivial,positive_outer q₁ q₂ s c hq₂ hc⟩⟩

theorem positive_deadCodes (n p q₁ q₂ s w Q k : ℕ)
    (hn : 0 < n) (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hs : 4 ≤ s) (hw : 0 < w) (hQ : 0 < Q) :
    Positive (deadCodes n p q₁ q₂ s w Q k).1 ∧
      Positive (deadCodes n p q₁ q₂ s w Q k).2 := by
  induction k with
  | zero => exact ⟨positive_copies p .bit trivial,hp⟩
  | succ k ih =>
    exact ⟨positive_copies Q _ ⟨hw,positive_deadTagged q₁ q₂ s _ hq₂ ih.2⟩,
      ⟨hQ,positive_copies w _ (positive_rows n q₁ q₂ s _ hn hq₁ hs ih.1)⟩⟩

theorem positive_deadSampleCode (n p q₁ q₂ s w Q k m : ℕ)
    (hn : 0 < n) (hp : 0 < p) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hs : 4 ≤ s) (hw : 0 < w) (hQ : 0 < Q) :
    Positive (deadSampleCode n p q₁ q₂ s w Q k m) := by
  have h := positive_deadCodes n p q₁ q₂ s w Q k hn hp hq₁ hq₂ hs hw hQ
  exact ⟨positive_copies m _ h.1,positive_copies m _ h.2⟩

def clock (n p q₁ q₂ s w Q k m b N : ℕ) : ℕ :=
  V39DeadSampleJoin.clock n p s q₁ q₂ w Q k m m +
    RoundedCodeOutput.publishedCoefficient * (N+1) *
      (codeSize (deadSampleCode n p q₁ q₂ s w Q k m)+b+3)^2 + 1

section Exact
variable (n p q₁ q₂ s w Q : ℕ)
variable [NeZero n] [NeZero p] [NeZero q₁] [NeZero q₂]
  [NeZero s] [NeZero (4*s)] [NeZero (s-3)] [NeZero w] [NeZero Q]

def sampledWord (hs : 4 ≤ s) (hq₁ : q₁ = s-2) (k m : ℕ)
    (bits : RoundedDraw.BitBlocks
      (publicBits (publicA n s q₂ w Q p) (sampleDrawBudget p q₁ q₂ s w Q k m))
      (sampleDrawBudget p q₁ q₂ s w Q k m)) : List Bool :=
  sampleWord n p q₁ q₂ s w Q k m (roundedLabels n p q₁ q₂ s w Q hs hq₁ k m bits)

def final (hs : 4 ≤ s) (hq₁ : q₁ = s-2) (k m : ℕ)
    (bits : RoundedDraw.BitBlocks
      (publicBits (publicA n s q₂ w Q p) (sampleDrawBudget p q₁ q₂ s w Q k m))
      (sampleDrawBudget p q₁ q₂ s w Q k m)) (suffix : List Bool) : Stack → List Bool :=
  let b := publicBits (publicA n s q₂ w Q p) (sampleDrawBudget p q₁ q₂ s w Q k m)
  RoundedCodeOutput.sharedFinal source (V39CurrentCodeConstructor.finalBank n p q₁ q₂ s w Q k m)
    (sampledWord n p q₁ q₂ s w Q hs hq₁ k m bits)
    ((RoundedCodeLoop.execute b _ (Paper2.GeneratorCode.initial (deadSampleCode n p q₁ q₂ s w Q k m)) bits).2 ++ suffix) b

/-- One fixed controller constructs and executes the exact current sampler.
Its output bank and unused random tape are identified in full on every tape. -/
theorem physical_sample (hs : 4 ≤ s) (hq₁ : q₁ = s-2) (k m : ℕ)
    (bits : RoundedDraw.BitBlocks
      (publicBits (publicA n s q₂ w Q p) (sampleDrawBudget p q₁ q₂ s w Q k m))
      (sampleDrawBudget p q₁ q₂ s w Q k m)) (suffix : List Bool) :
    let N := sampleDrawBudget p q₁ q₂ s w Q k m
    let b := publicBits (publicA n s q₂ w Q p) N
    ∃ t ≤ clock n p q₁ q₂ s w Q k m b N,
      ((advance program)^[t])
        (⟨some start,control,initial n p q₁ q₂ s w Q k m (RoundedCodeLoop.tapeWord b N bits ++ suffix) b⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none,control,final n p q₁ q₂ s w Q hs hq₁ k m bits suffix⟩ := by
  intro N b
  let tape := RoundedCodeLoop.tapeWord b N bits ++ suffix
  obtain ⟨ta,hta,hra⟩ := physical_construct n p q₁ q₂ s w Q k m (by omega) tape b
  have hc := positive_deadSampleCode n p q₁ q₂ s w Q k m
    (NeZero.pos n) (NeZero.pos p) (NeZero.pos q₁) (NeZero.pos q₂) hs (NeZero.pos w) (NeZero.pos Q)
  obtain ⟨tb,htb,hrb⟩ := RoundedCodeOutput.physical_shared_codec source
    (V39CurrentCodeConstructor.finalBank n p q₁ q₂ s w Q k m)
    (deadSampleCode n p q₁ q₂ s w Q k m) hc
    (V39CurrentCodeConstructor.final_output n p q₁ q₂ s w Q k m)
    (sampleProgram n p q₁ q₂ s w Q k m) (sampleWord n p q₁ q₂ s w Q k m)
    (deadSampleCode_exact n p q₁ q₂ s w Q k m) b N
    (alphabet_sampleProgram_le n p q₁ q₂ s w Q hs hq₁ k m)
    (draws_sampleProgram_le n p q₁ q₂ s w Q k m) bits suffix
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs constructorProgram interpreterProgram
    V39CurrentCodeConstructor.start interpreterStart V39CurrentCodeConstructor.control
    V39CurrentCodeConstructor.control RoundedCodeOutput.initial RoundedCodeOutput.initial
    _ _ _ ta tb hra hrb
  refine ⟨t,?_,hr⟩
  unfold clock
  omega

theorem final_output (hs : 4 ≤ s) (hq₁ : q₁ = s-2) (k m : ℕ)
    (bits : RoundedDraw.BitBlocks
      (publicBits (publicA n s q₂ w Q p) (sampleDrawBudget p q₁ q₂ s w Q k m))
      (sampleDrawBudget p q₁ q₂ s w Q k m)) (suffix : List Bool) :
    final n p q₁ q₂ s w Q hs hq₁ k m bits suffix (.inl source) =
      sampledWord n p q₁ q₂ s w Q hs hq₁ k m bits := by
  simp [final,RoundedCodeOutput.sharedFinal]

/-- Every event on the literal word physically produced by this same program
has the current complete-label law, up to the fixed 1/200 rounding budget. -/
theorem output_event_error_200 (hs : 4 ≤ s) (hq₁ : q₁ = s-2) (k m : ℕ)
    (suffix : List Bool) (E : List Bool → Prop) :
    |(RoundedDraw.bitBlocksLaw
      (publicBits (publicA n s q₂ w Q p) (sampleDrawBudget p q₁ q₂ s w Q k m))
      (sampleDrawBudget p q₁ q₂ s w Q k m)).prob
      (fun bits => E (final n p q₁ q₂ s w Q hs hq₁ k m bits suffix (.inl source))) -
      (sampleLaw n p q₁ q₂ s w Q k m).toFiniteLaw.prob
        (fun z => E (sampleWord n p q₁ q₂ s w Q k m z))| ≤ (1:ℝ)/200 := by
  simp_rw [final_output]
  exact rounded_map_event_error_200 n p q₁ q₂ s w Q hs hq₁ k m
    (sampleWord n p q₁ q₂ s w Q k m) E

end Exact

#print axioms physical_construct
#print axioms positive_deadSampleCode
#print axioms physical_sample
#print axioms output_event_error_200

end
end CurrentAdditive.V39PhysicalSample
