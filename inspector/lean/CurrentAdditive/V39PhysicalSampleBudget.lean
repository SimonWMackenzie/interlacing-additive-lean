import CurrentAdditive.V39PhysicalSample
import CurrentAdditive.V39FullSampleResources
import CurrentAdditive.RoundedCodeTape

/-! The same fixed sampler accepts any public draw reservation covering its
actual requests. The alphabet used for the block length is the literal
manuscript maximum. Larger draw caps alter only the reserved fair-bit tape. -/

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
open Paper2.GeneratorPositive Paper2.RecursiveSamplingProgram Paper2.RecursiveSamplingLaws
open V39DeadTaggedCompiler V39GeneratorCode V39RecursiveGenerator V38OneStep

variable (n p q₁ q₂ s w Q : ℕ)
variable [NeZero n] [NeZero p] [NeZero q₁] [NeZero q₂]
  [NeZero s] [NeZero (4*s)] [NeZero (s-3)] [NeZero w] [NeZero Q]

def blockLength (N : ℕ) : ℕ := publicBits (publicA n s q₂ w Q p) N

def sampleAtBudget (hs : 4 ≤ s) (hq₁ : q₁ = s-2) (k m N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (bits : RoundedDraw.BitBlocks (blockLength n p q₂ s w Q N) N) :=
  RoundedProgram.runProgram _ _
    ⟨sampleProgram n p q₁ q₂ s w Q k m,
      alphabet_sampleProgram_le n p q₁ q₂ s w Q hs hq₁ k m⟩
    ((draws_sampleProgram_le n p q₁ q₂ s w Q k m).trans hN) bits

def finalAtBudget (hs : 4 ≤ s) (hq₁ : q₁ = s-2) (k m N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (bits : RoundedDraw.BitBlocks (blockLength n p q₂ s w Q N) N)
    (suffix : List Bool) : Stack → List Bool :=
  let b := blockLength n p q₂ s w Q N
  RoundedCodeOutput.sharedFinal source (V39CurrentCodeConstructor.finalBank n p q₁ q₂ s w Q k m)
    (sampleWord n p q₁ q₂ s w Q k m (sampleAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits))
    ((RoundedCodeLoop.execute b N (Paper2.GeneratorCode.initial (deadSampleCode n p q₁ q₂ s w Q k m)) bits).2 ++ suffix) b

theorem physical_sample_at_budget (hs : 4 ≤ s) (hq₁ : q₁ = s-2) (k m N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (bits : RoundedDraw.BitBlocks (blockLength n p q₂ s w Q N) N)
    (suffix : List Bool) :
    let b := blockLength n p q₂ s w Q N
    ∃ t ≤ clock n p q₁ q₂ s w Q k m b N,
      ((advance program)^[t])
        (⟨some start,control,initial n p q₁ q₂ s w Q k m (RoundedCodeLoop.tapeWord b N bits ++ suffix) b⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
        ⟨none,control,finalAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits suffix⟩ := by
  intro b
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
    ((draws_sampleProgram_le n p q₁ q₂ s w Q k m).trans hN) bits suffix
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs constructorProgram interpreterProgram
    V39CurrentCodeConstructor.start interpreterStart V39CurrentCodeConstructor.control
    V39CurrentCodeConstructor.control RoundedCodeOutput.initial RoundedCodeOutput.initial
    _ _ _ ta tb hra hrb
  refine ⟨t,?_,hr⟩
  unfold clock
  omega

theorem finalAtBudget_output (hs : 4 ≤ s) (hq₁ : q₁ = s-2) (k m N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (bits : RoundedDraw.BitBlocks (blockLength n p q₂ s w Q N) N)
    (suffix : List Bool) :
    finalAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits suffix (.inl source) =
      sampleWord n p q₁ q₂ s w Q k m (sampleAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits) := by
  simp [finalAtBudget,RoundedCodeOutput.sharedFinal]

theorem budget_labels_event_error_200 (hs : 4 ≤ s) (hq₁ : q₁ = s-2) (k m N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (E : ((Fin m → Row n p q₁ q₂ s w Q k) × (Fin m → Column n p q₁ q₂ s w Q k)) → Prop) :
    |(RoundedDraw.bitBlocksLaw (blockLength n p q₂ s w Q N) N).prob
      (fun bits => E (sampleAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits)) -
      (sampleLaw n p q₁ q₂ s w Q k m).toFiniteLaw.prob E| ≤ (1:ℝ)/200 := by
  have h := RoundedProgram.runProgram_event_error_200
    (blockLength n p q₂ s w Q N) N
    ⟨sampleProgram n p q₁ q₂ s w Q k m,
      alphabet_sampleProgram_le n p q₁ q₂ s w Q hs hq₁ k m⟩
    ((draws_sampleProgram_le n p q₁ q₂ s w Q k m).trans hN)
    (publicBits_budget _ _) {z | E z}
  rw [generates_eventProb (generates_sampleProgram n p q₁ q₂ s w Q k m)] at h
  exact h

theorem budget_output_event_error_200 (hs : 4 ≤ s) (hq₁ : q₁ = s-2) (k m N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (suffix : List Bool) (E : List Bool → Prop) :
    |(RoundedDraw.bitBlocksLaw (blockLength n p q₂ s w Q N) N).prob
      (fun bits => E (finalAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits suffix (.inl source))) -
      (sampleLaw n p q₁ q₂ s w Q k m).toFiniteLaw.prob
        (fun z => E (sampleWord n p q₁ q₂ s w Q k m z))| ≤ (1:ℝ)/200 := by
  simp_rw [finalAtBudget_output]
  have h := RoundedCodeOutput.encoded_event_error_200
    (sampleProgram n p q₁ q₂ s w Q k m) (sampleWord n p q₁ q₂ s w Q k m)
    (blockLength n p q₂ s w Q N) N
    (alphabet_sampleProgram_le n p q₁ q₂ s w Q hs hq₁ k m)
    ((draws_sampleProgram_le n p q₁ q₂ s w Q k m).trans hN)
    (publicBits_budget _ _) {z | E z}
  rw [generates_eventProb (generates_sampleProgram n p q₁ q₂ s w Q k m)] at h
  exact h

theorem sampleWord_parser_layout (k m : ℕ)
    (z : (Fin m → Row n p q₁ q₂ s w Q k) × (Fin m → Column n p q₁ q₂ s w Q k)) :
    sampleWord n p q₁ q₂ s w Q k m z =
      tupleWord (V39PhysicalSelect.rowWord k) m z.1 ++
        tupleWord (V39PhysicalSelect.columnWord k) m z.2 := by
  have h := V39GeneratorEncodingBridge.words_match n p q₁ q₂ s w Q k
  have hr : (words n p q₁ q₂ s w Q k).1 = V39PhysicalSelect.rowWord k := funext h.1
  have hc : (words n p q₁ q₂ s w Q k).2 = V39PhysicalSelect.columnWord k := funext h.2
  simp only [sampleWord,hr,hc]

/-- Every indexed position is present in the physical word, even when label
values coincide, and all coordinates use the actual selector parser codec. -/
theorem budget_output_parser_layout (hs : 4 ≤ s) (hq₁ : q₁ = s-2) (k m N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (bits : RoundedDraw.BitBlocks (blockLength n p q₂ s w Q N) N)
    (suffix : List Bool) :
    let z := sampleAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits
    finalAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits suffix (.inl source) =
      tupleWord (V39PhysicalSelect.rowWord k) m z.1 ++
        tupleWord (V39PhysicalSelect.columnWord k) m z.2 := by
  rw [finalAtBudget_output,sampleWord_parser_layout]

theorem finalAtBudget_constructor_retained (hs : 4 ≤ s) (hq₁ : q₁ = s-2) (k m N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (bits : RoundedDraw.BitBlocks (blockLength n p q₂ s w Q N) N)
    (suffix : List Bool) (j : ConstructorStack) (hj : j ≠ source) :
    finalAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits suffix (.inl j) =
      V39CurrentCodeConstructor.finalBank n p q₁ q₂ s w Q k m j := by
  simp [finalAtBudget,RoundedCodeOutput.sharedFinal,hj]

/-- The complete fixed sampler can be placed beside a retained raw graph
or any other caller data. Its literal final bank includes those foreign cells. -/
theorem physical_sample_from_bank {K : Type*} [DecidableEq K]
    (ι : Stack ↪ K) (S : K → List Bool)
    (hs : 4 ≤ s) (hq₁ : q₁ = s-2) (k m N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (bits : RoundedDraw.BitBlocks (blockLength n p q₂ s w Q N) N)
    (suffix : List Bool)
    (hS : ∀ j, S (ι j) = initial n p q₁ q₂ s w Q k m
      (RoundedCodeLoop.tapeWord (blockLength n p q₂ s w Q N) N bits ++ suffix)
      (blockLength n p q₂ s w Q N) j) :
    ∃ t ≤ clock n p q₁ q₂ s w Q k m (blockLength n p q₂ s w Q N) N,
      ((advance (fun l => stackStmt ι (program l)))^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : K => Bool) Label Control) =
        ⟨none,control,bank ι S (finalAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits suffix)⟩ := by
  obtain ⟨t,ht,hr⟩ := physical_sample_at_budget n p q₁ q₂ s w Q hs hq₁ k m N hN bits suffix
  have he := BitMachineStackRun.run ι S program
    (⟨some start,control,initial n p q₁ q₂ s w Q k m
      (RoundedCodeLoop.tapeWord (blockLength n p q₂ s w Q N) N bits ++ suffix)
      (blockLength n p q₂ s w Q N)⟩ : TM2.Cfg (fun _ : Stack => Bool) Label Control) t
  rw [hr] at he
  have hi := bank_eq_self ι S _ (fun j => (hS j).symm)
  exact ⟨t,ht,by simpa only [stackCfg,hi] using he⟩

theorem sampler_foreign_retained {K : Type*} [DecidableEq K]
    (ι : Stack ↪ K) (S : K → List Bool)
    (hs : 4 ≤ s) (hq₁ : q₁ = s-2) (k m N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (bits : RoundedDraw.BitBlocks (blockLength n p q₂ s w Q N) N)
    (suffix : List Bool) (j : K) (hj : ¬ ∃ i, ι i = j) :
    bank ι S (finalAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits suffix) j = S j :=
  bank_outside ι S _ j hj

#print axioms physical_sample_at_budget
#print axioms budget_output_event_error_200
#print axioms budget_labels_event_error_200
#print axioms budget_output_parser_layout
#print axioms physical_sample_from_bank

end
end CurrentAdditive.V39PhysicalSample
