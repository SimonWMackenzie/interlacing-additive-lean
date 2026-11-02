import CurrentAdditive.V39PhysicalSampleBudget
import Paper2.CopyAll
import Paper2.CodeGeneratorExponentPublic

/-! Auxiliary navigation syntax is physically constructed once from the same
public count words. It is disjoint from the current sampler's actual Code,
emitted sample words and random tape. Every copy and compiler run is charged. -/

set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384

namespace CurrentAdditive.V39PhysicalShapeSample
noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2 Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
open CurrentAdditive.V39RecursiveGenerator CurrentAdditive.V38OneStep

abbrev Stack := V39PhysicalSample.Stack ⊕ (CodeRecursiveLoop.Stack ⊕ Fin 1)
def sampleSlots : V39PhysicalSample.Stack ↪ Stack := Function.Embedding.inl
def shapeSlots : CodeRecursiveLoop.Stack ↪ Stack :=
  ⟨fun j => .inr (.inl j),by intro a b h; cases h; rfl⟩
def scratch : Stack := .inr (.inr 0)
def publicIndices : Fin 8 → Fin 65 := ![12,16,17,18,31,32,63,64]
theorem publicIndices_injective : Function.Injective publicIndices := by decide

def copySlots (i : Fin 8) : Fin 3 ↪ Stack :=
  ⟨![.inl (.inl (.inl (publicIndices i))),shapeSlots (publicIndices i),scratch],by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [shapeSlots,scratch]⟩

theorem copy_hsd : ∀ i j, copySlots i 0 ≠ copySlots j 1 := by
  intro i j; simp [copySlots,shapeSlots]
theorem copy_hzd : ∀ i j, copySlots i 2 ≠ copySlots j 1 := by
  intro i j; simp [copySlots,shapeSlots,scratch]
theorem copy_hdd : ∀ i j, copySlots i 1 = copySlots j 1 → i=j := by
  intro i j h
  apply publicIndices_injective
  simpa [copySlots,shapeSlots] using h

def copyProgram := CopyAll.prog copySlots
abbrev ShapeLabel := BitMachineRawSequence.Label CodeGeneratorComplete.SeedLabel CodeRecursiveLoop.Label
def shapeProgram (l : ShapeLabel) :=
  stackStmt shapeSlots (CodeGeneratorComplete.program l)
def sampleProgram (l : V39PhysicalSample.Label) :=
  stackStmt sampleSlots (V39PhysicalSample.program l)
def shapeStart : BitMachineRawSequence.Label CodeGeneratorComplete.SeedLabel CodeRecursiveLoop.Label :=
  BitMachineRawSequence.leftLabel CodeGeneratorComplete.seedStart
def shapeControl := (CodeGeneratorComplete.seedControl,CodeGeneratorComplete.loopControl)
def firstProgram := BitMachineRawSequence.program copyProgram shapeProgram shapeStart
  (none:Option Bool) shapeControl
def firstControl := ((none:Option Bool),shapeControl)
def program := BitMachineRawSequence.program firstProgram sampleProgram V39PhysicalSample.start
  firstControl V39PhysicalSample.control
abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label (CopyAll.Lab 8) ShapeLabel) V39PhysicalSample.Label
def start : Label := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel (.inl (0:Fin 9) : CopyAll.Lab 8))
def control := (firstControl,V39PhysicalSample.control)

def initial (n p q₁ q₂ s w Q k m : ℕ) (tape : List Bool) (b : ℕ) : Stack → List Bool :=
  Sum.elim (V39PhysicalSample.initial n p q₁ q₂ s w Q k m tape b) (fun _ => [])

def copied (n p q₁ q₂ s w Q k m : ℕ) (tape : List Bool) (b : ℕ) : Stack → List Bool :=
  bank shapeSlots (initial n p q₁ q₂ s w Q k m tape b)
    (CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p (List.replicate k true))

def shapeFinal (n p q₁ q₂ s w Q k : ℕ) : CodeRecursiveLoop.Stack → List Bool :=
  (CodeRecursiveLoop.finished n s q₁ q₂ w Q
    (seedRecursiveCodes n p s q₁ q₂ w Q k).1
    (seedRecursiveCodes n p s q₁ q₂ w Q k).2).stk

def prepared (n p q₁ q₂ s w Q k m : ℕ) (tape : List Bool) (b : ℕ) : Stack → List Bool :=
  bank shapeSlots (initial n p q₁ q₂ s w Q k m tape b) (shapeFinal n p q₁ q₂ s w Q k)

def publicLength (n p q₁ q₂ s w Q k : ℕ) : ℕ := n+p+q₁+q₂+s+w+Q+k
def copyClock (n p q₁ q₂ s w Q k : ℕ) : ℕ :=
  8*(2*publicLength n p q₁ q₂ s w Q k+3)+1

theorem shapeFinal_row (n p q₁ q₂ s w Q k : ℕ) :
    shapeFinal n p q₁ q₂ s w Q k 2 =
      encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q k).1 := by
  change bank CodeRecursiveLoop.embedRound (CodeRecursiveLoop.foreign [])
    (CodeRecursiveColumn.initial n s q₁ q₂ w Q
      (seedRecursiveCodes n p s q₁ q₂ w Q k).1
      (seedRecursiveCodes n p s q₁ q₂ w Q k).2)
    (CodeRecursiveLoop.embedRound 2) = _
  rw [bank_at]
  rw [CodeRecursiveInitialLayout.initial_core_at n s q₁ q₂ w Q _ _ 2 (by decide)]
  exact CodeRowsGraphCompiler.initial_child n s q₁ q₂ _

theorem shapeFinal_column (n p q₁ q₂ s w Q k : ℕ) :
    shapeFinal n p q₁ q₂ s w Q k 33 =
      encodeCode (seedRecursiveCodes n p s q₁ q₂ w Q k).2 := by
  change bank CodeRecursiveLoop.embedRound (CodeRecursiveLoop.foreign [])
    (CodeRecursiveColumn.initial n s q₁ q₂ w Q
      (seedRecursiveCodes n p s q₁ q₂ w Q k).1
      (seedRecursiveCodes n p s q₁ q₂ w Q k).2)
    (CodeRecursiveLoop.embedRound 33) = _
  rw [bank_at,CodeRecursiveColumn.initial,
    CodeRecursiveColumn.foreign_at w Q _ _ 33 (by decide)]
  simp [CodeRecursiveColumn.foreignWords]

theorem initial_public (n p q₁ q₂ s w Q k m : ℕ) (tape : List Bool) (b : ℕ)
    (j : Fin 65) :
    initial n p q₁ q₂ s w Q k m tape b (.inl (.inl (.inl j))) =
      CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p (List.replicate k true) j := by
  exact bank_at CodeGeneratorSampleTransfer.compilerSlots _ _ j

theorem copied_exact (n p q₁ q₂ s w Q k m : ℕ) (tape : List Bool) (b : ℕ) :
    CopyAll.done copySlots 8 (initial n p q₁ q₂ s w Q k m tape b) =
      copied n p q₁ q₂ s w Q k m tape b := by
  funext j
  rcases j with j | (j | j)
  · rw [CopyAll.done_off copySlots _ _ (by intro i; simp [copySlots,shapeSlots])]
    exact (bank_outside shapeSlots _ _ _ (by rintro ⟨i,h⟩; cases h)).symm
  · by_cases hj : ∃ i, publicIndices i=j
    · obtain ⟨i,rfl⟩ := hj
      change CopyAll.done copySlots 8 _ (copySlots i 1) = _
      rw [CopyAll.done_dst copySlots copy_hdd]
      change initial n p q₁ q₂ s w Q k m tape b (.inl (.inl (.inl (publicIndices i)))) ++ [] =
        bank shapeSlots _ _ (shapeSlots (publicIndices i))
      rw [initial_public,bank_at,List.append_nil]
    · rw [CopyAll.done_off copySlots _ _ (by
        intro i h
        apply hj
        exact ⟨i,by simpa [copySlots,shapeSlots] using h⟩)]
      change [] = bank shapeSlots _ _ (shapeSlots j)
      rw [bank_at]
      have h12 : j≠12 := by intro h; apply hj; exact ⟨0,h.symm⟩
      have h16 : j≠16 := by intro h; apply hj; exact ⟨1,h.symm⟩
      have h17 : j≠17 := by intro h; apply hj; exact ⟨2,h.symm⟩
      have h18 : j≠18 := by intro h; apply hj; exact ⟨3,h.symm⟩
      have h31 : j≠31 := by intro h; apply hj; exact ⟨4,h.symm⟩
      have h32 : j≠32 := by intro h; apply hj; exact ⟨5,h.symm⟩
      have h63 : j≠63 := by intro h; apply hj; exact ⟨6,h.symm⟩
      have h64 : j≠64 := by intro h; apply hj; exact ⟨7,h.symm⟩
      simp [CodeRecursiveSeedPrep.publicBase,h12,h16,h17,h18,h31,h32,h63,h64]
  · rw [CopyAll.done_off copySlots _ _ (by intro i; simp [copySlots,shapeSlots])]
    exact (bank_outside shapeSlots _ _ _ (by rintro ⟨i,h⟩; cases h)).symm

theorem physical_copy (n p q₁ q₂ s w Q k m : ℕ) (tape : List Bool) (b : ℕ) :
    ∃ t ≤ copyClock n p q₁ q₂ s w Q k, ∃ v,
      ((advance copyProgram)^[t])
        (⟨some (.inl (0:Fin 9)),(none:Option Bool),initial n p q₁ q₂ s w Q k m tape b⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,v,copied n p q₁ q₂ s w Q k m tape b⟩ := by
  obtain ⟨t,ht,v,hr⟩ := CopyAll.all_run copySlots copy_hsd copy_hzd copy_hdd
    (initial n p q₁ q₂ s w Q k m tape b) (by intro i; rfl)
    (publicLength n p q₁ q₂ s w Q k) (by
      intro i
      change (initial n p q₁ q₂ s w Q k m tape b (.inl (.inl (.inl (publicIndices i))))).length ≤ _
      rw [initial_public]
      fin_cases i <;> simp [publicIndices,CodeRecursiveSeedPrep.publicBase,publicLength] <;> omega)
    (none:Option Bool)
  exact ⟨t,ht,v,by simpa only [copied_exact] using hr⟩

theorem physical_shape (n p q₁ q₂ s w Q k m : ℕ) (hs : 3 ≤ s) (tape : List Bool) (b : ℕ) :
    ∃ t ≤ CodeGeneratorComplete.clock n p s q₁ q₂ w Q k,
      ((advance shapeProgram)^[t])
        (⟨some shapeStart,shapeControl,copied n p q₁ q₂ s w Q k m tape b⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,shapeControl,prepared n p q₁ q₂ s w Q k m tape b⟩ := by
  obtain ⟨t,ht,hr⟩ := CodeGeneratorComplete.run_seedRecursiveCodes n p s q₁ q₂ w Q k hs
  have he := BitMachineStackRun.run shapeSlots
    (initial n p q₁ q₂ s w Q k m tape b) CodeGeneratorComplete.program
    (⟨some shapeStart,shapeControl,
      CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p (List.replicate k true)⟩ :
      TM2.Cfg (fun _ : CodeRecursiveLoop.Stack => Bool) _ _) t
  simp only [shapeStart,shapeControl] at he
  rw [hr] at he
  exact ⟨t,ht,by simpa only [shapeProgram,stackCfg,prepared,copied,shapeFinal] using he⟩

theorem prepared_sample (n p q₁ q₂ s w Q k m : ℕ) (tape : List Bool) (b : ℕ)
    (j : V39PhysicalSample.Stack) :
    prepared n p q₁ q₂ s w Q k m tape b (sampleSlots j) =
      V39PhysicalSample.initial n p q₁ q₂ s w Q k m tape b j := by
  rw [prepared,bank_outside]
  · rfl
  · rintro ⟨i,h⟩; cases h

def clock (n p q₁ q₂ s w Q k m b N : ℕ) : ℕ :=
  copyClock n p q₁ q₂ s w Q k + CodeGeneratorComplete.clock n p s q₁ q₂ w Q k +
    V39PhysicalSample.clock n p q₁ q₂ s w Q k m b N + 2

variable (n p q₁ q₂ s w Q : ℕ)
variable [NeZero n] [NeZero p] [NeZero q₁] [NeZero q₂]
  [NeZero s] [NeZero (4*s)] [NeZero (s-3)] [NeZero w] [NeZero Q]

def final (hs : 4 ≤ s) (hq₁ : q₁=s-2) (k m N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.blockLength n p q₂ s w Q N) N)
    (suffix : List Bool) : Stack → List Bool :=
  let b := V39PhysicalSample.blockLength n p q₂ s w Q N
  let tape := RoundedCodeLoop.tapeWord b N bits ++ suffix
  bank sampleSlots (prepared n p q₁ q₂ s w Q k m tape b)
    (V39PhysicalSample.finalAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits suffix)

theorem physical_shape_and_sample (hs : 4 ≤ s) (hq₁ : q₁=s-2) (k m N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.blockLength n p q₂ s w Q N) N)
    (suffix : List Bool) :
    let b := V39PhysicalSample.blockLength n p q₂ s w Q N
    ∃ t ≤ clock n p q₁ q₂ s w Q k m b N,
      ((advance program)^[t])
        (⟨some start,control,initial n p q₁ q₂ s w Q k m
          (RoundedCodeLoop.tapeWord b N bits ++ suffix) b⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,control,final n p q₁ q₂ s w Q hs hq₁ k m N hN bits suffix⟩ := by
  intro b
  let tape := RoundedCodeLoop.tapeWord b N bits ++ suffix
  obtain ⟨ta,hta,va,hra⟩ := physical_copy n p q₁ q₂ s w Q k m tape b
  obtain ⟨tb,htb,hrb⟩ := physical_shape n p q₁ q₂ s w Q k m (by omega) tape b
  obtain ⟨tc,htc,hrc⟩ := V39PhysicalSample.physical_sample_from_bank n p q₁ q₂ s w Q
    sampleSlots (prepared n p q₁ q₂ s w Q k m tape b) hs hq₁ k m N hN bits suffix
    (prepared_sample n p q₁ q₂ s w Q k m tape b)
  obtain ⟨tab,htab,hrab⟩ := BitMachineRawSequence.runs copyProgram shapeProgram
    (.inl (0:Fin 9)) shapeStart (none:Option Bool) va shapeControl shapeControl
    _ _ _ ta tb hra hrb
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs firstProgram sampleProgram
    (BitMachineRawSequence.leftLabel (.inl (0:Fin 9))) V39PhysicalSample.start
    firstControl firstControl V39PhysicalSample.control V39PhysicalSample.control
    _ _ _ tab tc hrab hrc
  change tc ≤ V39PhysicalSample.clock n p q₁ q₂ s w Q k m b N at htc
  exact ⟨t,by unfold clock; omega,by simpa only [program,start,control,final] using hr⟩

theorem final_shape_retained (hs : 4 ≤ s) (hq₁ : q₁=s-2) (k m N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.blockLength n p q₂ s w Q N) N)
    (suffix : List Bool) (j : CodeRecursiveLoop.Stack) :
    final n p q₁ q₂ s w Q hs hq₁ k m N hN bits suffix (shapeSlots j) =
      shapeFinal n p q₁ q₂ s w Q k j := by
  rw [final,bank_outside]
  · exact bank_at shapeSlots _ _ j
  · rintro ⟨i,h⟩; cases h

theorem final_sample_output (hs : 4 ≤ s) (hq₁ : q₁=s-2) (k m N : ℕ)
    (hN : sampleDrawBudget p q₁ q₂ s w Q k m ≤ N)
    (bits : RoundedDraw.BitBlocks (V39PhysicalSample.blockLength n p q₂ s w Q N) N)
    (suffix : List Bool) :
    final n p q₁ q₂ s w Q hs hq₁ k m N hN bits suffix (sampleSlots (.inl V39PhysicalSample.source)) =
      V39GeneratorCode.sampleWord n p q₁ q₂ s w Q k m
        (V39PhysicalSample.sampleAtBudget n p q₁ q₂ s w Q hs hq₁ k m N hN bits) := by
  rw [final,bank_at,V39PhysicalSample.finalAtBudget_output]

#print axioms physical_copy
#print axioms physical_shape_and_sample
#print axioms final_shape_retained
#print axioms final_sample_output

end
end CurrentAdditive.V39PhysicalShapeSample
