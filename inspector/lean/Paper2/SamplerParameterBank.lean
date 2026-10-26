import Paper2.CopyList
import Paper2.SamplerNRProducer
import Paper2.CodeFallbackEntryJoin

/-! Bank layout for the joined public-parameter producer. The ambient bank is
the admitted consumer bank `CodeFallbackEntryJoin.Stack` beside a private
producer region. This module fixes the raw-count and B/R cells of the
consumer bank and proves that `CodeFallbackEntryJoin.initial ... tape B R`
differs from the no-preloaded bank `... tape 0 0` exactly at the two cells
`CodeHeaderDraw.d 11` (B) and `CodeHeaderDraw.d 12` (R). -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Paper2.SamplerParameterBank

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

abbrev ConsumerStack := CodeFallbackEntryJoin.Stack
abbrev Private := SamplerBitWidthMachine.Stack ⊕ (SamplerNRProducer.Stack ⊕ Fin 1)
abbrev Stack := ConsumerStack ⊕ Private

def bwSlots : SamplerBitWidthMachine.Stack ↪ Stack :=
  ⟨fun k => .inr (.inl k), by intro a b h; cases h; rfl⟩
def nrSlots : SamplerNRProducer.Stack ↪ Stack :=
  ⟨fun k => .inr (.inr (.inl k)), by intro a b h; cases h; rfl⟩
def scr : Stack := .inr (.inr (.inr 0))

/-- Consumer cells: raw compiler counts, the two dimension counts, and the
draw-loader cells (`d 0` tape, `d 11` B, `d 12` R). -/
def compilerCell (i : Fin 65) : ConsumerStack := .inl (.inl (.inl i))
def countXCell : ConsumerStack := .inl (.inl (.inr (.inr 0)))
def countYCell : ConsumerStack := .inl (.inl (.inr (.inr 1)))
def drawCell (i : Fin 16) : ConsumerStack :=
  .inl (.inr (.inl (CodeHeaderDraw.d i)))

abbrev initial (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool) (B R : Nat) :=
  CodeFallbackEntryJoin.initial n p s q₁ q₂ w Q k mX mY tape B R

theorem initial_sample (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool)
    (B R : Nat) (y : CodeGeneratorSampleJoin.Stack) :
    initial n p s q₁ q₂ w Q k mX mY tape B R (.inl (.inl y)) =
      CodeGeneratorSampleJoin.initial n p s q₁ q₂ w Q k mX mY y := by
  show bank CodeSampleInterpreterLoader.sampleSlots
      (CodeSampleInterpreterLoader.foreign tape B R)
      (CodeGeneratorSampleJoin.initial n p s q₁ q₂ w Q k mX mY)
      (CodeSampleInterpreterLoader.sampleSlots y) = _
  exact bank_at _ _ _ y

theorem initial_consumer (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool)
    (B R : Nat) (z : CodeSampleInterpreterLoader.ConsumerStack ⊕ Fin 1) :
    initial n p s q₁ q₂ w Q k mX mY tape B R (.inl (.inr z)) =
      CodeSampleInterpreterLoader.foreign tape B R (.inr z) := by
  show bank CodeSampleInterpreterLoader.sampleSlots
      (CodeSampleInterpreterLoader.foreign tape B R)
      (CodeGeneratorSampleJoin.initial n p s q₁ q₂ w Q k mX mY) (.inr z) = _
  exact bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk)

theorem initial_writer (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool)
    (B R : Nat) (x : CodeFallbackDimensionLoader.WriterStack) :
    initial n p s q₁ q₂ w Q k mX mY tape B R (.inr x) = [] := rfl

theorem initial_compiler (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool)
    (B R : Nat) (i : Fin 65) :
    initial n p s q₁ q₂ w Q k mX mY tape B R (compilerCell i) =
      CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p (List.replicate k true) i := by
  rw [compilerCell, initial_sample]
  show bank CodeGeneratorSampleTransfer.compilerSlots
      (CodeGeneratorSampleTransfer.foreign mX mY)
      (CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p (List.replicate k true))
      (CodeGeneratorSampleTransfer.compilerSlots i) = _
  exact bank_at _ _ _ i

theorem initial_countX (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool)
    (B R : Nat) :
    initial n p s q₁ q₂ w Q k mX mY tape B R countXCell = List.replicate mX true := by
  rw [countXCell, initial_sample]
  show bank CodeGeneratorSampleTransfer.compilerSlots
      (CodeGeneratorSampleTransfer.foreign mX mY)
      (CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p (List.replicate k true))
      (.inr (.inr 0)) = _
  rw [bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk)]
  rfl

theorem initial_countY (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool)
    (B R : Nat) :
    initial n p s q₁ q₂ w Q k mX mY tape B R countYCell = List.replicate mY true := by
  rw [countYCell, initial_sample]
  show bank CodeGeneratorSampleTransfer.compilerSlots
      (CodeGeneratorSampleTransfer.foreign mX mY)
      (CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p (List.replicate k true))
      (.inr (.inr 1)) = _
  rw [bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk)]
  rfl

theorem initial_draw (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool)
    (B R : Nat) (i : Fin 16) :
    initial n p s q₁ q₂ w Q k mX mY tape B R (drawCell i) =
      DrawParameterLoader.initialBank tape 0 B R (.inl i) := by
  rw [drawCell, initial_consumer]
  rfl

theorem publicBase_q1 (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p fuel 16 =
      List.replicate q₁ true := by
  simp [CodeRecursiveSeedPrep.publicBase]
theorem publicBase_q2 (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p fuel 12 =
      List.replicate q₂ true := by
  simp [CodeRecursiveSeedPrep.publicBase]
theorem publicBase_s (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p fuel 17 =
      List.replicate s true := by
  simp [CodeRecursiveSeedPrep.publicBase]
theorem publicBase_n (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p fuel 18 =
      List.replicate n true := by
  simp [CodeRecursiveSeedPrep.publicBase]
theorem publicBase_w (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p fuel 31 =
      List.replicate w true := by
  simp [CodeRecursiveSeedPrep.publicBase]
theorem publicBase_Q (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p fuel 32 =
      List.replicate Q true := by
  simp [CodeRecursiveSeedPrep.publicBase]
theorem publicBase_p (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p fuel 63 =
      List.replicate p true := by
  simp [CodeRecursiveSeedPrep.publicBase]
theorem publicBase_k (n s q₁ q₂ w Q p : Nat) (fuel : List Bool) :
    CodeRecursiveSeedPrep.publicBase n s q₁ q₂ w Q p fuel 64 = fuel := by
  simp [CodeRecursiveSeedPrep.publicBase]

/-- The two consumer cells that receive B and R. -/
def cellB : ConsumerStack := drawCell 11
def cellR : ConsumerStack := drawCell 12

theorem drawBank_BR (tape : List Bool) (B R : Nat) :
    DrawParameterLoader.initialBank tape 0 B R =
      Function.update (Function.update (DrawParameterLoader.initialBank tape 0 0 0)
        (.inl 11) (List.replicate B true)) (.inl 12) (List.replicate R true) := by
  funext e
  rcases e with i | l
  · fin_cases i <;> simp [DrawParameterLoader.initialBank, DrawParameterLoader.mainBank]
  · simp [DrawParameterLoader.initialBank, DrawParameterLoader.mainBank]

/-- The admitted consumer bank with actual B,R is the no-preloaded bank with
exactly the two unary words written at `d 11` and `d 12`. -/
theorem initial_BR (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool) (B R : Nat) :
    initial n p s q₁ q₂ w Q k mX mY tape B R =
      Function.update (Function.update (initial n p s q₁ q₂ w Q k mX mY tape 0 0)
        cellB (List.replicate B true)) cellR (List.replicate R true) := by
  funext j
  rcases j with (y | z) | x
  · have h1 : (.inl (.inl y) : ConsumerStack) ≠ cellR := by
      simp [cellR, drawCell]
    have h2 : (.inl (.inl y) : ConsumerStack) ≠ cellB := by
      simp [cellB, drawCell]
    rw [Function.update_of_ne h1, Function.update_of_ne h2, initial_sample,
      initial_sample]
  · rcases z with c | f
    · rcases c with (i | l) | c
      · by_cases hB : i = 11
        · subst hB
          have hne : (.inl (.inr (.inl (.inl (.inl 11)))) : ConsumerStack) ≠ cellR := by
            simp [cellR, drawCell, CodeHeaderDraw.d]
          rw [Function.update_of_ne hne]
          show initial n p s q₁ q₂ w Q k mX mY tape B R cellB =
            Function.update (initial n p s q₁ q₂ w Q k mX mY tape 0 0) cellB
              (List.replicate B true) cellB
          rw [Function.update_self, cellB, initial_draw]
          simp [DrawParameterLoader.initialBank, DrawParameterLoader.mainBank]
        · by_cases hR : i = 12
          · subst hR
            show initial n p s q₁ q₂ w Q k mX mY tape B R cellR =
              Function.update (Function.update (initial n p s q₁ q₂ w Q k mX mY tape 0 0)
                cellB (List.replicate B true)) cellR (List.replicate R true) cellR
            rw [Function.update_self, cellR, initial_draw]
            simp [DrawParameterLoader.initialBank, DrawParameterLoader.mainBank]
          · have h1 : (.inl (.inr (.inl (.inl (.inl i)))) : ConsumerStack) ≠ cellR := by
              intro h
              apply hR
              simp only [cellR, drawCell, CodeHeaderDraw.d, Sum.inl.injEq,
                Sum.inr.injEq] at h
              exact h
            have h2 : (.inl (.inr (.inl (.inl (.inl i)))) : ConsumerStack) ≠ cellB := by
              intro h
              apply hB
              simp only [cellB, drawCell, CodeHeaderDraw.d, Sum.inl.injEq,
                Sum.inr.injEq] at h
              exact h
            rw [Function.update_of_ne h1, Function.update_of_ne h2]
            change initial n p s q₁ q₂ w Q k mX mY tape B R (drawCell i) =
              initial n p s q₁ q₂ w Q k mX mY tape 0 0 (drawCell i)
            rw [initial_draw, initial_draw, drawBank_BR,
              Function.update_of_ne (by simpa using hR),
              Function.update_of_ne (by simpa using hB)]
      · have h1 : (.inl (.inr (.inl (.inl (.inr l)))) : ConsumerStack) ≠ cellR := by
          simp [cellR, drawCell, CodeHeaderDraw.d]
        have h2 : (.inl (.inr (.inl (.inl (.inr l)))) : ConsumerStack) ≠ cellB := by
          simp [cellB, drawCell, CodeHeaderDraw.d]
        rw [Function.update_of_ne h1, Function.update_of_ne h2,
          initial_consumer, initial_consumer]
        rfl
      · have h1 : (.inl (.inr (.inl (.inr c))) : ConsumerStack) ≠ cellR := by
          simp [cellR, drawCell, CodeHeaderDraw.d]
        have h2 : (.inl (.inr (.inl (.inr c))) : ConsumerStack) ≠ cellB := by
          simp [cellB, drawCell, CodeHeaderDraw.d]
        rw [Function.update_of_ne h1, Function.update_of_ne h2,
          initial_consumer, initial_consumer]
        rfl
    · have h1 : (.inl (.inr (.inr f)) : ConsumerStack) ≠ cellR := by
        simp [cellR, drawCell]
      have h2 : (.inl (.inr (.inr f)) : ConsumerStack) ≠ cellB := by
        simp [cellB, drawCell]
      rw [Function.update_of_ne h1, Function.update_of_ne h2,
        initial_consumer, initial_consumer]
      rfl
  · have h1 : (.inr x : ConsumerStack) ≠ cellR := by simp [cellR, drawCell]
    have h2 : (.inr x : ConsumerStack) ≠ cellB := by simp [cellB, drawCell]
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
    rfl

theorem initial_cellB_zero (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool) :
    initial n p s q₁ q₂ w Q k mX mY tape 0 0 cellB = [] := by
  rw [cellB, initial_draw]
  simp [DrawParameterLoader.initialBank, DrawParameterLoader.mainBank]

theorem initial_cellR_zero (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool) :
    initial n p s q₁ q₂ w Q k mX mY tape 0 0 cellR = [] := by
  rw [cellR, initial_draw]
  simp [DrawParameterLoader.initialBank, DrawParameterLoader.mainBank]

theorem initial_tape (n p s q₁ q₂ w Q k mX mY : Nat) (tape : List Bool) (B R : Nat) :
    initial n p s q₁ q₂ w Q k mX mY tape B R (drawCell 0) = tape := by
  rw [initial_draw]
  simp [DrawParameterLoader.initialBank, DrawParameterLoader.mainBank]

end

#print axioms initial_BR
#print axioms initial_compiler
#print axioms initial_tape

end Paper2.SamplerParameterBank
