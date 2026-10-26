import CurrentAdditive.CanonicalThreshold
import CurrentAdditive.CanonicalSourcePrelude
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! A common finite-stack namespace for the Yao renderer. All physical
components are placed into disjoint summands; explicit copy stages will move
their outputs into the canonical writer cells. The first source stage already
runs in this one ambient namespace, preserving all foreign cells. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude

inductive Cell (t N : ℕ) where
  | source (k : Paper2.YaoMachine.WStack t 0)
  | field (k : CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff.Stack)
  | fieldInit (k : Fin 5)
  | writer (k : MatrixTableWriter.Stack 60)
  | header (k : Paper2.HeaderA.HB)
  | degree (k : Fin N)
  | width (k : Fin 8)
  | selector (k : Fin 12)
  | square (k : Fin 9)
  | dimensions (k : Fin 11)
  | threshold (k : Fin 3)
  | copyScratch (k : Fin 3)
  deriving DecidableEq, Fintype

def sourceEmbed (t N : ℕ) : Paper2.YaoMachine.WStack t 0 ↪ Cell t N :=
  ⟨Cell.source, by intro a b h; cases h; rfl⟩
def fieldEmbed (t N : ℕ) :
    CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff.Stack ↪ Cell t N :=
  ⟨Cell.field, by intro a b h; cases h; rfl⟩
def fieldCombinedEmbed (t N : ℕ) :
    (Fin 5 ⊕ CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff.Stack) ↪ Cell t N :=
  ⟨Sum.elim Cell.fieldInit Cell.field, by
    intro a b h
    cases a <;> cases b <;> simp_all⟩
def writerEmbed (t N : ℕ) : MatrixTableWriter.Stack 60 ↪ Cell t N :=
  ⟨Cell.writer, by intro a b h; cases h; rfl⟩
def writerCellEmbed (t N : ℕ) : CanonicalCell ↪ Cell t N :=
  ⟨fun k => .writer (.inl k), by intro a b h; cases h; rfl⟩
def headerEmbed (t N : ℕ) : Paper2.HeaderA.HB ↪ Cell t N :=
  ⟨Cell.header, by intro a b h; cases h; rfl⟩
def degreeEmbed (t N : ℕ) : Fin N ↪ Cell t N :=
  ⟨Cell.degree, by intro a b h; cases h; rfl⟩
def widthEmbed (t N : ℕ) : Fin 8 ↪ Cell t N :=
  ⟨Cell.width, by intro a b h; cases h; rfl⟩
def selectorEmbed (t N : ℕ) : Fin 12 ↪ Cell t N :=
  ⟨Cell.selector, by intro a b h; cases h; rfl⟩
def squareEmbed (t N : ℕ) : Fin 9 ↪ Cell t N :=
  ⟨Cell.square, by intro a b h; cases h; rfl⟩
def dimensionsEmbed (t N : ℕ) : Fin 11 ↪ Cell t N :=
  ⟨Cell.dimensions, by intro a b h; cases h; rfl⟩
def thresholdEmbed (t N : ℕ) : Fin 3 ↪ Cell t N :=
  ⟨Cell.threshold, by intro a b h; cases h; rfl⟩

def blank (t N : ℕ) : Cell t N → List Bool := fun _ => []

def sourceStage (t N : ℕ) :=
  fun l => stackStmt (sourceEmbed t N) (CanonicalSourcePrelude.program t l)

theorem physical_ambient_source (t N : ℕ) (ht : 1 ≤ t)
    (x : Paper2.YaoSourceCodec.YaoSource t) :
    ∃ steps ≤ CanonicalSourcePrelude.sourceClock x, ∃ control,
      ((advance (sourceStage t N))^[steps])
        (stackCfg (sourceEmbed t N) (blank t N)
          (⟨some (BitMachineRawSequence.leftLabel
              Paper2.YaoHeaderParser.startLabel),
            CanonicalSourcePrelude.initialControl t,
            Paper2.YaoMachine.initBank 0 x []⟩ :
              TM2.Cfg (fun _ : Paper2.YaoMachine.WStack t 0 => Bool) _ _)) =
        stackCfg (sourceEmbed t N) (blank t N)
          ⟨none, control, CanonicalSourcePrelude.sourceReady x⟩ := by
  obtain ⟨steps, hsteps, control, hrun⟩ :=
    CanonicalSourcePrelude.physical_source_prelude t ht x
  refine ⟨steps, hsteps, control, ?_⟩
  rw [show (sourceStage t N) =
      (fun l => stackStmt (sourceEmbed t N) (CanonicalSourcePrelude.program t l)) from rfl,
    BitMachineStackRun.run]
  exact congrArg (stackCfg (sourceEmbed t N) (blank t N)) hrun

#print axioms physical_ambient_source

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
