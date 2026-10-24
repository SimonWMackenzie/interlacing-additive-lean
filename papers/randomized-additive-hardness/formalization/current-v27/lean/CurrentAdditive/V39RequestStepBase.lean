import CurrentAdditive.V39EdgeSourceDispatch
import Paper2.TemplateStepX

/-! The new one-level physical request program. Navigation, selection, the
template arm, embeddings and two charged output copies are generic admitted
primitives. The source arm is the actual current edge-only two-family one.
This module defines the fixed program; branch runs are proved separately. -/

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace CurrentAdditive.V39RequestStep
noncomputable section

open Paper2
open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource
open RecursiveLabelCodecScratch RecursiveEntries
open BitMachineRawSequence (leftLabel)
open Paper2.TemplateStep (J srcCell armStart armCtl)
open Paper2.TemplateStepX (JT inJ ιE cpC cpR cp1 cp2 preX armX)

def srcXT := fun l => stackStmt ιE (V39EdgeSourceDispatch.program l)
def srcP1 := BitMachineRawSequence.program srcXT cp1 BitMachineCopy.Label.scan
  V39EdgeSourceDispatch.control (none : Option Bool)
def srcP := BitMachineRawSequence.program srcP1 cp2 BitMachineCopy.Label.scan
  (V39EdgeSourceDispatch.control, (none : Option Bool)) (none : Option Bool)
def srcPStart := FetchIndexed.labelOf srcP (leftLabel (leftLabel (.inl ())))
def srcPCtl := ((V39EdgeSourceDispatch.control, (none : Option Bool)), (none : Option Bool))

def stepX := BitMachineRawSequence.program preX
  (TagDispatch.ifProgram (inJ srcCell) armX srcP armStart srcPStart armCtl srcPCtl) (.inl ())
  (NavJoin.ctl, RequestSelect.startControl) ((none : Option Bool), (armCtl, srcPCtl))
def stepXCtl := ((NavJoin.ctl, RequestSelect.startControl),
  ((none : Option Bool), (armCtl, srcPCtl)))

end
end CurrentAdditive.V39RequestStep
