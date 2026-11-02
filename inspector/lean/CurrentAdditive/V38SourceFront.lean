import CurrentAdditive.V38SourceWidths

noncomputable section
namespace CurrentAdditive.V38SourceFront

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
open CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

def degreeControl (t : ℕ) :=
  ((initialControl t, ((none : Option Bool), ((none : Option Bool), (none : Option Bool)))),
    ((), ((), false)))
def widthsControl :=
  ((((none : Option Bool), (none : Option Bool)),
    ((none : Option Bool), ((), false))), false)

def program (t : ℕ) := BitMachineRawSequence.program
  (V38SourceDegree.program t) (V38SourceWidths.program t)
  (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
  (degreeControl t) widthsControl

def clock {t : ℕ} (x : YaoSource t) : ℕ :=
  V38SourceDegree.clock x + V38SourceWidths.clock x + 1

theorem run (t : ℕ) (ht : 1 ≤ t) (x : YaoSource t) :
    ∃ steps ≤ clock x,
      ((advance (program t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel Paper2.YaoHeaderParser.startLabel)))),
          (degreeControl t, widthsControl),
          bank (sourceEmbed t 16) (blank t 16) (initBank 0 x [])⟩ :
            TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
        ⟨none, (degreeControl t, widthsControl), V38SourceWidths.outputBank x⟩ := by
  obtain ⟨s,hs,hr⟩ := V38SourceDegree.source_run t ht x
  obtain ⟨u,hu,hw⟩ := V38SourceWidths.widths_run t x
  obtain ⟨v,hv,hc⟩ := BitMachineRawSequence.runs
    (V38SourceDegree.program t) (V38SourceWidths.program t)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel Paper2.YaoHeaderParser.startLabel)))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
    (degreeControl t) (degreeControl t) widthsControl widthsControl
    (bank (sourceEmbed t 16) (blank t 16) (initBank 0 x []))
    (V38SourceDegree.outputBank x) (V38SourceWidths.outputBank x) s u
    (by simpa [degreeControl] using hr) (by simpa [widthsControl] using hw)
  exact ⟨v, by unfold clock; omega, by simpa [program] using hc⟩

#print axioms run
end CurrentAdditive.V38SourceFront
