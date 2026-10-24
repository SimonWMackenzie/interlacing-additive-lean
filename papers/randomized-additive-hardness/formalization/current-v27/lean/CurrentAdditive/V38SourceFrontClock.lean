import CurrentAdditive.V38SourceFront

namespace CurrentAdditive.V38SourceFront

open Paper2.YaoSourceCodec Paper2.YaoLookup Paper2.YaoMachine
open Paper2.YaoClockPoly
open EthInapproximability.CurrentPaper
open CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude

theorem degree_clock_poly (t : ℕ) (ht : 1 ≤ t) :
    PolyIn (fun x : YaoSource t => V38SourceDegree.clock x) := by
  have hs := sourceClock_poly t ht
  unfold V38SourceDegree.clock V38DegreePhysical.clock MatrixAddressMachine.exactTime
  repeat' poly_step

theorem widths_clock_poly (t : ℕ) :
    PolyIn (fun x : YaoSource t => V38SourceWidths.clock x) := by
  unfold V38SourceWidths.clock MatrixAddressMachine.exactTime
  repeat' poly_step

theorem clock_poly (t : ℕ) (ht : 1 ≤ t) :
    PolyIn (fun x : YaoSource t => clock x) := by
  have hd := degree_clock_poly t ht
  have hw := widths_clock_poly t
  unfold clock
  repeat' poly_step

#print axioms degree_clock_poly
#print axioms widths_clock_poly
#print axioms clock_poly
end CurrentAdditive.V38SourceFront
