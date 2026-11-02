import CurrentAdditive.V40SourceCell
import CurrentAdditive.V40SourceClockBounds

namespace CurrentAdditive.V40SourceCell
noncomputable section
open V40SourceClockBounds V40SourceLocal D22PacketPrimitives
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

theorem remainder_polynomial : HasPolynomialEnvelope remainderQuery := by
  simpa only [finiteRun,pow_one,remainderQuery] using
    finite_run_polynomial V40ActivityIndex.remainderMachine 17 1
theorem pair_polynomial : HasPolynomialEnvelope pair :=
  append_polynomial (scalar_polynomial (4:Fin 7) 6 2 V40ActivityIndex.shiftedTerm (by decide))
    (append_polynomial (constant_polynomial [false])
      (scalar_polynomial (4:Fin 7) 6 2 V40IndexedLawLoop.divisor (by decide)))
theorem value_polynomial : HasPolynomialEnvelope itemValue :=
  compose_polynomial pair_polynomial remainder_polynomial
theorem kind_polynomial : HasPolynomialEnvelope kind :=
  compose_polynomial (scalar_polynomial (4:Fin 7) 6 2 V40ActivityIndex.kindTerm (by decide))
    (physical_polynomial bitProducer)
theorem group_polynomial : HasPolynomialEnvelope group :=
  scalar_polynomial (4:Fin 7) 6 2 V40IndexedLawLoop.lower (by decide)
theorem prepare_polynomial : HasPolynomialEnvelope prepare := by
  apply serialise_polynomial
  intro k
  fin_cases k
  · exact project_polynomial _
  · exact project_polynomial _
  · exact project_polynomial _
  · exact project_polynomial _
  · exact group_polynomial
  · exact value_polynomial
  · exact kind_polynomial
  · exact project_polynomial _
theorem query_polynomial : HasPolynomialEnvelope query :=
  finite_run_polynomial V40ActivityPrepare.machine V40ActivityClock.coefficient V40ActivityClock.degree
theorem producer_polynomial : HasPolynomialEnvelope producer :=
  compose_polynomial prepare_polynomial query_polynomial
def coefficient:=Classical.choose producer_polynomial
def degree:=Classical.choose (Classical.choose_spec producer_polynomial)
theorem envelope : Envelope producer coefficient degree :=
  Classical.choose_spec (Classical.choose_spec producer_polynomial)

#print axioms producer_polynomial
end
end CurrentAdditive.V40SourceCell
