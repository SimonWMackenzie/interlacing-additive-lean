import CurrentAdditive.GaussFetchedAdaptedRequest
import CurrentAdditive.GaussFourFetchEnvelope64

namespace CurrentAdditive.GaussRequestGrowth64

noncomputable section

set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128

open CurrentAdditive.GaussFetchedAdaptedRequest
open CurrentAdditive.GaussFourFetchEnvelope64
open EthInapproximability.CurrentPaper

abbrev Stack := Fin 64

noncomputable instance : Fintype GaussFourOperands64.Label := by
  letI : Fintype GaussFetchFromBackups64.Label := inferInstance
  letI : Fintype (BitMachineRawSequence.Label
    GaussFetchFromBackups64.Label GaussFetchFromBackups64.Label) := inferInstance
  letI : Fintype (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label GaussFetchFromBackups64.Label
      GaussFetchFromBackups64.Label) GaussFetchFromBackups64.Label) := inferInstance
  infer_instance

noncomputable instance : Fintype GaussFetchedAdaptedRequest.Label := by
  infer_instance

def requestPush : Nat := rawPushBound GaussFetchedAdaptedRequest.program

theorem stack_growth (S : Stack → List Bool) (a B : Nat)
    (hS : ∀ j, (S j).length ≤ B) (j : Stack) :
    ((GaussFetchedAdaptedRequest.run a (GaussFetchedAdaptedRequest.initial S)).stk j).length ≤
      B+a*requestPush := by
  have h := GaussFourFetchEnvelope64.run_length GaussFetchedAdaptedRequest.program
    (GaussFetchedAdaptedRequest.initial S) j a
  have h' : ((GaussFetchedAdaptedRequest.run a (GaussFetchedAdaptedRequest.initial S)).stk j).length ≤
      (S j).length+a*requestPush := by
    simpa only [GaussFetchedAdaptedRequest.run,GaussFetchedAdaptedRequest.initial,requestPush] using h
  exact h'.trans (Nat.add_le_add_right (hS j) _)

/-- Every scratch word cleared after request construction is charged from
the actual request run. Updating answer29 does not alter these scratch words. -/
theorem cleanup_sum_le (S : Stack → List Bool) (a B : Nat)
    (hS : ∀ j, (S j).length ≤ B) (answer : List Bool)
    (scratch : Fin 52 → Stack) (hscratch : ∀ i, scratch i ≠ 29) :
    (∑ i : Fin 52,
      (Function.update
        (GaussFetchedAdaptedRequest.run a (GaussFetchedAdaptedRequest.initial S)).stk
        (29 : Stack) answer (scratch i)).length) ≤ 52*(B+a*requestPush) := by
  have h : ∀ i : Fin 52,
      (Function.update
        (GaussFetchedAdaptedRequest.run a (GaussFetchedAdaptedRequest.initial S)).stk
        (29 : Stack) answer (scratch i)).length ≤ B+a*requestPush := by
    intro i
    rw [Function.update_of_ne (hscratch i)]
    exact stack_growth S a B hS (scratch i)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 52)))
    (fun i _ => h i)
  simpa using hsum

#print axioms stack_growth
#print axioms cleanup_sum_le

end
end CurrentAdditive.GaussRequestGrowth64
