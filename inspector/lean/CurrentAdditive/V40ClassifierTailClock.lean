import CurrentAdditive.V40ClassifierTail
import CurrentAdditive.V40MidpointRequestClock
namespace CurrentAdditive.V40ClassifierTailClock
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication V39PublicSchedule
open V40RandomPermittedFamily

theorem request_length (L K : Nat)
    (f : Fin (sampleSide L K) → Fin (sampleSide L K) → Bool) :
    (natField (2*B L K+K)++matrixWord L K f).length ≤ 9*sampleSide L K^2+3 := by
  have hn := numerator_le_entries L K

  have hh := EncodedGraph.natField_length_upper (2*B L K+K)
  have hm := V40MidpointRequest.matrix_length L K f
  simp only [List.length_append]
  dsimp only [numerator] at hn
  omega

theorem tape_length (C : SelectedTape.Algorithm) (L K : Nat)
    (f : Fin (sampleSide L K) → Fin (sampleSide L K) → Bool) :
    C.tapeLength (natField (2*B L K+K)++matrixWord L K f) ≤
      C.cR*(9*sampleSide L K^2+4)^C.dR := by
  have h := request_length L K f
  unfold SelectedTape.Algorithm.tapeLength
  gcongr

theorem cap_mono (C : SelectedTape.Algorithm) {a b : Nat} (h : a ≤ b) :
    V40ClassifierTail.cap C a ≤ V40ClassifierTail.cap C b := by
  unfold V40ClassifierTail.cap NPOwner1.Trunc.timeBound
  gcongr

def afterCap (C : SelectedTape.Algorithm) (N : Nat) :=
  11*N+10+V40ClassifierTail.cap C (3*N+1)

theorem after_cap_poly (C : SelectedTape.Algorithm) :
    Unit4Shell.Poly.PolyIn id (afterCap C) := by
  unfold afterCap V40ClassifierTail.cap NPOwner1.Trunc.timeBound
  repeat (first
    | exact Unit4Shell.Poly.self
    | exact Unit4Shell.Poly.const _
    | apply Unit4Shell.Poly.add
    | apply Unit4Shell.Poly.mul
    | apply Unit4Shell.Poly.pow)

theorem after_clock_le (C : SelectedTape.Algorithm) (input request tape : List Bool)
    (T N : Nat) (hi : input.length≤N) (hr : request.length≤N)
    (ht : tape.length≤N) (hT : T≤N) :
    V40ClassifierTail.afterClock C input request tape T≤afterCap C N := by
  have hp : (EncodedComplexity.pair request tape).length≤3*N+1 := by
    rw [EncodedComplexity.pair_length]; omega
  have hc := cap_mono C hp
  unfold V40ClassifierTail.afterClock afterCap
  omega

#print axioms request_length
#print axioms tape_length
#print axioms after_cap_poly
#print axioms after_clock_le
end
end CurrentAdditive.V40ClassifierTailClock
