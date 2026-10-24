import CurrentAdditive.GaussAdaptedRequestLength

/-! Charge the full k-column physical matrix clock to k ≤ m*M. -/

namespace CurrentAdditive.GaussMatrixSupportClock

open CurrentAdditive.GaussNestedMatrixMap
open CurrentAdditive.GaussMatrixClockPolynomial
open EthInapproximability.CurrentPaper

theorem listBytes_mono (k K L : Nat) (h : k ≤ K) :
    listBytes k L ≤ listBytes K L := by
  unfold listBytes
  gcongr

theorem polyRowTime_mono (M : BitMachine.Machine)
    (k K L R T : Nat) (h : k ≤ K) :
    polyRowTime M k L R T ≤ polyRowTime M K L R T := by
  unfold polyRowTime
  gcongr

theorem polyRowFramed_mono (M : BitMachine.Machine)
    (k K L R T : Nat) (h : k ≤ K) :
    polyRowFramed M k L R T ≤ polyRowFramed M K L R T := by
  unfold polyRowFramed
  gcongr
  · exact polyRowTime_mono M k K L R T h
  all_goals exact listBytes_mono k K R h

theorem polyRowEnvelope_mono (M : BitMachine.Machine)
    (k K L R T : Nat) (h : k ≤ K) :
    polyRowEnvelope M k L R T ≤ polyRowEnvelope M K L R T := by
  unfold polyRowEnvelope
  dsimp only
  gcongr
  all_goals first
    | exact listBytes_mono k K L h
    | exact listBytes_mono k K R h
    | exact polyRowFramed_mono M k K L R T h

theorem polyMatrixTime_mono_columns (M : BitMachine.Machine)
    (m k K L R T : Nat) (h : k ≤ K) :
    polyMatrixTime M m k L R T ≤ polyMatrixTime M m K L R T := by
  unfold polyMatrixTime
  gcongr
  · exact polyRowEnvelope_mono M k K L R T h
  exact listBytes_mono k K R h

theorem full_support_matrix_clock (M : BitMachine.Machine)
    (m k Mparam L R T : Nat) (hk : k ≤ m*Mparam) :
    polyMatrixTime M m k L R T ≤
      polyMatrixTime M m (m*Mparam) L R T :=
  polyMatrixTime_mono_columns M m k (m*Mparam) L R T hk

#print axioms full_support_matrix_clock

end CurrentAdditive.GaussMatrixSupportClock
