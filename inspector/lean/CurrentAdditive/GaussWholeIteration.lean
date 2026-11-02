import CurrentAdditive.GaussWholeStepUniform
import CurrentAdditive.GaussIterationBridge

namespace CurrentAdditive.GaussWholeIteration
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussWholeStepProgram (machine)

def storage (n : Nat) : Nat := GaussControlTrace.fullSupportStatePoly n n
def clock (n : Nat) : Nat := n*BitMachineIteration.roundBound machine (storage n)
  (GaussWholeStepUniform.polynomialClock (storage n))+1

theorem state_length {m k : Nat} (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀i j,A i j=0 ∨ A i j=1) (hm : 0 < m) (t : Nat) (ht : t ≤ k) :
    (GaussControlTrace.statePacket (GaussControlTrace.after (fun i j => (A i j : ℚ)) t)).length ≤
      storage (GaussPhysical.encodeTypedMatrix (fun i j => (A i j : ℚ))).length := by
  have hk : k ≤ m*k := by exact Nat.le_mul_of_pos_left k hm
  have hs:=GaussControlTrace.actual_statePacket_full_support A h01 hk t ht
  have hr:=GaussInitialByteDimensions.rows_le_initial_bytes (fun i j => (A i j : ℚ))
  have hc:=GaussInitialByteDimensions.columns_le_initial_bytes (fun i j => (A i j : ℚ)) hm
  apply hs.trans
  unfold storage GaussControlTrace.fullSupportStatePoly
  gcongr

theorem actual_step {m k : Nat} (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀i j,A i j=0 ∨ A i j=1) (hm : 0 < m) (t : Nat) (ht : t < k) :
    machine.OutputsWithin
      (GaussControlTrace.statePacket (GaussControlTrace.after (fun i j => (A i j : ℚ)) t))
      (GaussControlTrace.statePacket (GaussControlTrace.after (fun i j => (A i j : ℚ)) (t+1)))
      (GaussWholeStepUniform.polynomialClock
        (storage (GaussPhysical.encodeTypedMatrix (fun i j => (A i j : ℚ))).length)) := by
  have hc:=(GaussControlTrace.after_size (fun i j => (A i j : ℚ)) t).2.1
  have hout:=GaussWholeStepUniform.outputs_polynomial
    (GaussControlTrace.after (fun i j => (A i j : ℚ)) t) (by omega)
    (GaussControlTrace.after_pivotCount _ t)
  have hlen:=state_length A h01 hm t (Nat.le_of_lt ht)
  apply BitMachine.outputsWithin_mono machine _ (show
    GaussWholeStepUniform.polynomialClock
      (GaussControlTrace.statePacket (GaussControlTrace.after (fun i j => (A i j : ℚ)) t)).length ≤
      GaussWholeStepUniform.polynomialClock
        (storage (GaussPhysical.encodeTypedMatrix (fun i j => (A i j : ℚ))).length) from by
    unfold GaussWholeStepUniform.polynomialClock; gcongr)
  simpa only [GaussControlTrace.after,Function.iterate_succ_apply'] using hout

/-- The fixed fuel loop calls the concrete whole-step machine once per
column. Every output transfer and full machine-register reset is charged. -/
theorem actual_run {m k : Nat} (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀i j,A i j=0 ∨ A i j=1) (hm : 0 < m) :
    ∃u ≤ clock (GaussPhysical.encodeTypedMatrix (fun i j => (A i j : ℚ))).length,
      let c:=BitMachineIteration.run machine u
        (BitMachineIteration.ready machine
          (GaussControlTrace.statePacket (GaussControlTrace.initial (fun i j => (A i j : ℚ))))
          (List.replicate k true))
      c.l=none ∧ c.stk (.inl machine.input)=
        GaussControlTrace.statePacket (GaussControlTrace.after (fun i j => (A i j : ℚ)) k) := by
  let n:=(GaussPhysical.encodeTypedMatrix (fun i j => (A i j : ℚ))).length
  let states : Nat → List Bool:=fun t => GaussControlTrace.statePacket
    (GaussControlTrace.after (fun i j => (A i j : ℚ)) t)
  have hstep : ∀t < (List.replicate k true).length,
      machine.OutputsWithin (states t) (states (t+1))
        (GaussWholeStepUniform.polynomialClock (storage n)) := by
    intro t ht
    exact actual_step A h01 hm t (by simpa using ht)
  have hlen : ∀t < (List.replicate k true).length,(states t).length ≤ storage n := by
    intro t ht
    have ht' : t < k:=by simpa using ht
    exact state_length A h01 hm t (Nat.le_of_lt ht')
  obtain ⟨u,hu,hhalt,hout⟩:=BitMachineIteration.iteration_output machine states
    (List.replicate k true) (storage n) (GaussWholeStepUniform.polynomialClock (storage n)) hstep hlen
  have hk:=GaussInitialByteDimensions.columns_le_initial_bytes (fun i j => (A i j : ℚ)) hm
  refine ⟨u,?_,?_,?_⟩
  · simp only [List.length_replicate] at hu
    apply hu.trans
    unfold clock
    dsimp only [n]
    gcongr
  · simpa only [states,GaussControlTrace.after,Function.iterate_zero,Function.id_def] using hhalt
  · simpa only [states,GaussControlTrace.after,Function.iterate_zero,Function.id_def,
      List.length_replicate] using hout

theorem clock_polynomial : GaussCellPolynomialClock.PolynomialBound (fun _ n => clock n) := by
  open GaussCellPolynomialClock in
  have hs : PolynomialBound (fun _ n => storage n) := by
    unfold storage GaussControlTrace.fullSupportStatePoly
    repeat first | exact constant _ | exact second | apply add | apply mul | apply power
  open GaussCellPolynomialClock in
  have ht : PolynomialBound (fun _ n => GaussWholeStepUniform.polynomialClock (storage n)) := by
    unfold GaussWholeStepUniform.polynomialClock
    exact mul (constant _) (power (add hs (constant 1)) _)
  open GaussCellPolynomialClock in
  unfold clock BitMachineIteration.roundBound
  exact add (mul second (add (add (add ht
    (mul (constant _) (add hs (mul ht (constant _))))) (constant _)) (constant 4))) (constant 1)

#print axioms state_length
#print axioms actual_step
#print axioms actual_run
#print axioms clock_polynomial
end
end CurrentAdditive.GaussWholeIteration
