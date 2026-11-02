import CurrentAdditive.V40IndexedLawSize
import CurrentAdditive.GaussCellPolynomialClock

namespace CurrentAdditive.V40IndexedLawPolynomial
noncomputable section
open Paper2 EthInapproximability.CurrentPaper BitMachineBankCodec
open V40SourceContextSpec V40SourceLocal V40IndexedLawLoop V40SourceClockBounds
open GaussCellPolynomialClock
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

def uniformClock (s n L T : Nat) :=
  withFuel.clock (input s n)+2*(withFuel.result (input s n)).length+2+
  (5*((WeightedIterationDriver.input (state s n 0) (count s n)).length+1)+
    count s n*BitMachineIteration.roundBound body.machine L T+2)+
  2*(state s n (count s n)).length+2+14*((state s n (count s n)).length+1)

theorem outputs_uniform (s n : Nat) (hs : 4 ≤ s) (hn : 0 < n) (L T : Nat)
    (hstate : ∀ j<count s n, (state s n j).length ≤ L)
    (hbody : ∀ j<count s n, body.clock (state s n j) ≤ T) :
    machine.OutputsWithin (input s n)
      (StoredWeightedState.lawBytes (LiteralEdgeEncoder.indexedItemLaw s n hs hn))
      (uniformClock s n L T) := by
  have hl:=WeightedIterationDriver.outputs_uniform body.machine (state s n) (count s n) L T
    (by
      intro j hj
      have hd:=denominator_pos s n hs hn ⟨j,hj⟩
      apply BitMachine.outputsWithin_mono body.machine
        (show body.machine.OutputsWithin (state s n j) (state s n (j+1))
          (body.clock (state s n j)) from by
          simpa only [body_result s n j hd] using body_outputs s n j)
        (hbody j hj)) hstate
  rw [←withFuel_result] at hl
  have h:=BitMachineComposition.composition_outputsWithin _ _ (withFuel_outputs (input s n)) hl
  have hp:=BankFieldProjection.outputs (4:Fin 5) (state s n (count s n))
  have hh:=BitMachineComposition.composition_outputsWithin _ _ h hp
  have he : BankFieldProjection.result (4:Fin 5) (state s n (count s n))=
      StoredWeightedState.lawBytes (LiteralEdgeEncoder.indexedItemLaw s n hs hn) := by
    rw [lawBytes_eq]
    simp [state,BankFieldProjection.result_encode,accumulator,SourceListEncoding.encode,entries,count]
  simpa only [machine,loopMachine,uniformClock,he,withFuel_result] using hh

def stateCap (A e N : Nat) := A*(N+1)^e
def bodyCap (A e B b N : Nat) := B*(stateCap A e N+1)^b
def prepCap (W w N : Nat) := W*(N+1)^w
def loopCap (A e B b N : Nat) :=
  5*(2*(stateCap A e N+N)+2+1)+
    N*BitMachineIteration.roundBound body.machine (stateCap A e N) (bodyCap A e B b N)+2
def cap (A e B b W w N : Nat) :=
  3*prepCap W w N+2+loopCap A e B b N+16*(stateCap A e N+1)

theorem cap_polynomial (A e B b W w : Nat) : PolynomialBound (fun _ N=>cap A e B b W w N) := by
  have hstate : PolynomialBound (fun _ N=>stateCap A e N) :=
    mul (constant A) (power (add second (constant 1)) e)
  have hbody : PolynomialBound (fun _ N=>bodyCap A e B b N) :=
    mul (constant B) (power (add hstate (constant 1)) b)
  have hprep : PolynomialBound (fun _ N=>prepCap W w N) :=
    mul (constant W) (power (add second (constant 1)) w)
  have hround : PolynomialBound (fun _ N=>
      BitMachineIteration.roundBound body.machine (stateCap A e N) (bodyCap A e B b N)) :=
    add (add (add hbody
      (mul (constant (body.machine.stackCount+2))
        (add hstate (mul hbody (constant body.machine.pushBound)))))
      (constant body.machine.stackCount)) (constant 4)
  have hloop : PolynomialBound (fun _ N=>loopCap A e B b N) :=
    add (add (mul (constant 5)
      (add (add (mul (constant 2) (add hstate second)) (constant 2)) (constant 1)))
      (mul second hround)) (constant 2)
  exact add (add (add (mul (constant 3) hprep) (constant 2)) hloop)
    (mul (constant 16) (add hstate (constant 1)))

theorem uniformClock_le (A e B b W w s n : Nat) (hs : 4 ≤ s) (hn : 0 < n)
    (hstate : ∀ s n (hs : 4 ≤ s) (hn : 0 < n) j, j ≤ count s n →
      (state s n j).length+1 ≤ A*((input s n).length+1)^e)
    (hbody : Envelope body B b) (hprep : Envelope withFuel W w) :
    uniformClock s n (stateCap A e (input s n).length) (bodyCap A e B b (input s n).length) ≤
      cap A e B b W w (input s n).length := by
  let N:=(input s n).length
  have hc : count s n ≤ N:=(input_lengths s n).2.2
  have h0 : (state s n 0).length ≤ stateCap A e N := by
    have h:=hstate s n hs hn 0 (by omega)
    change _ ≤ stateCap A e N at h
    omega
  have hf : (state s n (count s n)).length ≤ stateCap A e N := by
    have h:=hstate s n hs hn (count s n) le_rfl
    change _ ≤ stateCap A e N at h
    omega
  have hp:=hprep (input s n)
  change withFuel.clock (input s n)+(withFuel.result (input s n)).length ≤ prepCap W w N at hp
  have hi : (WeightedIterationDriver.input (state s n 0) (count s n)).length ≤
      2*(stateCap A e N+N)+2 := by
    change (encode ![state s n 0,List.replicate (count s n) true]).length ≤ _
    rw [encode_length]
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,List.length_replicate]
    omega
  have hl : 5*((WeightedIterationDriver.input (state s n 0) (count s n)).length+1)+
      count s n*BitMachineIteration.roundBound body.machine (stateCap A e N) (bodyCap A e B b N)+2 ≤
      loopCap A e B b N := by
    unfold loopCap
    gcongr
  change _ ≤ 3*prepCap W w N+2+loopCap A e B b N+16*(stateCap A e N+1)
  unfold uniformClock
  change _ ≤ 3*prepCap W w N+2+loopCap A e B b N+16*(stateCap A e N+1)
  nlinarith

theorem outputs_polynomial : ∃ C d, ∀ s n (hs : 4 ≤ s) (hn : 0 < n),
    machine.OutputsWithin (input s n)
      (StoredWeightedState.lawBytes (LiteralEdgeEncoder.indexedItemLaw s n hs hn))
      (C*((input s n).length+1)^d) := by
  obtain ⟨A,e,hsizes⟩:=state_length_polynomial
  obtain ⟨B,b,hbody⟩:=body_polynomial
  obtain ⟨W,w,hprep⟩:=withFuel_polynomial
  obtain ⟨C,d,hcap⟩:=cap_polynomial A e B b W w
  refine ⟨C,d,?_⟩
  intro s n hs hn
  let N:=(input s n).length
  have hstates : ∀ j<count s n, (state s n j).length ≤ stateCap A e N := by
    intro j hj
    have hh:=hsizes s n hs hn j (by omega)
    change _ ≤ stateCap A e N at hh
    omega
  have hbodies : ∀ j<count s n, body.clock (state s n j) ≤ bodyCap A e B b N := by
    intro j hj
    have hh:=hbody (state s n j)
    have hlen : (state s n j).length+1 ≤ stateCap A e N+1:=by have := hstates j hj; omega
    have hm:=Nat.mul_le_mul_left B (Nat.pow_le_pow_left hlen b)
    change _ ≤ bodyCap A e B b N
    unfold bodyCap
    omega
  have hrun:=outputs_uniform s n hs hn (stateCap A e N) (bodyCap A e B b N) hstates hbodies
  apply BitMachine.outputsWithin_mono machine hrun
  exact (uniformClock_le A e B b W w s n hs hn hsizes hbody hprep).trans (by
    simpa only [Nat.zero_add] using hcap 0 (input s n).length)

theorem clock_le_uniform (s n L T : Nat)
    (hstate : ∀ j<count s n, (state s n j).length ≤ L)
    (hbody : ∀ j<count s n, body.clock (state s n j) ≤ T) :
    V40IndexedLawLoop.clock s n ≤ uniformClock s n L T := by
  have hc:=WeightedIterationClock.cumulative_le body.machine (state s n)
    (fun j=>body.clock (state s n j)) (count s n) L T hstate hbody
  unfold V40IndexedLawLoop.clock loopClock WeightedIterationDriver.clock uniformClock
  omega

theorem clock_polynomial : ∃ C d, ∀ s n, 4 ≤ s → 0 < n →
    V40IndexedLawLoop.clock s n ≤ C*((input s n).length+1)^d := by
  obtain ⟨A,e,hsizes⟩:=state_length_polynomial
  obtain ⟨B,b,hbody⟩:=body_polynomial
  obtain ⟨W,w,hprep⟩:=withFuel_polynomial
  obtain ⟨C,d,hcap⟩:=cap_polynomial A e B b W w
  refine ⟨C,d,?_⟩
  intro s n hs hn
  let N:=(input s n).length
  have hstates : ∀ j<count s n, (state s n j).length ≤ stateCap A e N := by
    intro j hj
    have hh:=hsizes s n hs hn j (by omega)
    change _ ≤ stateCap A e N at hh
    omega
  have hbodies : ∀ j<count s n, body.clock (state s n j) ≤ bodyCap A e B b N := by
    intro j hj
    have hh:=hbody (state s n j)
    have hlen : (state s n j).length+1 ≤ stateCap A e N+1:=by have := hstates j hj; omega
    have hm:=Nat.mul_le_mul_left B (Nat.pow_le_pow_left hlen b)
    unfold bodyCap
    omega
  exact (clock_le_uniform s n _ _ hstates hbodies).trans
    ((uniformClock_le A e B b W w s n hs hn hsizes hbody hprep).trans (by
      simpa only [Nat.zero_add] using hcap 0 (input s n).length))

#print axioms outputs_uniform
#print axioms outputs_polynomial
#print axioms clock_polynomial
end
end CurrentAdditive.V40IndexedLawPolynomial
