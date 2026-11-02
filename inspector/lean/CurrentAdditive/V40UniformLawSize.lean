import CurrentAdditive.V40UniformLawLoop

namespace CurrentAdditive.V40UniformLawLoop
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
open Paper2 EthInapproximability.CurrentPaper
open BitMachineBankCodec EncodedCommunication

theorem entry_length (n i : Nat) (hn : 0<n) (hi : i≤n) :
    (CodeDTargetV2.alphabetEntry (i,(n:ℚ)⁻¹)).length≤6*n+14 := by
  rw [show CodeDTargetV2.alphabetEntry (i,(n:ℚ)⁻¹)=
    encode ![i.bits,CodeDCodec.encodeRawRat (CodeDCanonicalSourceV2.rawOfRat ((n:ℚ)⁻¹))] by
      unfold CodeDTargetV2.alphabetEntry
      congr 1
      funext k
      fin_cases k <;> rfl]
  rw [V40SeedProducer.raw_inverse n hn]
  have hiB := UnaryBinaryEncoding.bits_length_le i
  have hnB := UnaryBinaryEncoding.bits_length_le n
  simp [encode,encodeFrom,CodeDCodec.encodeRawRat,CodeDCodec.rawRatBank,
    List.length_append,field_length,List.length_reverse]
  omega

theorem accumulator_length (n j : Nat) (hn : 0<n) (hj : j≤n) :
    (accumulator n j).length ≤ 2*n+1+j*(18*n+43) := by
  have ht := SourceListEncoding.totalLength_map_le (List.range j)
    (fun i => CodeDTargetV2.alphabetEntry (i,(n:ℚ)⁻¹)) (6*n+14) (by
      intro i hi
      exact entry_length n i hn (by have := List.mem_range.mp hi;omega))
  have hf := SourceListEncoding.fields_length (entries n j)
  have hh := EncodedGraph.natField_length_upper n
  simp only [List.length_range] at ht
  simp only [entries,List.length_map,List.length_range] at hf
  simp only [accumulator,List.length_append]
  dsimp only [entries] at *
  nlinarith

def sizeCap (n : Nat) := 100*(n+1)^2

theorem state_length (n j : Nat) (hn : 0<n) (hj : j≤n) :
    (state n j).length ≤ sizeCap n := by
  have ha := accumulator_length n j hn hj
  have hm := Nat.mul_le_mul_right (18*n+43) hj
  have he : (state n j).length=2*(j+n+(accumulator n j).length)+3 := by
    unfold state
    rw [encode_length]
    simp [Fin.sum_univ_succ,Nat.add_assoc]
  rw [he]
  dsimp only [sizeCap]
  nlinarith

def timeCap (n : Nat) := body.coefficient*(sizeCap n+1)^body.degree

theorem stepClock_le (n j : Nat) (hn : 0<n) (hj : j≤n) :
    stepClock n j≤timeCap n := by
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_left (Nat.add_le_add_right (state_length n j hn hj) 1) _

def loopBound (n : Nat) :=
  5*((WeightedIterationDriver.input (state n 0) n).length+1)+
    n*BitMachineIteration.roundBound body.machine (sizeCap n) (timeCap n)+2

theorem loop_outputs_bounded (n : Nat) (hn : 0<n) :
    loopMachine.OutputsWithin (WeightedIterationDriver.input (state n 0) n)
      (state n n) (loopBound n) := by
  exact WeightedIterationDriver.outputs_uniform body.machine (state n) n (sizeCap n) (timeCap n)
    (fun j hj => BitMachine.outputsWithin_mono _ (step_outputs n j hn)
      (stepClock_le n j hn (by omega)))
    (fun j hj => state_length n j hn (by omega))

theorem entries_uniform (n : Nat) [NeZero n] :
    SourceListEncoding.encode (entries n n)=
      StoredWeightedState.lawBytes (PositiveRationalLaw.uniform (Fin n)) := by
  have hl : (List.range n).map (fun i => CodeDTargetV2.alphabetEntry (i,(n:ℚ)⁻¹))=
      List.ofFn (fun i:Fin n => CodeDTargetV2.alphabetEntry (i.val,(n:ℚ)⁻¹)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  simp only [StoredWeightedState.lawBytes,StoredWeightedState.lawAlphabet,
    CodeDTargetV2.alphabetBytes,Array.toList_ofFn,List.map_ofFn,
    PositiveRationalLaw.uniform,Fintype.card_fin,CodeDCodecV2.encodeItems,
    Function.comp_def]
  exact congrArg SourceListEncoding.encode hl

#print axioms loop_outputs_bounded
#print axioms entries_uniform
end
end CurrentAdditive.V40UniformLawLoop
