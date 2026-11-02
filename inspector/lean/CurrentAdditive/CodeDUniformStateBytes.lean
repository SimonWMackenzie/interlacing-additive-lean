import CurrentAdditive.V40RawLivePacketBound
import CurrentAdditive.CodeDGeneratedIteration

/-! One original-input byte cap for all outer states and every padded inner
prefix. These are pure iteration facts; no machine run or size premise occurs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
namespace CurrentAdditive.CodeDUniformStateBytes
open EthInapproximability.CurrentPaper BitMachineBankCodec
open SequentialCode SequentialSourceCode LabelTrace IntegerBitSupport

def sourceAt (D : Nat) (alphabet : Array (Nat × ℚ)) (q : Nat) :
    Array ((Fin q → Nat) × ℚ) := (sequentialPreprocessed D alphabet q).getD #[]

theorem sourceAt_some (D : Nat) (alphabet : Array (Nat × ℚ)) (q : Nat) :
    sequentialPreprocessed D alphabet q=some (sourceAt D alphabet q) := by
  obtain ⟨s,hs,hp⟩ := sequentialPreprocessed_total D alphabet q
  rw [sourceAt,hs]
  rfl

theorem sourceAt_positive (D : Nat) (alphabet : Array (Nat × ℚ)) (q : Nat) :
    SourcePositive (sourceAt D alphabet q) :=
  CodeDGeneratedIteration.preprocessed_source_positive D alphabet q _ (sourceAt_some D alphabet q)

def seedSource : Array ((Fin 0 → Nat) × ℚ) := #[(Fin.elim0,1)]
def seedWord := CodeDCanonicalSourceV2.encodedSource seedSource

theorem sourceAt_zero (D : Nat) (alphabet : Array (Nat × ℚ)) :
    sourceAt D alphabet 0=seedSource := rfl

def source0 (D : Nat) (alphabet : Array (Nat × ℚ)) (j : Nat) :=
  appendSource (sourceAt D alphabet j) (positiveLaw alphabet)

def features (D : Nat) (alphabet : Array (Nat × ℚ)) (j : Nat) :=
  generatedFeatures (j+1) D ((positiveLaw alphabet).map Prod.fst)

def innerSource (D : Nat) (alphabet : Array (Nat × ℚ)) (j t : Nat) :=
  let F := features D alphabet j
  ((CodeDCompressionIteration.onePass F.size (fun v i => generatedFeatureValue v F[i]))^[t])
    (source0 D alphabet j)

theorem succ_iteration (D : Nat) (alphabet : Array (Nat × ℚ)) (j : Nat) :
    sourceAt D alphabet (j+1)=innerSource D alphabet j (source0 D alphabet j).size := by
  have h := CodeDGeneratedIteration.stage_source_size_iteration D alphabet j _ (sourceAt_some D alphabet j)
  rw [sourceAt_some D alphabet (j+1)] at h
  exact Option.some.inj h

def rawPacket (q : Nat) (alphabet : Array (Nat × ℚ)) (s : Array ((Fin q → Nat) × ℚ)) :=
  encode ![List.replicate q true,CodeDTargetV2.alphabetBytes (positiveLaw alphabet),
    CodeDCanonicalSourceV2.encodedSource s]

def outerState (D : Nat) (alphabet : Array (Nat × ℚ)) (q : Nat) :=
  rawPacket q alphabet (sourceAt D alphabet q)

def innerPacket (D : Nat) (alphabet : Array (Nat × ℚ)) (j t : Nat) :=
  rawPacket (j+1) alphabet (innerSource D alphabet j t)

theorem outer_zero (D : Nat) (alphabet : Array (Nat × ℚ)) :
    outerState D alphabet 0=encode ![[],CodeDTargetV2.alphabetBytes (positiveLaw alphabet),seedWord] := rfl

def wholeInput := V39CodeDLivePacketBound.wholeInput

def exponent (D : Nat) := 14*D+14

def coefficient (D : Nat) := (2*(126*D+1200)+20)+2*seedWord.length+20

def cap (D Q : Nat) (alphabet : Array (Nat × ℚ)) :=
  coefficient D*((wholeInput Q alphabet).length+1)^exponent D

theorem inner_length_le (D : Nat) (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2))=true)
    (hmass : sourceMass alphabet=1) (Q j : Nat) (hj : j<Q) (t : Nat) :
    (innerPacket D alphabet j t).length ≤ cap D Q alphabet := by
  obtain ⟨e,he,htrace⟩ := CodeDGeneratedIteration.stage_iterate_trace D alphabet j _
    (sourceAt_some D alphabet j) t
  have h := V40RawLivePacketBound.rawLivePacket_length_le D alphabet hnonneg hmass Q j hj
    (sourceAt D alphabet j) (sourceAt_some D alphabet j) (innerSource D alphabet j t) e htrace
  apply h.trans
  unfold cap coefficient exponent wholeInput
  exact Nat.mul_le_mul_right _ (by omega)

theorem zero_length_le (D : Nat) (alphabet : Array (Nat × ℚ))
    (hmass : sourceMass alphabet=1) (Q : Nat) :
    (outerState D alphabet 0).length ≤ cap D Q alphabet := by
  let X := (wholeInput Q alphabet).length+1
  let L := (CodeDTargetV2.alphabetBytes alphabet).length
  let E := exponent D
  have hx : X=2*(Q+L)+3 := by simp only [X,L,wholeInput,V39CodeDLivePacketBound.wholeInput_length]
  have hX : 1 ≤ X := by omega
  have hLX : L ≤ X := by omega
  have h2 : X ≤ X^2 := by nlinarith only [hX]
  have h2one : 1 ≤ X^2 := Nat.one_le_pow _ _ hX
  have ha : (CodeDTargetV2.alphabetBytes (positiveLaw alphabet)).length ≤ 7*X^2 := by
    calc
      _ ≤ 3*L*(L+1)+1 := V40RawLivePacketBound.filtered_alphabet_length alphabet hmass
      _ ≤ 3*X*(X+1)+1 := by gcongr
      _ ≤ 7*X^2 := by nlinarith only [h2,h2one]
  have h2E : X^2 ≤ X^E := Nat.pow_le_pow_right hX (by dsimp [E,exponent];omega)
  have h1E : 1 ≤ X^E := Nat.one_le_pow _ _ hX
  have hlen : (outerState D alphabet 0).length=
      2*((CodeDTargetV2.alphabetBytes (positiveLaw alphabet)).length+seedWord.length)+3 := by
    rw [outer_zero]
    simp [encode_length,Fin.sum_univ_succ,Nat.add_assoc]
  rw [hlen]
  change _ ≤ coefficient D*X^E
  have haE := ha.trans (Nat.mul_le_mul_left 7 h2E)
  have hs := Nat.mul_le_mul_left (2*seedWord.length+3) h1E
  unfold coefficient
  nlinarith only [haE,hs]

theorem outer_length_le (D : Nat) (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2))=true)
    (hmass : sourceMass alphabet=1) (Q q : Nat) (hq : q≤Q) :
    (outerState D alphabet q).length ≤ cap D Q alphabet := by
  cases q with
  | zero => exact zero_length_le D alphabet hmass Q
  | succ j =>
    have hj : j<Q := by omega
    unfold outerState
    rw [succ_iteration]
    exact inner_length_le D alphabet hnonneg hmass Q j hj (source0 D alphabet j).size

/-- Both actual fixed-count loops can use this same cap, independent of all
outer and inner prefix counters. -/
theorem all_states (D : Nat) (alphabet : Array (Nat × ℚ))
    (hnonneg : alphabet.all (fun e => decide (0 ≤ e.2))=true)
    (hmass : sourceMass alphabet=1) (Q : Nat) :
    (∀ q≤Q,(outerState D alphabet q).length≤cap D Q alphabet) ∧
      (∀ j<Q,∀ t,(innerPacket D alphabet j t).length≤cap D Q alphabet) :=
  ⟨outer_length_le D alphabet hnonneg hmass Q,inner_length_le D alphabet hnonneg hmass Q⟩

#print axioms sourceAt_some
#print axioms succ_iteration
#print axioms inner_length_le
#print axioms outer_length_le
#print axioms all_states
end CurrentAdditive.CodeDUniformStateBytes
