import CurrentAdditive.V42FiniteFieldComplete
import CurrentAdditive.D22PacketPrimitives
import EthInapproximability.CurrentPaper.DimensionNatUnary

/-! Binary-input completion of v42 `yao:finite-field-list`. This also
charges the physical conversion of the two binary integer parameters into
the unary arithmetic compiler's fixed input format. -/

namespace CurrentAdditive.V42FiniteFieldBinary

open Paper2 CurrentAdditive.SmallBias CurrentAdditive.FiniteFieldConstructor
open CurrentAdditive.FiniteFieldMachine CurrentAdditive.V42FiniteFieldList
open EthInapproximability.CurrentPaper BitMachineComposition
open D22PacketPrimitives

set_option maxHeartbeats 2000000

/-- Three framed binary integer fields, with a zero third field. -/
def input (n r : ℕ) : List Bool :=
  BitMachineBankCodec.encode (fun j => (D22NatExpression.values n r 0 j).bits)

def decodedValue (j : Fin 3) (x : List Bool) : ℕ :=
  MatrixBinaryAddress.valueFrom 0 (BankFieldProjection.result j x).reverse

noncomputable def decodeProducer (j : Fin 3) : Producer :=
  ⟨composition (BankFieldProjection.machine j) DimensionNatUnary.bitsMachine,
    fun x => List.replicate (decodedValue j x) true,
    fun x => 20*(x.length+decodedValue j x+1)⟩

noncomputable def preprocessor : Producer :=
  append (frame (decodeProducer 0))
    (append (frame (decodeProducer 1)) (frame (decodeProducer 2)))

noncomputable def machine : BitMachine.Machine :=
  composition preprocessor.machine V42FiniteFieldTheorem.machine

noncomputable def coefficient : ℕ := V42FiniteFieldTheorem.coefficient+5000

private theorem bits_outputs (q : List Bool) :
    DimensionNatUnary.bitsMachine.OutputsWithin q
      (List.replicate (MatrixBinaryAddress.valueFrom 0 q.reverse) true)
      (4*MatrixBinaryAddress.valueFrom 0 q.reverse+6*q.length+5) := by
  have h := composition_outputsWithin DimensionNatUnary.reverseMachine MatrixBinaryAddress.bitMachine
    (DimensionNatUnary.reverse_outputs q) (MatrixBinaryAddress.bitMachine_outputs q.reverse)
  exact BitMachine.outputsWithin_mono _ h (by simp only [List.length_reverse]; omega)

private theorem decodeProducer_outputs (j : Fin 3) (x : List Bool) :
    (decodeProducer j).machine.OutputsWithin x
      ((decodeProducer j).result x) ((decodeProducer j).clock x) := by
  have h := composition_outputsWithin (BankFieldProjection.machine j) DimensionNatUnary.bitsMachine
    (BankFieldProjection.outputs j x) (bits_outputs (BankFieldProjection.result j x))
  have hl := BankFieldProjection.result_length j x
  apply BitMachine.outputsWithin_mono _ h
  dsimp [decodeProducer, decodedValue]
  omega

private theorem preprocessor_outputs (x : List Bool) :
    preprocessor.machine.OutputsWithin x (preprocessor.result x) (preprocessor.clock x) :=
  append_outputs _ _ x (frame_outputs _ x (decodeProducer_outputs 0 x))
    (append_outputs _ _ x (frame_outputs _ x (decodeProducer_outputs 1 x))
      (frame_outputs _ x (decodeProducer_outputs 2 x)))

private theorem decodedValue_input (n r : ℕ) (j : Fin 3) :
    decodedValue j (input n r) = D22NatExpression.values n r 0 j := by
  simp only [decodedValue, input, BankFieldProjection.result_encode]
  exact WeightedRawWords.valueFrom_bits_reverse _

private theorem preprocessor_result (n r : ℕ) :
    preprocessor.result (input n r) = V42FiniteFieldTheorem.input n r := by
  simp only [preprocessor, append, frame, decodeProducer, decodedValue_input]
  simp [V42FiniteFieldTheorem.input, D22NatExpression.input, D22NatExpression.values,
    BitMachineBankCodec.encode_eq_list, List.ofFn_succ]

private theorem numeric_bounds (n r : ℕ) (hn : 1 ≤ n) :
    n ≤ target n r ∧ r ≤ target n r := by
  have hp : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hr : r ≤ 2 ^ r := Nat.lt_two_pow_self.le
  unfold target
  constructor <;> nlinarith

private theorem inputLength_le (n r : ℕ) (hn : 1 ≤ n) :
    (input n r).length ≤ 7*(target n r+1) := by
  have hnlen := UnaryBinaryEncoding.bits_length_le n
  have hrlen := UnaryBinaryEncoding.bits_length_le r
  obtain ⟨hnN, hrN⟩ := numeric_bounds n r hn
  unfold input
  rw [BitMachineBankCodec.encode_length]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, D22NatExpression.values,
    Matrix.cons_val_zero, Matrix.cons_val_succ,
    show Nat.bits 0 = [] by rfl, List.length_nil]
  omega

private theorem preprocessorClock_le (n r : ℕ) (hn : 1 ≤ n) :
    preprocessor.clock (input n r) ≤ 4000*(target n r+1) := by
  have hi := inputLength_le n r hn
  obtain ⟨hnN, hrN⟩ := numeric_bounds n r hn
  simp only [preprocessor, append, PhysicalConcatLocal.clock, frame, decodeProducer,
    decodedValue_input, List.length_append, EncodedCommunication.field_length,
    List.length_replicate]
  simp only [show D22NatExpression.values n r 0 0 = n by rfl,
    show D22NatExpression.values n r 0 1 = r by rfl,
    show D22NatExpression.values n r 0 2 = 0 by rfl]
  omega

/-- Binary integer parameters are physically decoded, and then the same
complete field/search/printer algorithm is executed. -/
theorem machine_outputs (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    ∃ c < order n r,
      TrialSearch.firstPassing (degree n r) = some (TrialSearch.monicBits (degree n r) c) ∧
      machine.OutputsWithin (input n r)
        (UnifiedFieldListMachine.packedBits (degree n r) c n)
        (coefficient*(target n r+1)^5) := by
  obtain ⟨c, hc, hfirst, hm⟩ := V42FiniteFieldTheorem.machine_outputs n r hn hr
  have hp := preprocessor_outputs (input n r)
  rw [preprocessor_result] at hp
  have h := composition_outputsWithin preprocessor.machine V42FiniteFieldTheorem.machine hp hm
  refine ⟨c, hc, hfirst, BitMachine.outputsWithin_mono machine h ?_⟩
  have hpre := preprocessorClock_le n r hn
  have hlen : (V42FiniteFieldTheorem.input n r).length = 2*(n+r)+3 := by
    unfold V42FiniteFieldTheorem.input D22NatExpression.input
    rw [BitMachineBankCodec.encode_length]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, List.length_replicate,
      D22NatExpression.values, Matrix.cons_val_zero, Matrix.cons_val_succ]
    omega
  obtain ⟨hnN, hrN⟩ := numeric_bounds n r hn
  have h1 : target n r+1 ≤ (target n r+1)^5 := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ target n r+1) (by omega : 1 ≤ 5)
  have h0 : 1 ≤ (target n r+1)^5 := one_le_pow₀ (by omega)
  rw [hlen]
  unfold coefficient
  nlinarith

/-- Source v42 `yao:finite-field-list` on binary integer parameters.
The same physical packed output has exactly R² labelled n-bit rows and
satisfies the all-coordinate-set pattern bound under its uniform row law.
No field, correctness, or runtime certificate is a premise. -/
theorem finite_field_list (n r : ℕ) (hn : 1 ≤ n) (hr : 1 ≤ r) :
    ∃ c < order n r,
      TrialSearch.firstPassing (degree n r) = some (TrialSearch.monicBits (degree n r) c) ∧
      let modulus := TrialSearch.monicBits (degree n r) c
      let packed := CanonicalTable.packedFieldBits (degree n r) modulus n
      let arrays := StreamingPrinter.labelledWords (degree n r) modulus n
      target n r ≤ order n r ∧ order n r < 2*target n r ∧
      (∀ k : ℕ, target n r ≤ 2^k → degree n r ≤ k) ∧
      TrialSearch.makeList (degree n r) n = some arrays ∧
      arrays.length = (order n r)^2 ∧ arrays ≠ [] ∧
      packed.length = (order n r)^2*n ∧ packed.length ≤ 4*(target n r+1)^3 ∧
      machine.OutputsWithin (input n r) packed (coefficient*(target n r+1)^5) ∧
      (∀ ℓ : Fin ((order n r)^2), ∀ j : Fin n,
        let xy := (printerPairLabel (degree n r)).symm ℓ
        arrays[ℓ.val]? = some (xy.1.val, xy.2.val,
          StreamingPrinter.word (degree n r) modulus n xy.1.val xy.2.val) ∧
        (StreamingPrinter.word (degree n r) modulus n xy.1.val xy.2.val)[j.val]? =
          some (word (degree n r) modulus n ℓ j) ∧
        packed[ℓ.val*n+j.val]?.getD false = word (degree n r) modulus n ℓ j) ∧
      (∀ x y, (StreamingPrinter.word (degree n r) modulus n x y).length = n) ∧
      (∀ (I : Finset (Fin n)) (z : Fin n → Bool),
        (FiniteLaw.uniform (Fin ((order n r)^2))).prob
          (fun ℓ => ∀ j ∈ I, word (degree n r) modulus n ℓ j = z j) ≤
            (1/2 : ℝ)^I.card+(1/2 : ℝ)^r) := by
  obtain ⟨c, hc, hfirst, hm⟩ := machine_outputs n r hn hr
  refine ⟨c, hc, hfirst, ?_⟩
  dsimp only
  have hlen := StreamingPrinter.labelledWords_length (degree n r)
    (TrialSearch.monicBits (degree n r) c) n
  have hnonempty : StreamingPrinter.labelledWords (degree n r)
      (TrialSearch.monicBits (degree n r) c) n ≠ [] := by
    intro he
    rw [he, List.length_nil] at hlen
    have hp : 0 < (2^degree n r)^2 := by positivity
    omega
  refine ⟨degree_lower n r, order_lt n r hn hr, degree_least n r,
    by simp [TrialSearch.makeList, hfirst], hlen, hnonempty,
    CanonicalTable.packedFieldBits_length _ _ _,
    V42FiniteFieldComplete.complete_output_length_le n r _ hn hr, hm,
    ?_, StreamingPrinter.word_length _ _ _, ?_⟩
  · intro ℓ j
    let xy := (printerPairLabel (degree n r)).symm ℓ
    have hxy : printerPairLabel (degree n r) xy = ℓ := Equiv.apply_symm_apply _ _
    refine ⟨?_, streaming_word_getElem? _ _ _ _ _ j,
      CanonicalTable.packedFieldBits_get _ _ _ ℓ j⟩
    simpa only [hxy] using streaming_labelledWords_getElem? (degree n r)
      (TrialSearch.monicBits (degree n r) c) n xy.1 xy.2
  · intro I z
    exact pattern_prob_le _ _ _ (by positivity) (source_bias n r _ hn hr hfirst) I z

#print axioms machine_outputs
#print axioms finite_field_list

end CurrentAdditive.V42FiniteFieldBinary
