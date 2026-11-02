import CurrentAdditive.V42FullWidthExpressions

/-! Source-facing polynomial bit complexity of lem:full-schedule. Positive
n is encoded by the canonical little-endian binary word for n-1. Its length
is exactly L=ceil(log2 n). Output has five ordinary binary widths and five
canonical rational encodings. The fixed program has no base or round input. -/
namespace CurrentAdditive.V42FullScheduleInterface
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open PhysicalProducer V42WidthPrimitives V42FullWidthExpressions
open V42Schedule V42PublicSchedule
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

def naturalValues (L : ℕ) : Fin 5 → ℕ := ![s (fullExponent L),q₁ (fullExponent L),
  q₂ (fullExponent L) L,w (fullExponent L),Q (fullExponent L)]
def rationalValues (L : ℕ) : Fin 5 → ℚ := ![rho L,x L,eta (fullExponent L),
  theta (fullExponent L),deltaU (fullExponent L)]
def rationalWord (q : ℚ) := CodeDCodec.encodeRawRat (CodeDCanonicalSourceV2.rawOfRat q)
def words (L : ℕ) : Fin 10 → List Bool := fun i =>
  if h : i.val<5 then (naturalValues L ⟨i.val,h⟩).bits
  else rationalWord (rationalValues L ⟨i.val-5,by omega⟩)
def recipeWord (L : ℕ) := BitMachineBankCodec.encode (words L)

def ordinary (i : Fin 10) := compose (unary i) V40SeedProducer.unaryBinary
def dyadic (i : Fin 10) := compose (unary i) powerBinary
def inverseBits (A : Producer) := concat
  (V40SeedProducer.constant (field []++field [true]))
  (compose (compose A V40SeedProducer.reverse) PhysicalProducer.field)
def rational (i : Fin 10) := inverseBits (dyadic i)
def fields (i : Fin 10) : Producer :=
  if i.val<2 then ordinary i else if i.val<5 then dyadic i else rational i
@[irreducible] def producer := V40SourceLocal.physicalBank fields
def machine := producer.machine
def coefficient := producer.coefficient
def degree := producer.degree

theorem ordinary_result (i : Fin 10) (input : List Bool) :
    (ordinary i).result input=(values input.length i).bits := by
  change V40SeedProducer.unaryBinary.result ((unary i).result input)=_
  rw [unary_result]
  simp [V40SeedProducer.unaryBinary]

#print axioms ordinary_result

theorem dyadic_result (i : Fin 10) (input : List Bool) :
    (dyadic i).result input=(2^(values input.length i)).bits := by
  change powerBinary.result ((unary i).result input)=_
  rw [unary_result]
  simp [powerBinary]

#print axioms dyadic_result

theorem inverseBits_result (A : Producer) (input : List Bool) (n : ℕ) (hn : 0<n)
    (hA : A.result input=n.bits) :
    (inverseBits A).result input=rationalWord ((n : ℚ)⁻¹) := by
  rw [rationalWord,V40SeedProducer.raw_inverse n hn]
  simp [inverseBits,concat,compose,V40SeedProducer.constant,V40SeedProducer.reverse,PhysicalProducer.field,
    hA,CodeDCodec.encodeRawRat,CodeDCodec.rawRatBank,BitMachineBankCodec.encode,BitMachineBankCodec.encodeFrom]

#print axioms inverseBits_result

theorem rational_result (i : Fin 10) (input : List Bool) :
    (rational i).result input=rationalWord (((2^(values input.length i) : ℕ) : ℚ)⁻¹) :=
  inverseBits_result _ _ _ (by positivity) (dyadic_result i input)

#print axioms rational_result

theorem fields_result (i : Fin 10) (input : List Bool) :
    (fields i).result input=words input.length i := by
  fin_cases i <;> simp [fields,words,ordinary_result,dyadic_result,rational_result,
    naturalValues,rationalValues,values,V42Schedule.q₂,V42Schedule.w,V42Schedule.Q,
    rho,x,eta,theta,deltaU,Nat.cast_pow,Nat.cast_ofNat,one_div]

#print axioms fields_result

theorem producer_result (input : List Bool) : producer.result input=recipeWord input.length := by
  rw [producer,V40SourceLocal.physicalBank_result]
  apply congrArg BitMachineBankCodec.encode
  funext i
  exact fields_result i input

#print axioms producer_result

private theorem realizes_at_length (P : Producer) (f : ℕ → List Bool)
    (hr : ∀ input, P.result input=f input.length) (input : List Bool) (L : ℕ)
    (hlen : input.length=L) : P.machine.OutputsWithin input (f L)
      (P.coefficient*(L+1)^P.degree) := by
  subst L
  rw [←hr input]
  exact P.outputs input

/-- Ordinary transition count is polynomial in L, the actual binary size
of the positive source parameter. There is no admissibility, base-matrix,
round-number, target-run or supplied-clock premise. -/
theorem full_schedule_widths_polytime (L : ℕ) :
    producer.machine.OutputsWithin (List.replicate L true) (recipeWord L)
      (producer.coefficient*(L+1)^producer.degree) :=
  realizes_at_length producer recipeWord producer_result _ L (by simp)

def positiveInput (n : ℕ) : List Bool := (n-1).bits

theorem positiveInput_length (n : ℕ) : (positiveInput n).length=Nat.clog 2 n :=
  (ExactParameterMachineLog.clog_eq_pred_bits_length n).symm

/-- The same fixed machine computes the exact full-product recipe from a
canonical binary positive-size input. The clock is polynomial in its bit
length L, rather than in the magnitude n or in any width. -/
theorem full_schedule_binary_widths_polytime (n : ℕ) (_hn : 1≤n) :
    producer.machine.OutputsWithin (positiveInput n) (recipeWord (Nat.clog 2 n))
      (producer.coefficient*(Nat.clog 2 n+1)^producer.degree) :=
  realizes_at_length producer recipeWord producer_result _ _ (positiveInput_length n)

private theorem fixed_before_inputs (P : Producer) (f : ℕ → List Bool)
    (hr : ∀ input, P.result input=f input.length) : ∃ M : BitMachine.Machine, ∃ C d : ℕ,
    ∀ n : ℕ, 1≤n → M.OutputsWithin (positiveInput n) (f (Nat.clog 2 n))
      (C*((positiveInput n).length+1)^d) := by
  refine ⟨P.machine,P.coefficient,P.degree,?_⟩
  intro n hn
  simpa only [positiveInput_length] using
    realizes_at_length P f hr (positiveInput n) (positiveInput n).length rfl

theorem fixed_machine_before_all_inputs : ∃ M : BitMachine.Machine, ∃ C d : ℕ,
    ∀ n : ℕ, 1≤n → M.OutputsWithin (positiveInput n) (recipeWord (Nat.clog 2 n))
      (C*((positiveInput n).length+1)^d) :=
  fixed_before_inputs producer recipeWord producer_result

theorem exact_full_recipe (L : ℕ) :
    naturalValues L 0=V38Schedule.pow2Ceil (2^16*(L+1)) ∧
    naturalValues L 1=naturalValues L 0-2 ∧
    (naturalValues L 2 : ℚ)=(naturalValues L 0 : ℚ)^2/rationalValues L 0 ∧
    naturalValues L 3=(naturalValues L 0)^8 ∧
    naturalValues L 4=(naturalValues L 0)^24 ∧
    rationalValues L 0=(1:ℚ)/2^L ∧
    rationalValues L 1=(rationalValues L 0)^8 ∧
    rationalValues L 2=1/(naturalValues L 0 : ℚ)^2 ∧
    rationalValues L 3=1/(512*(naturalValues L 4 : ℚ)) ∧
    rationalValues L 4=rationalValues L 2/(16*(naturalValues L 3 : ℚ)) := by
  have h:=recipe_exact (fullExponent L) L
  refine ⟨source_s_exact L,rfl,h.1,h.2.1,h.2.2.1,rfl,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩

theorem current_runtime_widths (L : ℕ) : naturalValues L=
    ![V42RuntimeSchedule.fullS L,V42RuntimeSchedule.fullQ₁ L,V42RuntimeSchedule.fullQ₂ L,
      V42RuntimeSchedule.fullW L,V42RuntimeSchedule.fullQ L] := rfl

#print axioms producer_result
#print axioms full_schedule_widths_polytime
#print axioms full_schedule_binary_widths_polytime
#print axioms fixed_machine_before_all_inputs
#print axioms exact_full_recipe
#print axioms current_runtime_widths
end
end CurrentAdditive.V42FullScheduleInterface
