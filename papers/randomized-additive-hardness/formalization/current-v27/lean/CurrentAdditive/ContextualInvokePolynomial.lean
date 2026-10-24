import CurrentAdditive.ContextualInvoke

/-! Uniform polynomial transport for a valid-request-only contextual call.
No all-input totality of the invoked machine is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
namespace CurrentAdditive.ContextualInvoke
open EthInapproximability.CurrentPaper
open BitMachineBankCodec MinimumRatioContext

theorem packet_length (context request : List Bool) :
    (packet context request).length=2*context.length+2*request.length+2 := by
  simp [packet,encode_length,Fin.sum_univ_two]
  omega

theorem output_length (context answer : List Bool) :
    (output context answer).length=2*context.length+2*answer.length+2 := by
  simp [output,encode_length,Fin.sum_univ_two]
  omega

def linearCoefficient (s : Nat) := 2*s+100

def timeCoefficient (s p : Nat) := 1+(s+6)*p

theorem clock_scalar (s p N c r b T : Nat) (hc : c ≤ N) (hr : r ≤ N) (hb : b ≤ r+T*p) :
    5*(N+1)+((2*r+2)+T+(2*(r+T*p)+2)+(s*(r+T*p)+s+2)+3)+
      2*(2*c+2*b+2)+4 ≤ linearCoefficient s*(N+1)+timeCoefficient s p*T := by
  have hcr := Nat.mul_le_mul_left 4 hc
  have hrr := Nat.mul_le_mul_left (s+8) hr
  have hbr := Nat.mul_le_mul_left 4 hb
  have hn : 0 ≤ (s+83)*N := Nat.zero_le _
  unfold linearCoefficient timeCoefficient
  nlinarith

theorem clock_bound (M : BitMachine.Machine) (context request answer : List Bool)
    (T : Nat) (hM : M.OutputsWithin request answer T) :
    clock M context request answer T ≤
      linearCoefficient M.stackCount*((packet context request).length+1)+
        timeCoefficient M.stackCount M.pushBound*T := by
  have hc := word_length_le_encode (![context,request]) (0 : Fin 2)
  have hr := word_length_le_encode (![context,request]) (1 : Fin 2)
  have hb := BitMachine.output_length_bound M hM
  have h := clock_scalar M.stackCount M.pushBound (packet context request).length
    context.length request.length answer.length T hc hr hb
  simpa only [clock,MachineInvokeFull.uniformBound,output_length] using h

def polynomialCoefficient (M : BitMachine.Machine) (a : Nat) :=
  linearCoefficient M.stackCount+timeCoefficient M.stackCount M.pushBound*a

theorem clock_polynomial (M : BitMachine.Machine) (a e : Nat)
    (context request answer : List Bool)
    (hM : M.OutputsWithin request answer (a*(request.length+1)^e)) :
    clock M context request answer (a*(request.length+1)^e) ≤
      polynomialCoefficient M a*((packet context request).length+1)^(e+1) := by
  let U := (packet context request).length+1
  have hU : 1 ≤ U := by dsimp [U]; omega
  have hr := word_length_le_encode (![context,request]) (1 : Fin 2)
  change request.length ≤ (packet context request).length at hr
  have hrU : request.length+1 ≤ U := by dsimp only [U]; omega
  have hT : a*(request.length+1)^e ≤ a*U^e := Nat.mul_le_mul_left a (Nat.pow_le_pow_left hrU e)
  have h1 : U ≤ U^(e+1) := le_self_pow hU (by omega)
  have he : U^e ≤ U^(e+1) := pow_le_pow_right₀ hU (by omega)
  calc
    _ ≤ linearCoefficient M.stackCount*U+timeCoefficient M.stackCount M.pushBound*(a*(request.length+1)^e) :=
      clock_bound M context request answer _ hM
    _ ≤ linearCoefficient M.stackCount*U+timeCoefficient M.stackCount M.pushBound*(a*U^e) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ hT) _
    _ ≤ linearCoefficient M.stackCount*U^(e+1)+(timeCoefficient M.stackCount M.pushBound*a)*U^(e+1) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ h1)
        (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (timeCoefficient M.stackCount M.pushBound*a) he)
    _ = _ := by unfold polynomialCoefficient; rw [Nat.add_mul]

theorem outputs_polynomial (M : BitMachine.Machine) (a e : Nat)
    (context request answer : List Bool)
    (hM : M.OutputsWithin request answer (a*(request.length+1)^e)) :
    (machine M).OutputsWithin (packet context request) (output context answer)
      (polynomialCoefficient M a*((packet context request).length+1)^(e+1)) :=
  BitMachine.outputsWithin_mono (machine M) (outputs M context request answer _ hM)
    (clock_polynomial M a e context request answer hM)

/-- A valid request execution suffices; M need not halt on unrelated inputs. -/
theorem uniform (M : BitMachine.Machine) (a e : Nat) :
    ∃ C E : Nat, ∀ context request answer : List Bool,
      M.OutputsWithin request answer (a*(request.length+1)^e) →
      (machine M).OutputsWithin (packet context request) (output context answer)
        (C*((packet context request).length+1)^E) :=
  ⟨polynomialCoefficient M a,e+1,outputs_polynomial M a e⟩

#print axioms outputs_polynomial
#print axioms uniform
end CurrentAdditive.ContextualInvoke
