import CurrentAdditive.GaussCellInitialClock
import CurrentAdditive.GaussFetchPolynomial64

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace CurrentAdditive.GaussCellPolynomialClock
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext GaussFetchedArithmetic GaussCellInitialClock
attribute [local irreducible] GaussFetchedArithmetic.M
  GaussFixedArithmeticClock.coefficient GaussUniformMatrixRun.exponent
  GaussRequestGrowth64.requestPush GaussFetchPolynomial64.coefficient
  UnaryBinaryEncoding.coefficient

/-- The coefficient and exponent are fixed before both input size arguments. -/
def PolynomialBound (f : Nat → Nat → Nat) : Prop :=
  ∃ C d : Nat, ∀ s n,f s n ≤ C*(s+n+1)^d

theorem constant (c : Nat) : PolynomialBound (fun _ _ => c) :=
  ⟨c,0,by intro s n; simp⟩
theorem first : PolynomialBound (fun s _ => s) :=
  ⟨1,1,by intro s n; simp; omega⟩
theorem second : PolynomialBound (fun _ n => n) :=
  ⟨1,1,by intro s n; simp; omega⟩

theorem add {f g : Nat → Nat → Nat} (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun s n => f s n+g s n) := by
  obtain ⟨C,d,hf⟩:=hf
  obtain ⟨D,e,hg⟩:=hg
  refine ⟨C+D,d+e,?_⟩
  intro s n
  have hq : 1 ≤ s+n+1 := by omega
  have hd:=Nat.pow_le_pow_right hq (show d ≤ d+e by omega)
  have he:=Nat.pow_le_pow_right hq (show e ≤ d+e by omega)
  calc
    f s n+g s n ≤ C*(s+n+1)^d+D*(s+n+1)^e := Nat.add_le_add (hf s n) (hg s n)
    _ ≤ C*(s+n+1)^(d+e)+D*(s+n+1)^(d+e) :=
      Nat.add_le_add (Nat.mul_le_mul_left C hd) (Nat.mul_le_mul_left D he)
    _ = (C+D)*(s+n+1)^(d+e) := by ring

theorem mul {f g : Nat → Nat → Nat} (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun s n => f s n*g s n) := by
  obtain ⟨C,d,hf⟩:=hf
  obtain ⟨D,e,hg⟩:=hg
  refine ⟨C*D,d+e,?_⟩
  intro s n
  calc
    f s n*g s n ≤ (C*(s+n+1)^d)*(D*(s+n+1)^e) := Nat.mul_le_mul (hf s n) (hg s n)
    _ = (C*D)*(s+n+1)^(d+e) := by rw [pow_add]; ring

theorem power {f : Nat → Nat → Nat} (hf : PolynomialBound f) (a : Nat) :
    PolynomialBound (fun s n => (f s n)^a) := by
  obtain ⟨C,d,hf⟩:=hf
  refine ⟨C^a,d*a,?_⟩
  intro s n
  calc
    (f s n)^a ≤ (C*(s+n+1)^d)^a := Nat.pow_le_pow_left (hf s n) a
    _ = C^a*(s+n+1)^(d*a) := by rw [mul_pow,pow_mul]

theorem mono {f g : Nat → Nat → Nat} (hg : PolynomialBound g)
    (h : ∀ s n,f s n ≤ g s n) : PolynomialBound f := by
  obtain ⟨C,d,hg⟩:=hg
  exact ⟨C,d,fun s n => (h s n).trans (hg s n)⟩

theorem four_polynomial : PolynomialBound
    (fun s n => GaussFourFetchEnvelope64.fourBound (s+n+1) n) := by
  apply mono (f:=fun s n => GaussFourFetchEnvelope64.fourBound (s+n+1) n)
    (g:=fun s n => GaussFetchPolynomial64.coefficient*(s+n+1+n+1)^3)
  · exact mul (constant _) (power (add (add (add (add first second) (constant 1)) second) (constant 1)) 3)
  · intro s n
    exact GaussFetchPolynomial64.fourBound_polynomial (s+n+1) n

attribute [local irreducible] PolynomialBound

theorem uniform_invocation (N : BitMachine.Machine) {f g : Nat → Nat → Nat}
    (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun s n => MachineInvokeFull.uniformBound N
      (List.replicate (f s n) true) (g s n)) := by
  unfold MachineInvokeFull.uniformBound
  simp only [List.length_replicate]
  have hsum:=add hf (mul hg (constant N.pushBound))
  have hfirst:=add (mul (constant 2) hf) (constant 2)
  have hthird:=add (mul (constant 2) hsum) (constant 2)
  have hfourth:=add (add (mul (constant N.stackCount) hsum)
    (constant N.stackCount)) (constant 2)
  exact add (add (add (add hfirst hg) hthird) hfourth) (constant 3)

theorem packet_polynomial : PolynomialBound (fun _ n => packetCap n) :=
  add (mul (constant 32) (add second (constant 1))) (constant 54)

theorem arithmetic_polynomial : PolynomialBound (fun _ n => arithmeticCap n) :=
  mul (constant GaussFixedArithmeticClock.coefficient)
    (power (add packet_polynomial (constant 1)) GaussUniformMatrixRun.exponent)

theorem answer_polynomial : PolynomialBound (fun _ n => answerCap n) :=
  add packet_polynomial (mul arithmetic_polynomial (constant M.pushBound))

theorem invocation_polynomial : PolynomialBound (fun _ n => invocationCap n) :=
  uniform_invocation M packet_polynomial arithmetic_polynomial

theorem request_polynomial : PolynomialBound requestCap :=
  add (add (add four_polynomial (add (mul (constant 2) second) (constant 5)))
    (mul (constant 2) packet_polynomial)) (constant 4)

theorem raw_polynomial : PolynomialBound rawCap := by
  have hinit:=add (add first second) (constant 1)
  have hcleanup:=add (mul (constant 52)
    (add hinit (mul request_polynomial (constant GaussRequestGrowth64.requestPush)))) (constant 54)
  exact add (add (add (add (add (mul (constant 14) second) (constant 30))
    request_polynomial) invocation_polynomial) hcleanup) (constant 3)

theorem framing_polynomial : PolynomialBound
    (fun _ n => V2FieldContext.clock (List.replicate (answerCap n) true)) := by
  have htime:=mul (constant (UnaryBinaryEncoding.coefficient+7))
    (power (add answer_polynomial (constant 1)) 2)
  have h:=uniform_invocation V2FieldContext.W answer_polynomial htime
  simpa only [V2FieldContext.clock,List.length_replicate] using h

/-- A uniform polynomial bound for the actual framed-cell clock. Its constants
come solely from fixed finite programs, and are chosen before every matrix,
cursor, caller bank, and both size caps. -/
theorem framedCap_polynomial : PolynomialBound framedCap :=
  add (add (add raw_polynomial (mul (constant 4) answer_polynomial))
    framing_polynomial) (constant 10)

#print axioms framedCap_polynomial
end CurrentAdditive.GaussCellPolynomialClock
