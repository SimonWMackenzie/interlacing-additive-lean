import CurrentAdditive.DyadicPowerWriter
import CurrentAdditive.V40SourceLocal
import CurrentAdditive.V22ExpressionClock
import EthInapproximability.CurrentPaper.ExactParameterMachineLog

/-! Binary schedule-output primitives. These are finite Boolean-stack
programs with clocks in the actual input word length. No exponentially long
unary width is constructed by the dyadic binary writer. -/
namespace CurrentAdditive.V42WidthPrimitives
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open PhysicalProducer V22UnaryExpression
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

def lengthUnary : Producer where
  machine := ExactParameterMachineLog.bitLengthMachine
  result x := List.replicate x.length true
  coefficient := 2
  degree := 1
  outputs x := BitMachine.outputsWithin_mono _ (ExactParameterMachineLog.bitLength_outputs x)
    (by simp only [pow_one];omega)

theorem bits_two_pow (e : ℕ) : (2^e).bits=List.replicate e false++[true] := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ,Nat.mul_comm,Nat.bit0_bits _ (by positivity),ih]
    simp [List.replicate_succ]

def powerMachine : BitMachine.Machine := ofFinite (0 : Fin 2) 1
  PublicScheduleDyadicPowerWriter.Label.start (none : Option Bool) PublicScheduleDyadicPowerWriter.program

theorem power_outputs (x : List Bool) :
    powerMachine.OutputsWithin x (2^x.length).bits (2*(x.length+1)) := by
  have hi : rawInit (0 : Fin 2) PublicScheduleDyadicPowerWriter.Label.start
      (none : Option Bool) x=PublicScheduleDyadicPowerWriter.cfg (some .start) none x [] := by
    simp [rawInit,PublicScheduleDyadicPowerWriter.cfg]
    funext k
    fin_cases k <;> rfl
  have hh : (((advance PublicScheduleDyadicPowerWriter.program)^[x.length+2])
      (rawInit (0 : Fin 2) PublicScheduleDyadicPowerWriter.Label.start (none : Option Bool) x)).l=none := by
    rw [hi]
    exact congrArg TM2.Cfg.l (PublicScheduleDyadicPowerWriter.run_correct x)
  have ho : (((advance PublicScheduleDyadicPowerWriter.program)^[x.length+2])
      (rawInit (0 : Fin 2) PublicScheduleDyadicPowerWriter.Label.start (none : Option Bool) x)).stk 1=
      (2^x.length).bits := by
    rw [hi]
    have h:=congrArg (fun c=>c.stk (1 : Fin 2)) (PublicScheduleDyadicPowerWriter.run_correct x)
    simpa only [PublicScheduleDyadicPowerWriter.cfg,Matrix.cons_val_one,bits_two_pow] using h
  exact outputsWithin_of_raw_run (0 : Fin 2) 1 PublicScheduleDyadicPowerWriter.Label.start
    (none : Option Bool) PublicScheduleDyadicPowerWriter.program x ((2^x.length).bits)
    (x.length+2) (2*(x.length+1)) (by omega) hh ho

def powerBinary : Producer where
  machine := powerMachine
  result x := (2^x.length).bits
  coefficient := 2
  degree := 1
  outputs x := by simpa only [pow_one] using power_outputs x

def arithmeticInput := concat lengthUnary (V40SeedProducer.constant [false])
theorem arithmeticInput_result (x : List Bool) :
    arithmeticInput.result x=MatrixUnaryArithmetic.encodeInput x.length 0 := by
  simp [arithmeticInput,concat,lengthUnary,V40SeedProducer.constant,MatrixUnaryArithmetic.encodeInput]

def cap (L : ℕ) := 1048576*(L+1)
def scalarCoefficient (e : Expr) := e.coefficient*(1048576+3)^2

theorem scalar_clock (e : Expr) (hpeak : ∀ L, e.peak L 0≤cap L) (L : ℕ) :
    e.clock L 0 ≤ scalarCoefficient e*(L+1)^2 := by
  have h:=e.clock_le_of_peak L 0 (cap L) (hpeak L)
  have hb : L+0+cap L+2≤(1048576+3)*(L+1) := by unfold cap;nlinarith
  calc
    _ ≤ e.coefficient*((1048576+3)*(L+1))^2 :=
      h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb _))
    _ = _ := by rw [mul_pow];unfold scalarCoefficient;ring

def scalar (e : Expr) (hpeak : ∀ L, e.peak L 0≤cap L) : Producer where
  machine := BitMachineComposition.composition arithmeticInput.machine e.machine
  result x := List.replicate (e.eval x.length 0) true
  coefficient := arithmeticInput.coefficient+2*(arithmeticInput.coefficient*arithmeticInput.machine.pushBound+1)+
    scalarCoefficient e*(arithmeticInput.coefficient*arithmeticInput.machine.pushBound+1)^2
  degree := (arithmeticInput.degree+1)*3
  outputs x := by
    have he:=e.outputs x.length 0
    rw [←arithmeticInput_result x] at he
    have hclock:=scalar_clock e hpeak x.length
    have hle : x.length+1≤(arithmeticInput.result x).length+1 := by
      rw [arithmeticInput_result]
      simp [MatrixUnaryArithmetic.encodeInput]
    have he':=BitMachine.outputsWithin_mono _ he
      (hclock.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hle 2)))
    apply BitMachine.outputsWithin_mono _
      (BitMachineComposition.composition_outputsWithin _ _ (arithmeticInput.outputs x) he')
    exact BitMachineCompositionArithmetic.composition_time_bound
      x.length arithmeticInput.coefficient arithmeticInput.degree (scalarCoefficient e) 2
      arithmeticInput.machine.pushBound (arithmeticInput.result x).length
      (BitMachine.output_length_bound _ (arithmeticInput.outputs x))

#print axioms power_outputs
#print axioms scalar
end
end CurrentAdditive.V42WidthPrimitives
