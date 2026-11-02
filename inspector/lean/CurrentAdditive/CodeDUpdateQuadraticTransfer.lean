import CurrentAdditive.CodeDUpdateProducerTransfer

/-! A producer-independent transfer from a quadratic output-size certificate
to the concrete arithmetic/update/filter clock. -/

namespace CurrentAdditive.CodeDUpdateQuadraticTransfer

open EthInapproximability.CurrentPaper

def quadraticOutputBound (input : List Bool) : Nat :=
  20 * (input.length+1)^2

theorem downstream_clock_le_quadratic {q : Nat}
    (input : List Bool) (source : Array ((Fin q → Nat) × ℚ))
    (coeff : Array ℚ) (lambda : ℚ)
    (hsize : (CodeDUpdateRequestABI.requestPacketList source coeff lambda).length ≤
      quadraticOutputBound input) :
    CodeDUpdateFullPipeline.clock source coeff lambda ≤
      CodeDUpdateArithmeticClock.fullPipelineBound
        (quadraticOutputBound input) (quadraticOutputBound input) := by
  have hc := CodeDUpdateUnivariateClock.valid_packet_clock_le
    source coeff lambda
  exact le_trans hc
    (CodeDUpdateUnivariateClock.fullPipelineBound_mono
      _ _ (quadraticOutputBound input) hsize hsize)

theorem composed_clock_le_quadratic {q : Nat}
    (input : List Bool) (source : Array ((Fin q → Nat) × ℚ))
    (coeff : Array ℚ) (lambda : ℚ) (t : Nat)
    (hsize : (CodeDUpdateRequestABI.requestPacketList source coeff lambda).length ≤
      quadraticOutputBound input) :
    t + 2*(CodeDUpdateRequestABI.requestPacketList source coeff lambda).length+2+
        CodeDUpdateFullPipeline.clock source coeff lambda ≤
      t + 2*quadraticOutputBound input+2+
        CodeDUpdateArithmeticClock.fullPipelineBound
          (quadraticOutputBound input) (quadraticOutputBound input) := by
  have hc := downstream_clock_le_quadratic input source coeff lambda hsize
  have htwice := Nat.mul_le_mul_left 2 hsize
  omega

#print axioms downstream_clock_le_quadratic
#print axioms composed_clock_le_quadratic

end CurrentAdditive.CodeDUpdateQuadraticTransfer
