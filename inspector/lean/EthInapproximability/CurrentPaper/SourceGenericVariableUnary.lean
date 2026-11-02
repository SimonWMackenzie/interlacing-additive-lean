import EthInapproximability.CurrentPaper.SourceAffineUnary
import EthInapproximability.CurrentPaper.SourceGenericOrder

/-!
# The exact generic source variable header

Locked v8 Section 6, sparse-gap source construction. The instruction table
depends only on the fixed positive alphabet and fixed arity, while n and m
are lengths of actual input words. This is a header-writing component, not a
proof that the original encoded CSP has already been parsed.
-/
namespace EthInapproximability.CurrentPaper.SourceGenericVariableUnary

open SourceBooleanEncoding

def vertexCoefficient (a q : Nat) : Nat :=
  a + (1 + a * a) * (width a q + 1)

def rowCoefficient (a q : Nat) : Nat :=
  (width a q + 1) * a ^ q

theorem vertexCoefficient_pos (a q : Nat) : 0 < vertexCoefficient a q := by
  unfold vertexCoefficient
  positivity

theorem rowCoefficient_pos {a : Nat} (ha : 0 < a) (q : Nat) :
    0 < rowCoefficient a q := by
  unfold rowCoefficient
  positivity

theorem sourceVariables_affine {n m a q : Nat} (P : CSP n m a q) :
    SourceGenericOrder.sourceVariables P =
      vertexCoefficient a q * n + rowCoefficient a q * m := by
  simp only [SourceGenericOrder.sourceVariables, vertexCoefficient,
    rowCoefficient, clauseCount]
  ring

/-- Predecessors encode two positive fixed coefficients in the generic
physical affine machine. Correctness below requires a positive alphabet. -/
def coefficients (a q : Nat) : Nat × Nat :=
  (vertexCoefficient a q - 1, rowCoefficient a q - 1)

theorem vertex_coefficient (a q : Nat) :
    SourceAffineUnary.vertexCoefficient (coefficients a q) =
      vertexCoefficient a q := by
  have hp := vertexCoefficient_pos a q
  simp only [SourceAffineUnary.vertexCoefficient, coefficients]
  omega

theorem row_coefficient {a : Nat} (ha : 0 < a) (q : Nat) :
    SourceAffineUnary.rowCoefficient (coefficients a q) =
      rowCoefficient a q := by
  have hp := rowCoefficient_pos ha q
  simp only [SourceAffineUnary.rowCoefficient, coefficients]
  omega

abbrev Config (a q : Nat) := SourceAffineUnary.Config (coefficients a q)

def program (a q : Nat) := SourceAffineUnary.program (coefficients a q)

def time (a q n m : Nat) :=
  ((vertexCoefficient a q + 1) * n + 1) +
  ((rowCoefficient a q + 1) * m + 1)

/-- Exact whole-bank run, including consumption of both count words. -/
theorem source_header_run {n m a q : Nat} (ha : 0 < a)
    (P : CSP n m a q) :
    ((BitMachineEncoding.advance (program a q))^[time a q n m])
      (SourceAffineUnary.cfg (some .vertexScan) none
        (List.replicate n true) (List.replicate m true) [] :
          Config a q) =
    SourceAffineUnary.cfg none none [] []
      (List.replicate (SourceGenericOrder.sourceVariables P) true) := by
  have hr := SourceAffineUnary.run_correct (coefficients a q) n m
  simpa only [SourceAffineUnary.run, vertex_coefficient,
    row_coefficient ha, sourceVariables_affine P, time, program] using hr

theorem time_linear (a q n m : Nat) :
    time a q n m ≤
      (vertexCoefficient a q + rowCoefficient a q + 2) * (n + m + 1) + 2 := by
  unfold time
  nlinarith

#print axioms source_header_run
#print axioms time_linear

end EthInapproximability.CurrentPaper.SourceGenericVariableUnary
