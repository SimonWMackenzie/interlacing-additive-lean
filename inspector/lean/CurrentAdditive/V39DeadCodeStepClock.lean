import CurrentAdditive.V39DeadCodeStep
import CurrentAdditive.V39DeadCodeSize
import Paper2.GeneratorSize

/-! A scalar-only fixed polynomial majorant for the physical one-level
compiler clock. The intermediate graph/tagged syntax sizes are eliminated
using the production serialization-size identities. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace CurrentAdditive.V39DeadCodeStepClock

open Paper2

open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorSource Paper2.CodeRecursiveColumn
open CurrentAdditive.V39DeadCodeRow CurrentAdditive.V39DeadCodeStep

def graphCap (n s q₁ q₂ r : Nat) : Nat :=
  1572 + (s+7+(q₂*(r+q₁+10)+4)) +
    (4*s+n+20) + (5*s+20) + 2*r

def taggedCap (q₁ q₂ s c : Nat) : Nat :=
  let outer := q₂+11+(q₁+s+1)*(c+3)
  803 + (11+(s+1)*(c+3)+s*(outer+3)) +
    (s*(outer+3)+4) + outer

theorem graph_size_le (n s q₁ q₂ : Nat) (previousRow : Code) :
    codeSize (graphCode n s q₁ q₂ previousRow) ≤
      graphCap n s q₁ q₂ (codeSize previousRow) := by
  rw [graphCode, GeneratorSize.graphRows_size,
    GeneratorSize.templateRow_size,
    GeneratorSize.template_size]
  unfold graphCap
  omega

theorem tagged_size_eq (q₁ q₂ s : Nat) (previousCol : Code) :
    codeSize (CurrentAdditive.V39DeadTaggedCompiler.deadTaggedCode q₁ q₂ s previousCol) =
      taggedCap q₁ q₂ s (codeSize previousCol) := by
  rw [CurrentAdditive.V39DeadTaggedCompiler.deadTagged_size, GeneratorSize.raw_size,
    GeneratorSize.fixedTail_size, GeneratorSize.outer_size]
  simp only [taggedCap]

theorem source_successor_outputs (n s q₁ q₂ w Q : Nat)
    (row₀ col₀ : Code) (k : Nat) :
    afterRow n s q₁ q₂ w Q
      (CurrentAdditive.V39DeadGenericCode.recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).1
      (CurrentAdditive.V39DeadGenericCode.recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).2 52 =
        encodeCode (CurrentAdditive.V39DeadGenericCode.recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k+1)).1 ∧
    afterRow n s q₁ q₂ w Q
      (CurrentAdditive.V39DeadGenericCode.recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).1
      (CurrentAdditive.V39DeadGenericCode.recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).2 37 =
        encodeCode (CurrentAdditive.V39DeadGenericCode.recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k+1)).2 := by
  constructor
  · rw [V39DeadCodeStep.row_output, V39DeadCodeRow.source_successor_row]
  · rw [V39DeadCodeStep.column_output]
    rfl

def polynomialClock (n s q₁ q₂ w Q r c : Nat) : Nat :=
  let g := graphCap n s q₁ q₂ r
  let tagged := taggedCap q₁ q₂ s c
  80*(n+s+q₁+q₂+r+g+1) +
    (2*w+5)+1 + (2*Q+8)+1 +
    (3+w*(2*g+4))+1 +
    (2*(Q+4+(4+w*(g+3)))+6)+1 +
    (2*q₁+5)+1 + (2*q₂+5)+1 + (2*Q+5)+1 +
    TaggedCompiler.polynomialClock q₁ q₂ s c+3 +
    (2*w+8)+1 +
    (2*(w+4+tagged)+6)+1 +
    (3+Q*(2*(w+7+tagged)+4))+1

theorem clock_le_polynomial (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (hs : 3 ≤ s) :
    V39DeadCodeStep.clockBound n s q₁ q₂ w Q
      previousRow previousCol ≤
    polynomialClock n s q₁ q₂ w Q
      (codeSize previousRow) (codeSize previousCol) := by
  let g := codeSize (graphCode n s q₁ q₂ previousRow)
  let gcap := graphCap n s q₁ q₂ (codeSize previousRow)
  let tagged := codeSize (CurrentAdditive.V39DeadTaggedCompiler.deadTaggedCode q₁ q₂ s previousCol)
  have hg : g ≤ gcap := graph_size_le n s q₁ q₂ previousRow
  have ht : tagged = taggedCap q₁ q₂ s (codeSize previousCol) :=
    tagged_size_eq q₁ q₂ s previousCol
  have hrow := CodeRowsGraphCompiler.clock_linear
    n s q₁ q₂ previousRow hs
  change CodeRowsGraphCompiler.clockBound n s q₁ q₂ previousRow ≤
    80*(n+s+q₁+q₂+codeSize previousRow+g+1) at hrow
  have htagClock := TaggedCompiler.taggedClock_eq_polynomial
    q₁ q₂ s previousCol
  rw [encodeCode_length] at htagClock
  have hcopyG : codeSize (copies w (graphCode n s q₁ q₂ previousRow)) =
      4+w*(g+3) := by
    have h := GeneratorSize.copies_size w
      (graphCode n s q₁ q₂ previousRow)
    dsimp [g]
    omega
  dsimp [g] at hcopyG
  have hrowunit : codeSize (rowUnitCode q₁ q₂ s w previousCol) =
      w+7+tagged := by
    change 3 + (3+(w+1)) + tagged = w+7+tagged
    omega
  have hticketQ : codeSize (.ticket Q) = Q+4 := by
    change 3+(Q+1)=Q+4
    omega
  have hticketW : codeSize (.ticket w) = w+4 := by
    change 3+(w+1)=w+4
    omega
  have hwG : w*(2*g+4) ≤ w*(2*gcap+4) := by
    apply Nat.mul_le_mul_left
    omega
  have hwG' : w*(g+3) ≤ w*(gcap+3) := by
    apply Nat.mul_le_mul_left
    omega
  have hQtag : Q*(2*(w+7+tagged)+4) ≤
      Q*(2*(w+7+taggedCap q₁ q₂ s (codeSize previousCol))+4) := by
    rw [← ht]
  simp only [V39DeadCodeStep.clockBound,
    V39DeadCodeStep.b₆, V39DeadCodeStep.b₅,
    V39DeadCodeStep.b₄, V39DeadCodeStep.b₃,
    V39DeadCodeStep.b₂, V39DeadCodeStep.b₁,
    CodeRecursiveColumn.clockBound,
    CodeCopiesMachine.clock,
    CodeConstructorMachine.appendClock,
    encodeCode_length, hcopyG, hrowunit,
    htagClock, hticketQ, hticketW,
    polynomialClock] at *
  dsimp [g, gcap] at hwG hwG'
  omega

#print axioms clock_le_polynomial

end CurrentAdditive.V39DeadCodeStepClock
