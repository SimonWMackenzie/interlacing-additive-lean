import CurrentAdditive.V22FullScheduleExpressions
import CurrentAdditive.V22ParameterBatch
import CurrentAdditive.V39DeadSampleJoin

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

namespace V22FullScheduleBatch
open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open V22UnaryExpression V22FullScheduleExpressions
open V38Schedule V39PublicSchedule V39FullSampleResources
abbrev Constructor := CurrentAdditive.V39DeadSampleJoin.Stack
abbrev Base := Constructor ⊕ Fin 13
def graphPort : Base := .inr 0
def kPort : Base := .inr 1
def sourcePort : Base := .inr 2
def nPort : Base := .inr 3
def precisionPort : Base := .inr 4
def drawPort : Base := .inr 5
def bitsPort : Base := .inr 6
def targets : Fin 19 → Base := ![
  .inl (.inl 12),.inl (.inl 16),.inl (.inl 17),.inl (.inl 18),
  .inl (.inl 31),.inl (.inl 32),.inl (.inl 63),.inl (.inl 64),
  .inl (.inr (.inr 0)),.inl (.inr (.inr 1)),
  .inr 4,.inr 5,.inr 6,.inr 7,.inr 8,.inr 9,.inr 10,.inr 11,.inr 12]
def expressions : Fin 19 → Expr := ![
  q2,q1,s,Expr.vertex,w,Q,seed,Expr.iteration,sample,sample,
  precision,draws,totalBits,alphabet,L,ellE,V22FullScheduleExpressions.B,
  V22FullScheduleExpressions.H,rank]
noncomputable def machines (i : Fin 19) := (expressions i).machine
abbrev Stack := V22ParameterBatch.Stack machines Base
noncomputable def program := V22ParameterBatch.program machines sourcePort targets
noncomputable def control := V22ParameterBatch.control machines
def start : V22ParameterBatch.Label machines := .inl 0
def results (n k : ℕ) (i : Fin 19) := List.replicate ((expressions i).eval n k) true
noncomputable def times (n k : ℕ) (i : Fin 19) := (expressions i).clock n k
noncomputable def clock (n k : ℕ) :=
  V22ParameterBatch.clockPrefix (MatrixUnaryArithmetic.encodeInput n k) (results n k) (times n k) 19+1

def preparedBase (bits : List Bool) (n k : ℕ) : Base → List Bool
  | .inl _ => []
  | .inr i => if i=0 then bits else if i=1 then List.replicate k true
      else if i=2 then MatrixUnaryArithmetic.encodeInput n k
      else if i=3 then List.replicate n true else []
def prepared (bits : List Bool) (n k : ℕ) : Stack → List Bool :=
  Sum.elim (preparedBase bits n k) (fun _ => [])
noncomputable def final (bits : List Bool) (n k : ℕ) : Stack → List Bool :=
  V22ParameterBatch.banks machines targets (prepared bits n k)
    (MatrixUnaryArithmetic.encodeInput n k) (results n k) (times n k) 19
noncomputable def constructorInput (n k : ℕ) : Constructor → List Bool :=
  let L := Nat.clog 2 n
  let m := sampleSide L k
  CurrentAdditive.V39DeadSampleJoin.initial n (seedWidth L) (fullS L)
    (fullQ₁ L) (fullQ₂ L) (fullW L) (fullQ L) k m m
noncomputable def expected (bits : List Bool) (n k : ℕ) : Base → List Bool
  | .inl j => constructorInput n k j
  | .inr i => if i=0 then bits else if i=1 then List.replicate k true
      else if i=2 then MatrixUnaryArithmetic.encodeInput n k
      else if i=3 then List.replicate n true
      else if i=4 then List.replicate (precision.eval n k) true
      else if i=5 then List.replicate (draws.eval n k) true
      else if i=6 then List.replicate (totalBits.eval n k) true
      else if i=7 then List.replicate (alphabet.eval n k) true
      else if i=8 then List.replicate (L.eval n k) true
      else if i=9 then List.replicate (ellE.eval n k) true
      else if i=10 then List.replicate (V22FullScheduleExpressions.B.eval n k) true
      else if i=11 then List.replicate (V22FullScheduleExpressions.H.eval n k) true
      else List.replicate (rank.eval n k) true

theorem targets_injective : Function.Injective targets := by decide
theorem source_ne_targets : ∀ i, sourcePort≠targets i := by decide
theorem targets_empty (bits : List Bool) (n k : ℕ) (i : Fin 19) :
    preparedBase bits n k (targets i)=[] := by
  fin_cases i <;> rfl
theorem run (bits : List Bool) (n k : ℕ) :
    ∃ t ≤ clock n k, ((advance program)^[t])
      (⟨some start,control,prepared bits n k⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,control,final bits n k⟩ := by
  exact V22ParameterBatch.run machines sourcePort targets targets_injective source_ne_targets
    (prepared bits n k) (MatrixUnaryArithmetic.encodeInput n k) (results n k) (times n k)
    rfl (targets_empty bits n k) (by intro i w; rfl)
    (fun i => (expressions i).outputs n k)

@[simp] theorem constructor_core (n k : ℕ) (j : Fin 65) :
    constructorInput n k (.inl j)=
    Paper2.CodeRecursiveSeedPrep.publicBase n (fullS (Nat.clog 2 n))
      (fullQ₁ (Nat.clog 2 n)) (fullQ₂ (Nat.clog 2 n))
      (fullW (Nat.clog 2 n)) (fullQ (Nat.clog 2 n)) (seedWidth (Nat.clog 2 n))
      (List.replicate k true) j := by
  exact bank_at Paper2.CodeGeneratorSampleTransfer.compilerSlots _ _ j
@[simp] theorem constructor_foreign (n k : ℕ) (j : Paper2.CodeGeneratorSampleTransfer.SampleStack ⊕ Fin 3) :
    constructorInput n k (.inr j)=
      Paper2.CodeGeneratorSampleTransfer.foreign (sampleSide (Nat.clog 2 n) k)
        (sampleSide (Nat.clog 2 n) k) (.inr j) := by
  apply bank_outside
  rintro ⟨a,h⟩; cases h

theorem expected_at (bits : List Bool) (n k : ℕ) (i : Fin 19) :
    expected bits n k (targets i)=results n k i := by
  fin_cases i <;>
    simp [expected,targets,results,expressions,constructor_core,constructor_foreign,
      Paper2.CodeRecursiveSeedPrep.publicBase,Paper2.CodeGeneratorSampleTransfer.foreign,
      V22UnaryExpression.Expr.eval]

private theorem outside_expected (bits : List Bool) (n k : ℕ) (b : Base)
    (h : ∀ i, targets i≠b) : preparedBase bits n k b=expected bits n k b := by
  cases b with
  | inl b =>
      cases b with
      | inl j =>
          fin_cases j <;>
            simp_all [Fin.forall_fin_succ,targets,preparedBase,expected,constructor_core,
              Paper2.CodeRecursiveSeedPrep.publicBase]
      | inr b =>
          cases b with
          | inl j => fin_cases j <;> simp [preparedBase,expected,constructor_foreign,
              Paper2.CodeGeneratorSampleTransfer.foreign]
          | inr j => fin_cases j <;>
              simp_all [Fin.forall_fin_succ,targets,preparedBase,expected,constructor_foreign,
                Paper2.CodeGeneratorSampleTransfer.foreign]
  | inr j =>
      fin_cases j <;> simp_all [Fin.forall_fin_succ,targets,preparedBase,expected]

theorem final_base (bits : List Bool) (n k : ℕ) (b : Base) :
    final bits n k (.inl b)=expected bits n k b := by
  classical
  by_cases h : ∃ i, targets i=b
  · obtain ⟨i,rfl⟩ := h
    have ht := V22ParameterBatch.banks_target machines targets targets_injective
      (prepared bits n k) (MatrixUnaryArithmetic.encodeInput n k) (results n k)
      (times n k) 19 le_rfl i
    rw [if_pos i.isLt] at ht
    exact ht.trans (expected_at bits n k i).symm
  · have h' : ∀ i, targets i≠b := by simpa only [not_exists] using h
    exact (V22ParameterBatch.banks_base_other machines targets (prepared bits n k)
      (MatrixUnaryArithmetic.encodeInput n k) (results n k) (times n k) 19 b
      (fun i hi => h' i hi.symm)).trans (outside_expected bits n k b h')

theorem constructor_projection (bits : List Bool) (n k : ℕ) :
    (fun j : Constructor => final bits n k (.inl (.inl j)))=constructorInput n k := by
  funext j
  exact final_base bits n k (.inl j)
theorem graph_preserved (bits : List Bool) (n k : ℕ) :
    final bits n k (.inl graphPort)=bits := final_base bits n k graphPort
theorem k_preserved (bits : List Bool) (n k : ℕ) :
    final bits n k (.inl kPort)=List.replicate k true := final_base bits n k kPort
theorem precision_exact (bits : List Bool) (n k : ℕ) :
    final bits n k (.inl precisionPort)=List.replicate
      (CurrentAdditive.V38OneStep.publicBits (fullAlphabet n (Nat.clog 2 n))
        (2^fullDrawExponent (Nat.clog 2 n) k)) true := by
  simpa only [precisionPort,expected,reduceIte,eval_precision] using final_base bits n k precisionPort

#print axioms run
#print axioms constructor_projection
#print axioms precision_exact
end V22FullScheduleBatch
