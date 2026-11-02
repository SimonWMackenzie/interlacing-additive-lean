import CurrentAdditive.D22GeneratedTerms
import CurrentAdditive.V39PublicGeneratedSchedule

/-! Agreed deterministic post-search ABI. The input contains the unchanged
encoded graph and already computed n,m,selected L,K. No generated widths,
repetition, item law or activity table is an initial input field. -/
namespace D22PostSearchPacket
open EthInapproximability.CurrentPaper
open CurrentAdditive V39GeneratedConstruction V38Schedule
open D22PolynomialExpression
noncomputable section

def rawWords (graph : List Bool) (n m L K : ℕ) : Fin 5 → List Bool :=
  ![graph,List.replicate n true,List.replicate m true,List.replicate L true,List.replicate K true]
def input (graph : List Bool) (n m L K : ℕ) := BitMachineBankCodec.encode (rawWords graph n m L K)
def ni (n L : ℕ) := 4*generatedS L*(n+(generatedS L-3))
def values (n m L : ℕ) : Fin 7 → ℕ :=
  ![generatedQ₁ L,generatedQ₂ L,generatedS L,generatedW L,generatedQ L,publicRepetition L m,ni n L]
def words (graph : List Bool) (n m L K : ℕ) : Fin 12 → List Bool :=
  ![graph,List.replicate n true,List.replicate m true,List.replicate L true,List.replicate K true,
    List.replicate (generatedQ₁ L) true,List.replicate (generatedQ₂ L) true,
    List.replicate (generatedS L) true,List.replicate (generatedW L) true,List.replicate (generatedQ L) true,
    List.replicate (publicRepetition L m) true,List.replicate (ni n L) true]
def output (graph : List Bool) (n m L K : ℕ) := BitMachineBankCodec.encode (words graph n m L K)

def withSourceWords (graph : List Bool) (n m L K : ℕ) (law activity : List Bool) : Fin 14 → List Bool :=
  ![graph,List.replicate n true,List.replicate m true,List.replicate L true,List.replicate K true,
    List.replicate (generatedQ₁ L) true,List.replicate (generatedQ₂ L) true,
    List.replicate (generatedS L) true,List.replicate (generatedW L) true,List.replicate (generatedQ L) true,
    List.replicate (publicRepetition L m) true,List.replicate (ni n L) true,law,activity]
def withSource (graph : List Bool) (n m L K : ℕ) (law activity : List Bool) :=
  BitMachineBankCodec.encode (withSourceWords graph n m L K law activity)
def stepContext (L : ℕ) (law activity : List Bool) := BitMachineBankCodec.encode
  ![List.replicate (generatedQ₁ L) true,List.replicate (generatedQ₂ L) true,
    List.replicate (generatedS L) true,List.replicate (generatedW L) true,List.replicate (generatedQ L) true,
    law,activity]
def envelope (L K : ℕ) (law activity : List Bool) := BitMachineBankCodec.encode
  ![List.replicate L true,List.replicate K true,stepContext L law activity]

open D22GeneratedTerms in
def repetitionTerm : Term := quot q2 (.powCeil (mul (mul (.const 4) s) (.var 1)))
open D22GeneratedTerms in
def niTerm : Term := mul (mul (.const 4) s) (add (.var 0) (.pred (.pred (.pred s))))
def terms : Fin 7 → Term :=
  ![D22GeneratedTerms.q1,D22GeneratedTerms.q2,D22GeneratedTerms.s,D22GeneratedTerms.w,
    D22GeneratedTerms.Q,repetitionTerm,niTerm]

theorem eval_repetitionTerm (n m L : ℕ) : repetitionTerm.eval n m L=publicRepetition L m := by
  simp [repetitionTerm,publicRepetition,paddedSourceWidth,D22NatExpression.values]
theorem eval_niTerm (n m L : ℕ) : niTerm.eval n m L=ni n L := by
  simp only [niTerm,D22GeneratedTerms.eval_mul,D22GeneratedTerms.eval_add,
    D22GeneratedTerms.eval_const,D22GeneratedTerms.eval_s,D22GeneratedTerms.eval_var,
    D22GeneratedTerms.eval_pred]
  change 4*generatedS L*(n+((generatedS L-1)-1-1))=ni n L
  have h : (generatedS L-1)-1-1=generatedS L-3 := by omega
  rw [h]
  rfl
theorem terms_eval (n m L : ℕ) (i : Fin 7) : (terms i).eval n m L=values n m L i := by
  fin_cases i <;> simp [terms,values,eval_repetitionTerm,eval_niTerm]

#print axioms terms_eval
end
end D22PostSearchPacket
