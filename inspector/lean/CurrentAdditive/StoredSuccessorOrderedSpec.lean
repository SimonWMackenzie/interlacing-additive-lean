import CurrentAdditive.StoredWeightedNumbered
import Mathlib.Data.List.OfFn

namespace CurrentAdditive.StoredSuccessorOrderedSpec

open Paper2
open EthInapproximability.CurrentPaper
open CurrentAdditive.V39GeneratedConstruction

theorem ofFn_product {α : Type*} {m n : ℕ} (f : Fin m × Fin n → α) :
    List.ofFn (fun k : Fin (m*n) => f (finProdFinEquiv.symm k))=
      (List.ofFn (fun i : Fin m => List.ofFn (fun j : Fin n => f (i,j)))).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hk : (⟨i.val*n+j.val,by have:=i.isLt;have:=j.isLt;nlinarith⟩ : Fin (m*n))=
      finProdFinEquiv (i,j) := by
    apply Fin.ext
    simp [finProdFinEquiv_apply_val,Nat.mul_comm,Nat.add_comm]
  rw [hk,Equiv.symm_apply_apply]

theorem ofFn_four {α : Type*} {a b c d : ℕ}
    (f : Fin a → Fin b → Fin c → Fin d → α) :
    List.ofFn (fun k : Fin (a*(b*(c*d))) =>
      let x:=finProdFinEquiv.symm k
      let y:=finProdFinEquiv.symm x.2
      let z:=finProdFinEquiv.symm y.2
      f x.1 y.1 z.1 z.2)=
    (List.ofFn (fun i : Fin a =>
      (List.ofFn (fun j : Fin b =>
        (List.ofFn (fun k : Fin c => List.ofFn (fun l : Fin d => f i j k l))).flatten)).flatten)).flatten := by
  rw [ofFn_product (fun x : Fin a × Fin (b*(c*d)) =>
    let y:=finProdFinEquiv.symm x.2
    let z:=finProdFinEquiv.symm y.2
    f x.1 y.1 z.1 z.2)]
  congr 1
  apply congrArg List.ofFn
  funext i
  rw [ofFn_product (fun y : Fin b × Fin (c*d) =>
    let z:=finProdFinEquiv.symm y.2
    f i y.1 z.1 z.2)]
  congr 1
  apply congrArg List.ofFn
  funext j
  exact ofFn_product (fun z => f i j z.1 z.2)

section Successor

variable {D q₁ q₂ s w Q nx ny ni : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  {μI : PositiveRationalLaw (Fin ni)}
  (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (st : src.Streams (w := w) (μI := μI))
  (out : ExactList D Q (Fin w × src.Column) (product (uniform w) src.columnLaw))

def rowWord (R : Fin nx → Fin ny → Bool) (activity : Fin ni → Fin q₂ → Option (Fin s))
    (r : Fin out.size) : List Bool :=
  (List.ofFn (fun p : Fin Q =>
    (List.ofFn (fun m : Fin st.metadata.size =>
      (List.ofFn (fun b : Fin st.base.size =>
        List.ofFn (fun z : Fin st.selector.size => src.successor st out R activity r (p,(m,(b,z)))))).flatten)).flatten)).flatten

theorem rowWord_numbered (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (r : Fin out.size) :
    List.ofFn (src.numberedEntry st out R activity r)=rowWord src st out R activity r := by
  exact ofFn_four (fun p m b z => src.successor st out R activity r (p,(m,(b,z))))

def cells (R : Fin nx → Fin ny → Bool) (activity : Fin ni → Fin q₂ → Option (Fin s)) : List Bool :=
  (List.ofFn (fun r : Fin out.size => rowWord src st out R activity r)).flatten

theorem cells_rowMajor (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s)) :
    cells src st out R activity=MatrixMaterialization.rowMajor (src.numberedEntry st out R activity) := by
  unfold MatrixMaterialization.rowMajor
  rw [ofFn_product (fun rc : Fin out.size ×
      Fin (Q*(st.metadata.size*(st.base.size*st.selector.size))) =>
    src.numberedEntry st out R activity rc.1 rc.2)]
  unfold cells
  congr 1
  apply congrArg List.ofFn
  funext r
  exact (rowWord_numbered src st out R activity r).symm

end Successor
end CurrentAdditive.StoredSuccessorOrderedSpec

#print axioms CurrentAdditive.StoredSuccessorOrderedSpec.cells_rowMajor
