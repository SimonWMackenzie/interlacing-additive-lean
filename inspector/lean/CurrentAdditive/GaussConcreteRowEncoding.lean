import CurrentAdditive.GaussConcreteRow
import CurrentAdditive.GaussNestedFraming64

namespace CurrentAdditive.GaussConcreteRowEncoding

open EthInapproximability.CurrentPaper
open GaussConcreteCellEntry

theorem rowWord_eq (entry : Nat → Nat → List Bool) (x y n : Nat) :
    GaussWordRowTraversal.rowWord entry x y n =
      GaussWordGridTraversal.rowWord entry x y n := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => simp only [GaussWordRowTraversal.rowWord,GaussWordGridTraversal.rowWord,ih]

theorem rowBits_exact {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c : Fin k) :
    GaussConcreteRow.rowBits B r pivot c i.val =
      SourceListEncoding.encode (GaussTypedGetterBridge.cellWords
        (SequentialTotality.clearTyped (SequentialTotality.swapTyped B r pivot) r c) i) := by
  let C := SequentialTotality.clearTyped (SequentialTotality.swapTyped B r pivot) r c
  have h := GaussWordGridTraversal.rowWord_finite (value B r pivot c) i.val 0 k
    (fun j => V2FieldContext.field (GaussFramedCell.answer B r pivot i c j))
    (by intro j; simp [value,i.isLt,j.isLt])
  rw [GaussConcreteRow.rowBits,rowWord_eq,h]
  simp [C,SourceListEncoding.encode,GaussTypedGetterBridge.cellWords,
    GaussNestedFraming64.fields_eq_flatMap,GaussNestedFraming64.frameWord,
    SourceListMachineWriter.result,V2FieldContext.field,GaussFramedCell.answer,List.flatMap_map]

theorem physical_row {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r pivot i : Fin m) (c : Fin k) (hn : B pivot c≠0) :
    ∃ t : Nat, ((BitMachineEncoding.advance GaussConcreteRow.program)^[t])
      (⟨some GaussConcreteRow.start,GaussConcreteRow.control,
        (GaussConcreteRow.initialData B r pivot i c).contents⟩ :
          Turing.TM2.Cfg (fun _ : GaussConcreteRow.Stack => Bool)
            GaussConcreteRow.Label GaussConcreteRow.Control) =
      ⟨none,GaussConcreteRow.control,
        Function.update (GaussConcreteRow.initialData B r pivot i c).contents
          (.inr .output)
          (V2FieldContext.field (SourceListEncoding.encode (GaussTypedGetterBridge.cellWords
            (SequentialTotality.clearTyped (SequentialTotality.swapTyped B r pivot) r c) i)))⟩ := by
  simpa only [rowBits_exact] using GaussConcreteRow.physical_row B r pivot i c hn

#print axioms rowBits_exact
#print axioms physical_row
end CurrentAdditive.GaussConcreteRowEncoding
