import EthInapproximability.CurrentPaper.MatrixStage4TemplateBitMachine

/-!
# Segment 2: the exact per-address seed of the admitted template branch

Lane owner:b-stage4-entry-program-3 (Paper B, unit 2, map item 3).

`template_seed` states, cell by cell, the WHOLE start bank of the admitted
`MatrixStage4TemplateBitMachine.actualSource R family code p ell` (the
configuration consumed by the admitted `actual_raw_template`). Exactly 21 of
its cells are non-blank. Only three words depend on the address: the unary
column code, the stride `binBase^(s-1-p)` (producible by `EntryStride`), and
the unary `ell`. The other eighteen are common operand words of the level:
`binBase^s`, `binBase`, `wordBase`, `q`, `qOne a` (twice), the two one-hot
family tables, `[true]` (twice), `cy` (three times), `firstLength a s - 1`,
`cy^(firstLength a s)`, `rx` (twice), and `rowMajor R`.

This is a specification of what a physical per-address seeding program must
produce; no machine is claimed here.
-/

namespace EthInapproximability.CurrentPaper.TemplateSeed

open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

abbrev TStack := MatrixStage4TemplateBitMachine.Stack

/-- The eighteen common words and the three address words, placed in their
admitted cells; every other cell blank. -/
def seed (codeV strideV ellV : ℕ)
    (binPowS binB wordB qV qOneV : ℕ) (firstTable : List Bool)
    (cyV firstExp cyPow rxV : ℕ) (rowTable Rtable : List Bool) : TStack → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (fun _ => [])
    (.inl (.inl (.inl (.inl (.inl (.inl (.inl 0))))))) (List.replicate codeV true))
    (.inl (.inl (.inl (.inl (.inl (.inl (.inl 1))))))) (List.replicate binPowS true))
    (.inl (.inl (.inl (.inl (.inl (.inl (.inl 2))))))) (List.replicate strideV true))
    (.inl (.inl (.inl (.inl (.inl (.inl (.inl 3))))))) (List.replicate binB true))
    (.inl (.inl (.inl (.inl (.inl (.inl (.inl 4))))))) (List.replicate wordB true))
    (.inl (.inl (.inl (.inl (.inl (.inl (.inr 0))))))) (List.replicate ellV true))
    (.inl (.inl (.inl (.inl (.inl (.inl (.inr 1))))))) (List.replicate qV true))
    (.inl (.inl (.inl (.inl (.inl (.inr 0)))))) (List.replicate qOneV true))
    (.inl (.inl (.inl (.inl (.inr 0))))) firstTable)
    (.inl (.inl (.inl (.inl (.inr 2))))) (List.replicate qOneV true))
    (.inl (.inl (.inr 0))) [true])
    (.inl (.inl (.inr 1))) (List.replicate cyV true))
    (.inl (.inl (.inr 6))) (List.replicate firstExp true))
    (.inl (.inl (.inr 10))) (List.replicate cyPow true))
    (.inl (.inl (.inr 11))) (List.replicate cyV true))
    (.inl (.inl (.inr 12))) [true])
    (.inl (.inr (.inl (.inl (.inr 0))))) (List.replicate rxV true))
    (.inl (.inr (.inl (.inr 0)))) rowTable)
    (.inl (.inr (.inl (.inr 2)))) (List.replicate rxV true))
    (.inr 0) (List.replicate cyV true))
    (.inr 4) Rtable

theorem template_seed {a s q L rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool)
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    (MatrixStage4TemplateBitMachine.actualSource R family code p ell).stk =
      seed code.val (binBase a s q cy ^ (s - 1 - p.val)) ell.val
        (binBase a s q cy ^ s) (binBase a s q cy) (wordBase a s cy) q (qOne a)
        (MatrixStage4FamilyData.fieldTable (MatrixStage4FamilyData.familyFirst family))
        cy (firstLength a s - 1) (cy ^ firstLength a s) rx
        (MatrixStage4FamilyData.fieldTable (MatrixStage4FamilyData.familyRow family))
        (rowMajor R) := by
  funext k
  fin_cases k <;> rfl

#print axioms template_seed

end EthInapproximability.CurrentPaper.TemplateSeed
