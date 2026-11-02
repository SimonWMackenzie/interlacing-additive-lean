import EthInapproximability.CurrentPaper.MatrixStage4RowGraphMachine

/-!
# Segment 2: the exact per-address seed of the admitted item branch

Lane owner:b-stage4-entry-program-3 (Paper B, unit 2, map item 3).

`item_seed` states, cell by cell, the WHOLE start bank of the admitted
`MatrixStage4RowGraphMachine.item_graph_run`, i.e.
`rowFrame (graphSeed hs vectors R code i x out) (itemRowInput order i x)`.
Exactly 22 of its 89 cells are non-blank. It contains NO item index `i`, NO
source row `x`, NO `activeRank`, NO first-bin coordinate and NO vector bit:
those are computed by the admitted row, alignment and vector phases. The
only address words are the unary column code (cell 19) and the unary raw
row ordinal `rowCode … (inr (i, x))` (cell 79); cell 48 is the output
accumulator `out` (blank for one entry). The other nineteen are common
operand words: `binBase`, `wordBase`, `s - 1`, `binBase^s` (twice), `cy^(s+1)`,
`[true]` (twice), `cy` (three times), `rowMajor R`, `s` (twice), `q`,
`rowMajor vectors` (segment 1's table), `s*L`, `L`, `rx`.

A specification of what a physical per-address seeding program must
produce; no machine is claimed here.
-/

set_option maxRecDepth 16384

namespace EthInapproximability.CurrentPaper.ItemSeed

open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

def seed (binB wordB sM1 binPowS codeV cyPow1 cyV : ℕ) (Rtable out : List Bool)
    (sV qV : ℕ) (vtable : List Bool) (rowV sL LV rxV : ℕ) : Fin 89 → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (Function.update (Function.update (Function.update
  (Function.update (Function.update (fun _ => [])
    1 (List.replicate binB true))
    6 (List.replicate wordB true))
    13 (List.replicate sM1 true))
    16 (List.replicate binPowS true))
    19 (List.replicate codeV true))
    22 (List.replicate cyPow1 true))
    23 [true])
    24 (List.replicate cyV true))
    25 [true])
    37 (List.replicate binPowS true))
    43 (List.replicate cyV true))
    47 Rtable)
    48 out)
    51 (List.replicate cyV true))
    56 (List.replicate sV true))
    62 (List.replicate sV true))
    63 (List.replicate qV true))
    68 vtable)
    79 (List.replicate rowV true))
    80 (List.replicate sL true))
    83 (List.replicate LV true))
    84 (List.replicate rxV true)

theorem item_seed {a s q L nv nb rx cy : ℕ} (hs : 0 < s)
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin (nv + nb)) (x : Fin rx)
    (out : List Bool) :
    (MatrixStage4RowGraphMachine.rowFrame
      (MatrixStage4RowGraphMachine.graphSeed hs vectors R code i x out)
      (MatrixStage4RowGraphMachine.itemRowInput (s := s) (L := L) order i x)).stk =
      seed (binBase a s q cy) (wordBase a s cy) (s - 1) (binBase a s q cy ^ s) code.val
        (cy ^ (s + 1)) cy (rowMajor R) out s q (rowMajor vectors)
        (rowCode s L nv nb rx order ((rawRowEquiv s L nv nb order).symm (.inr (i, x)))).val
        (s * L) L rx := by
  funext k
  fin_cases k <;> rfl

#print axioms item_seed

end EthInapproximability.CurrentPaper.ItemSeed
