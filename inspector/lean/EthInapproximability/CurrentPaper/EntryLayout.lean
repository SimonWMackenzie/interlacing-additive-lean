import EthInapproximability.CurrentPaper.MultiMove
import EthInapproximability.CurrentPaper.TemplateSeed
import EthInapproximability.CurrentPaper.ItemSeed
import EthInapproximability.CurrentPaper.EntryStride
import EthInapproximability.CurrentPaper.MatrixUnaryDivision

/-!
# Segment 2: the physical layout of the per-address entry program

Lane owner:b-stage4-entry-program-4 (Paper B, unit 2, map item 3).

One fixed bank type `ES` for the per-address entry program:
- `cw i` (`Fin 19`): the COMMON operand words, fixed for the whole table
  (they belong to the fixed `EntryRuns` bank; producing them from the level
  is the bank-preparation step, not a per-address step);
- `xc`, `yc`, `ac`: the unary row index, unary column index and the answer
  cell (the three `MatrixTableWriter` index/answer cells);
- `tc k` (`TemplateSeed.TStack`): the template branch region;
- `ic k` (`Fin 89`): the item branch region;
- `dc k` (`Fin 6`): the unary division region;
- `sc k` (`EntryStride.SK`): the stride region;
- `scr k` (`Fin 8`): scratch (`scr 0` is the move temporary).

Common words, in order: `binBase`, `wordBase`, `binBase^s`, `q`, `qOne a`,
first family table, `[true]`, `cy`, `firstLength a s - 1`,
`cy^(firstLength a s)`, `rx`, row family table, `rowMajor R`, `s`, `s - 1`,
`cy^(s+1)`, `rowMajor vectors`, `s*L`, `L`.
-/

namespace EthInapproximability.CurrentPaper.EntryLayout

abbrev TS := TemplateSeed.TStack
abbrev ES := Fin 19 ⊕ (Fin 3 ⊕ (TS ⊕ (Fin 89 ⊕ (Fin 6 ⊕ (EntryStride.SK ⊕ Fin 8)))))

instance instDecES : DecidableEq ES :=
  @instDecidableEqSum _ _ inferInstance
    (@instDecidableEqSum _ _ inferInstance
      (@instDecidableEqSum _ _ inferInstance
        (@instDecidableEqSum _ _ inferInstance
          (@instDecidableEqSum _ _ inferInstance
            (@instDecidableEqSum _ _ inferInstance inferInstance)))))

/-- The numeric and table common words (values, not machines). -/
structure Words where
  binB : ℕ
  wordB : ℕ
  binPowS : ℕ
  q : ℕ
  qOne : ℕ
  firstTable : List Bool
  cy : ℕ
  firstExp : ℕ
  cyPowF : ℕ
  rx : ℕ
  rowTable : List Bool
  Rtable : List Bool
  s : ℕ
  sM1 : ℕ
  cyPow1 : ℕ
  vtable : List Bool
  sL : ℕ
  L : ℕ

def rep (n : ℕ) : List Bool := List.replicate n true

def common (w : Words) : Fin 19 → List Bool :=
  ![rep w.binB, rep w.wordB, rep w.binPowS, rep w.q, rep w.qOne, w.firstTable, [true],
    rep w.cy, rep w.firstExp, rep w.cyPowF, rep w.rx, w.rowTable, w.Rtable, rep w.s,
    rep w.sM1, rep w.cyPow1, w.vtable, rep w.sL, rep w.L]

def cw (i : Fin 19) : ES := .inl i
def xc : ES := .inr (.inl 0)
def yc : ES := .inr (.inl 1)
def ac : ES := .inr (.inl 2)
def tc (k : TS) : ES := .inr (.inr (.inl k))
def ic (k : Fin 89) : ES := .inr (.inr (.inr (.inl k)))
def dc (k : Fin 6) : ES := .inr (.inr (.inr (.inr (.inl k))))
def sc (k : EntryStride.SK) : ES := .inr (.inr (.inr (.inr (.inr (.inl k)))))
def scr (k : Fin 8) : ES := .inr (.inr (.inr (.inr (.inr (.inr k)))))
def temp : ES := scr 0

/-- The per-address start bank: common words, unary `x`, unary `y`, blank
answer, every region blank. -/
def start (w : Words) (x y : ℕ) (ans : List Bool) : ES → List Bool :=
  Sum.elim (common w) (Sum.elim ![rep x, rep y, ans] (fun _ => []))

end EthInapproximability.CurrentPaper.EntryLayout
