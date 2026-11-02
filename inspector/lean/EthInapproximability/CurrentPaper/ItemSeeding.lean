import EthInapproximability.CurrentPaper.EntryLayout
import EthInapproximability.CurrentPaper.CopyFill

/-!
# Segment 2 (item branch): the physical per-address seeding program

Lane owner:b-stage4-entry-program-4 (Paper B, unit 2, map item 3).

ONE fixed `MultiMove` program (sixteen source-preserving charged copies)
from the per-address start bank (`EntryLayout.start`: common words, unary
row index `x`, unary column index `y`, answer cell `ans`, all regions blank)
to the bank whose item region is EXACTLY the checked item seed
`ItemSeed.seed` with column code `y` (cell 19), raw row ordinal `x`
(cell 79), blank output accumulator (cell 48) and the common words at
their admitted cells; every other cell (common words, `x`, `y`, `ans`, the
other regions, the temporary) equals the start bank.
-/

set_option maxRecDepth 16384

namespace EthInapproximability.CurrentPaper.ItemSeeding

open EntryLayout CopyFill

/-- The sixteen copy jobs `(source, destinations)`. -/
def jobs : List (ES × List ES) :=
  [(cw 0, [ic 1]), (cw 1, [ic 6]), (cw 14, [ic 13]), (cw 2, [ic 16, ic 37]),
   (yc, [ic 19]), (cw 15, [ic 22]), (cw 6, [ic 23, ic 25]), (cw 7, [ic 24, ic 43, ic 51]),
   (cw 12, [ic 47]), (cw 13, [ic 56, ic 62]), (cw 3, [ic 63]), (cw 16, [ic 68]),
   (xc, [ic 79]), (cw 17, [ic 80]), (cw 18, [ic 83]), (cw 10, [ic 84])]

/-- The single fixed seeding program. -/
def program := MultiMove.program (jobs.map toJob) temp

/-- Bank after seeding: the start bank with the item region replaced by the
exact item seed. -/
def seeded (w : Words) (x y : ℕ) (ans : List Bool) : ES → List Bool :=
  Sum.elim (common w) (Sum.elim ![rep x, rep y, ans] (Sum.elim (fun _ => [])
    (Sum.elim (ItemSeed.seed w.binB w.wordB w.sM1 w.binPowS y w.cyPow1 w.cy w.Rtable []
      w.s w.q w.vtable x w.sL w.L w.rx) (fun _ => []))))

theorem good : Good temp jobs where
  src_not_dst := by
    simp [jobs, cw, ic, xc, yc]
  dst_nodup := by
    simp [jobs, ic]
  src_temp := by
    simp [jobs, cw, xc, yc, temp, scr]
  temp_dst := by
    simp [jobs, ic, temp, scr]

theorem blank (w : Words) (x y : ℕ) (ans : List Bool) :
    ∀ j ∈ jobs, ∀ d ∈ j.2, start w x y ans d = [] := by
  simp [jobs, ic, start]

theorem fill_eq (w : Words) (x y : ℕ) (ans : List Bool) :
    fill jobs (start w x y ans) = seeded w x y ans := by
  funext k
  rcases k with k | k | k | k | k
  · fin_cases k <;> rfl
  · fin_cases k <;> rfl
  · rfl
  · fin_cases k <;> rfl
  · rfl

/-- Exact step count of the sixteen copies (each `2 * |word| + 2`). -/
def seedCost (w : Words) (x y : ℕ) : ℕ :=
  (2 * w.binB + 2) + (2 * w.wordB + 2) + (2 * w.sM1 + 2) + (2 * w.binPowS + 2) +
  (2 * y + 2) + (2 * w.cyPow1 + 2) + (2 * 1 + 2) + (2 * w.cy + 2) +
  (2 * w.Rtable.length + 2) + (2 * w.s + 2) + (2 * w.q + 2) + (2 * w.vtable.length + 2) +
  (2 * x + 2) + (2 * w.sL + 2) + (2 * w.L + 2) + (2 * w.rx + 2)

theorem cost_eq (w : Words) (x y : ℕ) (ans : List Bool) :
    fillCost jobs (start w x y ans) = seedCost w x y := by
  simp [fillCost, jobs, start, common, cw, xc, yc, rep, seedCost]
  omega

/-- The item seeding run: one fixed program, exact exit bank, exact time. -/
theorem item_seeding (w : Words) (x y : ℕ) (ans : List Bool) :
    ((BitMachineEncoding.advance program)^[seedCost w x y + 1])
      (⟨some (MultiMove.startLabel (jobs.map toJob)), MultiMove.initial, start w x y ans⟩ :
        Turing.TM2.Cfg (fun _ : ES => Bool) (MultiMove.Label (jobs.map toJob).length)
          MultiMove.Control) =
      ⟨none, MultiMove.initial, seeded w x y ans⟩ := by
  have h := CopyFill.run temp jobs good (start w x y ans) rfl (blank w x y ans)
  rw [fill_eq, cost_eq] at h
  exact h

#print axioms good
#print axioms fill_eq
#print axioms cost_eq
#print axioms item_seeding

end EthInapproximability.CurrentPaper.ItemSeeding
