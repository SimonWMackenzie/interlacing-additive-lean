import Paper2.ScanDecodeMachine

/-! Unit 3, segment (1): the physical group-and-padding test of
`SourceActiveRank.scanAtCanonical` (value target `ScanCoordDecode.scan_none`:
the scan is `none` unless `0 < m ∧ a / r / 3 / m = ig`).

ONE fixed program `prog` on the `ScanDecodeMachine` bank: a non-destructive
peek of unary `m` (cell 2; the popped mark is pushed back), then a lockstep
comparison of unary `g` (cell 7) with the unary item group `ig` (cell 12),
clearing both, and one pushed answer bit in cell 13:
`decide (0 < m ∧ g = ig)`. Every popped cell, test and push is a charged
step. -/

namespace Paper2.ScanSelect

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.ScanDecodeMachine (K u)

inductive SLabel where
  | peek | cmp | clrG | clrI
  deriving DecidableEq

abbrev Ctl := Option Bool × Option Bool

/-! Cells (literal): `g` = 7, `ig` = 12, `m` = 2, answer = 13. -/

def prog : SLabel → TM2.Stmt (fun _ : K => Bool) SLabel Ctl
  | .peek => pop (2 : K) (fun v b => (b, v.2))
      (branch (fun v => v.1.isSome) (push (2 : K) (fun _ => true) (goto (fun _ => .cmp)))
        (goto (fun _ => .clrG)))
  | .cmp => pop (7 : K) (fun v b => (b, v.2)) (pop (12 : K) (fun v b => (v.1, b))
      (branch (fun v => v.1.isSome && v.2.isSome) (goto (fun _ => .cmp))
        (branch (fun v => v.1.isNone && v.2.isNone) (push (13 : K) (fun _ => true) halt)
          (goto (fun _ => .clrG)))))
  | .clrG => pop (7 : K) (fun v b => (b, v.2))
      (branch (fun v => v.1.isSome) (goto (fun _ => .clrG)) (goto (fun _ => .clrI)))
  | .clrI => pop (12 : K) (fun v b => (v.1, b))
      (branch (fun v => v.2.isSome) (goto (fun _ => .clrI)) (push (13 : K) (fun _ => false) halt))

/-- Exit bank: `g`, `ig` cleared, the answer bit pushed on cell 13. -/
def F (S : K → List Bool) (b : Bool) : K → List Bool :=
  Function.update (Function.update (Function.update S (7 : K) []) (12 : K) []) (13 : K) (b :: S (13 : K))

theorem iter_trans {α : Type*} {f : α → α} {a b c : α} {m n : ℕ}
    (h1 : f^[m] a = b) (h2 : f^[n] b = c) : f^[n + m] a = c := by
  rw [Function.iterate_add_apply, h1, h2]

theorem u_succ (k : ℕ) : u (k + 1) = true :: u k := rfl

/-! ### Single steps -/

theorem step_clrG_cons (S : K → List Bool) (v : Ctl) (x : List Bool) (h : S (7 : K) = true :: x) :
    advance prog (⟨some .clrG, v, S⟩ : TM2.Cfg (fun _ : K => Bool) SLabel Ctl) =
      ⟨some .clrG, (some true, v.2), Function.update S (7 : K) x⟩ := by
  simp [advance, TM2.step, TM2.stepAux, prog, h]

theorem step_clrG_nil (S : K → List Bool) (v : Ctl) (h : S (7 : K) = []) :
    advance prog (⟨some .clrG, v, S⟩ : TM2.Cfg (fun _ : K => Bool) SLabel Ctl) =
      ⟨some .clrI, (none, v.2), Function.update S (7 : K) []⟩ := by
  simp [advance, TM2.step, TM2.stepAux, prog, h]

theorem step_clrI_cons (S : K → List Bool) (v : Ctl) (x : List Bool) (h : S (12 : K) = true :: x) :
    advance prog (⟨some .clrI, v, S⟩ : TM2.Cfg (fun _ : K => Bool) SLabel Ctl) =
      ⟨some .clrI, (v.1, some true), Function.update S (12 : K) x⟩ := by
  simp [advance, TM2.step, TM2.stepAux, prog, h]

theorem step_clrI_nil (S : K → List Bool) (v : Ctl) (h : S (12 : K) = []) :
    advance prog (⟨some .clrI, v, S⟩ : TM2.Cfg (fun _ : K => Bool) SLabel Ctl) =
      ⟨none, (v.1, none), Function.update (Function.update S (12 : K) []) (13 : K) (false :: S (13 : K))⟩ := by
  simp [advance, TM2.step, TM2.stepAux, prog, h]

/-! ### Clearing loops -/

theorem clrG_run : ∀ (j : ℕ) (S : K → List Bool) (v : Ctl), S (7 : K) = u j →
    (advance prog)^[j + 1] (⟨some .clrG, v, S⟩ : TM2.Cfg (fun _ : K => Bool) SLabel Ctl) =
      ⟨some .clrI, (none, v.2), Function.update S (7 : K) []⟩
  | 0, S, v, h => by
      rw [Function.iterate_one]
      exact step_clrG_nil S v h
  | j + 1, S, v, h => by
      rw [Function.iterate_succ_apply, step_clrG_cons S v (u j) h,
        clrG_run j _ _ (by simp [u])]
      simp

theorem clrI_run : ∀ (j : ℕ) (S : K → List Bool) (v : Ctl), S (12 : K) = u j →
    (advance prog)^[j + 1] (⟨some .clrI, v, S⟩ : TM2.Cfg (fun _ : K => Bool) SLabel Ctl) =
      ⟨none, (v.1, none), Function.update (Function.update S (12 : K) []) (13 : K) (false :: S (13 : K))⟩
  | 0, S, v, h => by
      rw [Function.iterate_one]
      exact step_clrI_nil S v h
  | j + 1, S, v, h => by
      rw [Function.iterate_succ_apply, step_clrI_cons S v (u j) h,
        clrI_run j _ _ (by simp [u])]
      simp

/-! ### Comparison loop -/

theorem cmp_run : ∀ (g ig : ℕ) (S : K → List Bool) (v : Ctl), S (7 : K) = u g → S (12 : K) = u ig →
    ∃ t ≤ g + ig + 3, ∃ c,
      (advance prog)^[t] (⟨some .cmp, v, S⟩ : TM2.Cfg (fun _ : K => Bool) SLabel Ctl) =
        ⟨none, c, F S (decide (g = ig))⟩
  | 0, 0, S, v, hg, hi => by
      refine ⟨1, by omega, (none, none), ?_⟩
      rw [Function.iterate_one]
      have hg' : S (7 : K) = [] := hg
      have hi' : S (12 : K) = [] := hi
      simp [advance, TM2.step, TM2.stepAux, prog, F, hg', hi']
  | 0, j + 1, S, v, hg, hi => by
      have hg' : S (7 : K) = [] := hg
      have hs : advance prog (⟨some .cmp, v, S⟩ : TM2.Cfg (fun _ : K => Bool) SLabel Ctl) =
          ⟨some .clrG, (none, some true),
            Function.update (Function.update S (7 : K) []) (12 : K) (u j)⟩ := by
        rw [u_succ] at hi
        simp [advance, TM2.step, TM2.stepAux, prog, hg', hi]
      have h1 := clrG_run 0 (Function.update (Function.update S (7 : K) []) (12 : K) (u j))
        (none, some true) (by simp [u])
      have h2 := clrI_run j
        (Function.update (Function.update (Function.update S (7 : K) []) (12 : K) (u j)) (7 : K) [])
        ((none : Option Bool), (some true : Option Bool)) (by simp [u])
      refine ⟨(j + 1) + ((0 + 1) + 1), by omega, ((none : Option Bool), (none : Option Bool)), ?_⟩
      refine iter_trans (iter_trans (by rw [Function.iterate_one]; exact hs) h1) (h2.trans ?_)
      congr 1
      funext x
      simp only [F, Function.update_apply]
      by_cases h13 : x = (13 : K) <;> by_cases h12 : x = (12 : K) <;> by_cases h7 : x = (7 : K) <;>
        simp_all
  | g + 1, 0, S, v, hg, hi => by
      have hi' : S (12 : K) = [] := hi
      have hs : advance prog (⟨some .cmp, v, S⟩ : TM2.Cfg (fun _ : K => Bool) SLabel Ctl) =
          ⟨some .clrG, (some true, none),
            Function.update (Function.update S (7 : K) (u g)) (12 : K) []⟩ := by
        rw [u_succ] at hg
        simp [advance, TM2.step, TM2.stepAux, prog, hg, hi']
      have h1 := clrG_run g (Function.update (Function.update S (7 : K) (u g)) (12 : K) [])
        (some true, none) (by simp [u])
      have h2 := clrI_run 0
        (Function.update (Function.update (Function.update S (7 : K) (u g)) (12 : K) []) (7 : K) [])
        ((none : Option Bool), (none : Option Bool)) (by simp [u])
      refine ⟨(0 + 1) + ((g + 1) + 1), by omega, ((none : Option Bool), (none : Option Bool)), ?_⟩
      refine iter_trans (iter_trans (by rw [Function.iterate_one]; exact hs) h1) (h2.trans ?_)
      congr 1
      funext x
      simp only [F, Function.update_apply]
      by_cases h13 : x = (13 : K) <;> by_cases h12 : x = (12 : K) <;> by_cases h7 : x = (7 : K) <;>
        simp_all
  | g + 1, j + 1, S, v, hg, hi => by
      have hs : advance prog (⟨some .cmp, v, S⟩ : TM2.Cfg (fun _ : K => Bool) SLabel Ctl) =
          ⟨some .cmp, (some true, some true),
            Function.update (Function.update S (7 : K) (u g)) (12 : K) (u j)⟩ := by
        rw [u_succ] at hg hi
        simp [advance, TM2.step, TM2.stepAux, prog, hg, hi]
      obtain ⟨t, ht, c, hr⟩ := cmp_run g j (Function.update (Function.update S (7 : K) (u g)) (12 : K) (u j))
        (some true, some true) (by simp [u]) (by simp [u])
      refine ⟨t + 1, by omega, c, ?_⟩
      refine iter_trans (by rw [Function.iterate_one]; exact hs) (hr.trans ?_)
      congr 1
      funext x
      simp only [F, Function.update_apply]
      by_cases h13 : x = (13 : K) <;> by_cases h12 : x = (12 : K) <;> by_cases h7 : x = (7 : K) <;>
        simp_all

/-- The test: non-destructive peek of `m`, then compare and clear. -/
theorem select_run (g ig m : ℕ) (S : K → List Bool) (v : Ctl)
    (hg : S (7 : K) = u g) (hi : S (12 : K) = u ig) (hm : S (2 : K) = u m) :
    ∃ t ≤ g + ig + 4, ∃ c,
      (advance prog)^[t] (⟨some .peek, v, S⟩ : TM2.Cfg (fun _ : K => Bool) SLabel Ctl) =
        ⟨none, c, F S (decide (0 < m ∧ g = ig))⟩ := by
  cases m with
  | zero =>
      have hm' : S (2 : K) = [] := hm
      have hs : advance prog (⟨some .peek, v, S⟩ : TM2.Cfg (fun _ : K => Bool) SLabel Ctl) =
          ⟨some .clrG, (none, v.2), S⟩ := by
        have hS : Function.update S (2 : K) [] = S := by rw [← hm']; exact Function.update_eq_self _ _
        simp [advance, TM2.step, TM2.stepAux, prog, hm', hS]
      have h1 := clrG_run g S (none, v.2) hg
      have h2 := clrI_run ig (Function.update S (7 : K) []) ((none : Option Bool), v.2) (by simp [hi, u])
      refine ⟨(ig + 1) + ((g + 1) + 1), by omega, ((none : Option Bool), (none : Option Bool)), ?_⟩
      refine iter_trans (iter_trans (by rw [Function.iterate_one]; exact hs) h1) (h2.trans ?_)
      congr 1
  | succ k =>
      have hs : advance prog (⟨some .peek, v, S⟩ : TM2.Cfg (fun _ : K => Bool) SLabel Ctl) =
          ⟨some .cmp, (some true, v.2), S⟩ := by
        rw [u_succ] at hm
        have hS : Function.update (Function.update S (2 : K) (u k)) (2 : K) (true :: u k) = S := by
          rw [Function.update_idem, ← hm]; exact Function.update_eq_self _ _
        simp [advance, TM2.step, TM2.stepAux, prog, hm, hS]
      obtain ⟨t, ht, c, hr⟩ := cmp_run g ig S (some true, v.2) hg hi
      refine ⟨t + 1, by omega, c, ?_⟩
      refine iter_trans (by rw [Function.iterate_one]; exact hs) (hr.trans ?_)
      simp

#print axioms clrG_run
#print axioms clrI_run
#print axioms cmp_run
#print axioms select_run

end

end Paper2.ScanSelect
