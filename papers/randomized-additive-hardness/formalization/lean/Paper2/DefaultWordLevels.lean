import Paper2.DefaultWordLoopRun

/-! The canonical default words of every level `j` by ONE fixed program: the
generic `CountedLoop.loop` around the checked level body. From the seed
bank (`words 0 = (replicate p false, [false])`, unary `q₁, s, Q, w`, `j`
counter marks) it halts with exactly `words j` in the level cells; the
column word `(words j).2` is the encoding of every entry of the canonical
default tail `canonicalDefaultTails … j` (`canonical_tail_encoded`). -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.DefaultWordLoop

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.CanonicalDefaultWordScratch (repeatWord words successor_words)

/-- The level loop: ONE fixed program. -/
def levelLoop := CountedLoop.loop ctrC body bodyStart bodyCtl

def levelBound (p s q₁ q₂ w Q j : ℕ) : ℕ :=
  (Finset.range j).sum (fun i => bodyBound q₁ s Q w (words p s q₁ q₂ w Q i).1
    (words p s q₁ q₂ w Q i).2)

theorem upd_ctr (q₁ s Q w : ℕ) (R C ctr x : List Bool) :
    Function.update (S q₁ s Q w R C ctr) ctrC x = S q₁ s Q w R C x := by
  unfold S
  rw [show ctrC = .inr (.inr 0) from rfl, upd_D]
  congr 1
  funext i; fin_cases i <;> rfl

theorem level_loop_run (p s q₁ q₂ w Q j : ℕ) (c : Option Bool × _) :
    ∃ t ≤ j * (levelBound p s q₁ q₂ w Q j + 2) + 1, ∃ c',
      ((advance levelLoop)^[t])
        (⟨some (.inl ()), c, S q₁ s Q w (words p s q₁ q₂ w Q 0).1 (words p s q₁ q₂ w Q 0).2
          (List.replicate j true)⟩ : TM2.Cfg (fun _ : LB => Bool) _ _) =
        ⟨none, c', S q₁ s Q w (words p s q₁ q₂ w Q j).1 (words p s q₁ q₂ w Q j).2 []⟩ := by
  have h := CountedLoop.loop_run ctrC body bodyStart bodyCtl j (levelBound p s q₁ q₂ w Q j)
    (fun i => S q₁ s Q w (words p s q₁ q₂ w Q i).1 (words p s q₁ q₂ w Q i).2
      (List.replicate (j - i) true))
    (fun i _ => rfl)
    (by
      intro i hi
      rw [upd_ctr]
      obtain ⟨t, ht, v, hr⟩ := body_run q₁ s Q w (words p s q₁ q₂ w Q i).1
        (words p s q₁ q₂ w Q i).2 (List.replicate (j - i - 1) true)
      refine ⟨t, le_trans ht ?_, v, ?_⟩
      · unfold levelBound
        exact Finset.single_le_sum
          (f := fun i => bodyBound q₁ s Q w (words p s q₁ q₂ w Q i).1
            (words p s q₁ q₂ w Q i).2) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)
      · rw [hr, show j - i - 1 = j - (i + 1) by omega]
        rfl)
    c
  simpa using h

end

#print axioms upd_ctr
#print axioms level_loop_run

end Paper2.DefaultWordLoop
