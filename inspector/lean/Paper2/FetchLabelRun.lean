import Paper2.FetchLabel

/-! Correctness of `skipN` (skip `n` produced labels of one code) and
`capture` (extract the next produced label, forward, into `lbl`). -/

namespace Paper2.FetchLabel

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding
open GeneratorCode GeneratorSerialization
open RecursiveRequestCodeShape
open OutputSkipper (bk ctl0 ready Shape)

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- Empty skipper bank with a given output word. -/
def eb (O : List Bool) : SkStack → List Bool := bk [] [] [] [] [] [] [] [] O [] []

theorem eb_h0 (O : List Bool) : eb O (OutputSkipper.hc 0) = [] := rfl

theorem eb_set_code (O code : List Bool) :
    Function.update (eb O) (OutputSkipper.hc 0) code =
      bk code [] [] [] [] [] [] [] O [] [] := by
  funext j; rcases j with j | j <;> fin_cases j <;> rfl

theorem set_pending (code O : List Bool) :
    Function.update (bk code [] [] [] [] [] [] [] O [] []) OutputSkipper.pending
      (true :: (bk code [] [] [] [] [] [] [] O [] []) OutputSkipper.pending) =
      bk code [] [] [] [] [] [] [true] O [] [] := by
  funext j; rcases j with j | j <;> fin_cases j <;> rfl

theorem clear_used (O U : List Bool) :
    Function.update (bk [] [] [] [] [] [] [] [] O U []) OutputSkipper.used [] = eb O := by
  funext j; rcases j with j | j <;> fin_cases j <;> rfl

def iterBound (c : Code) (w : List Bool) : Nat := 11 * codeSize c * (w.length + 1) + 7

/-- One loop iteration: consume one produced label. -/
theorem iter_run (c : Code) (hc : Shape c) (w : List Bool) (hw : Produces (meaning c) w)
    (O code : List Bool) (hcode : code = encodeCode c) (n : Nat) (lbl : List Bool)
    (v : Control) :
    ∃ t ≤ iterBound c w,
      run false t ⟨some .cnt, v, fb (eb (w ++ O)) code (List.replicate (n + 1) true) [] lbl⟩ =
        ⟨some .cnt, (none, (none, (ctl0.1, (none, (none, 0))))),
          fb (eb O) code (List.replicate n true) [] lbl⟩ := by
  subst hcode
  obtain ⟨tc, htc, hcp⟩ := copy_phase false (eb (w ++ O)) (encodeCode c)
    (List.replicate n true) lbl (eb_h0 _)
  rw [eb_set_code] at hcp
  have hmark := mark_step false (bk (encodeCode c) [] [] [] [] [] [] [] (w ++ O) [] [])
    (encodeCode c) (List.replicate n true) [] lbl base
  rw [set_pending] at hmark
  obtain ⟨ts, hts, hsk⟩ := skip_phase false c hc w hw O [] (encodeCode c)
    (List.replicate n true) lbl
  simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil] at hsk
  have hclr := clr_loop (bk [] [] [] [] [] [] [] [] O w.reverse []) (encodeCode c)
    (List.replicate n true) [] lbl w.reverse (none, (none, (ctl0.1, (none, (none, 0))))) rfl
  rw [clear_used] at hclr
  refine ⟨1 + (tc + (1 + (ts + (w.reverse.length + 1)))), ?_, ?_⟩
  · simp only [iterBound, List.length_reverse]
    rw [encodeCode_length] at htc
    have h1 : codeSize c ≤ codeSize c * (w.length + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h2 : w.length ≤ codeSize c * (w.length + 1) := by
      have : 1 ≤ codeSize c := by cases c <;> simp [codeSize] <;> omega
      calc w.length ≤ 1 * (w.length + 1) := by omega
        _ ≤ codeSize c * (w.length + 1) := Nat.mul_le_mul_right _ this
    rw [Nat.mul_assoc] at hts ⊢
    omega
  · rw [run_add, run_one, List.replicate_succ, cnt_cons, run_add, hcp, run_add, run_one,
      hmark, run_add, hsk, hclr]

def loopBound (c : Code) (ws : List (List Bool)) : Nat :=
  (ws.map (iterBound c)).sum + 1

theorem skipN_run (c : Code) (hc : Shape c) (code : List Bool) (hcode : code = encodeCode c)
    (lbl : List Bool) :
    ∀ (ws : List (List Bool)), (∀ w ∈ ws, Produces (meaning c) w) →
      ∀ (O : List Bool) (v : Control),
        ∃ t ≤ loopBound c ws, ∃ v' : Control,
          run false t ⟨some .cnt, v,
            fb (eb (ws.flatten ++ O)) code (List.replicate ws.length true) [] lbl⟩ =
            ⟨none, v', fb (eb O) code [] [] lbl⟩
  | [], _, O, v => ⟨1, by simp [loopBound], (none, v.2), by
      show run false 1 _ = _
      rw [run_one]; simpa using cnt_nil false (eb O) code [] lbl v⟩
  | w :: ws, hws, O, v => by
      obtain ⟨t1, ht1, h1⟩ := iter_run c hc w (hws w (List.mem_cons_self ..))
        (ws.flatten ++ O) code hcode ws.length lbl v
      obtain ⟨t2, ht2, v', h2⟩ := skipN_run c hc code hcode lbl ws
        (fun x hx => hws x (List.mem_cons_of_mem _ hx)) O
        (none, (none, (ctl0.1, (none, (none, 0)))))
      refine ⟨t1 + t2, ?_, v', ?_⟩
      · simp only [loopBound, List.map_cons, List.sum_cons] at ht2 ⊢; omega
      · rw [run_add]
        simp only [List.flatten_cons, List.append_assoc, List.length_cons] at h1 ⊢
        rw [h1, h2]

/-- Capture: one produced label moved forward into `lbl`. -/
theorem capture_run (c : Code) (hc : Shape c) (w : List Bool) (hw : Produces (meaning c) w)
    (O code cnt : List Bool) (hcode : code = encodeCode c) :
    ∃ t ≤ iterBound c w, ∃ v' : Control,
      run true t ⟨some (.copy .scan), base, fb (eb (w ++ O)) code cnt [] []⟩ =
        ⟨none, v', fb (eb O) code cnt [] w⟩ := by
  subst hcode
  obtain ⟨tc, htc, hcp⟩ := copy_phase true (eb (w ++ O)) (encodeCode c) cnt [] (eb_h0 _)
  rw [eb_set_code] at hcp
  have hmark := mark_step true (bk (encodeCode c) [] [] [] [] [] [] [] (w ++ O) [] [])
    (encodeCode c) cnt [] [] base
  rw [set_pending] at hmark
  obtain ⟨ts, hts, hsk⟩ := skip_phase true c hc w hw O [] (encodeCode c) cnt []
  simp only [↓reduceIte, List.append_nil] at hsk
  have hrev := rev_loop (bk [] [] [] [] [] [] [] [] O w.reverse []) (encodeCode c) cnt []
    w.reverse [] (none, (none, (ctl0.1, (none, (none, 0))))) rfl
  rw [clear_used, List.reverse_reverse, List.append_nil] at hrev
  refine ⟨tc + (1 + (ts + (w.reverse.length + 1))), ?_,
    (none, (none, (ctl0.1, (none, (none, 0))))), ?_⟩
  · simp only [iterBound, List.length_reverse]
    rw [encodeCode_length] at htc
    have h1 : codeSize c ≤ codeSize c * (w.length + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have h2 : w.length ≤ codeSize c * (w.length + 1) := by
      have : 1 ≤ codeSize c := by cases c <;> simp [codeSize] <;> omega
      calc w.length ≤ 1 * (w.length + 1) := by omega
        _ ≤ codeSize c * (w.length + 1) := Nat.mul_le_mul_right _ this
    rw [Nat.mul_assoc] at hts ⊢
    omega
  · rw [run_add, hcp, run_add, run_one, hmark, run_add, hsk, hrev]

#print axioms iter_run
#print axioms skipN_run
#print axioms capture_run

end Paper2.FetchLabel
