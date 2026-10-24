import Paper2.OutputSkipper

/-! Loops and phases of the whole-Code output skipper: emit/ticket/peek/
restore loops, the counted layout loop, the header phase (the admitted
`CodeHeaderMachine` lifted), and the six-cell clear phase. -/

namespace Paper2.OutputSkipper

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineComposition
open GeneratorCode GeneratorSerialization

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-! ### Loops -/

theorem emit_loop (h0 h1 h2 h3 h4 h6 P K : List Bool) (hcv : CodeHeaderMachine.Control)
    (m : Option Bool) (r : Fin 3) :
    ∀ (bits O U : List Bool) (s : Option Bool),
      run (2 * bits.length + 1) ⟨some (.inr .emitNext), (hcv, (s, (m, r))),
        bk h0 h1 h2 h3 h4 bits h6 P (bits ++ O) U K⟩ =
      ⟨some (.inr (.clear 0)), (hcv, (none, (m, r))),
        bk h0 h1 h2 h3 h4 [] h6 P O (bits.reverse ++ U) K⟩
  | [], O, U, s => by
      show run 1 _ = _
      rw [run_one]; simpa using emitNext_nil h0 h1 h2 h3 h4 h6 P O U K hcv s m r
  | b :: bits, O, U, s => by
      have e1 := emitNext_cons h0 h1 h2 h3 h4 bits h6 P (b :: (bits ++ O)) U K hcv s m r b
      have e2 := emitTake_step h0 h1 h2 h3 h4 bits h6 P (bits ++ O) U K hcv (some b) m r b
      have ih := emit_loop h0 h1 h2 h3 h4 h6 P K hcv m r bits O (b :: U) (some b)
      rw [show 2 * (b :: bits).length + 1 = 1 + (1 + (2 * bits.length + 1)) by
        simp; omega, run_add, run_one, List.cons_append, e1, run_add, run_one, e2, ih]
      simp

theorem ticket_loop (h0 h1 h2 h3 h4 h5 h6 P K : List Bool)
    (hcv : CodeHeaderMachine.Control) (m : Option Bool) (r : Fin 3) :
    ∀ (j : Nat) (O U : List Bool) (s : Option Bool),
      run (j + 1) ⟨some (.inr .ticketTake), (hcv, (s, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P (List.replicate j true ++ false :: O) U K⟩ =
      ⟨some (.inr (.clear 0)), (hcv, (some false, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P O
          ((List.replicate j true ++ [false]).reverse ++ U) K⟩
  | 0, O, U, s => by
      rw [run_one]; simpa using ticketTake_false h0 h1 h2 h3 h4 h5 h6 P O U K hcv s m r
  | j + 1, O, U, s => by
      have e1 := ticketTake_true h0 h1 h2 h3 h4 h5 h6 P
        (List.replicate j true ++ false :: O) U K hcv s m r
      have ih := ticket_loop h0 h1 h2 h3 h4 h5 h6 P K hcv m r j O (true :: U) (some true)
      rw [show j + 1 + 1 = 1 + (j + 1) by omega, run_add, run_one]
      rw [show List.replicate (j + 1) true ++ false :: O =
        true :: (List.replicate j true ++ false :: O) by simp [List.replicate_succ], e1, ih]
      simp [List.replicate_succ, List.append_assoc]

theorem rowsScan_loop (h0 h1 h2 h3 h4 h5 h6 P U : List Bool)
    (hcv : CodeHeaderMachine.Control) (m : Option Bool) (r : Fin 3) :
    ∀ (j : Nat) (O K : List Bool) (s : Option Bool),
      run (j + 1) ⟨some (.inr .rowsScan), (hcv, (s, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P (List.replicate j true ++ false :: O) U K⟩ =
      ⟨some (.inr .rowsTag), (hcv, (some false, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P O U
          ((List.replicate j true ++ [false]).reverse ++ K)⟩
  | 0, O, K, s => by
      rw [run_one]; simpa using rowsScan_false h0 h1 h2 h3 h4 h5 h6 P O U K hcv s m r
  | j + 1, O, K, s => by
      have e1 := rowsScan_true h0 h1 h2 h3 h4 h5 h6 P
        (List.replicate j true ++ false :: O) U K hcv s m r
      have ih := rowsScan_loop h0 h1 h2 h3 h4 h5 h6 P U hcv m r j O (true :: K) (some true)
      rw [show j + 1 + 1 = 1 + (j + 1) by omega, run_add, run_one]
      rw [show List.replicate (j + 1) true ++ false :: O =
        true :: (List.replicate j true ++ false :: O) by simp [List.replicate_succ], e1, ih]
      simp [List.replicate_succ, List.append_assoc]

theorem restore_loop (h0 h1 h2 h3 h4 h5 h6 P U : List Bool)
    (hcv : CodeHeaderMachine.Control) (m : Option Bool) (r : Fin 3) :
    ∀ (L O : List Bool) (s : Option Bool),
      run (L.length + 1) ⟨some (.inr .restore), (hcv, (s, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P O U L⟩ =
      ⟨some (.inr .pushRoute), (hcv, (none, (m, r))),
        bk h0 h1 h2 h3 h4 h5 h6 P (L.reverse ++ O) U []⟩
  | [], O, s => by
      show run 1 _ = _
      rw [run_one]; simpa using restore_nil h0 h1 h2 h3 h4 h5 h6 P O U hcv s m r
  | b :: L, O, s => by
      have e1 := restore_cons h0 h1 h2 h3 h4 h5 h6 P O U L hcv s m r b
      have ih := restore_loop h0 h1 h2 h3 h4 h5 h6 P U hcv m r L (b :: O) (some b)
      rw [show (b :: L).length + 1 = 1 + (L.length + 1) by simp; omega, run_add,
        run_one, e1, ih]
      simp

/-- Counted layout loop, tagged exit: `c + x = 256` bits left to pop. -/
theorem layout_tagged (h0 h2 h3 h4 h5 h6 P O U K : List Bool)
    (hcv : CodeHeaderMachine.Control) (m : Option Bool) (r : Fin 3) :
    ∀ (x : Nat) (c : Fin 257) (s : Option Bool), c.val + x = 256 →
      run (x + 1) ⟨some (.inr (.layout c)), (hcv, (s, (m, r))),
        bk h0 (List.replicate x true) h2 h3 h4 h5 h6 P O U K⟩ =
      ⟨some (.inr .tagged1), (hcv, (none, (m, r))),
        bk h0 [] h2 h3 h4 h5 h6 P O U K⟩
  | 0, c, s, _ => by
      rw [run_one]; simpa using layout_nil h0 h2 h3 h4 h5 h6 P O U K hcv s m r c
  | x + 1, c, s, h => by
      have hc' : c.val < 256 := by omega
      have e1 := layout_cons_lt h0 (List.replicate x true) h2 h3 h4 h5 h6 P O U K
        hcv s m r c hc' true
      have ih := layout_tagged h0 h2 h3 h4 h5 h6 P O U K hcv m r x
        ⟨c.val + 1, by omega⟩ (some true) (by simp; omega)
      rw [show x + 1 + 1 = 1 + (x + 1) by omega, run_add, run_one,
        List.replicate_succ, e1, ih]

/-- Counted layout loop, rows exit: the 257th bit exists. -/
theorem layout_rows (h0 h2 h3 h4 h5 h6 P O U K : List Bool)
    (hcv : CodeHeaderMachine.Control) (m : Option Bool) (r : Fin 3) (rest : List Bool) :
    ∀ (x : Nat) (c : Fin 257) (s : Option Bool), c.val + x = 256 →
      run (x + 1) ⟨some (.inr (.layout c)), (hcv, (s, (m, r))),
        bk h0 (List.replicate x true ++ true :: rest) h2 h3 h4 h5 h6 P O U K⟩ =
      ⟨some (.inr .rows1), (hcv, (some true, (m, r))),
        bk h0 rest h2 h3 h4 h5 h6 P O U K⟩
  | 0, c, s, h => by
      have hc : c = 256 := Fin.ext (by simp at h; simpa using h)
      subst hc
      rw [run_one]; simpa using layout_cons_top h0 rest h2 h3 h4 h5 h6 P O U K hcv s m r true
  | x + 1, c, s, h => by
      have hc' : c.val < 256 := by omega
      have e1 := layout_cons_lt h0 (List.replicate x true ++ true :: rest) h2 h3 h4 h5 h6
        P O U K hcv s m r c hc' true
      have ih := layout_rows h0 h2 h3 h4 h5 h6 P O U K hcv m r rest x
        ⟨c.val + 1, by omega⟩ (some true) (by simp; omega)
      rw [show x + 1 + 1 = 1 + (x + 1) by omega, run_add, run_one,
        List.replicate_succ, List.cons_append, e1, ih]

/-! ### Clear phase -/

theorem clear_cons (i j : Fin 7) (hi : i.val < 6) (hj : j.val = i.val + 1)
    (v : Control) (S : Stack → List Bool)
    (b : Bool) (xs : List Bool) (hS : S (hc j) = b :: xs) :
    advance program ⟨some (.inr (.clear i)), v, S⟩ =
      ⟨some (.inr (.clear i)), rec v (some b), Function.update S (hc j) xs⟩ := by
  have hj' : j = ⟨i.val + 1, by omega⟩ := Fin.ext hj
  rw [hj'] at hS ⊢
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, hi, hS, rec]

theorem clear_nil (i j : Fin 7) (hi : i.val < 6) (hj : j.val = i.val + 1)
    (v : Control) (S : Stack → List Bool) (hS : S (hc j) = []) :
    advance program ⟨some (.inr (.clear i)), v, S⟩ =
      ⟨some (.inr (.clear j)), rec v none, S⟩ := by
  have hj' : j = ⟨i.val + 1, by omega⟩ := Fin.ext hj
  rw [hj'] at hS ⊢
  have hS' : Function.update S (hc ⟨i.val + 1, by omega⟩) [] = S := by
    rw [← hS]; exact Function.update_eq_self _ _
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, hi, hS, rec, hS']

theorem clear_cell (i j : Fin 7) (hi : i.val < 6) (hj : j.val = i.val + 1) :
    ∀ (xs : List Bool) (v : Control) (S : Stack → List Bool),
      S (hc j) = xs →
      run (xs.length + 1) ⟨some (.inr (.clear i)), v, S⟩ =
        ⟨some (.inr (.clear j)), rec v none, Function.update S (hc j) []⟩
  | [], v, S, hS => by
      show run 1 _ = _
      rw [run_one, clear_nil i j hi hj v S hS]
      rw [← hS, Function.update_eq_self]
  | b :: xs, v, S, hS => by
      rw [show (b :: xs).length + 1 = 1 + (xs.length + 1) by simp; omega, run_add,
        run_one, clear_cons i j hi hj v S b xs hS]
      rw [clear_cell i j hi hj xs (rec v (some b)) _ (by simp)]
      simp [rec]

theorem clear_finish (v : Control) (S : Stack → List Bool) :
    advance program ⟨some (.inr (.clear 6)), v, S⟩ =
      ⟨some (.inr .check), ctl0, S⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, program]

def clearCost (x1 x2 x3 x4 x5 x6 : List Bool) : Nat :=
  x1.length + x2.length + x3.length + x4.length + x5.length + x6.length + 7

theorem clear_all (h0 x1 x2 x3 x4 x5 x6 P O U K : List Bool) (v : Control) :
    run (clearCost x1 x2 x3 x4 x5 x6) ⟨some (.inr (.clear 0)), v,
      bk h0 x1 x2 x3 x4 x5 x6 P O U K⟩ =
      ⟨some (.inr .check), ctl0, bk h0 [] [] [] [] [] [] P O U K⟩ := by
  have c1 := clear_cell 0 1 (by decide) rfl x1 v (bk h0 x1 x2 x3 x4 x5 x6 P O U K) rfl
  have c2 := clear_cell 1 2 (by decide) rfl x2 (rec v none)
    (bk h0 [] x2 x3 x4 x5 x6 P O U K) rfl
  have c3 := clear_cell 2 3 (by decide) rfl x3 (rec (rec v none) none)
    (bk h0 [] [] x3 x4 x5 x6 P O U K) rfl
  have c4 := clear_cell 3 4 (by decide) rfl x4 (rec (rec (rec v none) none) none)
    (bk h0 [] [] [] x4 x5 x6 P O U K) rfl
  have c5 := clear_cell 4 5 (by decide) rfl x5
    (rec (rec (rec (rec v none) none) none) none)
    (bk h0 [] [] [] [] x5 x6 P O U K) rfl
  have c6 := clear_cell 5 6 (by decide) rfl x6
    (rec (rec (rec (rec (rec v none) none) none) none) none)
    (bk h0 [] [] [] [] [] x6 P O U K) rfl
  rw [up_h1] at c1; rw [up_h2] at c2; rw [up_h3] at c3; rw [up_h4] at c4
  rw [up_h5] at c5; rw [up_h6] at c6
  have hcost : clearCost x1 x2 x3 x4 x5 x6 =
      (x1.length + 1) + ((x2.length + 1) + ((x3.length + 1) + ((x4.length + 1) +
        ((x5.length + 1) + ((x6.length + 1) + 1))))) := by
    simp only [clearCost]; omega
  rw [hcost, run_add, c1, run_add, c2, run_add, c3, run_add, c4, run_add, c5,
    run_add, c6, run_one, clear_finish]

/-! ### Header phase: the admitted header machine, lifted -/

theorem header_run (c : Code) (rest P O U K : List Bool) (w : W) :
    ∃ t ≤ CodeHeaderMachine.headerCost c,
      run t ⟨some (.inl .first), ((none, none), w),
        bk (encodeCode c ++ rest) [] [] [] [] [] [] P O U K⟩ =
      ⟨some (.inr .after), ((none, some (CodeHeaderMachine.headerKind c)), w),
        bk (CodeHeaderMachine.headerTail c rest) (CodeHeaderMachine.headerN c)
          (CodeHeaderMachine.headerA c) (CodeHeaderMachine.headerB c) []
          (CodeHeaderMachine.headerWord c) [] P O U K⟩ := by
  have hh := CodeHeaderMachine.run_header c rest
  have hhalt : (((advance CodeHeaderMachine.program)^[CodeHeaderMachine.headerCost c])
      (CodeHeaderMachine.initial (encodeCode c ++ rest))).l = none := by
    rw [← CodeHeaderMachine.run, hh]
    rfl
  obtain ⟨t, ht, hr⟩ := BitMachineSubroutine.lift_outputs
    CodeHeaderMachine.program program (some Admin.after) (by intro l; rfl)
    w (ext P O U K)
    (CodeHeaderMachine.initial (encodeCode c ++ rest))
    (CodeHeaderMachine.headerCost c) hhalt
  refine ⟨t, ht, ?_⟩
  change ((advance program)^[t]) _ =
    liftCfg (some Admin.after) w (ext P O U K)
      (CodeHeaderMachine.run (CodeHeaderMachine.headerCost c)
        (CodeHeaderMachine.initial (encodeCode c ++ rest))) at hr
  rw [hh] at hr
  simpa [liftCfg, CodeHeaderMachine.initial, CodeHeaderMachine.cfg, bk] using hr

#print axioms emit_loop
#print axioms ticket_loop
#print axioms rowsScan_loop
#print axioms restore_loop
#print axioms layout_tagged
#print axioms layout_rows
#print axioms clear_all
#print axioms header_run

end Paper2.OutputSkipper
