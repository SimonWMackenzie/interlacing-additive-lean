import Paper2.OutputSkipperRun

/-! The branch-node overhead of the output skipper for the two actual layouts:
header, physical layout count, nondestructive route peek and restore, route
markers, clear. The route is determined by the output bits actually present. -/

namespace Paper2.OutputSkipper

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineComposition
open GeneratorCode GeneratorSerialization

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def marks : Fin 3 → List Bool
  | 0 => [true, false, false]
  | 1 => [false, true, false]
  | 2 => [false, false, true]

theorem rep256 : List.replicate 256 true = true :: List.replicate 255 true := rfl
theorem rep512 : List.replicate 512 true =
    true :: (List.replicate 255 true ++ true :: List.replicate 255 true) := by
  simp only [← List.replicate_succ, List.replicate_append_replicate]

/-- Tagged layout (`branch3 256 254 255`). The peeked prefix `pre` is
`[false]`, `[true,false]` or `[true,true]` and fixes the route. -/
theorem tagged_node (f s t : Code) (rest P U O' : List Bool) (route : Fin 3)
    (pre : List Bool)
    (hpre : (pre = [false] ∧ route = 0) ∨ (pre = [true, false] ∧ route = 1) ∨
      (pre = [true, true] ∧ route = 2)) :
    ∃ n ≤ 1600, run n (ready (encodeCode (.branch3 256 254 255 f s t) ++ rest)
        (true :: P) (pre ++ O') U) =
      ready (encodeCode f ++ encodeCode s ++ encodeCode t ++ rest)
        (marks route ++ P) (pre ++ O') U := by
  obtain ⟨t1, ht1, h1⟩ := node_prefix (.branch3 256 254 255 f s t) rest true P (pre ++ O') U
  have hcost1 : t1 ≤ 773 := by simpa [CodeHeaderMachine.headerCost] using ht1
  let H0 := encodeCode f ++ encodeCode s ++ encodeCode t ++ rest
  let A := List.replicate 254 true
  let Bb := List.replicate 255 true
  let hcv : CodeHeaderMachine.Control := (none, some .branch3)
  have e2 := after_trav_branch rest P (pre ++ O') U 256 254 255 f s t
  rw [rep256] at e2
  have e3 := branchStart_cons H0 (List.replicate 255 true) A Bb [] [] [] P (pre ++ O') U []
    hcv none (some true) 0 true
  have e4 := layout_tagged H0 A Bb [] [] [] P (pre ++ O') U [] hcv (some true) 0 255 1
    (some true) (by decide)
  have hclear := clear_all H0 [] A Bb [] [] [] (marks route ++ P) (pre ++ O') U []
  rcases hpre with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have e5 := tagged1_false H0 [] A Bb [] [] [] P O' U [] hcv none (some true) 0
    have e6 := restore_loop H0 [] A Bb [] [] [] P U hcv (some true) 0 [false] O'
      (some false)
    rw [show ([false] : List Bool).length + 1 = 2 from rfl] at e6
    have e7 := pushRoute_0 H0 [] A Bb [] [] [] P ([false] ++ O') U [] hcv none (some true)
    refine ⟨t1 + (1 + (1 + (256 + (1 + (2 + (1 + clearCost [] A Bb [] [] [])))))),
      ?_, ?_⟩
    · simp only [clearCost, List.length_replicate, List.length_nil, A, Bb]; omega
    · rw [run_add, h1, run_add, run_one, e2, run_add, run_one, e3, run_add, e4,
        run_add, run_one, List.singleton_append, e5, run_add, e6]
      simp only [List.reverse_singleton, List.singleton_append] at e7 ⊢
      rw [run_add, run_one, e7]
      exact hclear _
  · have e5 := tagged1_true H0 [] A Bb [] [] [] P (false :: O') U [] hcv none (some true) 0
    have e5b := tagged2_step H0 [] A Bb [] [] [] P O' U [true] hcv (some true) (some true) 0
      false
    simp only [Bool.false_eq_true, ↓reduceIte] at e5b
    have e6 := restore_loop H0 [] A Bb [] [] [] P U hcv (some true) 1 [false, true] O'
      (some false)
    rw [show ([false, true] : List Bool).length + 1 = 3 from rfl] at e6
    have e7 := pushRoute_1 H0 [] A Bb [] [] [] P ([true, false] ++ O') U [] hcv none
      (some true)
    refine ⟨t1 + (1 + (1 + (256 + (1 + (1 + (3 + (1 + clearCost [] A Bb [] [] []))))))),
      ?_, ?_⟩
    · simp only [clearCost, List.length_replicate, List.length_nil, A, Bb]; omega
    · rw [run_add, h1, run_add, run_one, e2, run_add, run_one, e3, run_add, e4]
      simp only [List.cons_append, List.nil_append] at e5 e6 e7 ⊢
      rw [run_add, run_one, e5, run_add, run_one, e5b, run_add, e6]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append] at e7 ⊢
      rw [run_add, run_one, e7]
      exact hclear _
  · have e5 := tagged1_true H0 [] A Bb [] [] [] P (true :: O') U [] hcv none (some true) 0
    have e5b := tagged2_step H0 [] A Bb [] [] [] P O' U [true] hcv (some true) (some true) 0
      true
    simp only [↓reduceIte] at e5b
    have e6 := restore_loop H0 [] A Bb [] [] [] P U hcv (some true) 2 [true, true] O'
      (some true)
    rw [show ([true, true] : List Bool).length + 1 = 3 from rfl] at e6
    have e7 := pushRoute_2 H0 [] A Bb [] [] [] P ([true, true] ++ O') U [] hcv none
      (some true)
    refine ⟨t1 + (1 + (1 + (256 + (1 + (1 + (3 + (1 + clearCost [] A Bb [] [] []))))))),
      ?_, ?_⟩
    · simp only [clearCost, List.length_replicate, List.length_nil, A, Bb]; omega
    · rw [run_add, h1, run_add, run_one, e2, run_add, run_one, e3, run_add, e4]
      simp only [List.cons_append, List.nil_append] at e5 e6 e7 ⊢
      rw [run_add, run_one, e5, run_add, run_one, e5b, run_add, e6]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append] at e7 ⊢
      rw [run_add, run_one, e7]
      exact hclear _

/-- Rows layout (`branch3 512 510 511`). The peeked prefix is `[false]`
(route 0) or `true ++ true^j ++ false ++ tag` (route 1/2 by the tag). -/
theorem rows_node (f s t : Code) (rest P U O' : List Bool) (route : Fin 3)
    (pre : List Bool)
    (hpre : (pre = [false] ∧ route = 0) ∨
      (∃ j, pre = true :: (List.replicate j true ++ [false, false]) ∧ route = 1) ∨
      (∃ j, pre = true :: (List.replicate j true ++ [false, true]) ∧ route = 2)) :
    ∃ n ≤ 3100 + 2 * pre.length,
      run n (ready (encodeCode (.branch3 512 510 511 f s t) ++ rest)
        (true :: P) (pre ++ O') U) =
      ready (encodeCode f ++ encodeCode s ++ encodeCode t ++ rest)
        (marks route ++ P) (pre ++ O') U := by
  obtain ⟨t1, ht1, h1⟩ := node_prefix (.branch3 512 510 511 f s t) rest true P (pre ++ O') U
  have hcost1 : t1 ≤ 1541 := by simpa [CodeHeaderMachine.headerCost] using ht1
  let H0 := encodeCode f ++ encodeCode s ++ encodeCode t ++ rest
  let A := List.replicate 510 true
  let Bb := List.replicate 511 true
  let R255 := List.replicate 255 true
  let hcv : CodeHeaderMachine.Control := (none, some .branch3)
  have e2 := after_trav_branch rest P (pre ++ O') U 512 510 511 f s t
  rw [rep512] at e2
  have e3 := branchStart_cons H0 (R255 ++ true :: R255) A Bb [] [] [] P (pre ++ O') U []
    hcv none (some true) 0 true
  have e4 := layout_rows H0 A Bb [] [] [] P (pre ++ O') U [] hcv (some true) 0 R255 255 1
    (some true) (by decide)
  have hclear := clear_all H0 R255 A Bb [] [] [] (marks route ++ P) (pre ++ O') U []
  have hcc : clearCost R255 A Bb [] [] [] = 1283 := by
    simp [clearCost, R255, A, Bb]
  rcases hpre with ⟨rfl, rfl⟩ | ⟨j, rfl, rfl⟩ | ⟨j, rfl, rfl⟩
  · have e5 := rows1_false H0 R255 A Bb [] [] [] P O' U [] hcv (some true) (some true) 0
    have e6 := restore_loop H0 R255 A Bb [] [] [] P U hcv (some true) 0 [false] O'
      (some false)
    rw [show ([false] : List Bool).length + 1 = 2 from rfl] at e6
    have e7 := pushRoute_0 H0 R255 A Bb [] [] [] P ([false] ++ O') U [] hcv none (some true)
    refine ⟨t1 + (1 + (1 + (256 + (1 + (2 + (1 + clearCost R255 A Bb [] [] [])))))),
      ?_, ?_⟩
    · rw [hcc]; simp only [List.length_singleton]; omega
    · rw [run_add, h1, run_add, run_one, e2, run_add, run_one, e3, run_add, e4,
        run_add, run_one, List.singleton_append, e5, run_add, e6]
      simp only [List.reverse_singleton, List.singleton_append] at e7 ⊢
      rw [run_add, run_one, e7]
      exact hclear _
  · have hL : (true :: (List.replicate j true ++ [false, false])) ++ O' =
        true :: (List.replicate j true ++ false :: (false :: O')) := by simp
    rw [hL] at h1 e2 e3 e4 ⊢
    have e5 := rows1_true H0 R255 A Bb [] [] [] P
      (List.replicate j true ++ false :: (false :: O')) U [] hcv (some true) (some true) 0
    have e6 := rowsScan_loop H0 R255 A Bb [] [] [] P U hcv (some true) 0 j
      (false :: O') [true] (some true)
    have e6b := rowsTag_step H0 R255 A Bb [] [] [] P O' U
      ((List.replicate j true ++ [false]).reverse ++ [true]) hcv (some false) (some true) 0
      false
    simp only [Bool.false_eq_true, ↓reduceIte] at e6b
    let L := false :: ((List.replicate j true ++ [false]).reverse ++ [true])
    have e7 := restore_loop H0 R255 A Bb [] [] [] P U hcv (some true) 1 L O' (some false)
    have hrev : L.reverse ++ O' =
        true :: (List.replicate j true ++ false :: (false :: O')) := by
      simp [L, List.reverse_append, List.append_assoc]
    rw [hrev] at e7
    have e8 := pushRoute_1 H0 R255 A Bb [] [] [] P
      (true :: (List.replicate j true ++ false :: (false :: O'))) U [] hcv none (some true)
    have hLlen : L.length = j + 3 := by simp [L]
    refine ⟨t1 + (1 + (1 + (256 + (1 + ((j + 1) + (1 + ((L.length + 1) +
      (1 + clearCost R255 A Bb [] [] [])))))))), ?_, ?_⟩
    · rw [hcc, hLlen]; simp only [List.length_cons, List.length_append,
        List.length_replicate, List.length_nil]; omega
    · rw [run_add, h1, run_add, run_one, e2, run_add, run_one, e3, run_add, e4,
        run_add, run_one, e5, run_add, e6, run_add, run_one, e6b, run_add, e7,
        run_add, run_one, e8]
      rw [hL] at hclear
      exact hclear _
  · have hL : (true :: (List.replicate j true ++ [false, true])) ++ O' =
        true :: (List.replicate j true ++ false :: (true :: O')) := by simp
    rw [hL] at h1 e2 e3 e4 ⊢
    have e5 := rows1_true H0 R255 A Bb [] [] [] P
      (List.replicate j true ++ false :: (true :: O')) U [] hcv (some true) (some true) 0
    have e6 := rowsScan_loop H0 R255 A Bb [] [] [] P U hcv (some true) 0 j
      (true :: O') [true] (some true)
    have e6b := rowsTag_step H0 R255 A Bb [] [] [] P O' U
      ((List.replicate j true ++ [false]).reverse ++ [true]) hcv (some false) (some true) 0
      true
    simp only [↓reduceIte] at e6b
    let L := true :: ((List.replicate j true ++ [false]).reverse ++ [true])
    have e7 := restore_loop H0 R255 A Bb [] [] [] P U hcv (some true) 2 L O' (some true)
    have hrev : L.reverse ++ O' =
        true :: (List.replicate j true ++ false :: (true :: O')) := by
      simp [L, List.reverse_append, List.append_assoc]
    rw [hrev] at e7
    have e8 := pushRoute_2 H0 R255 A Bb [] [] [] P
      (true :: (List.replicate j true ++ false :: (true :: O'))) U [] hcv none (some true)
    have hLlen : L.length = j + 3 := by simp [L]
    refine ⟨t1 + (1 + (1 + (256 + (1 + ((j + 1) + (1 + ((L.length + 1) +
      (1 + clearCost R255 A Bb [] [] [])))))))), ?_, ?_⟩
    · rw [hcc, hLlen]; simp only [List.length_cons, List.length_append,
        List.length_replicate, List.length_nil]; omega
    · rw [run_add, h1, run_add, run_one, e2, run_add, run_one, e3, run_add, e4,
        run_add, run_one, e5, run_add, e6, run_add, run_one, e6b, run_add, e7,
        run_add, run_one, e8]
      rw [hL] at hclear
      exact hclear _

#print axioms tagged_node
#print axioms rows_node

end Paper2.OutputSkipper
