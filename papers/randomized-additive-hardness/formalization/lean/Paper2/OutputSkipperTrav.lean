import Paper2.OutputSkipperOne

/-! Traversal theorem of the whole-Code output skipper: for every code of the
admissible shape and every word it can produce, a `true` marker consumes
exactly that word from the forward output and records it on `used`. -/

namespace Paper2.OutputSkipper

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineComposition
open GeneratorCode GeneratorSerialization
open RecursiveRequestCodeShape
open RecursiveSamplingProgram

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- Rows layout with a positive item alphabet (the actual codes use `4*s`). -/
def RowsShapeP (a b c : Code) : Prop :=
  ∃ d : Nat, 0 < d ∧ ∃ x y z r : Code,
    a = .append (.emit [false]) x ∧
    b = .append (.emit [true])
      (.append (.append (.ticket d) (.append (.emit [false]) y)) r) ∧
    c = .append (.emit [true])
      (.append (.append (.ticket d) (.append (.emit [true]) z)) r)

/-- Admissible grammar: every `branch3` node is inert (`n = 0`) or one of the
two actual layouts. -/
def Shape : Code → Prop
  | .emit _ | .ticket _ | .bit => True
  | .append a b => Shape a ∧ Shape b
  | .branch3 n x y a b c =>
      ((n = 0) ∨ (n = 256 ∧ x = 254 ∧ y = 255 ∧ TaggedShape a b c) ∨
       (n = 512 ∧ x = 510 ∧ y = 511 ∧ RowsShapeP a b c)) ∧
      Shape a ∧ Shape b ∧ Shape c

theorem produces_bit_word {w : List Bool} (h : Produces (meaning .bit) w) :
    ∃ b, w = [b] := by
  change Produces (Program.map RecursiveLabelCodecScratch.boolCodec.encode
    RecursiveSamplingSeed.bit) w at h
  obtain ⟨b, _, rfl⟩ := (produces_map _ _).mp h
  exact ⟨b, rfl⟩

theorem produces_append {a b : Code} {w : List Bool}
    (h : Produces (meaning (.append a b)) w) :
    ∃ x y, Produces (meaning a) x ∧ Produces (meaning b) y ∧ w = x ++ y := by
  change Produces (GeneratorCode.concat (meaning a) (meaning b)) w at h
  exact (produces_concat _ _).mp h

theorem produces_branch_zero {x y : Nat} {f s t : Code} {w : List Bool}
    (h : Produces (meaning (.branch3 0 x y f s t)) w) : w = [] := by
  change Produces (.pure []) w at h
  cases h; rfl

theorem bound_mul (t X Y : Nat) (hY : 1 ≤ Y) (h : t ≤ 8 * X) : t ≤ 8 * X * Y := by
  have : X ≤ X * Y := Nat.le_mul_of_pos_right X hY
  rw [Nat.mul_assoc]; omega

/-- Rows second/third child output structure. -/
theorem rows_child_word (d : Nat) (hd : 0 < d) (tag : Bool) (y r : Code) (w : List Bool)
    (h : Produces (meaning (.append (.emit [true])
      (.append (.append (.ticket d) (.append (.emit [tag]) y)) r))) w) :
    ∃ j rest, w = true :: (List.replicate j true ++ [false, tag]) ++ rest := by
  obtain ⟨w1, hw1, rfl⟩ := (produces_prefixed [true] w _).mp h
  obtain ⟨u, v, hu, _, rfl⟩ := produces_append hw1
  obtain ⟨item, u2, hitem, hu2, rfl⟩ := produces_append hu
  obtain ⟨u3, _, rfl⟩ := (produces_prefixed [tag] u2 y).mp hu2
  rcases (produces_ticket d item).mp hitem with ⟨hd0, _⟩ | ⟨i, rfl⟩
  · omega
  · refine ⟨i.val, u3 ++ v, ?_⟩
    simp [RecursiveLabelCodecScratch.finCodec, List.append_assoc]

theorem trav_one : ∀ (c : Code), Shape c → ∀ (w : List Bool), Produces (meaning c) w →
    ∀ (rest P O U : List Bool), ∃ t ≤ 8 * codeSize c * (w.length + 1),
      run t (ready (encodeCode c ++ rest) (true :: P) (w ++ O) U) =
        ready rest P O (w.reverse ++ U) := by
  intro c
  induction c with
  | emit bits =>
    intro _ w hw rest P O U
    have hw' := (produces_emit bits w).mp hw
    subst hw'
    obtain ⟨t1, ht1, h1⟩ := node_prefix (.emit w) rest true P (w ++ O) U
    have hl := emit_loop rest (List.replicate w.length true) [] [] [] [] P []
      (none, some .emit) (some true) 0 w O U none
    have hc := clear_all rest (List.replicate w.length true) [] [] [] [] [] P O
      (w.reverse ++ U) [] ((none, some .emit), (none, (some true, 0)))
    refine ⟨t1 + (1 + ((2 * w.length + 1) +
      clearCost (List.replicate w.length true) [] [] [] [] [])), ?_, ?_⟩
    · apply bound_mul _ _ _ (by omega)
      simp only [CodeHeaderMachine.headerCost] at ht1
      simp only [clearCost, codeSize, List.length_replicate, List.length_nil]; omega
    · rw [run_add, h1, run_add, run_one, after_trav_emit, run_add, hl, hc]; rfl
  | ticket n =>
    intro _ w hw rest P O U
    rcases (produces_ticket n w).mp hw with ⟨rfl, rfl⟩ | ⟨i, rfl⟩
    · obtain ⟨t1, ht1, h1⟩ := node_prefix (.ticket 0) rest true P ([] ++ O) U
      have hc := clear_all rest [] [] [] [] [] [] P O U []
        ((none, some .ticket), (none, (some true, 0)))
      refine ⟨t1 + (1 + (1 + clearCost [] [] [] [] [] [])), ?_, ?_⟩
      · apply bound_mul _ _ _ (by omega)
        simp only [CodeHeaderMachine.headerCost] at ht1
        simp only [clearCost, codeSize, List.length_nil]; omega
      · rw [run_add, h1, run_add, run_one, after_trav_ticket, run_add, run_one]
        simp only [List.replicate_zero, List.nil_append] at hc ⊢
        rw [ticketCheck_nil, hc]; rfl
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := i.isLt; omega⟩
      let tok := List.replicate i.val true ++ [false]
      have htok : (RecursiveLabelCodecScratch.finCodec (k + 1)).encode i = tok := rfl
      rw [htok]
      obtain ⟨t1, ht1, h1⟩ := node_prefix (.ticket (k + 1)) rest true P (tok ++ O) U
      have e3 := ticketCheck_cons rest (List.replicate k true) [] [] [] [] [] P (tok ++ O) U []
        (none, some .ticket) none (some true) 0 true
      have hl := ticket_loop rest (List.replicate k true) [] [] [] [] [] P []
        (none, some .ticket) (some true) 0 i.val O U (some true)
      have hc := clear_all rest (List.replicate k true) [] [] [] [] [] P O (tok.reverse ++ U) []
        ((none, some .ticket), (some false, (some true, 0)))
      refine ⟨t1 + (1 + (1 + ((i.val + 1) +
        clearCost (List.replicate k true) [] [] [] [] []))), ?_, ?_⟩
      · apply bound_mul _ _ _ (by omega)
        have := i.isLt
        simp only [CodeHeaderMachine.headerCost] at ht1
        simp only [clearCost, codeSize, List.length_replicate, List.length_nil]; omega
      · rw [run_add, h1, run_add, run_one, after_trav_ticket]
        rw [show List.replicate (k + 1) true = true :: List.replicate k true from rfl]
        rw [run_add, run_one, e3, run_add]
        simp only [tok, List.append_assoc, List.singleton_append] at hl ⊢
        rw [hl]
        exact hc
  | bit =>
    intro _ w hw rest P O U
    obtain ⟨b, rfl⟩ := produces_bit_word hw
    obtain ⟨t1, ht1, h1⟩ := node_prefix .bit rest true P ([b] ++ O) U
    have e3 := bitTake_step rest [] [] [] [] [] [] P O U [] (none, some .bit) none (some true) 0 b
    have hc := clear_all rest [] [] [] [] [] [] P O ([b].reverse ++ U) []
      ((none, some .bit), (some b, (some true, 0)))
    refine ⟨t1 + (1 + (1 + clearCost [] [] [] [] [] [])), ?_, ?_⟩
    · apply bound_mul _ _ _ (by omega)
      simp only [CodeHeaderMachine.headerCost] at ht1
      simp only [clearCost, codeSize, List.length_nil]; omega
    · rw [run_add, h1, run_add, run_one, after_trav_bit, run_add, run_one]
      simp only [List.singleton_append, List.reverse_singleton] at e3 hc ⊢
      rw [e3, hc]; rfl
  | append a b iha ihb =>
    intro hshape w hw rest P O U
    obtain ⟨x, y, hx, hy, rfl⟩ := produces_append hw
    obtain ⟨ta, hta, ha⟩ := iha hshape.1 x hx (encodeCode b ++ rest) (true :: P) (y ++ O) U
    obtain ⟨tb, htb, hb⟩ := ihb hshape.2 y hy rest P O (x.reverse ++ U)
    obtain ⟨t1, ht1, h1⟩ := node_prefix (.append a b) rest true P (x ++ y ++ O) U
    have hc := clear_all (encodeCode a ++ encodeCode b ++ rest) [] [] [] [] [] []
      (true :: true :: P) (x ++ y ++ O) U [] ((none, some .append), (none, (some true, 0)))
    refine ⟨t1 + (1 + clearCost [] [] [] [] [] []) + ta + tb, ?_, ?_⟩
    · simp only [CodeHeaderMachine.headerCost] at ht1
      have hx1 : codeSize a * (x.length + 1) ≤ codeSize a * ((x ++ y).length + 1) :=
        Nat.mul_le_mul_left _ (by simp)
      have hy1 : codeSize b * (y.length + 1) ≤ codeSize b * ((x ++ y).length + 1) :=
        Nat.mul_le_mul_left _ (by simp)
      have hexp : 8 * codeSize (.append a b) * ((x ++ y).length + 1) =
          24 * ((x ++ y).length + 1) + 8 * (codeSize a * ((x ++ y).length + 1)) +
            8 * (codeSize b * ((x ++ y).length + 1)) := by
        simp only [codeSize]; ring
      rw [hexp]
      rw [Nat.mul_assoc] at hta htb
      simp only [clearCost, List.length_nil]
      omega
    · rw [run_add, run_add, run_add, h1, run_add, run_one, after_trav_append, hc]
      simp only [List.append_assoc]
      change run tb (run ta (ready (encodeCode a ++ (encodeCode b ++ rest))
        (true :: true :: P) (x ++ (y ++ O)) U)) = _
      rw [ha, hb]
      simp [List.reverse_append, List.append_assoc]
  | branch3 n xa xb f s t ihf ihs iht =>
    intro hshape w hw rest P O U
    obtain ⟨hcase, hsf, hss, hst⟩ := hshape
    rcases hcase with rfl | ⟨rfl, rfl, rfl, htag⟩ | ⟨rfl, rfl, rfl, hrows⟩
    · -- inert branch: no output, all children skipped
      have hw0 := produces_branch_zero hw
      subst hw0
      obtain ⟨t1, ht1, h1⟩ := node_prefix (.branch3 0 xa xb f s t) rest true P ([] ++ O) U
      have hc := clear_all (encodeCode f ++ encodeCode s ++ encodeCode t ++ rest)
        [] (List.replicate xa true) (List.replicate xb true) [] [] []
        (false :: false :: false :: P) O U [] ((none, some .branch3), (none, (some true, 0)))
      obtain ⟨tf, htf, hf⟩ := skip_one f (encodeCode s ++ (encodeCode t ++ rest))
        (false :: false :: P) O U
      obtain ⟨ts, hts, hs⟩ := skip_one s (encodeCode t ++ rest) (false :: P) O U
      obtain ⟨tt, htt, ht⟩ := skip_one t rest P O U
      refine ⟨t1 + (1 + (1 + clearCost [] (List.replicate xa true)
        (List.replicate xb true) [] [] [])) + tf + ts + tt, ?_, ?_⟩
      · apply bound_mul _ _ _ (by omega)
        simp only [CodeHeaderMachine.headerCost] at ht1
        simp only [clearCost, codeSize, List.length_replicate, List.length_nil]; omega
      · rw [run_add, run_add, run_add, run_add, h1, run_add, run_one, after_trav_branch,
          run_add, run_one]
        simp only [List.replicate_zero, List.nil_append] at hc ⊢
        rw [branchStart_nil, hc]
        simp only [List.append_assoc]
        change run tt (run ts (run tf (ready (encodeCode f ++ (encodeCode s ++
          (encodeCode t ++ rest))) (false :: false :: false :: P) O U))) = _
        rw [hf, hs, ht]; rfl
    · -- tagged layout
      obtain ⟨fx, sy, tz, rfl, rfl, rfl⟩ := htag
      obtain ⟨i, hi⟩ := (produces_branch3 (by decide) _ _ _ w).mp hw
      have hsize : 1600 ≤ 8 * codeSize (.branch3 256 254 255
          (.append (.emit [false]) fx) (.append (.emit [true, false]) sy)
          (.append (.emit [true, true]) tz)) := by
        simp only [codeSize]; omega
      by_cases h₁ : i.val < 254
      · have hp : Produces (meaning (.append (.emit [false]) fx)) w := by
          simpa only [h₁, ↓reduceIte] using hi
        obtain ⟨w', _, hw'⟩ := (produces_prefixed [false] w fx).mp hp
        obtain ⟨tn, htn, hn⟩ := tagged_node (.append (.emit [false]) fx)
          (.append (.emit [true, false]) sy) (.append (.emit [true, true]) tz)
          rest P U (w' ++ O) 0 [false] (Or.inl ⟨rfl, rfl⟩)
        obtain ⟨tf, htf, hf⟩ := ihf hsf w hp
          (encodeCode (.append (.emit [true, false]) sy) ++
            (encodeCode (.append (.emit [true, true]) tz) ++ rest))
          (false :: false :: P) O U
        obtain ⟨ts, hts, hs⟩ := skip_one (.append (.emit [true, false]) sy)
          (encodeCode (.append (.emit [true, true]) tz) ++ rest) (false :: P) O
          (w.reverse ++ U)
        obtain ⟨tt, htt, ht⟩ := skip_one (.append (.emit [true, true]) tz) rest P O
          (w.reverse ++ U)
        refine ⟨tn + tf + ts + tt, ?_, ?_⟩
        · have hW : 1 ≤ w.length + 1 := by omega
          have e1 := Nat.le_mul_of_pos_right (8 * codeSize (.branch3 256 254 255
            (.append (.emit [false]) fx) (.append (.emit [true, false]) sy)
            (.append (.emit [true, true]) tz))) hW
          have hexp : 8 * codeSize (.branch3 256 254 255
              (.append (.emit [false]) fx) (.append (.emit [true, false]) sy)
              (.append (.emit [true, true]) tz)) * (w.length + 1) =
              8 * 771 * (w.length + 1) +
              8 * (codeSize (.append (.emit [false]) fx) * (w.length + 1)) +
              8 * (codeSize (.append (.emit [true, false]) sy) * (w.length + 1)) +
              8 * (codeSize (.append (.emit [true, true]) tz) * (w.length + 1)) := by
            simp only [codeSize]; ring
          have hs1 := Nat.le_mul_of_pos_right
            (codeSize (.append (.emit [true, false]) sy)) hW
          have ht1 := Nat.le_mul_of_pos_right
            (codeSize (.append (.emit [true, true]) tz)) hW
          rw [hexp]; rw [Nat.mul_assoc] at htf; omega
        · have hwO : w ++ O = [false] ++ (w' ++ O) := by rw [hw']; simp
          rw [hwO, run_add, run_add, run_add, hn]
          simp only [List.append_assoc]
          rw [← hwO]
          change run tt (run ts (run tf (ready (encodeCode (.append (.emit [false]) fx) ++
            (encodeCode (.append (.emit [true, false]) sy) ++
              (encodeCode (.append (.emit [true, true]) tz) ++ rest)))
            (true :: false :: false :: P) (w ++ O) U))) = _
          rw [hf, hs, ht]
      · by_cases h₂ : i.val < 255
        · have hp : Produces (meaning (.append (.emit [true, false]) sy)) w := by
            simpa only [h₁, h₂, ↓reduceIte] using hi
          obtain ⟨w', _, hw'⟩ := (produces_prefixed [true, false] w sy).mp hp
          obtain ⟨tn, htn, hn⟩ := tagged_node (.append (.emit [false]) fx)
            (.append (.emit [true, false]) sy) (.append (.emit [true, true]) tz)
            rest P U (w' ++ O) 1 [true, false] (Or.inr (Or.inl ⟨rfl, rfl⟩))
          obtain ⟨tf, htf, hf⟩ := skip_one (.append (.emit [false]) fx)
            (encodeCode (.append (.emit [true, false]) sy) ++
              (encodeCode (.append (.emit [true, true]) tz) ++ rest))
            (true :: false :: P) (w ++ O) U
          obtain ⟨ts, hts, hs⟩ := ihs hss w hp
            (encodeCode (.append (.emit [true, true]) tz) ++ rest) (false :: P) O U
          obtain ⟨tt, htt, ht⟩ := skip_one (.append (.emit [true, true]) tz) rest P O
            (w.reverse ++ U)
          refine ⟨tn + tf + ts + tt, ?_, ?_⟩
          · have hW : 1 ≤ w.length + 1 := by omega
            have hexp : 8 * codeSize (.branch3 256 254 255
                (.append (.emit [false]) fx) (.append (.emit [true, false]) sy)
                (.append (.emit [true, true]) tz)) * (w.length + 1) =
                8 * 771 * (w.length + 1) +
                8 * (codeSize (.append (.emit [false]) fx) * (w.length + 1)) +
                8 * (codeSize (.append (.emit [true, false]) sy) * (w.length + 1)) +
                8 * (codeSize (.append (.emit [true, true]) tz) * (w.length + 1)) := by
              simp only [codeSize]; ring
            have hf1 := Nat.le_mul_of_pos_right
              (codeSize (.append (.emit [false]) fx)) hW
            have ht1 := Nat.le_mul_of_pos_right
              (codeSize (.append (.emit [true, true]) tz)) hW
            rw [hexp]; rw [Nat.mul_assoc] at hts; omega
          · have hwO : w ++ O = [true, false] ++ (w' ++ O) := by rw [hw']; simp
            rw [hwO, run_add, run_add, run_add, hn]
            simp only [List.append_assoc]
            rw [← hwO]
            change run tt (run ts (run tf (ready (encodeCode (.append (.emit [false]) fx) ++
              (encodeCode (.append (.emit [true, false]) sy) ++
                (encodeCode (.append (.emit [true, true]) tz) ++ rest)))
              (false :: true :: false :: P) (w ++ O) U))) = _
            rw [hf, hs, ht]
        · have hp : Produces (meaning (.append (.emit [true, true]) tz)) w := by
            simpa only [h₁, h₂, ↓reduceIte] using hi
          obtain ⟨w', _, hw'⟩ := (produces_prefixed [true, true] w tz).mp hp
          obtain ⟨tn, htn, hn⟩ := tagged_node (.append (.emit [false]) fx)
            (.append (.emit [true, false]) sy) (.append (.emit [true, true]) tz)
            rest P U (w' ++ O) 2 [true, true] (Or.inr (Or.inr ⟨rfl, rfl⟩))
          obtain ⟨tf, htf, hf⟩ := skip_one (.append (.emit [false]) fx)
            (encodeCode (.append (.emit [true, false]) sy) ++
              (encodeCode (.append (.emit [true, true]) tz) ++ rest))
            (false :: true :: P) (w ++ O) U
          obtain ⟨ts, hts, hs⟩ := skip_one (.append (.emit [true, false]) sy)
            (encodeCode (.append (.emit [true, true]) tz) ++ rest) (true :: P) (w ++ O) U
          obtain ⟨tt, htt, ht⟩ := iht hst w hp rest P O U
          refine ⟨tn + tf + ts + tt, ?_, ?_⟩
          · have hW : 1 ≤ w.length + 1 := by omega
            have hexp : 8 * codeSize (.branch3 256 254 255
                (.append (.emit [false]) fx) (.append (.emit [true, false]) sy)
                (.append (.emit [true, true]) tz)) * (w.length + 1) =
                8 * 771 * (w.length + 1) +
                8 * (codeSize (.append (.emit [false]) fx) * (w.length + 1)) +
                8 * (codeSize (.append (.emit [true, false]) sy) * (w.length + 1)) +
                8 * (codeSize (.append (.emit [true, true]) tz) * (w.length + 1)) := by
              simp only [codeSize]; ring
            have hf1 := Nat.le_mul_of_pos_right
              (codeSize (.append (.emit [false]) fx)) hW
            have hs1 := Nat.le_mul_of_pos_right
              (codeSize (.append (.emit [true, false]) sy)) hW
            rw [hexp]; rw [Nat.mul_assoc] at htt; omega
          · have hwO : w ++ O = [true, true] ++ (w' ++ O) := by rw [hw']; simp
            rw [hwO, run_add, run_add, run_add, hn]
            simp only [List.append_assoc]
            rw [← hwO]
            change run tt (run ts (run tf (ready (encodeCode (.append (.emit [false]) fx) ++
              (encodeCode (.append (.emit [true, false]) sy) ++
                (encodeCode (.append (.emit [true, true]) tz) ++ rest)))
              (false :: false :: true :: P) (w ++ O) U))) = _
            rw [hf, hs, ht]
    · -- rows layout
      obtain ⟨d, hd, fx, y, z, r, rfl, rfl, rfl⟩ := hrows
      obtain ⟨i, hi⟩ := (produces_branch3 (by decide) _ _ _ w).mp hw
      have hW : 1 ≤ w.length + 1 := by omega
      have hexp : 8 * codeSize (.branch3 512 510 511 (.append (.emit [false]) fx)
          (.append (.emit [true])
            (.append (.append (.ticket d) (.append (.emit [false]) y)) r))
          (.append (.emit [true])
            (.append (.append (.ticket d) (.append (.emit [true]) z)) r))) * (w.length + 1) =
          8 * 1539 * (w.length + 1) +
          8 * (codeSize (.append (.emit [false]) fx) * (w.length + 1)) +
          8 * (codeSize (.append (.emit [true])
            (.append (.append (.ticket d) (.append (.emit [false]) y)) r)) * (w.length + 1)) +
          8 * (codeSize (.append (.emit [true])
            (.append (.append (.ticket d) (.append (.emit [true]) z)) r)) * (w.length + 1)) := by
        simp only [codeSize]; ring
      have hF1 := Nat.le_mul_of_pos_right (codeSize (.append (.emit [false]) fx)) hW
      have hS1 := Nat.le_mul_of_pos_right (codeSize (.append (.emit [true])
        (.append (.append (.ticket d) (.append (.emit [false]) y)) r))) hW
      have hT1 := Nat.le_mul_of_pos_right (codeSize (.append (.emit [true])
        (.append (.append (.ticket d) (.append (.emit [true]) z)) r))) hW
      by_cases h₁ : i.val < 510
      · have hp : Produces (meaning (.append (.emit [false]) fx)) w := by
          simpa only [h₁, ↓reduceIte] using hi
        obtain ⟨w', _, hw'⟩ := (produces_prefixed [false] w fx).mp hp
        obtain ⟨tn, htn, hn⟩ := rows_node (.append (.emit [false]) fx)
          (.append (.emit [true])
            (.append (.append (.ticket d) (.append (.emit [false]) y)) r))
          (.append (.emit [true])
            (.append (.append (.ticket d) (.append (.emit [true]) z)) r))
          rest P U (w' ++ O) 0 [false] (Or.inl ⟨rfl, rfl⟩)
        obtain ⟨tf, htf, hf⟩ := ihf hsf w hp
          (encodeCode (.append (.emit [true])
            (.append (.append (.ticket d) (.append (.emit [false]) y)) r)) ++
            (encodeCode (.append (.emit [true])
              (.append (.append (.ticket d) (.append (.emit [true]) z)) r)) ++ rest))
          (false :: false :: P) O U
        obtain ⟨ts, hts, hs⟩ := skip_one (.append (.emit [true])
            (.append (.append (.ticket d) (.append (.emit [false]) y)) r))
          (encodeCode (.append (.emit [true])
            (.append (.append (.ticket d) (.append (.emit [true]) z)) r)) ++ rest)
          (false :: P) O (w.reverse ++ U)
        obtain ⟨tt, htt, ht⟩ := skip_one (.append (.emit [true])
            (.append (.append (.ticket d) (.append (.emit [true]) z)) r)) rest P O
          (w.reverse ++ U)
        refine ⟨tn + tf + ts + tt, ?_, ?_⟩
        · have hlen : w.length = 1 + w'.length := by rw [hw']; simp; omega
          simp only [List.length_singleton] at htn
          rw [hexp]; rw [Nat.mul_assoc] at htf; omega
        · have hwO : w ++ O = [false] ++ (w' ++ O) := by rw [hw']; simp
          rw [hwO, run_add, run_add, run_add, hn]
          simp only [List.append_assoc]
          rw [← hwO]
          change run tt (run ts (run tf (ready (encodeCode (.append (.emit [false]) fx) ++
            (encodeCode (.append (.emit [true])
              (.append (.append (.ticket d) (.append (.emit [false]) y)) r)) ++
              (encodeCode (.append (.emit [true])
                (.append (.append (.ticket d) (.append (.emit [true]) z)) r)) ++ rest)))
            (true :: false :: false :: P) (w ++ O) U))) = _
          rw [hf, hs, ht]
      · by_cases h₂ : i.val < 511
        · have hp : Produces (meaning (.append (.emit [true])
              (.append (.append (.ticket d) (.append (.emit [false]) y)) r))) w := by
            simpa only [h₁, h₂, ↓reduceIte] using hi
          obtain ⟨j, w', hw'⟩ := rows_child_word d hd false y r w hp
          obtain ⟨tn, htn, hn⟩ := rows_node (.append (.emit [false]) fx)
            (.append (.emit [true])
              (.append (.append (.ticket d) (.append (.emit [false]) y)) r))
            (.append (.emit [true])
              (.append (.append (.ticket d) (.append (.emit [true]) z)) r))
            rest P U (w' ++ O) 1 (true :: (List.replicate j true ++ [false, false]))
            (Or.inr (Or.inl ⟨j, rfl, rfl⟩))
          obtain ⟨tf, htf, hf⟩ := skip_one (.append (.emit [false]) fx)
            (encodeCode (.append (.emit [true])
              (.append (.append (.ticket d) (.append (.emit [false]) y)) r)) ++
              (encodeCode (.append (.emit [true])
                (.append (.append (.ticket d) (.append (.emit [true]) z)) r)) ++ rest))
            (true :: false :: P) (w ++ O) U
          obtain ⟨ts, hts, hs⟩ := ihs hss w hp
            (encodeCode (.append (.emit [true])
              (.append (.append (.ticket d) (.append (.emit [true]) z)) r)) ++ rest)
            (false :: P) O U
          obtain ⟨tt, htt, ht⟩ := skip_one (.append (.emit [true])
              (.append (.append (.ticket d) (.append (.emit [true]) z)) r)) rest P O
            (w.reverse ++ U)
          refine ⟨tn + tf + ts + tt, ?_, ?_⟩
          · have hlen : w.length =
                (true :: (List.replicate j true ++ [false, false])).length + w'.length := by
              rw [hw']; simp; omega
            rw [hexp]; rw [Nat.mul_assoc] at hts; omega
          · have hwO : w ++ O =
                (true :: (List.replicate j true ++ [false, false])) ++ (w' ++ O) := by
              rw [hw']; simp
            rw [hwO, run_add, run_add, run_add, hn]
            rw [← hwO]
            simp only [List.append_assoc]
            change run tt (run ts (run tf (ready (encodeCode (.append (.emit [false]) fx) ++
              (encodeCode (.append (.emit [true])
                (.append (.append (.ticket d) (.append (.emit [false]) y)) r)) ++
                (encodeCode (.append (.emit [true])
                  (.append (.append (.ticket d) (.append (.emit [true]) z)) r)) ++ rest)))
              (false :: true :: false :: P) (w ++ O) U))) = _
            rw [hf, hs, ht]
        · have hp : Produces (meaning (.append (.emit [true])
              (.append (.append (.ticket d) (.append (.emit [true]) z)) r))) w := by
            simpa only [h₁, h₂, ↓reduceIte] using hi
          obtain ⟨j, w', hw'⟩ := rows_child_word d hd true z r w hp
          obtain ⟨tn, htn, hn⟩ := rows_node (.append (.emit [false]) fx)
            (.append (.emit [true])
              (.append (.append (.ticket d) (.append (.emit [false]) y)) r))
            (.append (.emit [true])
              (.append (.append (.ticket d) (.append (.emit [true]) z)) r))
            rest P U (w' ++ O) 2 (true :: (List.replicate j true ++ [false, true]))
            (Or.inr (Or.inr ⟨j, rfl, rfl⟩))
          obtain ⟨tf, htf, hf⟩ := skip_one (.append (.emit [false]) fx)
            (encodeCode (.append (.emit [true])
              (.append (.append (.ticket d) (.append (.emit [false]) y)) r)) ++
              (encodeCode (.append (.emit [true])
                (.append (.append (.ticket d) (.append (.emit [true]) z)) r)) ++ rest))
            (false :: true :: P) (w ++ O) U
          obtain ⟨ts, hts, hs⟩ := skip_one (.append (.emit [true])
              (.append (.append (.ticket d) (.append (.emit [false]) y)) r))
            (encodeCode (.append (.emit [true])
              (.append (.append (.ticket d) (.append (.emit [true]) z)) r)) ++ rest)
            (true :: P) (w ++ O) U
          obtain ⟨tt, htt, ht⟩ := iht hst w hp rest P O U
          refine ⟨tn + tf + ts + tt, ?_, ?_⟩
          · have hlen : w.length =
                (true :: (List.replicate j true ++ [false, true])).length + w'.length := by
              rw [hw']; simp; omega
            rw [hexp]; rw [Nat.mul_assoc] at htt; omega
          · have hwO : w ++ O =
                (true :: (List.replicate j true ++ [false, true])) ++ (w' ++ O) := by
              rw [hw']; simp
            rw [hwO, run_add, run_add, run_add, hn]
            rw [← hwO]
            simp only [List.append_assoc]
            change run tt (run ts (run tf (ready (encodeCode (.append (.emit [false]) fx) ++
              (encodeCode (.append (.emit [true])
                (.append (.append (.ticket d) (.append (.emit [false]) y)) r)) ++
                (encodeCode (.append (.emit [true])
                  (.append (.append (.ticket d) (.append (.emit [true]) z)) r)) ++ rest)))
              (false :: false :: true :: P) (w ++ O) U))) = _
            rw [hf, hs, ht]

#print axioms produces_bit_word
#print axioms rows_child_word
#print axioms trav_one

end Paper2.OutputSkipper
