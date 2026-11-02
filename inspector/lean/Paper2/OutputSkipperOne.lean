import Paper2.OutputSkipperBranch

/-! One-subtree theorems of the whole-Code output skipper. -/

namespace Paper2.OutputSkipper

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineComposition
open GeneratorCode GeneratorSerialization
open RecursiveRequestCodeShape

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- Skipping one serialized subtree with a `false` marker: syntax only. -/
theorem skip_one : ∀ (c : Code) (rest P O U : List Bool),
    ∃ t ≤ 8 * codeSize c,
      run t (ready (encodeCode c ++ rest) (false :: P) O U) = ready rest P O U := by
  intro c
  induction c with
  | emit bits =>
    intro rest P O U
    obtain ⟨t1, ht1, h1⟩ := node_prefix (.emit bits) rest false P O U
    have hc := clear_all rest (List.replicate bits.length true) [] [] [] bits [] P O U []
      ((none, some .emit), (none, (some false, 0)))
    refine ⟨t1 + (1 + clearCost (List.replicate bits.length true) [] [] [] bits []), ?_, ?_⟩
    · simp only [CodeHeaderMachine.headerCost] at ht1
      simp only [clearCost, codeSize, List.length_replicate, List.length_nil]; omega
    · rw [run_add, h1, run_add, run_one, after_skip_emit, hc]; rfl
  | ticket n =>
    intro rest P O U
    obtain ⟨t1, ht1, h1⟩ := node_prefix (.ticket n) rest false P O U
    have hc := clear_all rest (List.replicate n true) [] [] [] [] [] P O U []
      ((none, some .ticket), (none, (some false, 0)))
    refine ⟨t1 + (1 + clearCost (List.replicate n true) [] [] [] [] []), ?_, ?_⟩
    · simp only [CodeHeaderMachine.headerCost] at ht1
      simp only [clearCost, codeSize, List.length_replicate, List.length_nil]; omega
    · rw [run_add, h1, run_add, run_one, after_skip_ticket, hc]; rfl
  | bit =>
    intro rest P O U
    obtain ⟨t1, ht1, h1⟩ := node_prefix .bit rest false P O U
    have hc := clear_all rest [] [] [] [] [] [] P O U []
      ((none, some .bit), (none, (some false, 0)))
    refine ⟨t1 + (1 + clearCost [] [] [] [] [] []), ?_, ?_⟩
    · simp only [CodeHeaderMachine.headerCost] at ht1
      simp only [clearCost, codeSize, List.length_nil]; omega
    · rw [run_add, h1, run_add, run_one, after_skip_bit, hc]; rfl
  | append a b iha ihb =>
    intro rest P O U
    obtain ⟨t1, ht1, h1⟩ := node_prefix (.append a b) rest false P O U
    have hc := clear_all (encodeCode a ++ encodeCode b ++ rest) [] [] [] [] [] []
      (false :: false :: P) O U [] ((none, some .append), (none, (some false, 0)))
    obtain ⟨ta, hta, ha⟩ := iha (encodeCode b ++ rest) (false :: P) O U
    obtain ⟨tb, htb, hb⟩ := ihb rest P O U
    refine ⟨t1 + (1 + clearCost [] [] [] [] [] []) + ta + tb, ?_, ?_⟩
    · simp only [CodeHeaderMachine.headerCost] at ht1
      simp only [clearCost, codeSize, List.length_nil]; omega
    · rw [run_add, run_add, run_add, h1, run_add, run_one, after_skip_append, hc]
      simp only [List.append_assoc]
      change run tb (run ta (ready (encodeCode a ++ (encodeCode b ++ rest))
        (false :: false :: P) O U)) = _
      rw [ha, hb]
  | branch3 n x y f s t ihf ihs iht =>
    intro rest P O U
    obtain ⟨t1, ht1, h1⟩ := node_prefix (.branch3 n x y f s t) rest false P O U
    have hc := clear_all (encodeCode f ++ encodeCode s ++ encodeCode t ++ rest)
      (List.replicate n true) (List.replicate x true) (List.replicate y true) [] [] []
      (false :: false :: false :: P) O U [] ((none, some .branch3), (none, (some false, 0)))
    obtain ⟨tf, htf, hf⟩ := ihf (encodeCode s ++ (encodeCode t ++ rest)) (false :: false :: P) O U
    obtain ⟨ts, hts, hs⟩ := ihs (encodeCode t ++ rest) (false :: P) O U
    obtain ⟨tt, htt, ht⟩ := iht rest P O U
    refine ⟨t1 + (1 + clearCost (List.replicate n true) (List.replicate x true)
      (List.replicate y true) [] [] []) + tf + ts + tt, ?_, ?_⟩
    · simp only [CodeHeaderMachine.headerCost] at ht1
      simp only [clearCost, codeSize, List.length_replicate, List.length_nil]; omega
    · rw [run_add, run_add, run_add, run_add, h1, run_add, run_one, after_skip_branch, hc]
      simp only [List.append_assoc]
      change run tt (run ts (run tf (ready (encodeCode f ++ (encodeCode s ++ (encodeCode t ++ rest)))
          (false :: false :: false :: P) O U))) = _
      rw [hf]
      rw [hs, ht]

#print axioms skip_one

end Paper2.OutputSkipper
