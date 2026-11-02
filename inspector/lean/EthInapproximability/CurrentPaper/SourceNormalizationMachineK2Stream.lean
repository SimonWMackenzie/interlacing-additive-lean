import EthInapproximability.CurrentPaper.SourceNormalizationMachineMark

/-!
# Physical unary endpoint suffix for the adjoined K2

From the decoded unary vertex count `v`, this fixed finite-stack program
writes the two endpoint fields `unary v ++ unary (v+1)` into an initially
empty output stack. It restores `v`, retains the original SAT variable count
and graph payload, and charges every pushed bit.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineK2Stream

open Turing TM2.Stmt BitMachineEncoding

inductive Phase where
  | start | scan | extra | boundary | restore
  deriving DecidableEq, Fintype

abbrev Stack := Fin 5
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Phase (Option Bool)

def program : Phase → TM2.Stmt (fun _ : Stack => Bool) Phase (Option Bool)
  | .start => push 2 (fun _ => false) (goto (fun _ => .scan))
  | .scan => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 1 (fun _ => true)
          (push 2 (fun _ => true) (goto (fun _ => .scan))))
        (goto (fun _ => .extra)))
  | .extra => push 2 (fun _ => true) (goto (fun _ => .boundary))
  | .boundary => push 2 (fun _ => false) (goto (fun _ => .restore))
  | .restore => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun _ => true)
          (push 2 (fun _ => true) (goto (fun _ => .restore))))
        halt)

def cfg (l : Option Phase) (s : Option Bool)
    (vertices saved output payload originalN : List Bool) : Config :=
  ⟨l, s, ![vertices, saved, output, payload, originalN]⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem scan_run (v a : ℕ) (s : Option Bool)
    (out payload originalN : List Bool) :
    run (v + 1) (cfg (some .scan) s (List.replicate v true)
      (List.replicate a true) out payload originalN) =
    cfg (some .extra) none [] (List.replicate (a + v) true)
      (List.replicate v true ++ out) payload originalN := by
  induction v generalizing a s out with
  | zero =>
      apply congrArg (fun S => (⟨some Phase.extra, none, S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | succ v ih =>
      have hs : TM2.step program (cfg (some .scan) s (List.replicate (v + 1) true)
          (List.replicate a true) out payload originalN) =
          some (cfg (some .scan) (some true) (List.replicate v true)
            (List.replicate (a + 1) true) (true :: out) payload originalN) := by
        apply congrArg (fun S => some (⟨some Phase.scan, some true, S⟩ : Config))
        funext k
        fin_cases k <;> rfl
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.replicate_add, List.append_assoc] using
        (run_succ hs (v + 1)).trans (ih (a + 1) (some true) (true :: out))

private theorem restore_run (a v : ℕ) (s : Option Bool)
    (out payload originalN : List Bool) :
    run (a + 1) (cfg (some .restore) s (List.replicate v true)
      (List.replicate a true) out payload originalN) =
    cfg none none (List.replicate (v + a) true) []
      (List.replicate a true ++ out) payload originalN := by
  induction a generalizing v s out with
  | zero =>
      apply congrArg (fun S => (⟨none, none, S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | succ a ih =>
      have hs : TM2.step program (cfg (some .restore) s (List.replicate v true)
          (List.replicate (a + 1) true) out payload originalN) =
          some (cfg (some .restore) (some true) (List.replicate (v + 1) true)
            (List.replicate a true) (true :: out) payload originalN) := by
        apply congrArg (fun S => some (⟨some Phase.restore, some true, S⟩ : Config))
        funext k
        fin_cases k <;> rfl
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.replicate_add, List.append_assoc] using
        (run_succ hs (a + 1)).trans (ih (v + 1) (some true) (true :: out))

/-- The new edge's endpoint fields are physically written in canonical
unary-delimited order. -/
theorem k2_run (v : ℕ) (payload originalN : List Bool) :
    run (2 * v + 5)
      (cfg (some .start) none (List.replicate v true) [] [] payload originalN) =
    cfg none none (List.replicate v true) []
      (SourceNormalizationMachineMark.endpointStream [v, v + 1])
      payload originalN := by
  have hstart : TM2.step program
      (cfg (some .start) none (List.replicate v true) [] [] payload originalN) =
      some (cfg (some .scan) none (List.replicate v true) [] [false]
        payload originalN) := by
    apply congrArg (fun S => some (⟨some Phase.scan, none, S⟩ : Config))
    funext k
    fin_cases k <;> rfl
  have hs := scan_run v 0 none [false] payload originalN
  simp only [Nat.zero_add, List.replicate_zero] at hs
  have he : TM2.step program
      (cfg (some .extra) none [] (List.replicate v true)
        (List.replicate v true ++ [false]) payload originalN) =
      some (cfg (some .boundary) none [] (List.replicate v true)
        (List.replicate (v + 1) true ++ [false]) payload originalN) := by
    apply congrArg (fun S => some (⟨some Phase.boundary, none, S⟩ : Config))
    funext k
    fin_cases k <;> rfl
  have hb : TM2.step program
      (cfg (some .boundary) none [] (List.replicate v true)
        (List.replicate (v + 1) true ++ [false]) payload originalN) =
      some (cfg (some .restore) none [] (List.replicate v true)
        (false :: List.replicate (v + 1) true ++ [false]) payload originalN) := by
    apply congrArg (fun S => some (⟨some Phase.restore, none, S⟩ : Config))
    funext k
    fin_cases k <;> rfl
  have hr := restore_run v 0 none
    (false :: List.replicate (v + 1) true ++ [false]) payload originalN
  simp only [Nat.zero_add, List.replicate_zero] at hr
  have h₁ := (run_succ hstart (v + 1)).trans hs
  have h₂ : run 2 (cfg (some .extra) none [] (List.replicate v true)
      (List.replicate v true ++ [false]) payload originalN) =
      cfg (some .restore) none [] (List.replicate v true)
        (false :: List.replicate (v + 1) true ++ [false]) payload originalN :=
    (run_succ he 1).trans (run_succ hb 0)
  have h₃ := (run_add h₁ 2).trans h₂
  have h₄ := (run_add h₃ (v + 1)).trans hr
  have htime : v + 1 + 1 + 2 + (v + 1) = 2 * v + 5 := by omega
  rw [htime] at h₄
  simpa [SourceNormalizationMachineMark.endpointStream, EncodedGraph.unary,
    List.append_assoc] using h₄

end EthInapproximability.CurrentPaper.SourceNormalizationMachineK2Stream
