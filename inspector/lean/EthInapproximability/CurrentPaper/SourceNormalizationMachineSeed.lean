import EthInapproximability.CurrentPaper.BitMachineEncoding

/-!
# Physical all-false support seed

Starting with a unary vertex count, this fixed finite-stack program creates
one false support cell per vertex. It restores the count and leaves the
original SAT variable count and graph payload untouched.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineSeed

open Turing TM2.Stmt BitMachineEncoding

inductive Phase where
  | copy | restore
  deriving DecidableEq, Fintype

abbrev Stack := Fin 5
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Phase (Option Bool)

def program : Phase → TM2.Stmt (fun _ : Stack => Bool) Phase (Option Bool)
  | .copy => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 1 (fun _ => true)
          (push 2 (fun _ => false) (goto (fun _ => .copy))))
        (goto (fun _ => .restore)))
  | .restore => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun _ => true) (goto (fun _ => .restore)))
        halt)

def cfg (l : Option Phase) (s : Option Bool)
    (vertices saved support payload originalN : List Bool) : Config :=
  ⟨l, s, ![vertices, saved, support, payload, originalN]⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem copy_run (v a b : ℕ) (s : Option Bool)
    (payload originalN : List Bool) :
    run (v + 1) (cfg (some .copy) s (List.replicate v true)
      (List.replicate a true) (List.replicate b false) payload originalN) =
    cfg (some .restore) none [] (List.replicate (a + v) true)
      (List.replicate (b + v) false) payload originalN := by
  induction v generalizing a b s with
  | zero =>
      apply congrArg (fun S => (⟨some Phase.restore, none, S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | succ v ih =>
      have hs : TM2.step program (cfg (some .copy) s (List.replicate (v + 1) true)
          (List.replicate a true) (List.replicate b false) payload originalN) =
          some (cfg (some .copy) (some true) (List.replicate v true)
            (List.replicate (a + 1) true) (List.replicate (b + 1) false)
            payload originalN) := by
        apply congrArg (fun S => some (⟨some Phase.copy, some true, S⟩ : Config))
        funext k
        fin_cases k <;> rfl
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (run_succ hs (v + 1)).trans (ih (a + 1) (b + 1) (some true))

private theorem restore_run (a v : ℕ) (s : Option Bool)
    (support payload originalN : List Bool) :
    run (a + 1) (cfg (some .restore) s (List.replicate v true)
      (List.replicate a true) support payload originalN) =
    cfg none none (List.replicate (v + a) true) [] support payload originalN := by
  induction a generalizing v s with
  | zero =>
      apply congrArg (fun S => (⟨none, none, S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | succ a ih =>
      have hs : TM2.step program (cfg (some .restore) s (List.replicate v true)
          (List.replicate (a + 1) true) support payload originalN) =
          some (cfg (some .restore) (some true) (List.replicate (v + 1) true)
            (List.replicate a true) support payload originalN) := by
        apply congrArg (fun S => some (⟨some Phase.restore, some true, S⟩ : Config))
        funext k
        fin_cases k <;> rfl
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (run_succ hs (a + 1)).trans (ih (v + 1) (some true))

theorem seed_run (v : ℕ) (payload originalN : List Bool) :
    run (2 * v + 2) (cfg (some .copy) none (List.replicate v true)
      [] [] payload originalN) =
    cfg none none (List.replicate v true) [] (List.replicate v false)
      payload originalN := by
  have hc := copy_run v 0 0 none payload originalN
  simp only [Nat.zero_add, List.replicate_zero] at hc
  have hr := restore_run v 0 none (List.replicate v false) payload originalN
  simp only [Nat.zero_add, List.replicate_zero] at hr
  have ht := (run_add hc (v + 1)).trans hr
  have htime : v + 1 + (v + 1) = 2 * v + 2 := by omega
  rw [htime] at ht
  exact ht

end EthInapproximability.CurrentPaper.SourceNormalizationMachineSeed
