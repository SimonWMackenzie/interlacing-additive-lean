import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! A finite-stack scan doubles the retained unary padded edge count into
the endpoint-field counter used by the copy-offset controller. -/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineDoubleUnary

open Turing TM2.Stmt BitMachineEncoding

inductive Phase where
  | scan | restore
  deriving DecidableEq, Fintype

abbrev Stack := Fin 3
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Phase (Option Bool)

def program : Phase → TM2.Stmt (fun _ : Stack => Bool) Phase (Option Bool)
  | .scan => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 1 (fun _ => true)
          (push 2 (fun _ => true)
            (push 2 (fun _ => true) (goto (fun _ => .scan)))))
        (goto (fun _ => .restore)))
  | .restore => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun _ => true) (goto (fun _ => .restore)))
        halt)

def cfg (l : Option Phase) (s : Option Bool)
    (source scratch output : List Bool) : Config :=
  ⟨l,s,![source,scratch,output]⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem scan_run (d a b : ℕ) (s : Option Bool) :
    run (d + 1) (cfg (some .scan) s (List.replicate d true)
      (List.replicate a true) (List.replicate b true)) =
    cfg (some .restore) none [] (List.replicate (a + d) true)
      (List.replicate (b + 2 * d) true) := by
  induction d generalizing a b s with
  | zero =>
      apply congrArg (fun S => (⟨some Phase.restore,none,S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | succ d ih =>
      have hs : TM2.step program
          (cfg (some .scan) s (List.replicate (d + 1) true)
            (List.replicate a true) (List.replicate b true)) =
          some (cfg (some .scan) (some true) (List.replicate d true)
            (List.replicate (a + 1) true) (List.replicate (b + 2) true)) := by
        apply congrArg (fun S => some (⟨some Phase.scan,some true,S⟩ : Config))
        funext k
        fin_cases k <;> simp [List.replicate_succ, List.replicate_add]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        Nat.succ_mul] using
        (run_succ hs (d + 1)).trans
          (ih (a + 1) (b + 2) (some true))

private theorem restore_run (d a b : ℕ) (s : Option Bool) :
    run (d + 1) (cfg (some .restore) s
      (List.replicate a true) (List.replicate d true)
      (List.replicate b true)) =
    cfg none none (List.replicate (a + d) true) []
      (List.replicate b true) := by
  induction d generalizing a s with
  | zero =>
      apply congrArg (fun S => (⟨none,none,S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | succ d ih =>
      have hs : TM2.step program
          (cfg (some .restore) s (List.replicate a true)
            (List.replicate (d + 1) true) (List.replicate b true)) =
          some (cfg (some .restore) (some true)
            (List.replicate (a + 1) true)
            (List.replicate d true) (List.replicate b true)) := by
        apply congrArg (fun S => some (⟨some Phase.restore,some true,S⟩ : Config))
        funext k
        fin_cases k <;> simp [List.replicate_succ]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (run_succ hs (d + 1)).trans (ih (a + 1) (some true))

theorem double_run (d : ℕ) :
    run (2 * d + 2)
      (cfg (some .scan) none (List.replicate d true) [] []) =
    cfg none none (List.replicate d true) []
      (List.replicate (2 * d) true) := by
  have hs := scan_run d 0 0 none
  have hr := restore_run d 0 (2 * d) none
  simp only [Nat.zero_add, List.replicate_zero] at hs hr
  have h := (run_add hs (d + 1)).trans hr
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end EthInapproximability.CurrentPaper.SourceNormalizationMachineDoubleUnary
