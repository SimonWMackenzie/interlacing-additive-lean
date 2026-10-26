import EthInapproximability.CurrentPaper.BitMachineEncoding

/-!
# Physical terminal-edge append for source normalization

The existing support vector is scanned into a work stack. Two true cells are
then written at the bottom of the vector, and the old cells are restored in
their original order. The graph payload and original SAT variable count are
ambient stacks and are never addressed by an instruction.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachinePad

open Turing TM2.Stmt BitMachineEncoding

inductive Phase where
  | scan | addFirst | addSecond | restore
  deriving DecidableEq, Fintype

abbrev Stack := Fin 4
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Phase (Option Bool)

def program : Phase → TM2.Stmt (fun _ : Stack => Bool) Phase (Option Bool)
  | .scan => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 1 (fun v => v.getD false) (goto (fun _ => .scan)))
        (goto (fun _ => .addFirst)))
  | .addFirst => push 0 (fun _ => true) (goto (fun _ => .addSecond))
  | .addSecond => push 0 (fun _ => true) (goto (fun _ => .restore))
  | .restore => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun v => v.getD false) (goto (fun _ => .restore)))
        halt)

def cfg (l : Option Phase) (s : Option Bool)
    (vector saved payload originalN : List Bool) : Config :=
  ⟨l, s, ![vector, saved, payload, originalN]⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem scan_run (bits saved payload originalN : List Bool)
    (s : Option Bool) :
    run (bits.length + 1) (cfg (some .scan) s bits saved payload originalN) =
      cfg (some .addFirst) none [] (bits.reverse ++ saved) payload originalN := by
  induction bits generalizing saved s with
  | nil =>
      apply congrArg (fun S => (⟨some Phase.addFirst, none, S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | cons b bs ih =>
      have hs : TM2.step program (cfg (some .scan) s (b :: bs) saved payload originalN) =
          some (cfg (some .scan) (some b) bs (b :: saved) payload originalN) := by
        apply congrArg (fun S => some (⟨some Phase.scan, some b, S⟩ : Config))
        funext k
        fin_cases k <;> rfl
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using (run_succ hs (bs.length + 1)).trans
          (ih (b :: saved) (some b))

private theorem restore_run (saved bits payload originalN : List Bool)
    (s : Option Bool) :
    run (saved.length + 1) (cfg (some .restore) s bits saved payload originalN) =
      cfg none none (saved.reverse ++ bits) [] payload originalN := by
  induction saved generalizing bits s with
  | nil =>
      apply congrArg (fun S => (⟨none, none, S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | cons b bs ih =>
      have hs : TM2.step program (cfg (some .restore) s bits (b :: bs) payload originalN) =
          some (cfg (some .restore) (some b) (b :: bits) bs payload originalN) := by
        apply congrArg (fun S => some (⟨some Phase.restore, some b, S⟩ : Config))
        funext k
        fin_cases k <;> rfl
      simpa only [List.length_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using (run_succ hs (bs.length + 1)).trans
          (ih (b :: bits) (some b))

/-- Appending the new edge's two supported vertices is charged to the actual
vector length; it does not call a host-language list append instruction. -/
theorem append_run (bits payload originalN : List Bool) :
    run (2 * bits.length + 4)
      (cfg (some .scan) none bits [] payload originalN) =
    cfg none none (bits ++ [true, true]) [] payload originalN := by
  have hs := scan_run bits [] payload originalN none
  simp only [List.append_nil] at hs
  have h₁ : TM2.step program (cfg (some .addFirst) none [] bits.reverse payload originalN) =
      some (cfg (some .addSecond) none [true] bits.reverse payload originalN) := by
    apply congrArg (fun S => some (⟨some Phase.addSecond, none, S⟩ : Config))
    funext k
    fin_cases k <;> rfl
  have h₂ : TM2.step program (cfg (some .addSecond) none [true] bits.reverse payload originalN) =
      some (cfg (some .restore) none [true, true] bits.reverse payload originalN) := by
    apply congrArg (fun S => some (⟨some Phase.restore, none, S⟩ : Config))
    funext k
    fin_cases k <;> rfl
  have hr := restore_run bits.reverse [true, true] payload originalN none
  simp only [List.length_reverse, List.reverse_reverse] at hr
  have h12 : run 2 (cfg (some .addFirst) none [] bits.reverse payload originalN) =
      cfg (some .restore) none [true, true] bits.reverse payload originalN :=
    (run_succ h₁ 1).trans (run_succ h₂ 0)
  have ht := (run_add hs 2).trans h12
  have hall := (run_add ht (bits.length + 1)).trans hr
  have htime : bits.length + 1 + 2 + (bits.length + 1) =
      2 * bits.length + 4 := by omega
  rw [htime] at hall
  exact hall

end EthInapproximability.CurrentPaper.SourceNormalizationMachinePad
