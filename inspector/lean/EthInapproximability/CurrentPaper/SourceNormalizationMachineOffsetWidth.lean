import EthInapproximability.CurrentPaper.BitMachineEncoding

/-!
# Physical copy-offset increment by padded support width

The scan counts true support bits into a unary offset and restores the
Boolean vector. This is the per-copy offset update required by ordered
graph normalization; no arithmetic operation is treated as a free clock.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineOffsetWidth

open Turing TM2.Stmt BitMachineEncoding

inductive Phase where
  | scan | restore
  deriving DecidableEq, Fintype

abbrev Stack := Fin 4
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Phase (Option Bool)

def program : Phase → TM2.Stmt (fun _ : Stack => Bool) Phase (Option Bool)
  | .scan => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 1 (fun b => b.getD false)
          (branch (fun b => b.getD false)
            (push 2 (fun _ => true) (goto (fun _ => .scan)))
            (goto (fun _ => .scan))))
        (goto (fun _ => .restore)))
  | .restore => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun b => b.getD false) (goto (fun _ => .restore)))
        halt)

def cfg (l : Option Phase) (s : Option Bool)
    (bits scratch offset payload : List Bool) : Config :=
  ⟨l,s,![bits,scratch,offset,payload]⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem scan_run (bits scratch payload : List Bool) (o : ℕ)
    (s : Option Bool) :
    run (bits.length + 1)
      (cfg (some .scan) s bits scratch (List.replicate o true) payload) =
      cfg (some .restore) none [] (bits.reverse ++ scratch)
        (List.replicate (o + bits.count true) true) payload := by
  induction bits generalizing scratch o s with
  | nil =>
      apply congrArg (fun S => (⟨some Phase.restore, none, S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | cons b bs ih =>
      have hs : TM2.step program
          (cfg (some .scan) s (b :: bs) scratch (List.replicate o true) payload) =
          some (cfg (some .scan) (some b) bs (b :: scratch)
            (List.replicate (o + if b then 1 else 0) true) payload) := by
        cases b <;>
          apply congrArg (fun S => some (⟨some Phase.scan, some _, S⟩ : Config))
        all_goals
          funext k
          fin_cases k <;> simp [List.replicate_succ]
      have h := (run_succ hs (bs.length + 1)).trans
        (ih (b :: scratch) (o + if b then 1 else 0) (some b))
      cases b <;> simpa [Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm, List.append_assoc] using h

private theorem restore_run (bits vector offset payload : List Bool)
    (s : Option Bool) :
    run (bits.length + 1)
      (cfg (some .restore) s vector bits offset payload) =
      cfg none none (bits.reverse ++ vector) [] offset payload := by
  induction bits generalizing vector s with
  | nil =>
      apply congrArg (fun S => (⟨none, none, S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | cons b bs ih =>
      have hs : TM2.step program
          (cfg (some .restore) s vector (b :: bs) offset payload) =
          some (cfg (some .restore) (some b) (b :: vector) bs offset payload) := by
        apply congrArg (fun S => some (⟨some Phase.restore, some b, S⟩ : Config))
        funext k
        fin_cases k <;> rfl
      simpa only [List.length_cons, List.reverse_cons,
        List.singleton_append, List.append_assoc] using
        (run_succ hs (bs.length + 1)).trans (ih (b :: vector) (some b))

/-- A literal `2*bits.length+2` transition scan adding the number of true
support cells to the offset and restoring every input bit. -/
theorem add_width_run (bits payload : List Bool) (o : ℕ) :
    run (2 * bits.length + 2)
      (cfg (some .scan) none bits [] (List.replicate o true) payload) =
      cfg none none bits []
        (List.replicate (o + bits.count true) true) payload := by
  have hs := scan_run bits [] payload o none
  have hr := restore_run bits.reverse []
    (List.replicate (o + bits.count true) true) payload none
  simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hs hr
  have h := (run_add hs (bits.length + 1)).trans hr
  simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end EthInapproximability.CurrentPaper.SourceNormalizationMachineOffsetWidth
