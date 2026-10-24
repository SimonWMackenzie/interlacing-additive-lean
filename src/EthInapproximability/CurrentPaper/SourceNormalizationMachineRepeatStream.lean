import EthInapproximability.CurrentPaper.BitMachineEncoding

/-!
# Retained physical stream repetition

This finite-stack loop copies an arbitrary Boolean stream once per unary
counter token, retaining the source stream. The output is in copy-major
order. It is the stream-copy stage used before per-copy endpoint ranking.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineRepeatStream

open Turing TM2.Stmt BitMachineEncoding

inductive Phase where
  | next | copy | restore
  deriving DecidableEq, Fintype

abbrev Stack := Fin 5
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Phase (Option Bool)

def program : Phase → TM2.Stmt (fun _ : Stack => Bool) Phase (Option Bool)
  | .next => pop 2 (fun _ b => b)
      (branch Option.isSome
        (goto (fun _ => .copy))
        halt)
  | .copy => pop 0 (fun _ b => b)
      (branch Option.isSome
        (push 1 (fun b => b.getD false) (goto (fun _ => .copy)))
        (goto (fun _ => .restore)))
  | .restore => pop 1 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun b => b.getD false)
          (push 3 (fun b => b.getD false) (goto (fun _ => .restore))))
        (goto (fun _ => .next)))

def cfg (l : Option Phase) (s : Option Bool)
    (source scratch counter output payload : List Bool) : Config :=
  ⟨l,s,![source,scratch,counter,output,payload]⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

def repeated (xs : List Bool) : ℕ → List Bool
  | 0 => []
  | r + 1 => repeated xs r ++ xs

theorem repeated_eq_flatMap_range (xs : List Bool) (r : ℕ) :
    repeated xs r = (List.range r).flatMap (fun _ => xs) := by
  induction r with
  | zero => rfl
  | succ r ih => simp [repeated, List.range_succ, ih]

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem copy_run (xs scratch counter output payload : List Bool)
    (s : Option Bool) :
    run (xs.length + 1) (cfg (some .copy) s xs scratch counter output payload) =
      cfg (some .restore) none [] (xs.reverse ++ scratch) counter output payload := by
  induction xs generalizing scratch s with
  | nil =>
      apply congrArg (fun S => (⟨some Phase.restore, none, S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | cons b bs ih =>
      have hs : TM2.step program
          (cfg (some .copy) s (b :: bs) scratch counter output payload) =
          some (cfg (some .copy) (some b) bs (b :: scratch) counter output payload) := by
        apply congrArg (fun S => some (⟨some Phase.copy, some b, S⟩ : Config))
        funext k
        fin_cases k <;> rfl
      simpa only [List.length_cons, List.reverse_cons,
        List.singleton_append, List.append_assoc] using
        (run_succ hs (bs.length + 1)).trans (ih (b :: scratch) (some b))

private theorem restore_run (ys source counter output payload : List Bool)
    (s : Option Bool) :
    run (ys.length + 1) (cfg (some .restore) s source ys counter output payload) =
      cfg (some .next) none (ys.reverse ++ source) [] counter
        (ys.reverse ++ output) payload := by
  induction ys generalizing source output s with
  | nil =>
      apply congrArg (fun S => (⟨some Phase.next, none, S⟩ : Config))
      funext k
      fin_cases k <;> rfl
  | cons b bs ih =>
      have hs : TM2.step program
          (cfg (some .restore) s source (b :: bs) counter output payload) =
          some (cfg (some .restore) (some b) (b :: source) bs counter
            (b :: output) payload) := by
        apply congrArg (fun S => some (⟨some Phase.restore, some b, S⟩ : Config))
        funext k
        fin_cases k <;> rfl
      simpa only [List.length_cons, List.reverse_cons,
        List.singleton_append, List.append_assoc] using
        (run_succ hs (bs.length + 1)).trans
          (ih (b :: source) (b :: output) (some b))

private theorem next_run (xs output payload : List Bool) (r : ℕ)
    (s : Option Bool) :
    run 1 (cfg (some .next) s xs [] (List.replicate (r + 1) true)
      output payload) =
    cfg (some .copy) (some true) xs [] (List.replicate r true)
      output payload := by
  apply congrArg (fun S => (⟨some Phase.copy, some true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem finish_run (xs output payload : List Bool) (s : Option Bool) :
    run 1 (cfg (some .next) s xs [] [] output payload) =
      cfg none none xs [] [] output payload := by
  apply congrArg (fun S => (⟨none, none, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

/-- The exact finite-stack loop, with a retained stream and a charged copy
bound. The source-pattern payload is never inspected or changed. -/
theorem repeat_run (xs output payload : List Bool) (r : ℕ)
    (s : Option Bool) :
    run (r * (2 * xs.length + 3) + 1)
      (cfg (some .next) s xs [] (List.replicate r true) output payload) =
      cfg none none xs [] [] (repeated xs r ++ output) payload := by
  induction r generalizing output s with
  | zero =>
      simpa [repeated] using finish_run xs output payload s
  | succ r ih =>
      have hn := next_run xs output payload r s
      have hc := copy_run xs [] (List.replicate r true) output payload (some true)
      have hr := restore_run xs.reverse [] (List.replicate r true) output payload none
      simp only [List.append_nil, List.reverse_reverse, List.length_reverse] at hc hr
      have h := (run_add hn (xs.length + 1)).trans hc
      have h := (run_add h (xs.length + 1)).trans hr
      have h := (run_add h (r * (2 * xs.length + 3) + 1)).trans
        (ih (xs ++ output) none)
      simpa [repeated, List.append_assoc, Nat.succ_mul, Nat.mul_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end EthInapproximability.CurrentPaper.SourceNormalizationMachineRepeatStream
