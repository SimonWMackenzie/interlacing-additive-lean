import EthInapproximability.CurrentPaper.MatrixIndexQuotient

/-!
# Unit 4 (Paper A), segment A4-S8 (part 1): the preserving unary REMAINDER machine

Owner lane `owner:a-unit4-shell-2` (private, 25 September 2026).

This is the remainder variant of the admitted `MatrixIndexQuotient` machine. It has the SAME
labels, control, stack layout and sub-programs (copy, then the admitted
`MatrixUnaryDivision` program, reused by exact name through
`MatrixIndexQuotient.program`); it differs ONLY at the terminal clear label, which clears the
quotient stack (6) instead of the remainder stack (5). Hence it leaves `n % m` in unary,
preserves the input `n` and divisor `m`, and leaves every other stack empty. Nothing is computed
in finite control. Diff against `MatrixIndexQuotient.program`: the clause
`| .inr (.inr ()) => pop 5 …` became `pop 6 …`; the other two clauses are the production
clauses themselves.

**None of these statements closes a ledger row** (U17 stays open).
-/

namespace Paper2.Unit4Shell.Remainder

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineComposition
open EthInapproximability.CurrentPaper.BitMachineSubroutine
open EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

abbrev Stack := MatrixIndexQuotient.Stack
abbrev Label := MatrixIndexQuotient.Label
abbrev Control := MatrixIndexQuotient.Control
abbrev Config := MatrixIndexQuotient.Config

/-- The remainder program: `MatrixIndexQuotient.program` except at the clear label. -/
def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => MatrixIndexQuotient.program (.inl l)
  | .inr (.inl l) => MatrixIndexQuotient.program (.inr (.inl l))
  | .inr (.inr ()) => pop 6 (fun v b => (v.1, b.isSome))
      (branch Prod.snd (goto (fun _ => MatrixIndexQuotient.clear))
        (load (fun _ => MatrixIndexQuotient.initial) halt))

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem copy_run (n m : ℕ) :
    ∃ t ≤ 2 * n + 2,
      run t (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.start)
        MatrixIndexQuotient.initial (List.replicate n true)
        (List.replicate m true) [] [] [] [] [] []) =
      MatrixIndexQuotient.cfg (some MatrixIndexQuotient.divide) MatrixIndexQuotient.initial
        (List.replicate n true) (List.replicate m true) (List.replicate n true)
        [] [] [] [] [] := by
  have he := BitMachineCopy.run_correct none (List.replicate n true) []
  simp only [List.length_replicate, List.append_nil] at he
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed MatrixIndexQuotient.copyStacks
    (Equiv.refl _) (Equiv.refl _) BitMachineCopy.program program
    (some (.inl MatrixUnaryDivision.Label.start)) (fun _ => rfl)
    false (fun i => ![List.replicate m true,[],[],[],[]] i)
    (BitMachineCopy.cfg (some .scan) none (List.replicate n true) [] [])
    (2*n+2) (by rw [show ((advance BitMachineCopy.program)^[2*n+2]) _ = _ from he]; rfl)
  change run t (MatrixIndexQuotient.copyFrame (List.replicate m true) [] [] [] [] _) =
    MatrixIndexQuotient.copyFrame (List.replicate m true) [] [] [] []
      (BitMachineCopy.run _ _) at hr
  rw [he] at hr
  have hi : MatrixIndexQuotient.copyFrame (List.replicate m true) [] [] [] []
      (BitMachineCopy.cfg (some .scan) none (List.replicate n true) [] []) =
      MatrixIndexQuotient.cfg (some MatrixIndexQuotient.start) MatrixIndexQuotient.initial
        (List.replicate n true) (List.replicate m true) [] [] [] [] [] [] := by
    unfold MatrixIndexQuotient.copyFrame renameCfg liftCfg MatrixIndexQuotient.cfg
      BitMachineCopy.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : MatrixIndexQuotient.copyFrame (List.replicate m true) [] [] [] []
      (BitMachineCopy.cfg none none (List.replicate n true)
        (List.replicate n true) []) =
      MatrixIndexQuotient.cfg (some MatrixIndexQuotient.divide) MatrixIndexQuotient.initial
        (List.replicate n true) (List.replicate m true) (List.replicate n true)
        [] [] [] [] [] := by
    unfold MatrixIndexQuotient.copyFrame renameCfg liftCfg MatrixIndexQuotient.cfg
      BitMachineCopy.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

theorem division_run (n m : ℕ) :
    ∃ t ≤ MatrixUnaryDivision.totalTime n m,
      run t (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.divide)
        MatrixIndexQuotient.initial (List.replicate n true)
        (List.replicate m true) (List.replicate n true) [] [] [] [] []) =
      MatrixIndexQuotient.cfg (some MatrixIndexQuotient.clear) MatrixIndexQuotient.initial
        (List.replicate n true) (List.replicate m true) [] [] []
        (List.replicate (n % m) true) (List.replicate (n / m) true) [] := by
  have he := MatrixUnaryDivision.division_total_run n m
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed MatrixIndexQuotient.divisionStacks
    MatrixIndexQuotient.divisionLabels
    (Equiv.prodComm _ _) MatrixUnaryDivision.program program
    (some (.inr ())) (fun _ => rfl) none
    (fun i => ![List.replicate n true,[]] i)
    (MatrixUnaryDivision.cfg (some .start) false (List.replicate n true)
      (List.replicate m true) [] [] [] [])
    (MatrixUnaryDivision.totalTime n m)
    (by rw [show ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime n m]) _ = _ from he]; rfl)
  change run t (MatrixIndexQuotient.divisionFrame (List.replicate n true) [] _) =
    MatrixIndexQuotient.divisionFrame (List.replicate n true) []
      (MatrixUnaryDivision.run _ _) at hr
  rw [he] at hr
  have hi : MatrixIndexQuotient.divisionFrame (List.replicate n true) []
      (MatrixUnaryDivision.cfg (some .start) false (List.replicate n true)
        (List.replicate m true) [] [] [] []) =
      MatrixIndexQuotient.cfg (some MatrixIndexQuotient.divide) MatrixIndexQuotient.initial
        (List.replicate n true) (List.replicate m true) (List.replicate n true)
        [] [] [] [] [] := by
    unfold MatrixIndexQuotient.divisionFrame renameCfg liftCfg MatrixIndexQuotient.cfg
      MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : MatrixIndexQuotient.divisionFrame (List.replicate n true) []
      (MatrixUnaryDivision.cfg none false [] (List.replicate m true) []
        (List.replicate (n % m) true) (List.replicate (n / m) true) []) =
      MatrixIndexQuotient.cfg (some MatrixIndexQuotient.clear) MatrixIndexQuotient.initial
        (List.replicate n true) (List.replicate m true) [] [] []
        (List.replicate (n % m) true) (List.replicate (n / m) true) [] := by
    unfold MatrixIndexQuotient.divisionFrame renameCfg liftCfg MatrixIndexQuotient.cfg
      MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

/-- The remainder variant clears the QUOTIENT stack. -/
theorem clear_run (input divisor remainder quotient : List Bool) (v : Control) :
    run (quotient.length+1)
      (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.clear) v input divisor
        [] [] [] remainder quotient []) =
      MatrixIndexQuotient.cfg none MatrixIndexQuotient.initial input divisor
        [] [] [] remainder [] [] := by
  induction quotient generalizing v with
  | nil => simp [run,advance,MatrixIndexQuotient.cfg,MatrixIndexQuotient.clear,program,
      TM2.step,TM2.stepAux]
  | cons b quotient ih =>
      have hs : advance program
          (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.clear) v input divisor
            [] [] [] remainder (b::quotient) []) =
          MatrixIndexQuotient.cfg (some MatrixIndexQuotient.clear) (v.1,true) input divisor
            [] [] [] remainder quotient [] := by
        simp [advance,MatrixIndexQuotient.cfg,MatrixIndexQuotient.clear,program,
          TM2.step,TM2.stepAux]
        funext k
        fin_cases k <;> rfl
      simp only [List.length_cons,run,Function.iterate_succ_apply,hs]
      exact ih (v.1,true)

/-- **Preserving unary remainder.** The fixed remainder machine leaves `n % m` (unary) on stack
5, preserves the input `n` and divisor `m`, and empties every other stack, within
`11 n + 3 m + 7` steps. Does not close a ledger row. -/
theorem remainder_run (n m : ℕ) :
    ∃ t ≤ 11*n + 3*m + 7,
      run t (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.start)
        MatrixIndexQuotient.initial (List.replicate n true)
        (List.replicate m true) [] [] [] [] [] []) =
      MatrixIndexQuotient.cfg none MatrixIndexQuotient.initial (List.replicate n true)
        (List.replicate m true) [] [] [] (List.replicate (n % m) true) [] [] := by
  obtain ⟨a,ha,he⟩ := copy_run n m
  obtain ⟨b,hb,hr⟩ := division_run n m
  have hc := clear_run (List.replicate n true) (List.replicate m true)
    (List.replicate (n%m) true) (List.replicate (n/m) true) MatrixIndexQuotient.initial
  simp only [List.length_replicate] at hc
  refine ⟨a+(b+(n/m+1)),?_,?_⟩
  · have htime := MatrixUnaryDivision.totalTime_bound n m
    have hdiv : n/m ≤ n := Nat.div_le_self _ _
    omega
  · rw [run_add he,run_add hr,hc]

end Paper2.Unit4Shell.Remainder
