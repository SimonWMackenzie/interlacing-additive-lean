import EthInapproximability.CurrentPaper.ExactParameterMachineLog
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! A physical copy-then-clog call that leaves its unary source word intact.
The later six-field controller can embed this fixed call at each source slot. -/

namespace EthInapproximability.CurrentPaper.ETHParameterScaleMachineLogCopy

open Turing BitMachineEncoding

noncomputable abbrev logMachine := ExactParameterMachineLog.machine

abbrev Stack := Fin 1 ⊕ (Fin logMachine.stackCount ⊕ Fin 1)
abbrev Label := BitMachineCopy.Label ⊕ Fin logMachine.labelCount
abbrev Control := Option Bool × Fin logMachine.controlCount
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

noncomputable def copyStack : Fin 3 ↪ Stack where
  toFun
    | 0 => .inl 0
    | 1 => .inr (.inl logMachine.input)
    | _ => .inr (.inr 0)
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp at h ⊢

def logStack : Fin logMachine.stackCount ↪ Stack where
  toFun k := .inr (.inl k)
  inj' := by intro a b h; exact Sum.inl_injective (Sum.inr_injective h)

noncomputable def copyControl (v : Option Bool) : Control := (v,logMachine.initial)
def logControl (v : Fin logMachine.controlCount) : Control := (none,v)

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt copyStack Sum.inl
      copyControl Prod.fst (some (.inr logMachine.start))
      (BitMachineCopy.program l)
  | .inr l => BitMachineStackEmbedding.stmt logStack Sum.inr
      logControl Prod.snd none (logMachine.program l)

noncomputable def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

noncomputable def start (q : List Bool) : Config :=
  BitMachineStackEmbedding.cfg copyStack (fun _ => []) Sum.inl
    copyControl (some (.inr logMachine.start))
    (BitMachineCopy.cfg (some .scan) none q [] [])

noncomputable def afterCopy (q : List Bool) : Config :=
  BitMachineStackEmbedding.cfg copyStack (fun _ => []) Sum.inl
    copyControl (some (.inr logMachine.start))
    (BitMachineCopy.cfg none none q q [])

private theorem copy_program_eq (l : BitMachineCopy.Label) :
    program (.inl l) = BitMachineStackEmbedding.stmt copyStack Sum.inl
      copyControl Prod.fst (some (.inr logMachine.start))
      (BitMachineCopy.program l) := rfl

theorem copy_run (q : List Bool) :
    ∃ t ≤ 2*q.length+2, run t (start q) = afterCopy q := by
  have hc := BitMachineCopy.run_correct none q []
  have hh : (BitMachineCopy.run (2*q.length+2)
      (BitMachineCopy.cfg (some .scan) none q [] [])).l = none := by
    rw [hc]; rfl
  obtain ⟨t,ht,he⟩ := BitMachineStackEmbedding.outputs copyStack
    (fun _ => []) Sum.inl copyControl Prod.fst (by intro v; rfl)
    (some (.inr logMachine.start)) BitMachineCopy.program program
    copy_program_eq (BitMachineCopy.cfg (some .scan) none q [] [])
    (2*q.length+2) (by simpa only [BitMachineCopy.run] using hh)
  refine ⟨t,ht,?_⟩
  change ((advance program)^[t]) _ = _ at he
  unfold BitMachineCopy.run at hc
  rw [hc] at he
  simpa only [run, start, afterCopy, List.append_nil] using he

private theorem afterCopy_log_stack (q : List Bool)
    (k : Fin logMachine.stackCount) :
    (afterCopy q).stk (logStack k) =
      if k = logMachine.input then q else [] := by
  dsimp only [afterCopy, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  by_cases hk : k = logMachine.input
  · subst k
    rw [show logStack logMachine.input = copyStack (1 : Fin 3) by
      simp [logStack, copyStack]]
    rw [BitMachineStackEmbedding.bank_at]
    simp [BitMachineCopy.cfg]
  · have hout : ¬ ∃ p : Fin 3, copyStack p = logStack k := by
      rintro ⟨p,hp⟩
      fin_cases p
      · simp [copyStack, logStack] at hp
      · simp [copyStack, logStack] at hp
        exact hk hp.symm
      · simp [copyStack, logStack] at hp
    rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hout]
    simp [hk]

private theorem log_initial (q : List Bool) :
    afterCopy q = BitMachineStackEmbedding.cfg logStack (afterCopy q).stk
      Sum.inr logControl none (logMachine.init q) := by
  have hb := BitMachineStackEmbedding.bank_eq_self logStack
    (afterCopy q).stk (logMachine.init q).stk (by
      intro k
      simpa only [BitMachine.Machine.init] using (afterCopy_log_stack q k).symm)
  change (⟨some (.inr logMachine.start), copyControl none,
      (afterCopy q).stk⟩ : Config) =
    ⟨some (.inr logMachine.start), logControl logMachine.initial,
      BitMachineStackEmbedding.bank logStack (afterCopy q).stk
        (logMachine.init q).stk⟩
  rw [hb]
  rfl

noncomputable def afterLog (q : List Bool) (c : logMachine.Config) : Config :=
  BitMachineStackEmbedding.cfg logStack (afterCopy q).stk Sum.inr
    logControl none c

private theorem log_program_eq (l : Fin logMachine.labelCount) :
    program (.inr l) = BitMachineStackEmbedding.stmt logStack Sum.inr
      logControl Prod.snd none (logMachine.program l) := rfl

theorem log_run (n : ℕ) :
    ∃ (t : ℕ) (c : logMachine.Config),
      t ≤ (UnaryBinaryEncoding.coefficient+6)*(n+1)^2 ∧
      run t (afterCopy (List.replicate n true)) =
        afterLog (List.replicate n true) c ∧
      c.l = none ∧
      c.stk logMachine.output = List.replicate (Nat.clog 2 n) true := by
  obtain ⟨t,ht,hhalt,hout⟩ := ExactParameterMachineLog.outputs n
  let q := List.replicate n true
  have hh : (((advance logMachine.program)^[t]) (logMachine.init q)).l = none :=
    hhalt
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs logStack
    (afterCopy q).stk Sum.inr logControl Prod.snd (by intro v; rfl)
    none logMachine.program program log_program_eq (logMachine.init q) t hh
  let c := logMachine.run t (logMachine.init q)
  refine ⟨u,c,hu.trans ht,?_,hhalt,hout⟩
  change ((advance program)^[u]) _ = _ at he
  exact (congrArg (run u) (log_initial q)).trans he

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t+u) c = run u d := by
  simp only [run] at h ⊢
  rw [show t+u=u+t by omega, Function.iterate_add_apply, h]

theorem copied_log_run (n : ℕ) :
    ∃ (t : ℕ) (c : logMachine.Config),
      t ≤ 2*n+2 + (UnaryBinaryEncoding.coefficient+6)*(n+1)^2 ∧
      run t (start (List.replicate n true)) =
        afterLog (List.replicate n true) c ∧
      c.l = none ∧
      c.stk logMachine.output = List.replicate (Nat.clog 2 n) true := by
  obtain ⟨a,ha,hcopy⟩ := copy_run (List.replicate n true)
  simp only [List.length_replicate] at ha
  obtain ⟨b,c,hb,hlog,hh,ho⟩ := log_run n
  refine ⟨a+b,c,by omega,(run_add hcopy b).trans hlog,hh,ho⟩

theorem afterLog_source (n : ℕ) (c : logMachine.Config) :
    (afterLog (List.replicate n true) c).stk (.inl (0 : Fin 1)) =
      List.replicate n true := by
  have ho : ¬ ∃ k : Fin logMachine.stackCount,
      logStack k = (.inl (0 : Fin 1) : Stack) := by
    rintro ⟨k,hk⟩
    exact Sum.inr_ne_inl hk
  change BitMachineStackEmbedding.bank logStack _ _ _ = _
  rw [BitMachineStackEmbedding.bank_outside _ _ _ _ ho]
  dsimp only [afterCopy, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  rw [show (.inl (0 : Fin 1) : Stack) = copyStack (0 : Fin 3) by
    simp [copyStack]]
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem afterLog_output (n : ℕ) (c : logMachine.Config) :
    (afterLog (List.replicate n true) c).stk (logStack logMachine.output) =
      c.stk logMachine.output := by
  change BitMachineStackEmbedding.bank logStack _ _
    (logStack logMachine.output) = _
  exact BitMachineStackEmbedding.bank_at _ _ _ _

noncomputable def machine : BitMachine.Machine :=
  ofFinite (.inl (0 : Fin 1)) (logStack logMachine.output)
    (.inl .scan) (copyControl none) program

private theorem start_eq_rawInit (q : List Bool) :
    start q = rawInit (.inl (0 : Fin 1)) (.inl .scan)
      (copyControl none) q := by
  let S : Stack → List Bool :=
    fun k => if k = .inl (0 : Fin 1) then q else []
  have hs : ∀ p : Fin 3,
      (BitMachineCopy.cfg (some .scan) none q [] []).stk p = S (copyStack p) := by
    intro p
    fin_cases p <;> simp [S, copyStack, BitMachineCopy.cfg]
  have hb : BitMachineStackEmbedding.bank copyStack (fun _ => [])
      (BitMachineCopy.cfg (some .scan) none q [] []).stk = S := by
    funext k
    by_cases hk : ∃ p : Fin 3, copyStack p = k
    · obtain ⟨p,rfl⟩ := hk
      rw [BitMachineStackEmbedding.bank_at]
      exact hs p
    · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hk]
      have hne : k ≠ (.inl (0 : Fin 1) : Stack) := by
        intro he
        exact hk ⟨0, by simpa [copyStack] using he.symm⟩
      simp [S, hne]
  change (⟨some (.inl .scan), copyControl none,
      BitMachineStackEmbedding.bank copyStack (fun _ => [])
        (BitMachineCopy.cfg (some .scan) none q [] []).stk⟩ : Config) =
    ⟨some (.inl .scan), copyControl none, S⟩
  rw [hb]

theorem outputs (n : ℕ) :
    machine.OutputsWithin (List.replicate n true)
      (List.replicate (Nat.clog 2 n) true)
      (2*n+2 + (UnaryBinaryEncoding.coefficient+6)*(n+1)^2) := by
  obtain ⟨t,c,ht,hr,hh,ho⟩ := copied_log_run n
  apply outputsWithin_of_raw_run (.inl (0 : Fin 1))
    (logStack logMachine.output) (.inl .scan) (copyControl none)
    program (List.replicate n true) (List.replicate (Nat.clog 2 n) true)
    t _ ht
  · rw [← start_eq_rawInit, ← run, hr]
    simp [afterLog, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hh]
  · rw [← start_eq_rawInit, ← run, hr, afterLog_output, ho]

end EthInapproximability.CurrentPaper.ETHParameterScaleMachineLogCopy
