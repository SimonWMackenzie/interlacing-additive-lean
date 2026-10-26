import CurrentAdditive.GenericParameterBranch

/-! A fixed finite bank controller for a fixed finite family of scalar
subprograms. Every subprogram reads the same physical source word, preserves
it, and writes to its own initially empty persistent destination. -/
namespace V22ParameterBatch
open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
variable {Base : Type*} [DecidableEq Base] {q : ℕ}
abbrev Work (M : BitMachine.Machine) := Fin M.stackCount ⊕ Fin 3
abbrev Stack (M : Fin q → BitMachine.Machine) (Base : Type*) := Base ⊕ ((i : Fin q) × Work (M i))
abbrev Label (M : Fin q → BitMachine.Machine) :=
  Fin (q+1) ⊕ ((i : Fin q) × CurrentAdditive.GenericParameterBranch.Label (M i))
abbrev Control (M : Fin q → BitMachine.Machine) :=
  (i : Fin q) → CurrentAdditive.GenericParameterBranch.Control (M i)
def control (M : Fin q → BitMachine.Machine) : Control M :=
  fun i => CurrentAdditive.GenericParameterBranch.startControl (M i)
def slots (M : Fin q → BitMachine.Machine) (i : Fin q) :
    CurrentAdditive.GenericParameterBranch.Stack (M i) Base ↪ Stack M Base where
  toFun | .inl j => .inl j | .inr j => .inr ⟨i,j⟩
  inj' := by
    intro a b h
    cases a with
    | inl a => cases b <;> simp_all
    | inr a => cases b with
      | inl b => cases h
      | inr b => exact congrArg Sum.inr (by simpa using h)
def next (i : Fin q) : Fin (q+1) := ⟨i.val+1,by omega⟩
def injectLabel (M : Fin q → BitMachine.Machine) (i : Fin q)
    (l : CurrentAdditive.GenericParameterBranch.Label (M i)) : Label M := .inr ⟨i,l⟩
def branch (M : Fin q → BitMachine.Machine) (source : Base) (targets : Fin q → Base) (i : Fin q) :=
  CurrentAdditive.GenericParameterBranch.framedProgram (M i) source (targets i) (slots M i)
def program (M : Fin q → BitMachine.Machine) (source : Base) (targets : Fin q → Base) :
    Label M → TM2.Stmt (fun _ : Stack M Base => Bool) (Label M) (Control M)
  | .inl j => if h : j.val<q then
      .load (fun _ => control M) (.goto fun _ =>
        injectLabel M ⟨j.val,h⟩ (CurrentAdditive.GenericParameterBranch.startLabel (M ⟨j.val,h⟩)))
    else .halt
  | .inr ⟨i,l⟩ => BitMachineInline.stmt (injectLabel M i)
      (fun v => Function.update (control M) i v) (fun v => v i)
      (some (.inl (next i))) (branch M source targets i l)

noncomputable def finish (M : Fin q → BitMachine.Machine) (targets : Fin q → Base)
    (i : Fin q) (S : Stack M Base → List Bool) (bits result : List Bool) (T : ℕ) :=
  bank (slots M i) S (CurrentAdditive.GenericParameterBranch.terminal (M i)
    (fun j => S (.inl j)) (targets i) bits result T)
theorem finish_base (M : Fin q → BitMachine.Machine) (targets : Fin q → Base)
    (i : Fin q) (S : Stack M Base → List Bool) (bits result : List Bool) (T : ℕ) (b : Base) :
    finish M targets i S bits result T (.inl b) =
      if b=targets i then result else S (.inl b) := by
  by_cases h : b=targets i
  · subst b
    exact (CurrentAdditive.GenericParameterBranch.ambient_target (M i) (targets i) _ bits result T (slots M i) S).trans (by simp)
  · rw [if_neg h]
    exact CurrentAdditive.GenericParameterBranch.ambient_base_other (M i) (targets i) b h _ bits result T (slots M i) S
theorem finish_work_other (M : Fin q → BitMachine.Machine) (targets : Fin q → Base)
    (i j : Fin q) (hne : j ≠ i) (S : Stack M Base → List Bool)
    (bits result : List Bool) (T : ℕ) (w : Work (M j)) :
    finish M targets i S bits result T (.inr ⟨j,w⟩) = S (.inr ⟨j,w⟩) := by
  apply bank_outside
  rintro ⟨x,hx⟩
  cases x with
  | inl x => cases hx
  | inr x =>
      have h : i=j := congrArg Sigma.fst (Sum.inr.inj hx)
      exact hne h.symm

theorem stage (M : Fin q → BitMachine.Machine) (source : Base) (targets : Fin q → Base)
    (i : Fin q) (S : Stack M Base → List Bool) (bits result : List Bool) (T : ℕ)
    (hsource : S (.inl source)=bits) (htarget : S (.inl (targets i))=[])
    (hfresh : ∀ w : Work (M i), S (.inr ⟨i,w⟩)=[])
    (hM : (M i).OutputsWithin bits result T) :
    ∃ t ≤ 2*bits.length+T+2*result.length+7,
      ((advance (program M source targets))^[t])
        (⟨some (.inl ⟨i.val,by omega⟩),control M,S⟩ :
          TM2.Cfg (fun _ : Stack M Base => Bool) _ _) =
        ⟨some (.inl (next i)),control M,finish M targets i S bits result T⟩ := by
  obtain ⟨u,hu,hr⟩ := CurrentAdditive.GenericParameterBranch.run_install_framed_from_ambient
    (M i) source (targets i) bits result T (slots M i) S hsource htarget hfresh hM
  have hh := congrArg TM2.Cfg.l hr
  have hinv : ∀ v : CurrentAdditive.GenericParameterBranch.Control (M i),
      (Function.update (control M) i v) i = v := fun _ => Function.update_self _ _ _
  obtain ⟨v,hv,hvRun⟩ := BitMachineInline.outputs
    (injectLabel M i) (fun v => Function.update (control M) i v) (fun v => v i)
    hinv (some (.inl (next i))) (branch M source targets i)
    (program M source targets) (by intro l; rfl)
    (⟨some (CurrentAdditive.GenericParameterBranch.startLabel (M i)),CurrentAdditive.GenericParameterBranch.startControl (M i),S⟩ :
      TM2.Cfg (fun _ : Stack M Base => Bool) _ _) u (by simpa only [branch] using hh)
  have hlocal : ((advance (branch M source targets i))^[u])
      (⟨some (CurrentAdditive.GenericParameterBranch.startLabel (M i)),CurrentAdditive.GenericParameterBranch.startControl (M i),S⟩ :
        TM2.Cfg (fun _ : Stack M Base => Bool) _ _) =
      ⟨none,CurrentAdditive.GenericParameterBranch.startControl (M i),finish M targets i S bits result T⟩ := by
    simpa only [branch,finish,slots] using hr
  rw [hlocal] at hvRun
  have hc : Function.update (control M) i (CurrentAdditive.GenericParameterBranch.startControl (M i)) = control M :=
    Function.update_eq_self _ _
  simp only [BitMachineInline.cfg,hc,Option.map_some,Option.getD_none] at hvRun
  have hs : advance (program M source targets)
      (⟨some (.inl ⟨i.val,by omega⟩),control M,S⟩ : TM2.Cfg (fun _ : Stack M Base => Bool) _ _) =
      ⟨some (injectLabel M i (CurrentAdditive.GenericParameterBranch.startLabel (M i))),control M,S⟩ := by
    simp only [advance,TM2.step,program,i.isLt,↓reduceDIte,TM2.stepAux,Option.getD_some]
  exact ⟨v+1,by omega,by rw [Function.iterate_succ_apply,hs]; exact hvRun⟩

noncomputable def banks (M : Fin q → BitMachine.Machine) (targets : Fin q → Base)
    (S : Stack M Base → List Bool) (bits : List Bool)
    (results : Fin q → List Bool) (times : Fin q → ℕ) : ℕ → Stack M Base → List Bool
  | 0 => S
  | j+1 => if h : j<q then finish M targets ⟨j,h⟩
      (banks M targets S bits results times j) bits (results ⟨j,h⟩) (times ⟨j,h⟩)
    else banks M targets S bits results times j
def clockPrefix (bits : List Bool) (results : Fin q → List Bool)
    (times : Fin q → ℕ) : ℕ → ℕ
  | 0 => 0
  | j+1 => if h : j<q then clockPrefix bits results times j+
      (2*bits.length+times ⟨j,h⟩+2*(results ⟨j,h⟩).length+7)
    else clockPrefix bits results times j

theorem banks_base_other (M : Fin q → BitMachine.Machine) (targets : Fin q → Base)
    (S : Stack M Base → List Bool) (bits : List Bool) (results : Fin q → List Bool)
    (times : Fin q → ℕ) (j : ℕ) (b : Base) (hb : ∀ i, b≠targets i) :
    banks M targets S bits results times j (.inl b)=S (.inl b) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [banks]
      split_ifs with h
      · rw [finish_base,if_neg (hb ⟨j,h⟩),ih]
      · exact ih
theorem banks_target (M : Fin q → BitMachine.Machine) (targets : Fin q → Base)
    (hinj : Function.Injective targets) (S : Stack M Base → List Bool) (bits : List Bool)
    (results : Fin q → List Bool) (times : Fin q → ℕ) (j : ℕ) (hj : j≤q) (i : Fin q) :
    banks M targets S bits results times j (.inl (targets i))=
      if i.val<j then results i else S (.inl (targets i)) := by
  induction j with
  | zero => simp [banks]
  | succ j ih =>
      have hlt : j<q := by omega
      simp only [banks,hlt,↓reduceDIte,finish_base]
      by_cases he : i=⟨j,hlt⟩
      · subst i; simp
      · have hne : targets i ≠ targets ⟨j,hlt⟩ := fun h => he (hinj h)
        rw [if_neg hne,ih (by omega)]
        have hiv : i.val≠j := fun h => he (Fin.ext h)
        by_cases h : i.val<j <;> simp [h,show (i.val<j+1)↔(i.val<j) by omega]
theorem banks_work_fresh (M : Fin q → BitMachine.Machine) (targets : Fin q → Base)
    (S : Stack M Base → List Bool) (bits : List Bool) (results : Fin q → List Bool)
    (times : Fin q → ℕ) (j : ℕ) (i : Fin q) (hi : j ≤ i.val) (w : Work (M i)) :
    banks M targets S bits results times j (.inr ⟨i,w⟩)=S (.inr ⟨i,w⟩) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      have hj : j<q := by omega
      simp only [banks,hj,↓reduceDIte]
      rw [finish_work_other M targets ⟨j,hj⟩ i (by
        intro h
        have he := congrArg Fin.val h
        change i.val=j at he
        omega)]
      exact ih (by omega)

theorem run (M : Fin q → BitMachine.Machine) (source : Base) (targets : Fin q → Base)
    (hinj : Function.Injective targets) (hsourceTarget : ∀ i, source≠targets i)
    (S : Stack M Base → List Bool) (bits : List Bool)
    (results : Fin q → List Bool) (times : Fin q → ℕ)
    (hsource : S (.inl source)=bits) (htarget : ∀ i, S (.inl (targets i))=[])
    (hfresh : ∀ i (w : Work (M i)), S (.inr ⟨i,w⟩)=[])
    (hM : ∀ i, (M i).OutputsWithin bits (results i) (times i)) :
    ∃ t ≤ clockPrefix bits results times q+1,
      ((advance (program M source targets))^[t])
        (⟨some (.inl ⟨0,by omega⟩),control M,S⟩ : TM2.Cfg (fun _ : Stack M Base => Bool) _ _) =
        ⟨none,control M,banks M targets S bits results times q⟩ := by
  have hp : ∀ j (hj : j≤q), ∃ t ≤ clockPrefix bits results times j,
      ((advance (program M source targets))^[t])
        (⟨some (.inl ⟨0,by omega⟩),control M,S⟩ : TM2.Cfg (fun _ : Stack M Base => Bool) _ _) =
        ⟨some (.inl ⟨j,by omega⟩),control M,banks M targets S bits results times j⟩ := by
    intro j
    induction j with
    | zero => intro hj; exact ⟨0,by simp [clockPrefix],rfl⟩
    | succ j ih =>
        intro hj
        have hlt : j<q := by omega
        obtain ⟨a,ha,hra⟩ := ih (by omega)
        obtain ⟨b,hb,hrb⟩ := stage M source targets ⟨j,hlt⟩
          (banks M targets S bits results times j) bits (results ⟨j,hlt⟩) (times ⟨j,hlt⟩)
          ((banks_base_other M targets S bits results times j source hsourceTarget).trans hsource)
          (by rw [banks_target M targets hinj S bits results times j (by omega) ⟨j,hlt⟩]; simp [htarget])
          (fun w => (banks_work_fresh M targets S bits results times j ⟨j,hlt⟩ (Nat.le_refl j) w).trans (hfresh _ _))
          (hM ⟨j,hlt⟩)
        refine ⟨b+a,?_,?_⟩
        · simp only [clockPrefix,hlt,↓reduceDIte]; omega
        · rw [Function.iterate_add_apply,hra,hrb]
          simp only [banks,hlt,↓reduceDIte,next]
  obtain ⟨t,ht,hr⟩ := hp q le_rfl
  refine ⟨t+1,by omega,?_⟩
  rw [Function.iterate_succ_apply',hr]
  simp [advance,program,TM2.step,TM2.stepAux]

#print axioms run
end V22ParameterBatch
