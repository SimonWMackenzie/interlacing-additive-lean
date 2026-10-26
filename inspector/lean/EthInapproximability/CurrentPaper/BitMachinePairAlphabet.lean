import EthInapproximability.CurrentPaper.BitMachine
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Exact two-bit lowering of finite stack alphabets

Source: frozen v8 `06-eth.tex`, fixed deterministic bit-machine convention,
and `B-effectivity-details.tex`, cutoff-computation and materialization
algorithms. This is a compiler component, not an assumed machine correctness
certificate. Each pair of Boolean symbols is stored as two consecutive bits.
One finite source statement becomes one finite target statement; a source
stack operation expands to at most a fixed number of target stack operations.
-/

namespace EthInapproximability.CurrentPaper.BitMachinePairAlphabet

open Turing Function

variable {K Λ σ τ : Type*}

def encodeStack : List (Bool × Bool) → List Bool
  | [] => []
  | x :: xs => x.1 :: x.2 :: encodeStack xs

def encodeStacks (S : K → List (Bool × Bool)) : K → List Bool :=
  fun k => encodeStack (S k)

def pairOption : Option Bool → Option Bool → Option (Bool × Bool)
  | some a, some b => some (a, b)
  | _, _ => none

def encodeConfig (c : TM2.Cfg (fun _ : K => Bool × Bool) Λ σ) :
    TM2.Cfg (fun _ : K => Bool) Λ (σ × Option Bool) :=
  ⟨c.l, (c.var, none), encodeStacks c.stk⟩

/-- The second control component holds just one popped bit. It is reset
before any translated continuation or label jump. -/
def lowerStmt : TM2.Stmt (fun _ : K => Bool × Bool) Λ σ →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Option Bool)
  | .push k f q => .push k (fun v => (f v.1).2)
      (.push k (fun v => (f v.1).1) (lowerStmt q))
  | .peek k f q => .pop k (fun v b => (v.1, b))
      (.peek k (fun v b => (f v.1 (pairOption v.2 b), v.2))
        (.branch (fun v => v.2.isSome)
          (.push k (fun v => v.2.getD false)
            (.load (fun v => (v.1, none)) (lowerStmt q)))
          (.load (fun v => (v.1, none)) (lowerStmt q))))
  | .pop k f q => .pop k (fun v b => (v.1, b))
      (.pop k (fun v b => (f v.1 (pairOption v.2 b), none)) (lowerStmt q))
  | .load f q => .load (fun v => (f v.1, none)) (lowerStmt q)
  | .branch f q₁ q₂ => .branch (fun v => f v.1) (lowerStmt q₁) (lowerStmt q₂)
  | .goto f => .goto (fun v => f v.1)
  | .halt => .halt

theorem encodeStack_length (xs : List (Bool × Bool)) :
    (encodeStack xs).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [encodeStack, List.length_cons, ih]; omega

theorem encodeStacks_update [DecidableEq K] (S : K → List (Bool × Bool))
    (k : K) (xs : List (Bool × Bool)) :
    encodeStacks (update S k xs) = update (encodeStacks S) k (encodeStack xs) := by
  funext j
  by_cases h : j = k
  · subst j; simp [encodeStacks]
  · simp [encodeStacks, h]

theorem lowerStmt_correct [DecidableEq K]
    (q : TM2.Stmt (fun _ : K => Bool × Bool) Λ σ)
    (v : σ) (S : K → List (Bool × Bool)) :
    TM2.stepAux (lowerStmt q) (v, none) (encodeStacks S) =
      encodeConfig (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simpa [lowerStmt, TM2.stepAux, encodeConfig, encodeStacks_update,
      encodeStacks, encodeStack] using ih v (update S k (f v :: S k))
  | peek k f q ih =>
    cases hs : S k with
    | nil =>
      have hu : update (encodeStacks S) k [] = encodeStacks S := by
        apply update_eq_self_iff.mpr
        simp [encodeStacks, hs, encodeStack]
      simpa [lowerStmt, TM2.stepAux, encodeConfig, encodeStacks, encodeStack, hs,
        pairOption, hu] using ih (f v none) S
    | cons x xs =>
      rcases x with ⟨a, b⟩
      have hu : update (encodeStacks S) k (a :: b :: encodeStack xs) = encodeStacks S := by
        apply update_eq_self_iff.mpr
        simp [encodeStacks, hs, encodeStack]
      simpa [lowerStmt, TM2.stepAux, encodeConfig, encodeStacks, encodeStack, hs,
        pairOption, hu] using ih (f v (some (a, b))) S
  | pop k f q ih =>
    cases hs : S k with
    | nil =>
      simpa [lowerStmt, TM2.stepAux, encodeConfig, encodeStacks_update,
        encodeStacks, encodeStack, hs, pairOption] using ih (f v none) (update S k [])
    | cons x xs =>
      rcases x with ⟨a, b⟩
      simpa [lowerStmt, TM2.stepAux, encodeConfig, encodeStacks_update,
        encodeStacks, encodeStack, hs, pairOption] using ih (f v (some (a, b))) (update S k xs)
  | load f q ih => simpa only [lowerStmt, TM2.stepAux] using ih (f v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
    cases h : f v <;> simp only [lowerStmt, TM2.stepAux, h,
      cond_false, cond_true, ih₁, ih₂]
  | goto f => rfl
  | halt => rfl

/-- Renumber finite control without changing a stack operation. -/
def renameControl (e : τ ≃ σ) : TM2.Stmt (fun _ : K => Bool) Λ σ →
    TM2.Stmt (fun _ : K => Bool) Λ τ
  | .push k f q => .push k (fun v => f (e v)) (renameControl e q)
  | .peek k f q => .peek k (fun v b => e.symm (f (e v) b)) (renameControl e q)
  | .pop k f q => .pop k (fun v b => e.symm (f (e v) b)) (renameControl e q)
  | .load f q => .load (fun v => e.symm (f (e v))) (renameControl e q)
  | .branch f q₁ q₂ => .branch (fun v => f (e v))
      (renameControl e q₁) (renameControl e q₂)
  | .goto f => .goto (fun v => f (e v))
  | .halt => .halt

def renameConfig (e : τ ≃ σ) (c : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    TM2.Cfg (fun _ : K => Bool) Λ τ := ⟨c.l, e.symm c.var, c.stk⟩

theorem renameControl_correct [DecidableEq K] (e : τ ≃ σ)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (v : σ) (S : K → List Bool) :
    TM2.stepAux (renameControl e q) (e.symm v) S =
      renameConfig e (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => simpa [renameControl, TM2.stepAux] using ih v (update S k (f v :: S k))
  | peek k f q ih => simpa [renameControl, TM2.stepAux] using ih (f v (S k).head?) S
  | pop k f q ih =>
    simpa [renameControl, TM2.stepAux] using ih (f v (S k).head?) (update S k (S k).tail)
  | load f q ih => simpa [renameControl, TM2.stepAux] using ih (f v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
    cases h : f v <;> simp [renameControl, TM2.stepAux, h, ih₁, ih₂]
  | goto f => simp [renameControl, TM2.stepAux, renameConfig]
  | halt => rfl

/-- An explicit three-state encoding, without a choice of finite enumeration. -/
def bitOptionEquiv : Fin 3 ≃ Option Bool where
  toFun i := if i.val = 0 then none else some (decide (i.val = 2))
  invFun
    | none => 0
    | some false => 1
    | some true => 2
  left_inv i := by fin_cases i <;> rfl
  right_inv o := by cases o with | none => rfl | some b => cases b <;> rfl

def controlEquiv (c : ℕ) : Fin (c * 3) ≃ Fin c × Option Bool :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) bitOptionEquiv)

/-- A genuinely finite source machine; every symbol occupies exactly two bits. -/
structure Machine where
  stackCount : ℕ
  labelCount : ℕ
  controlCount : ℕ
  input : Fin stackCount
  output : Fin stackCount
  start : Fin labelCount
  initial : Fin controlCount
  program : Fin labelCount → TM2.Stmt (fun _ : Fin stackCount => Bool × Bool)
    (Fin labelCount) (Fin controlCount)

abbrev Machine.Config (M : Machine) :=
  TM2.Cfg (fun _ : Fin M.stackCount => Bool × Bool)
    (Fin M.labelCount) (Fin M.controlCount)

def Machine.init (M : Machine) (symbols : List (Bool × Bool)) : M.Config :=
  ⟨some M.start, M.initial, fun k => if k = M.input then symbols else []⟩

def Machine.step (M : Machine) (c : M.Config) : M.Config :=
  (TM2.step M.program c).getD c

def Machine.run (M : Machine) (fuel : ℕ) (c : M.Config) : M.Config :=
  (M.step^[fuel]) c

def Machine.compile (M : Machine) : BitMachine.Machine where
  stackCount := M.stackCount
  labelCount := M.labelCount
  controlCount := M.controlCount * 3
  input := M.input
  output := M.output
  start := M.start
  initial := (controlEquiv M.controlCount).symm (M.initial, none)
  program l := renameControl (controlEquiv M.controlCount) (lowerStmt (M.program l))

def Machine.encode (M : Machine) (c : M.Config) : M.compile.Config :=
  renameConfig (controlEquiv M.controlCount) (encodeConfig c)

theorem compile_init (M : Machine) (xs : List (Bool × Bool)) :
    M.compile.init (encodeStack xs) = M.encode (M.init xs) := by
  simp only [BitMachine.Machine.init, Machine.compile, Machine.encode,
    Machine.init, renameConfig, encodeConfig]
  congr 1
  funext k
  by_cases h : k = M.input <;> simp [encodeStacks, h, encodeStack]

theorem compile_step (M : Machine) (c : M.Config) :
    M.compile.step (M.encode c) = M.encode (M.step c) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => rfl
  | some l =>
    change TM2.stepAux (renameControl (controlEquiv M.controlCount)
        (lowerStmt (M.program l))) ((controlEquiv M.controlCount).symm (v, none))
      (encodeStacks S) =
        renameConfig (controlEquiv M.controlCount)
          (encodeConfig (TM2.stepAux (M.program l) v S))
    rw [renameControl_correct, lowerStmt_correct]

theorem compile_run (M : Machine) (fuel : ℕ) (c : M.Config) :
    M.compile.run fuel (M.encode c) = M.encode (M.run fuel c) := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
    have hs : M.run (n + 1) c = M.step (M.run n c) :=
      Function.iterate_succ_apply' _ _ _
    rw [BitMachine.run_succ, hs, ih, compile_step]

theorem compile_run_input (M : Machine) (fuel : ℕ) (xs : List (Bool × Bool)) :
    M.compile.run fuel (M.compile.init (encodeStack xs)) =
      M.encode (M.run fuel (M.init xs)) := by
  rw [compile_init, compile_run]

theorem compile_outputs (M : Machine) (xs ys : List (Bool × Bool)) (fuel : ℕ)
    (hh : (M.run fuel (M.init xs)).l = none)
    (ho : (M.run fuel (M.init xs)).stk M.output = ys) :
    M.compile.OutputsWithin (encodeStack xs) (encodeStack ys) fuel := by
  refine ⟨fuel, le_rfl, ?_, ?_⟩ <;> rw [compile_run_input]
  · exact hh
  · change encodeStack ((M.run fuel (M.init xs)).stk M.output) = encodeStack ys
    rw [ho]

section FiniteLabels

variable {Γ : K → Type*} [DecidableEq Λ]

/-- Restrict labels to a proved finite forward-closed support. The source
program itself is retained, and every possible goto is assigned its witness. -/
def restrictStmt (S : Finset Λ) (q : TM2.Stmt Γ Λ σ) :
    TM2.SupportsStmt S q → TM2.Stmt Γ ↥S σ := by
  intro h
  cases q with
  | push k f q => exact .push k f (restrictStmt S q h)
  | peek k f q => exact .peek k f (restrictStmt S q h)
  | pop k f q => exact .pop k f (restrictStmt S q h)
  | load f q => exact .load f (restrictStmt S q h)
  | branch f q₁ q₂ => exact .branch f (restrictStmt S q₁ h.1) (restrictStmt S q₂ h.2)
  | goto f => exact .goto fun v => ⟨f v, h v⟩
  | halt => exact .halt

def liftLabelConfig (S : Finset Λ) (c : TM2.Cfg Γ ↥S σ) : TM2.Cfg Γ Λ σ :=
  ⟨c.l.map Subtype.val, c.var, c.stk⟩

theorem restrictStmt_correct [DecidableEq K] (S : Finset Λ)
    (q : TM2.Stmt Γ Λ σ) (h : TM2.SupportsStmt S q)
    (v : σ) (tapes : ∀ k, List (Γ k)) :
    liftLabelConfig S (TM2.stepAux (restrictStmt S q h) v tapes) =
      TM2.stepAux q v tapes := by
  induction q generalizing v tapes with
  | push k f q ih => exact ih h v _
  | peek k f q ih => exact ih h _ _
  | pop k f q ih => exact ih h _ _
  | load f q ih => exact ih h _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    change liftLabelConfig S (cond (f v)
      (TM2.stepAux (restrictStmt S q₁ h.1) v tapes)
      (TM2.stepAux (restrictStmt S q₂ h.2) v tapes)) =
      cond (f v) (TM2.stepAux q₁ v tapes) (TM2.stepAux q₂ v tapes)
    cases hf : f v
    · simp only [hf, cond_false]
      exact ih₂ h.2 v tapes
    · simp only [hf, cond_true]
      exact ih₁ h.1 v tapes
  | goto f => rfl
  | halt => rfl

def restrictProgram (S : Finset Λ) (P : Λ → TM2.Stmt Γ Λ σ)
    (hP : ∀ l ∈ S, TM2.SupportsStmt S (P l)) : ↥S → TM2.Stmt Γ ↥S σ :=
  fun l => restrictStmt S (P l.val) (hP l.val l.property)

theorem restrict_step [DecidableEq K] (S : Finset Λ)
    (P : Λ → TM2.Stmt Γ Λ σ) (hP : ∀ l ∈ S, TM2.SupportsStmt S (P l))
    (c : TM2.Cfg Γ ↥S σ) :
    liftLabelConfig S ((TM2.step (restrictProgram S P hP) c).getD c) =
      (TM2.step P (liftLabelConfig S c)).getD (liftLabelConfig S c) := by
  rcases c with ⟨l, v, tapes⟩
  cases l with
  | none => rfl
  | some l => exact restrictStmt_correct S (P l.val) (hP l.val l.property) v tapes

theorem restrict_run [DecidableEq K] (S : Finset Λ)
    (P : Λ → TM2.Stmt Γ Λ σ) (hP : ∀ l ∈ S, TM2.SupportsStmt S (P l))
    (c : TM2.Cfg Γ ↥S σ) (fuel : ℕ) :
    liftLabelConfig S
      (((fun c => (TM2.step (restrictProgram S P hP) c).getD c)^[fuel]) c) =
    ((fun c => (TM2.step P c).getD c)^[fuel]) (liftLabelConfig S c) := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', restrict_step, ih]

end FiniteLabels

section Renumber

variable {K₂ Λ₂ σ₂ Γ₁ Γ₂ : Type*}

def relocateStacks (ek : K₂ ≃ K) (eg : Γ₂ ≃ Γ₁)
    (S : K → List Γ₁) : K₂ → List Γ₂ := fun k => (S (ek k)).map eg.symm

def relocateConfig (ek : K₂ ≃ K) (el : Λ₂ ≃ Λ) (es : σ₂ ≃ σ) (eg : Γ₂ ≃ Γ₁)
    (c : TM2.Cfg (fun _ : K => Γ₁) Λ σ) : TM2.Cfg (fun _ : K₂ => Γ₂) Λ₂ σ₂ :=
  ⟨c.l.map el.symm, es.symm c.var, relocateStacks ek eg c.stk⟩

/-- Change finite encodings by explicit equivalences. -/
def relocateStmt (ek : K₂ ≃ K) (el : Λ₂ ≃ Λ) (es : σ₂ ≃ σ) (eg : Γ₂ ≃ Γ₁) :
    TM2.Stmt (fun _ : K => Γ₁) Λ σ → TM2.Stmt (fun _ : K₂ => Γ₂) Λ₂ σ₂
  | .push k f q => .push (ek.symm k) (fun v => eg.symm (f (es v))) (relocateStmt ek el es eg q)
  | .peek k f q => .peek (ek.symm k)
      (fun v b => es.symm (f (es v) (b.map eg))) (relocateStmt ek el es eg q)
  | .pop k f q => .pop (ek.symm k)
      (fun v b => es.symm (f (es v) (b.map eg))) (relocateStmt ek el es eg q)
  | .load f q => .load (fun v => es.symm (f (es v))) (relocateStmt ek el es eg q)
  | .branch f q₁ q₂ => .branch (fun v => f (es v))
      (relocateStmt ek el es eg q₁) (relocateStmt ek el es eg q₂)
  | .goto f => .goto (fun v => el.symm (f (es v)))
  | .halt => .halt

theorem relocateStacks_update [DecidableEq K] [DecidableEq K₂]
    (ek : K₂ ≃ K) (eg : Γ₂ ≃ Γ₁) (S : K → List Γ₁) (k : K) (xs : List Γ₁) :
    relocateStacks ek eg (update S k xs) =
      update (relocateStacks ek eg S) (ek.symm k) (xs.map eg.symm) := by
  funext j
  by_cases hj : j = ek.symm k
  · subst j
    rw [Function.update_self]
    change List.map eg.symm (update S k xs (ek (ek.symm k))) = xs.map eg.symm
    rw [ek.apply_symm_apply k, Function.update_self]
  · have hj' : ek j ≠ k := by
      intro he
      apply hj
      exact ek.injective (he.trans (ek.apply_symm_apply k).symm)
    simp [relocateStacks, hj, hj']

theorem relocateStacks_head (ek : K₂ ≃ K) (eg : Γ₂ ≃ Γ₁)
    (S : K → List Γ₁) (k : K) :
    ((relocateStacks ek eg S (ek.symm k)).head?).map eg = (S k).head? := by
  cases hs : S k <;> simp [relocateStacks, hs]

theorem relocateStacks_tail [DecidableEq K] [DecidableEq K₂]
    (ek : K₂ ≃ K) (eg : Γ₂ ≃ Γ₁) (S : K → List Γ₁) (k : K) :
    relocateStacks ek eg (update S k (S k).tail) =
      update (relocateStacks ek eg S) (ek.symm k)
        (relocateStacks ek eg S (ek.symm k)).tail := by
  rw [relocateStacks_update]
  simp [relocateStacks, List.map_tail]

theorem relocateStmt_correct [DecidableEq K] [DecidableEq K₂]
    (ek : K₂ ≃ K) (el : Λ₂ ≃ Λ) (es : σ₂ ≃ σ) (eg : Γ₂ ≃ Γ₁)
    (q : TM2.Stmt (fun _ : K => Γ₁) Λ σ) (v : σ) (S : K → List Γ₁) :
    TM2.stepAux (relocateStmt ek el es eg q) (es.symm v) (relocateStacks ek eg S) =
      relocateConfig ek el es eg (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    simpa [relocateStmt, TM2.stepAux, relocateStacks_update, relocateStacks] using
      ih v (update S k (f v :: S k))
  | peek k f q ih =>
    simpa only [relocateStmt, TM2.stepAux, Equiv.apply_symm_apply, relocateStacks_head] using
      ih (f v (S k).head?) S
  | pop k f q ih =>
    simpa only [relocateStmt, TM2.stepAux, Equiv.apply_symm_apply, relocateStacks_head,
      relocateStacks_tail] using ih (f v (S k).head?) (update S k (S k).tail)
  | load f q ih => simpa [relocateStmt, TM2.stepAux] using ih (f v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
    cases h : f v <;> simp [relocateStmt, TM2.stepAux, h, ih₁, ih₂]
  | goto f => simp [relocateStmt, TM2.stepAux, relocateConfig]
  | halt => rfl

theorem relocate_step [DecidableEq K] [DecidableEq K₂]
    (ek : K₂ ≃ K) (el : Λ₂ ≃ Λ) (es : σ₂ ≃ σ) (eg : Γ₂ ≃ Γ₁)
    (P : Λ → TM2.Stmt (fun _ : K => Γ₁) Λ σ)
    (c : TM2.Cfg (fun _ : K => Γ₁) Λ σ) :
    (TM2.step (fun l => relocateStmt ek el es eg (P (el l)))
      (relocateConfig ek el es eg c)).getD (relocateConfig ek el es eg c) =
    relocateConfig ek el es eg ((TM2.step P c).getD c) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => rfl
  | some l =>
    simpa only [relocateConfig, TM2.step, Option.map_some, Option.getD_some,
      Equiv.apply_symm_apply] using relocateStmt_correct ek el es eg (P l) v S

theorem relocate_run [DecidableEq K] [DecidableEq K₂]
    (ek : K₂ ≃ K) (el : Λ₂ ≃ Λ) (es : σ₂ ≃ σ) (eg : Γ₂ ≃ Γ₁)
    (P : Λ → TM2.Stmt (fun _ : K => Γ₁) Λ σ)
    (c : TM2.Cfg (fun _ : K => Γ₁) Λ σ) (fuel : ℕ) :
    ((fun c => (TM2.step (fun l => relocateStmt ek el es eg (P (el l))) c).getD c)^[fuel])
      (relocateConfig ek el es eg c) =
    relocateConfig ek el es eg (((fun c => (TM2.step P c).getD c)^[fuel]) c) := by
  induction fuel with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, relocate_step]

end Renumber

end EthInapproximability.CurrentPaper.BitMachinePairAlphabet
