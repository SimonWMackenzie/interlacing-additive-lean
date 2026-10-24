import EthInapproximability.CurrentPaper.MatrixIndexQuotient
import EthInapproximability.CurrentPaper.MatrixTableLookup
import EthInapproximability.CurrentPaper.MatrixTableWriter
import EthInapproximability.CurrentPaper.FinalPadding

/-!
# Unit 4 (Paper B), segment B4-S4 (core): the physical first-input padded-table writer

Lane owner:b-unit4-shell-3 (private, 26 September 2026). Source: lock v8 `06-eth.tex`, the
common square padding `FinalPadding.table R p hm hr` (first-input repetition
`FinalPadding.inputMap`, NOT a modulo repetition).

1. `Clamp`: the admitted `MatrixIndexQuotient` machine (copy the label, divide the copy by the
   dimension with the admitted `MatrixUnaryDivision`) with ONE changed clause: the terminal
   clear label clears the quotient and, iff the quotient was nonzero, also the remainder. It
   leaves `clampQ x d = if x / d = 0 then x % d else 0` in unary (for `d > 0`, exactly
   `if x < d then x else 0`, the zero-based `FinalPadding.inputMap` index), preserving `x` and
   `d`. The copy and division clauses are the production clauses themselves.
2. One fixed 13-stack entry program: clamp the row index against `m`, clamp the column index
   against `r`, admitted `MatrixTableLookup.lookup_run` at `clamp(x,m) * r + clamp(y,r)` in the
   row-major source word, clear both clamps. Structure adapted (text template only, nothing
   imported) from the Paper A private lane module `a-unit4-shell-owner-2/A4SquareWriter.lean`
   (remainder replaced by the clamp).
3. The admitted `MatrixTableWriter.write_rowMajor` with `2^p × 2^p` cells writes exactly
   `FinalPadding.table R p hm hr`.

The writer's entry configuration (unary `2^p` in both counters, and the persistent bank
`![unary m, unary r, rowMajor R, …]`) is the stated start state; `U4PostExponent` produces the
counters and the H-B2 bank supplies `m`, `r`, `rowMajor R`; their join into ONE machine on the
encoded word is NOT done in this module.
-/

namespace EthInapproximability.CurrentPaper.Unit4Post

open Turing Turing.TM2.Stmt
open BitMachineEncoding BitMachineComposition BitMachineSubroutine BitMachineSubroutineRenaming

/-- The clamp value computed by the machine (for `d > 0`: `x` if `x < d`, else `0`). -/
def clampQ (x d : ℕ) : ℕ := if x / d = 0 then x % d else 0

theorem clampQ_le (x d : ℕ) : clampQ x d ≤ x := by
  unfold clampQ
  split
  · exact Nat.mod_le _ _
  · omega

theorem clampQ_eq {x d : ℕ} (hd : 0 < d) : clampQ x d = if x < d then x else 0 := by
  unfold clampQ
  by_cases h : x < d
  · have h0 : x / d = 0 := Nat.div_eq_of_lt h
    rw [if_pos h0, if_pos h, Nat.mod_eq_of_lt h]
  · have h0 : x / d ≠ 0 := by
      intro h0
      rw [Nat.div_eq_zero_iff] at h0
      omega
    rw [if_neg h0, if_neg h]

theorem clampQ_inputMap {d : ℕ} (p : ℕ) (hd : 0 < d) (u : Fin (2 ^ p)) :
    clampQ u.val d = (FinalPadding.inputMap d p hd u).val := by
  rw [clampQ_eq hd]
  by_cases h : u.val < d
  · simp [FinalPadding.inputMap, h]
  · simp [FinalPadding.inputMap, h]

namespace Clamp

abbrev Stack := MatrixIndexQuotient.Stack
abbrev Label := MatrixIndexQuotient.Label
abbrev Control := MatrixIndexQuotient.Control
abbrev Config := MatrixIndexQuotient.Config

/-- `MatrixIndexQuotient.program` except at the clear label. -/
def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => MatrixIndexQuotient.program (.inl l)
  | .inr (.inl l) => MatrixIndexQuotient.program (.inr (.inl l))
  | .inr (.inr ()) => pop 6 (fun v b => (if b.isSome then some true else v.1, b.isSome))
      (branch Prod.snd (goto (fun _ => MatrixIndexQuotient.clear))
        (branch (fun v => v.1.isSome)
          (pop 5 (fun v b => (v.1, b.isSome))
            (branch Prod.snd (goto (fun _ => MatrixIndexQuotient.clear))
              (load (fun _ => MatrixIndexQuotient.initial) halt)))
          (load (fun _ => MatrixIndexQuotient.initial) halt)))

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
    (by rw [show ((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime n m]) _
      = _ from he]; rfl)
  change run t (MatrixIndexQuotient.divisionFrame (List.replicate n true) [] _) =
    MatrixIndexQuotient.divisionFrame (List.replicate n true) []
      (MatrixUnaryDivision.run _ _) at hr
  rw [he] at hr
  have hi : MatrixIndexQuotient.divisionFrame (List.replicate n true) []
      (MatrixUnaryDivision.cfg (some .start) false (List.replicate n true)
        (List.replicate m true) [] [] [] []) =
      MatrixIndexQuotient.cfg (some MatrixIndexQuotient.divide) MatrixIndexQuotient.initial
        (List.replicate n true)
        (List.replicate m true) (List.replicate n true) [] [] [] [] [] := by
    unfold MatrixIndexQuotient.divisionFrame renameCfg liftCfg MatrixIndexQuotient.cfg
      MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : MatrixIndexQuotient.divisionFrame (List.replicate n true) []
      (MatrixUnaryDivision.cfg none false [] (List.replicate m true) []
        (List.replicate (n % m) true) (List.replicate (n / m) true) []) =
      MatrixIndexQuotient.cfg (some MatrixIndexQuotient.clear) MatrixIndexQuotient.initial
        (List.replicate n true)
        (List.replicate m true) [] [] [] (List.replicate (n % m) true)
        (List.replicate (n / m) true) [] := by
    unfold MatrixIndexQuotient.divisionFrame renameCfg liftCfg MatrixIndexQuotient.cfg
      MatrixUnaryDivision.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t,ht,by simpa only [hi,hf] using hr⟩

theorem quot_step (x d rem quo : List Bool) (b : Bool) (v : Control) :
    advance program (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.clear) v x d [] [] []
      rem (b :: quo) []) =
    MatrixIndexQuotient.cfg (some MatrixIndexQuotient.clear) (some true, true) x d [] [] []
      rem quo [] := by
  apply congrArg (fun S => (⟨some MatrixIndexQuotient.clear, (some true, true), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem rem_step (x d rem : List Bool) (b c : Bool) :
    advance program (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.clear) (some true, c)
      x d [] [] [] (b :: rem) [] []) =
    MatrixIndexQuotient.cfg (some MatrixIndexQuotient.clear) (some true, true) x d [] [] []
      rem [] [] := by
  apply congrArg (fun S => (⟨some MatrixIndexQuotient.clear, (some true, true), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem rem_done (x d : List Bool) (c : Bool) :
    advance program (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.clear) (some true, c)
      x d [] [] [] [] [] []) =
    MatrixIndexQuotient.cfg none MatrixIndexQuotient.initial x d [] [] [] [] [] [] := by
  apply congrArg (fun S => (⟨none, MatrixIndexQuotient.initial, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem keep_done (x d rem : List Bool) :
    advance program (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.clear)
      MatrixIndexQuotient.initial x d [] [] [] rem [] []) =
    MatrixIndexQuotient.cfg none MatrixIndexQuotient.initial x d [] [] [] rem [] [] := by
  apply congrArg (fun S => (⟨none, MatrixIndexQuotient.initial, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem quot_run (x d rem : List Bool) (q : ℕ) (v : Control) :
    run (q + 1) (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.clear) v x d [] [] []
      rem (List.replicate (q + 1) true) []) =
    MatrixIndexQuotient.cfg (some MatrixIndexQuotient.clear) (some true, true) x d [] [] []
      rem [] [] := by
  induction q generalizing v with
  | zero =>
      simp only [Nat.zero_add, run, Function.iterate_one, List.replicate_one]
      exact quot_step x d rem [] true v
  | succ q ih =>
      rw [run, Function.iterate_succ_apply, List.replicate_succ, quot_step]
      exact ih (some true, true)

theorem rem_run (x d : List Bool) (r : ℕ) (c : Bool) :
    run (r + 1) (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.clear) (some true, c)
      x d [] [] [] (List.replicate r true) [] []) =
    MatrixIndexQuotient.cfg none MatrixIndexQuotient.initial x d [] [] [] [] [] [] := by
  induction r generalizing c with
  | zero =>
      simp only [Nat.zero_add, run, Function.iterate_one, List.replicate_zero]
      exact rem_done x d c
  | succ r ih =>
      rw [run, Function.iterate_succ_apply, List.replicate_succ, rem_step]
      exact ih true

/-- **The preserving clamp.** Unary `x` and `d` survive; `clampQ x d` is left in unary on
the remainder stack; every other stack is empty. -/
theorem clamp_run (x d : ℕ) :
    ∃ t ≤ 12 * x + 3 * d + 8,
      run t (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.start)
        MatrixIndexQuotient.initial (List.replicate x true)
        (List.replicate d true) [] [] [] [] [] []) =
      MatrixIndexQuotient.cfg none MatrixIndexQuotient.initial (List.replicate x true)
        (List.replicate d true) [] [] [] (List.replicate (clampQ x d) true) [] [] := by
  obtain ⟨a, ha, he⟩ := copy_run x d
  obtain ⟨b, hb, hr⟩ := division_run x d
  have htime := MatrixUnaryDivision.totalTime_bound x d
  have hmod : x % d ≤ x := Nat.mod_le _ _
  have hdiv : x / d ≤ x := Nat.div_le_self _ _
  by_cases hq : x / d = 0
  · have hk := keep_done (List.replicate x true) (List.replicate d true)
      (List.replicate (x % d) true)
    rw [hq, List.replicate_zero] at hr
    refine ⟨a + (b + 1), by omega, ?_⟩
    rw [run_add he, run_add hr]
    simp only [clampQ, hq, ↓reduceIte]
    exact hk
  · obtain ⟨q, hq'⟩ := Nat.exists_eq_succ_of_ne_zero hq
    rw [hq'] at hr
    have h1 := quot_run (List.replicate x true) (List.replicate d true)
      (List.replicate (x % d) true) q MatrixIndexQuotient.initial
    have h2 := rem_run (List.replicate x true) (List.replicate d true) (x % d) true
    refine ⟨a + (b + ((q + 1) + (x % d + 1))), by omega, ?_⟩
    rw [run_add he, run_add hr, run_add h1, h2]
    simp only [clampQ, hq, ↓reduceIte, List.replicate_zero]

end Clamp

namespace PadWriter

abbrev Stack := Fin 13
abbrev RLabel := MatrixIndexQuotient.Label
abbrev Label := RLabel ⊕ (RLabel ⊕ (MatrixTableLookup.Label ⊕ Bool))
abbrev Control := MatrixIndexQuotient.Control × MatrixTableLookup.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (MatrixIndexQuotient.initial, MatrixTableLookup.initial)
def start : Label := .inl MatrixIndexQuotient.start
def colStart : Label := .inr (.inl MatrixIndexQuotient.start)
def lookStart : Label := .inr (.inr (.inl MatrixTableLookup.start))
def clearX : Label := .inr (.inr (.inr false))
def clearY : Label := .inr (.inr (.inr true))

/-! Global stack layout: `0 x, 1 m, 2 y, 3 r, 4 source, 5 answer, 6 cx, 7 cy, 8-12 scratch`. -/

def rowPermutation : Stack ≃ Stack where
  toFun := ![0,1,8,9,10,6,11,12,2,3,4,5,7]
  invFun := ![0,1,8,9,10,11,5,12,2,3,4,6,7]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def rowStacks : MatrixIndexQuotient.Stack ⊕ Fin 5 ≃ Stack :=
  finSumFinEquiv.trans rowPermutation

def colPermutation : Stack ≃ Stack where
  toFun := ![2,3,8,9,10,7,11,12,0,1,4,5,6]
  invFun := ![8,9,0,1,10,11,12,5,2,3,4,6,7]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def colStacks : MatrixIndexQuotient.Stack ⊕ Fin 5 ≃ Stack :=
  finSumFinEquiv.trans colPermutation

def lookPermutation : Stack ≃ Stack where
  toFun := ![6,3,7,8,9,10,4,5,11,12,0,1,2]
  invFun := ![10,11,12,1,6,7,0,2,3,4,5,8,9]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def lookStacks : MatrixTableLookup.Stack ⊕ Fin 3 ≃ Stack :=
  finSumFinEquiv.trans lookPermutation

def colLabels : RLabel ⊕ (RLabel ⊕ (MatrixTableLookup.Label ⊕ Bool)) ≃ Label where
  toFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inr l)
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inr l)
  left_inv l := by rcases l with l | (l | l) <;> rfl
  right_inv l := by rcases l with l | (l | l) <;> rfl

def lookLabels : MatrixTableLookup.Label ⊕ (RLabel ⊕ (RLabel ⊕ Bool)) ≃ Label where
  toFun
    | .inl l => .inr (.inr (.inl l))
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inl l)
    | .inr (.inr (.inr b)) => .inr (.inr (.inr b))
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inr (.inr (.inl l))
    | .inr (.inr (.inl l)) => .inl l
    | .inr (.inr (.inr b)) => .inr (.inr (.inr b))
  left_inv l := by rcases l with l | (l | (l | b)) <;> rfl
  right_inv l := by rcases l with l | (l | (l | b)) <;> rfl

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt rowStacks (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixIndexQuotient.start)) (Clamp.program l))
  | .inr (.inl l) => renameStmt colStacks colLabels (Equiv.refl _)
      (liftStmt (some (.inr (.inl MatrixTableLookup.start))) (Clamp.program l))
  | .inr (.inr (.inl l)) => renameStmt lookStacks lookLabels (Equiv.prodComm _ _)
      (liftStmt (some (.inr (.inr false))) (MatrixTableLookup.program l))
  | .inr (.inr (.inr false)) => pop 6 (fun v b => ((v.1.1, b.isSome), v.2))
      (branch (fun v => v.1.2) (goto (fun _ => clearX)) (goto (fun _ => clearY)))
  | .inr (.inr (.inr true)) => pop 7 (fun v b => ((v.1.1, b.isSome), v.2))
      (branch (fun v => v.1.2) (goto (fun _ => clearY)) (load (fun _ => initial) halt))

def cfg (l : Option Label) (v : Control) (x m y n source answer : List Bool)
    (rx ry : List Bool := []) : Config :=
  ⟨l, v, ![x, m, y, n, source, answer, rx, ry, [], [], [], [], []]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def rowFrame (y n source answer ry : List Bool) (c : Clamp.Config) : Config :=
  renameCfg rowStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl MatrixIndexQuotient.start)) MatrixTableLookup.initial
      (fun i => ![y, n, source, answer, ry] i) c)

theorem row_run (x m : ℕ) (y n source answer : List Bool) :
    ∃ t ≤ 12*x + 3*m + 8,
      run t (cfg (some start) initial (List.replicate x true) (List.replicate m true)
        y n source answer) =
      cfg (some colStart) initial (List.replicate x true) (List.replicate m true)
        y n source answer (List.replicate (clampQ x m) true) [] := by
  obtain ⟨a,ha,hh⟩ := Clamp.clamp_run x m
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed rowStacks (Equiv.refl _) (Equiv.refl _)
    Clamp.program program (some (.inl MatrixIndexQuotient.start)) (fun _ => rfl)
    MatrixTableLookup.initial (fun i => ![y, n, source, answer, []] i)
    (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.start) MatrixIndexQuotient.initial
      (List.replicate x true) (List.replicate m true) [] [] [] [] [] []) a
    (by rw [show ((advance Clamp.program)^[a]) _ = _ from hh]; rfl)
  change run t (rowFrame y n source answer [] _) =
    rowFrame y n source answer [] (Clamp.run _ _) at hr
  rw [hh] at hr
  have hi : rowFrame y n source answer []
      (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.start) MatrixIndexQuotient.initial
        (List.replicate x true) (List.replicate m true) [] [] [] [] [] []) =
      cfg (some start) initial (List.replicate x true) (List.replicate m true)
        y n source answer := by
    unfold rowFrame renameCfg liftCfg cfg MatrixIndexQuotient.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : rowFrame y n source answer []
      (MatrixIndexQuotient.cfg none MatrixIndexQuotient.initial (List.replicate x true)
        (List.replicate m true) [] [] [] (List.replicate (clampQ x m) true) [] []) =
      cfg (some colStart) initial (List.replicate x true) (List.replicate m true)
        y n source answer (List.replicate (clampQ x m) true) [] := by
    unfold rowFrame renameCfg liftCfg cfg MatrixIndexQuotient.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t, ht.trans ha, by simpa only [hi, hf] using hr⟩

def colFrame (x m source answer rx : List Bool) (c : Clamp.Config) : Config :=
  renameCfg colStacks colLabels (Equiv.refl _)
    (liftCfg (some (.inr (.inl MatrixTableLookup.start))) MatrixTableLookup.initial
      (fun i => ![x, m, source, answer, rx] i) c)

theorem col_run (y n : ℕ) (x m source answer rx : List Bool) :
    ∃ t ≤ 12*y + 3*n + 8,
      run t (cfg (some colStart) initial x m (List.replicate y true) (List.replicate n true)
        source answer rx []) =
      cfg (some lookStart) initial x m (List.replicate y true) (List.replicate n true)
        source answer rx (List.replicate (clampQ y n) true) := by
  obtain ⟨a,ha,hh⟩ := Clamp.clamp_run y n
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed colStacks colLabels (Equiv.refl _)
    Clamp.program program (some (.inr (.inl MatrixTableLookup.start))) (fun _ => rfl)
    MatrixTableLookup.initial (fun i => ![x, m, source, answer, rx] i)
    (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.start) MatrixIndexQuotient.initial
      (List.replicate y true) (List.replicate n true) [] [] [] [] [] []) a
    (by rw [show ((advance Clamp.program)^[a]) _ = _ from hh]; rfl)
  change run t (colFrame x m source answer rx _) =
    colFrame x m source answer rx (Clamp.run _ _) at hr
  rw [hh] at hr
  have hi : colFrame x m source answer rx
      (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.start) MatrixIndexQuotient.initial
        (List.replicate y true) (List.replicate n true) [] [] [] [] [] []) =
      cfg (some colStart) initial x m (List.replicate y true) (List.replicate n true)
        source answer rx [] := by
    unfold colFrame renameCfg liftCfg cfg MatrixIndexQuotient.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : colFrame x m source answer rx
      (MatrixIndexQuotient.cfg none MatrixIndexQuotient.initial (List.replicate y true)
        (List.replicate n true) [] [] [] (List.replicate (clampQ y n) true) [] []) =
      cfg (some lookStart) initial x m (List.replicate y true) (List.replicate n true)
        source answer rx (List.replicate (clampQ y n) true) := by
    unfold colFrame renameCfg liftCfg cfg MatrixIndexQuotient.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t, ht.trans ha, by simpa only [hi, hf] using hr⟩

def lookFrame (x m y : List Bool) (c : MatrixTableLookup.Config) : Config :=
  renameCfg lookStacks lookLabels (Equiv.prodComm _ _)
    (liftCfg (some (.inr (.inr false))) MatrixIndexQuotient.initial
      (fun i => ![x, m, y] i) c)

theorem look_run (rx n ry : ℕ) (x m y source answer : List Bool) :
    ∃ t ≤ 32*(rx+n+ry+source.length+1)^2,
      run t (cfg (some lookStart) initial x m y (List.replicate n true) source answer
        (List.replicate rx true) (List.replicate ry true)) =
      cfg (some clearX) initial x m y (List.replicate n true) source
        (source[rx*n+ry]?.getD false :: answer)
        (List.replicate rx true) (List.replicate ry true) := by
  obtain ⟨a,ha,hh⟩ := MatrixTableLookup.lookup_run rx n ry source answer
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed lookStacks lookLabels (Equiv.prodComm _ _)
    MatrixTableLookup.program program (some (.inr (.inr false))) (fun _ => rfl)
    MatrixIndexQuotient.initial (fun i => ![x, m, y] i)
    (MatrixTableLookup.cfg (some MatrixTableLookup.start) MatrixTableLookup.initial
      (List.replicate rx true) (List.replicate n true) (List.replicate ry true) []
      source answer) a
    (by rw [show ((advance MatrixTableLookup.program)^[a]) _ = _ from hh]; rfl)
  change run t (lookFrame x m y _) = lookFrame x m y (MatrixTableLookup.run _ _) at hr
  rw [hh] at hr
  have hi : lookFrame x m y
      (MatrixTableLookup.cfg (some MatrixTableLookup.start) MatrixTableLookup.initial
        (List.replicate rx true) (List.replicate n true) (List.replicate ry true) []
        source answer) =
      cfg (some lookStart) initial x m y (List.replicate n true) source answer
        (List.replicate rx true) (List.replicate ry true) := by
    unfold lookFrame renameCfg liftCfg cfg MatrixTableLookup.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : lookFrame x m y
      (MatrixTableLookup.cfg none MatrixTableLookup.initial
        (List.replicate rx true) (List.replicate n true) (List.replicate ry true) []
        source (source[rx*n+ry]?.getD false :: answer)) =
      cfg (some clearX) initial x m y (List.replicate n true) source
        (source[rx*n+ry]?.getD false :: answer)
        (List.replicate rx true) (List.replicate ry true) := by
    unfold lookFrame renameCfg liftCfg cfg MatrixTableLookup.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t, ht.trans ha, by simpa only [hi, hf] using hr⟩

theorem clearX_run (x m y n source answer rx ry : List Bool) (v : Control) :
    run (rx.length+1) (cfg (some clearX) v x m y n source answer rx ry) =
      cfg (some clearY) ((v.1.1, false), v.2) x m y n source answer [] ry := by
  induction rx generalizing v with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, run, Function.iterate_one]
      simp [advance, cfg, clearX, clearY, program, TM2.step, TM2.stepAux]
  | cons b rx ih =>
      have hs : advance program (cfg (some clearX) v x m y n source answer (b::rx) ry) =
          cfg (some clearX) ((v.1.1, true), v.2) x m y n source answer rx ry := by
        simp [advance, cfg, clearX, program, TM2.step, TM2.stepAux]
        funext k
        fin_cases k <;> rfl
      simp only [List.length_cons, run, Function.iterate_succ_apply, hs]
      exact ih ((v.1.1, true), v.2)

theorem clearY_run (x m y n source answer ry : List Bool) (v : Control) :
    run (ry.length+1) (cfg (some clearY) v x m y n source answer [] ry) =
      cfg none initial x m y n source answer := by
  induction ry generalizing v with
  | nil =>
      simp only [List.length_nil, Nat.zero_add, run, Function.iterate_one]
      simp [advance, cfg, clearY, program, TM2.step, TM2.stepAux]
  | cons b ry ih =>
      have hs : advance program (cfg (some clearY) v x m y n source answer [] (b::ry)) =
          cfg (some clearY) ((v.1.1, true), v.2) x m y n source answer [] ry := by
        simp [advance, cfg, clearY, program, TM2.step, TM2.stepAux]
        funext k
        fin_cases k <;> rfl
      simp only [List.length_cons, run, Function.iterate_succ_apply, hs]
      exact ih ((v.1.1, true), v.2)

/-- The uniform callback bound (quadratic in all unary inputs and the source length). -/
def callbackBound (x y m n sourceLength : ℕ) : ℕ :=
  80 * (x + y + m + n + sourceLength + 1) ^ 2

/-- **One physical first-input padding lookup.** -/
theorem pad_lookup_run (x y m n : ℕ) (source answer : List Bool) :
    ∃ t ≤ callbackBound x y m n source.length,
      run t (cfg (some start) initial (List.replicate x true) (List.replicate m true)
        (List.replicate y true) (List.replicate n true) source answer) =
      cfg none initial (List.replicate x true) (List.replicate m true)
        (List.replicate y true) (List.replicate n true) source
        (source[clampQ x m * n + clampQ y n]?.getD false :: answer) := by
  obtain ⟨a,ha,h1⟩ := row_run x m (List.replicate y true) (List.replicate n true) source answer
  obtain ⟨b,hb,h2⟩ := col_run y n (List.replicate x true) (List.replicate m true) source answer
    (List.replicate (clampQ x m) true)
  obtain ⟨c,hc,h3⟩ := look_run (clampQ x m) n (clampQ y n) (List.replicate x true)
    (List.replicate m true) (List.replicate y true) source answer
  have h4 := clearX_run (List.replicate x true) (List.replicate m true)
    (List.replicate y true) (List.replicate n true) source
    (source[clampQ x m * n + clampQ y n]?.getD false :: answer)
    (List.replicate (clampQ x m) true) (List.replicate (clampQ y n) true) initial
  have h5 := clearY_run (List.replicate x true) (List.replicate m true)
    (List.replicate y true) (List.replicate n true) source
    (source[clampQ x m * n + clampQ y n]?.getD false :: answer)
    (List.replicate (clampQ y n) true) ((initial.1.1, false), initial.2)
  simp only [List.length_replicate] at h4 h5
  refine ⟨a + (b + (c + ((clampQ x m + 1) + (clampQ y n + 1)))), ?_, ?_⟩
  · let N := x + y + m + n + source.length + 1
    have hN : 1 ≤ N := by dsimp [N]; omega
    have hxm : clampQ x m ≤ x := clampQ_le _ _
    have hyn : clampQ y n ≤ y := clampQ_le _ _
    have hq : clampQ x m + n + clampQ y n + source.length + 1 ≤ N := by dsimp [N]; omega
    have hsq := Nat.pow_le_pow_left hq 2
    have hlin : 12*x + 3*m + 8 + (12*y + 3*n + 8) + (clampQ x m + 1 + (clampQ y n + 1))
        ≤ 30 * N := by
      dsimp [N]; omega
    have hN2 : N ≤ N ^ 2 := by nlinarith [Nat.mul_le_mul (le_refl N) hN]
    change a + (b + (c + ((clampQ x m + 1) + (clampQ y n + 1)))) ≤ 80 * N ^ 2
    nlinarith
  · rw [run_add h1, run_add h2, run_add h3, run_add h4, h5]

/-! ## The entry program inside the admitted writer -/

abbrev CellStack := MatrixTableWriter.CellStack 10

private def writerPermutation : Stack ≃ Stack where
  toFun := ![1,3,4,6,7,8,9,10,11,12,0,2,5]
  invFun := ![10,0,11,1,2,12,3,4,5,6,7,8,9]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def writerSlots : CellStack ≃ Stack := finSumFinEquiv.trans writerPermutation

def entryProgram (l : Label) : TM2.Stmt (fun _ : CellStack => Bool) Label Control :=
  renameStmt writerSlots.symm (Equiv.refl _) (Equiv.refl _) (program l)

/-- The persistent writer bank: unary `m`, unary `r`, the row-major source word, and seven
stacks that are empty before and after every cell. -/
def persistentBank (m n : ℕ) (source : List Bool) : Fin 10 → List Bool :=
  ![List.replicate m true, List.replicate n true, source, [], [], [], [], [], [], []]

theorem input_frame (m n x y : ℕ) (source answer : List Bool)
    (l : Option Label) (s : Control) :
    renameCfg writerSlots.symm (Equiv.refl _) (Equiv.refl _)
      (cfg l s (List.replicate x true) (List.replicate m true)
        (List.replicate y true) (List.replicate n true) source answer) =
      MatrixTableWriter.cellCfg l s (persistentBank m n source) x y answer := by
  unfold renameCfg cfg MatrixTableWriter.cellCfg
  cases l with
  | none =>
      apply congrArg
        (fun S => (⟨none, s, S⟩ : TM2.Cfg (fun _ : CellStack => Bool) Label Control))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | some l =>
      apply congrArg
        (fun S => (⟨some l, s, S⟩ : TM2.Cfg (fun _ : CellStack => Bool) Label Control))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl

theorem renamed_run {m n x y t : ℕ} {source answer : List Bool} {s : Control}
    (h : run t (cfg (some start) initial (List.replicate x true) (List.replicate m true)
      (List.replicate y true) (List.replicate n true) source []) =
      cfg none s (List.replicate x true) (List.replicate m true)
        (List.replicate y true) (List.replicate n true) source answer) :
    ((advance entryProgram)^[t])
      (MatrixTableWriter.cellCfg (some start) initial (persistentBank m n source) x y []) =
      MatrixTableWriter.cellCfg none s (persistentBank m n source) x y answer := by
  have hr := rename_run writerSlots.symm (Equiv.refl Label) (Equiv.refl Control)
    program (cfg (some start) initial (List.replicate x true) (List.replicate m true)
      (List.replicate y true) (List.replicate n true) source []) t
  change ((advance entryProgram)^[t]) _ =
    renameCfg writerSlots.symm (Equiv.refl _) (Equiv.refl _) (run t _) at hr
  rw [h, input_frame, input_frame] at hr
  exact hr

theorem entry_runs (rr cc m n : ℕ) (source : List Bool) :
    MatrixTableWriter.EntryRuns entryProgram start initial
      (persistentBank m n source) rr cc (callbackBound rr cc m n source.length)
      (fun x y => source[clampQ x m * n + clampQ y n]?.getD false) := by
  intro x hx y hy
  obtain ⟨t,ht,he⟩ := pad_lookup_run x y m n source []
  refine ⟨t, ?_, initial, renamed_run he⟩
  have hle : x + y + m + n + source.length + 1 ≤ rr + cc + m + n + source.length + 1 := by
    omega
  have hpow := Nat.pow_le_pow_left hle 2
  exact ht.trans (Nat.mul_le_mul_left 80 hpow)

/-- The literal entry identity: the clamped lookup in `rowMajor R` is the source's padded
matrix `FinalPadding.matrix R p hm hr` (first-input repetition in both coordinates). -/
theorem entry_eq_matrix {m r : ℕ} (R : Fin m → Fin r → Bool) (p : ℕ)
    (hm : 0 < m) (hr : 0 < r) (x y : Fin (2 ^ p)) :
    (MatrixMaterialization.rowMajor R)[clampQ x.val m * r + clampQ y.val r]?.getD false =
      FinalPadding.matrix R p hm hr x y := by
  have h := MatrixMaterialization.rowMajor_entry R (FinalPadding.inputMap m p hm x)
    (FinalPadding.inputMap r p hr y)
  rw [clampQ_inputMap p hm x, clampQ_inputMap p hr y, h]
  rfl

theorem table_eq_rowMajor {m r : ℕ} (R : Fin m → Fin r → Bool) (p : ℕ)
    (hm : 0 < m) (hr : 0 < r) :
    FinalPadding.table R p hm hr =
      MatrixMaterialization.rowMajor (FinalPadding.matrix R p hm hr) := by
  rw [FinalPadding.table_eq_ofFn]
  rfl

/-- **B4-S4 core: physical first-input padded-table writer.** For every `m, r > 0`, every `R`
and every `p`, the ONE fixed writer program (the admitted `MatrixTableWriter` controller over
`entryProgram`), started on the writer's entry configuration with unary `2^p` in both counters
and the persistent bank `![unary m, unary r, rowMajor R, …]`, writes exactly
`FinalPadding.table R p hm hr` in front of an arbitrary old output, restores its bank and
counters, and halts within `writerBound (2^p) (2^p) (callbackBound (2^p) (2^p) m r (m*r))`. -/
theorem padded_table {m r : ℕ} (R : Fin m → Fin r → Bool) (p : ℕ) (hm : 0 < m) (hr : 0 < r)
    (output : List Bool) :
    ∃ t ≤ MatrixTableWriter.writerBound (2 ^ p) (2 ^ p)
        (callbackBound (2 ^ p) (2 ^ p) m r (m * r)), ∃ v,
      MatrixTableWriter.run entryProgram start initial t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows))) (initial, none)
          (MatrixTableWriter.ready (persistentBank m r (MatrixMaterialization.rowMajor R))
            (2 ^ p) (2 ^ p) 0 0 0 0 [] output)) =
      MatrixTableWriter.cfg none v
        (MatrixTableWriter.ready (persistentBank m r (MatrixMaterialization.rowMajor R))
          (2 ^ p) (2 ^ p) 0 0 0 0 [] (FinalPadding.table R p hm hr ++ output)) := by
  have hcell := entry_runs (2 ^ p) (2 ^ p) m r (MatrixMaterialization.rowMajor R)
  rw [MatrixMaterialization.rowMajor_length] at hcell
  rw [table_eq_rowMajor R p hm hr]
  exact MatrixTableWriter.write_rowMajor entryProgram start initial
    (persistentBank m r (MatrixMaterialization.rowMajor R)) (2 ^ p) (2 ^ p)
    (callbackBound (2 ^ p) (2 ^ p) m r (m * r))
    (fun x y => (MatrixMaterialization.rowMajor R)[clampQ x m * r + clampQ y r]?.getD false)
    (FinalPadding.matrix R p hm hr) (entry_eq_matrix R p hm hr) hcell output

/-- Polynomial clock of the padded writer in `2^p + m + r`. -/
theorem padded_clock (m r p : ℕ) :
    MatrixTableWriter.writerBound (2 ^ p) (2 ^ p) (callbackBound (2 ^ p) (2 ^ p) m r (m * r)) ≤
      20 * (2 * 2 ^ p + 80 * (2 * 2 ^ p + m + r + m * r + 1) ^ 2 + 1) ^ 3 := by
  have hw := MatrixTableWriter.writerBound_polynomial (2 ^ p) (2 ^ p)
    (callbackBound (2 ^ p) (2 ^ p) m r (m * r))
  refine hw.trans (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left ?_ 3))
  unfold callbackBound
  have : 2 ^ p + 2 ^ p + m + r + m * r + 1 = 2 * 2 ^ p + m + r + m * r + 1 := by ring
  rw [this]
  omega

end PadWriter

end EthInapproximability.CurrentPaper.Unit4Post
