import Paper2.A4Remainder
import EthInapproximability.CurrentPaper.MatrixTableLookup
import EthInapproximability.CurrentPaper.MatrixTableWriter
import Paper2.SquarePadding

/-!
# Unit 4 (Paper A), segment A4-S8: the physical square writer (U17 square padding)

Owner lane `owner:a-unit4-shell-2` (private, 25 September 2026). Source: lock v12, U17
(`E:83,144`, least-power-of-two square padding) with the banked semantic padding
`Paper2.SquarePadding` (`side`, `repeatIndex i = i % d`, `matrix`, `matrix_apply`, and the exact
`D_matrix`).

This is the REMAINDER variant of the admitted repeated-column writer
`MatrixTableColumnRepeat`: one fixed entry program (a Boolean-stack program on 13 stacks, never
a table oracle) that, on unary row index `x` and column index `y`, computes `x % m` and `y % n`
with two instances of the private remainder machine `A4Remainder` (the admitted
`MatrixIndexQuotient` machine with the clear moved to the quotient stack), looks up the
row-major source word with the admitted `MatrixTableLookup.lookup_run`, and clears both
remainders. The admitted `MatrixTableWriter.write_rowMajor` then enumerates the
`side × side` cells, so the written word is exactly
`MatrixMaterialization.rowMajor (SquarePadding.matrix hm hn F)`.

Charged: every step of both remainders, the lookup, both clears and the writer's own loops and
cleanup (`MatrixTableWriter.writerBound`). SUPPLIED (named, not produced here): the writer's
entry configuration `MatrixTableWriter.ready`, i.e. the unary side `SquarePadding.side m n` in
the writer's row/column counters and the persistent bank `![unary m, unary n, rowMajor F, …]`.
A charged machine producing the unary side `2^clog₂(max m n)` from unary `m`, `n` is NOT built.

This index map must not be identified with Paper B's `FinalPadding.inputMap`.

**None of these statements closes a ledger row** (U17, T01 square option, T24 square option stay
open).
-/

namespace Paper2.Unit4Shell.SquareWriter

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineComposition
open EthInapproximability.CurrentPaper.BitMachineSubroutine
open EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

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

/-! Global stack layout: `0 x, 1 m, 2 y, 3 n, 4 source, 5 answer, 6 rx, 7 ry, 8-12 scratch`. -/

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
      (liftStmt (some (.inl MatrixIndexQuotient.start)) (Remainder.program l))
  | .inr (.inl l) => renameStmt colStacks colLabels (Equiv.refl _)
      (liftStmt (some (.inr (.inl MatrixTableLookup.start))) (Remainder.program l))
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

def rowFrame (y n source answer ry : List Bool) (c : Remainder.Config) : Config :=
  renameCfg rowStacks (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inl MatrixIndexQuotient.start)) MatrixTableLookup.initial
      (fun i => ![y, n, source, answer, ry] i) c)

theorem row_run (x m : ℕ) (y n source answer : List Bool) :
    ∃ t ≤ 11*x + 3*m + 7,
      run t (cfg (some start) initial (List.replicate x true) (List.replicate m true)
        y n source answer) =
      cfg (some colStart) initial (List.replicate x true) (List.replicate m true)
        y n source answer (List.replicate (x % m) true) [] := by
  obtain ⟨a,ha,hh⟩ := Remainder.remainder_run x m
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed rowStacks (Equiv.refl _) (Equiv.refl _)
    Remainder.program program (some (.inl MatrixIndexQuotient.start)) (fun _ => rfl)
    MatrixTableLookup.initial (fun i => ![y, n, source, answer, []] i)
    (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.start) MatrixIndexQuotient.initial
      (List.replicate x true) (List.replicate m true) [] [] [] [] [] []) a
    (by rw [show ((advance Remainder.program)^[a]) _ = _ from hh]; rfl)
  change run t (rowFrame y n source answer [] _) =
    rowFrame y n source answer [] (Remainder.run _ _) at hr
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
        (List.replicate m true) [] [] [] (List.replicate (x % m) true) [] []) =
      cfg (some colStart) initial (List.replicate x true) (List.replicate m true)
        y n source answer (List.replicate (x % m) true) [] := by
    unfold rowFrame renameCfg liftCfg cfg MatrixIndexQuotient.cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨t, ht.trans ha, by simpa only [hi, hf] using hr⟩

def colFrame (x m source answer rx : List Bool) (c : Remainder.Config) : Config :=
  renameCfg colStacks colLabels (Equiv.refl _)
    (liftCfg (some (.inr (.inl MatrixTableLookup.start))) MatrixTableLookup.initial
      (fun i => ![x, m, source, answer, rx] i) c)

theorem col_run (y n : ℕ) (x m source answer rx : List Bool) :
    ∃ t ≤ 11*y + 3*n + 7,
      run t (cfg (some colStart) initial x m (List.replicate y true) (List.replicate n true)
        source answer rx []) =
      cfg (some lookStart) initial x m (List.replicate y true) (List.replicate n true)
        source answer rx (List.replicate (y % n) true) := by
  obtain ⟨a,ha,hh⟩ := Remainder.remainder_run y n
  obtain ⟨t,ht,hr⟩ := lift_outputs_renamed colStacks colLabels (Equiv.refl _)
    Remainder.program program (some (.inr (.inl MatrixTableLookup.start))) (fun _ => rfl)
    MatrixTableLookup.initial (fun i => ![x, m, source, answer, rx] i)
    (MatrixIndexQuotient.cfg (some MatrixIndexQuotient.start) MatrixIndexQuotient.initial
      (List.replicate y true) (List.replicate n true) [] [] [] [] [] []) a
    (by rw [show ((advance Remainder.program)^[a]) _ = _ from hh]; rfl)
  change run t (colFrame x m source answer rx _) =
    colFrame x m source answer rx (Remainder.run _ _) at hr
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
        (List.replicate n true) [] [] [] (List.replicate (y % n) true) [] []) =
      cfg (some lookStart) initial x m (List.replicate y true) (List.replicate n true)
        source answer rx (List.replicate (y % n) true) := by
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

/-- **One physical square-padding lookup.** On unary row index `x`, column index `y`, row
divisor `m`, column divisor/width `n` and a source word, the fixed program pushes
`source[(x % m) * n + y % n]` onto the answer stack, preserves every other input, and empties
all its work stacks, within `callbackBound`. Does not close a ledger row. -/
theorem square_lookup_run (x y m n : ℕ) (source answer : List Bool) :
    ∃ t ≤ callbackBound x y m n source.length,
      run t (cfg (some start) initial (List.replicate x true) (List.replicate m true)
        (List.replicate y true) (List.replicate n true) source answer) =
      cfg none initial (List.replicate x true) (List.replicate m true)
        (List.replicate y true) (List.replicate n true) source
        (source[(x % m) * n + y % n]?.getD false :: answer) := by
  obtain ⟨a,ha,h1⟩ := row_run x m (List.replicate y true) (List.replicate n true) source answer
  obtain ⟨b,hb,h2⟩ := col_run y n (List.replicate x true) (List.replicate m true) source answer
    (List.replicate (x % m) true)
  obtain ⟨c,hc,h3⟩ := look_run (x % m) n (y % n) (List.replicate x true)
    (List.replicate m true) (List.replicate y true) source answer
  have h4 := clearX_run (List.replicate x true) (List.replicate m true)
    (List.replicate y true) (List.replicate n true) source
    (source[(x % m) * n + y % n]?.getD false :: answer)
    (List.replicate (x % m) true) (List.replicate (y % n) true) initial
  have h5 := clearY_run (List.replicate x true) (List.replicate m true)
    (List.replicate y true) (List.replicate n true) source
    (source[(x % m) * n + y % n]?.getD false :: answer)
    (List.replicate (y % n) true) ((initial.1.1, false), initial.2)
  simp only [List.length_replicate] at h4 h5
  refine ⟨a + (b + (c + ((x % m + 1) + (y % n + 1)))), ?_, ?_⟩
  · let N := x + y + m + n + source.length + 1
    have hN : 1 ≤ N := by dsimp [N]; omega
    have hxm : x % m ≤ x := Nat.mod_le _ _
    have hyn : y % n ≤ y := Nat.mod_le _ _
    have hq : x % m + n + y % n + source.length + 1 ≤ N := by dsimp [N]; omega
    have hsq := Nat.pow_le_pow_left hq 2
    have hlin : 11*x + 3*m + 7 + (11*y + 3*n + 7) + (x % m + 1 + (y % n + 1)) ≤ 28 * N := by
      dsimp [N]; omega
    have hN2 : N ≤ N ^ 2 := by nlinarith [Nat.mul_le_mul (le_refl N) hN]
    change a + (b + (c + ((x % m + 1) + (y % n + 1)))) ≤ 80 * N ^ 2
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

/-- The persistent writer bank: unary `m`, unary `n`, the row-major source word, and seven
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

/-- The writer's local contract for the square-padding entry map, for ANY dimensions `r × c`
(the square case is `r = c = SquarePadding.side m n`). -/
theorem entry_runs (r c m n : ℕ) (source : List Bool) :
    MatrixTableWriter.EntryRuns entryProgram start initial
      (persistentBank m n source) r c (callbackBound r c m n source.length)
      (fun x y => source[(x % m) * n + y % n]?.getD false) := by
  intro x hx y hy
  obtain ⟨t,ht,he⟩ := square_lookup_run x y m n source []
  refine ⟨t, ?_, initial, renamed_run he⟩
  have hle : x + y + m + n + source.length + 1 ≤ r + c + m + n + source.length + 1 := by omega
  have hpow := Nat.pow_le_pow_left hle 2
  exact ht.trans (Nat.mul_le_mul_left 80 hpow)

/-- The literal square entry identity: the remainder lookup in the row-major word of `F` is
the banked padded matrix `SquarePadding.matrix hm hn F`. -/
theorem entry_eq_matrix {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (F : Fin m → Fin n → Bool)
    (x y : Fin (SquarePadding.side m n)) :
    (MatrixMaterialization.rowMajor F)[(x.val % m) * n + y.val % n]?.getD false =
      SquarePadding.matrix hm hn F x y := by
  have h := MatrixMaterialization.rowMajor_entry F (SquarePadding.repeatIndex hm x)
    (SquarePadding.repeatIndex hn y)
  rw [SquarePadding.matrix_apply]
  change (MatrixMaterialization.rowMajor F)[(x.val % m) * n + y.val % n]? =
    some (F (SquarePadding.repeatIndex hm x) (SquarePadding.repeatIndex hn y)) at h
  rw [h]
  rfl

/-- **Physical square writer (U17 square padding), with the entry configuration supplied.**
For every `m, n > 0` and every `F`, the ONE fixed writer program (the admitted
`MatrixTableWriter` controller over `entryProgram`), started on the writer's entry
configuration with unary side `SquarePadding.side m n` in both counters and the persistent bank
`![unary m, unary n, rowMajor F, …]`, writes exactly
`rowMajor (SquarePadding.matrix hm hn F)` in front of an arbitrary old output, restores its
bank and counters, and halts within
`writerBound side side (callbackBound side side m n (m*n))` steps. The unary side and the bank
are SUPPLIED by the caller (not produced here). Does not close a ledger row (U17). -/
theorem square_table {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (F : Fin m → Fin n → Bool)
    (output : List Bool) :
    ∃ t ≤ MatrixTableWriter.writerBound (SquarePadding.side m n) (SquarePadding.side m n)
        (callbackBound (SquarePadding.side m n) (SquarePadding.side m n) m n (m * n)), ∃ v,
      MatrixTableWriter.run entryProgram start initial t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows))) (initial, none)
          (MatrixTableWriter.ready (persistentBank m n (MatrixMaterialization.rowMajor F))
            (SquarePadding.side m n) (SquarePadding.side m n) 0 0 0 0 [] output)) =
      MatrixTableWriter.cfg none v
        (MatrixTableWriter.ready (persistentBank m n (MatrixMaterialization.rowMajor F))
          (SquarePadding.side m n) (SquarePadding.side m n) 0 0 0 0 []
          (MatrixMaterialization.rowMajor (SquarePadding.matrix hm hn F) ++ output)) := by
  have hcell := entry_runs (SquarePadding.side m n) (SquarePadding.side m n) m n
    (MatrixMaterialization.rowMajor F)
  rw [MatrixMaterialization.rowMajor_length] at hcell
  exact MatrixTableWriter.write_rowMajor entryProgram start initial
    (persistentBank m n (MatrixMaterialization.rowMajor F))
    (SquarePadding.side m n) (SquarePadding.side m n)
    (callbackBound (SquarePadding.side m n) (SquarePadding.side m n) m n (m * n))
    (fun x y => (MatrixMaterialization.rowMajor F)[(x % m) * n + y % n]?.getD false)
    (SquarePadding.matrix hm hn F) (entry_eq_matrix hm hn F) hcell output

theorem side_le_two_sum {m n : ℕ} (hm : 0 < m) : SquarePadding.side m n ≤ 2 * (m + n) := by
  have h := SquarePadding.side_lt_twice_max (m := m) (n := n) (by omega)
  have : max m n ≤ m + n := max_le (by omega) (by omega)
  omega

/-- **Polynomial clock of the square writer** in `m + n` (for `m > 0`). -/
theorem square_clock_polynomial {m n : ℕ} (hm : 0 < m) :
    MatrixTableWriter.writerBound (SquarePadding.side m n) (SquarePadding.side m n)
        (callbackBound (SquarePadding.side m n) (SquarePadding.side m n) m n (m * n)) ≤
      20 * (4 * (m + n) + 80 * (5 * (m + n) + (m + n) ^ 2 + 1) ^ 2 + 1) ^ 3 := by
  have hs := side_le_two_sum (n := n) hm
  have hmn : m * n ≤ (m + n) ^ 2 := by nlinarith
  have hcb : callbackBound (SquarePadding.side m n) (SquarePadding.side m n) m n (m * n) ≤
      80 * (5 * (m + n) + (m + n) ^ 2 + 1) ^ 2 := by
    unfold callbackBound
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    omega
  have hw := MatrixTableWriter.writerBound_polynomial (SquarePadding.side m n)
    (SquarePadding.side m n)
    (callbackBound (SquarePadding.side m n) (SquarePadding.side m n) m n (m * n))
  refine hw.trans (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left ?_ 3))
  omega

end Paper2.Unit4Shell.SquareWriter
