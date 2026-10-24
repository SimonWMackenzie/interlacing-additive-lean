import EthInapproximability.CurrentPaper.MatrixUnaryCut
import EthInapproximability.CurrentPaper.MatrixUnaryDivision
import EthInapproximability.CurrentPaper.MatrixLabelArithmetic
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Physical decoding of template and source row labels

The controller first performs an actual unary threshold test at `4*N₂`.
Source rows leave their source index on stack zero. Template rows undergo
actual unary division by `N₂`; the remainder is their template index, and
their quotient (less than four) is read into finite control. Threshold and
divisor are preserved. This is one fixed seven-stack program, not a
case-dependent family of programs.
-/

namespace EthInapproximability.CurrentPaper.MatrixRowDecode

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition BitMachineSubroutine
open BitMachineSubroutineRenaming

inductive Admin where
  | dispatch | counter
  deriving DecidableEq, Fintype

abbrev CLabel := MatrixUnaryCut.Label
abbrev DLabel := MatrixUnaryDivision.Label
abbrev Label := CLabel ⊕ (DLabel ⊕ Admin)
abbrev Counter := Fin 4 × Bool
abbrev Control := MatrixUnaryCut.Control × (Bool × Counter)
abbrev Config := TM2.Cfg (fun _ : Fin 7 => Bool) Label Control

def cutBank : Fin 4 ⊕ Fin 3 ≃ Fin 7 := finSumFinEquiv

private def divisionPerm : Fin 7 ≃ Fin 7 where
  toFun k := ![0, 4, 2, 5, 6, 3, 1] k
  invFun k := ![0, 6, 2, 5, 1, 3, 4] k
  left_inv k := by fin_cases k <;> rfl
  right_inv k := by fin_cases k <;> rfl

def divisionBank : Fin 6 ⊕ Fin 1 ≃ Fin 7 := finSumFinEquiv.trans divisionPerm

def divisionLabels : DLabel ⊕ (CLabel ⊕ Admin) ≃ Label where
  toFun := Sum.elim (fun l => .inr (.inl l)) (Sum.elim Sum.inl (fun l => .inr (.inr l)))
  invFun := Sum.elim (fun l => .inr (.inl l)) (Sum.elim Sum.inl (fun l => .inr (.inr l)))
  left_inv l := by rcases l with l | (l | l) <;> rfl
  right_inv l := by rcases l with l | (l | l) <;> rfl

def divisionControls : Bool × (MatrixUnaryCut.Control × Counter) ≃ Control where
  toFun s := (s.2.1, s.1, s.2.2)
  invFun s := (s.2.1, s.1, s.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def program : Label → TM2.Stmt (fun _ : Fin 7 => Bool) Label Control
  | .inl l => renameStmt cutBank (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inr Admin.dispatch)) (MatrixUnaryCut.program l))
  | .inr (.inl l) => renameStmt divisionBank divisionLabels divisionControls
      (liftStmt (some (.inr Admin.counter)) (MatrixUnaryDivision.program l))
  | .inr (.inr .dispatch) => branch (fun s => s.1.1) halt
      (goto (fun _ => .inr (.inl .start)))
  | .inr (.inr .counter) => pop 6 (fun s b => (s.1, s.2.1, s.2.2.1, b.isSome))
      (branch (fun s => s.2.2.2)
        (load (fun s => (s.1, s.2.1, s.2.2.1 + 1, true))
          (goto (fun _ => .inr (.inr .counter)))) halt)

def cfg (l : Option Label) (s : Control) (row threshold divisor z p : List Bool) : Config :=
  ⟨l, s, ![row, threshold, [], [], divisor, z, p]⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem cut_cfg (l : Option CLabel) (s : MatrixUnaryCut.Control)
    (row threshold divisor : List Bool) :
    renameCfg cutBank (Equiv.refl _) (Equiv.refl _)
      (liftCfg (some (.inr Admin.dispatch)) (false, (0, false))
        (![divisor, [], []] : Fin 3 → List Bool)
        (MatrixUnaryCut.cfg l s row threshold [] [])) =
      cfg (l.elim (some (.inr (.inr .dispatch))) (fun l => some (.inl l)))
        (s, false, (0, false)) row threshold divisor [] [] := by
  cases l <;> apply congrArg (fun S => (⟨_, (s, false, (0, false)), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem division_cfg (l : Option DLabel)
    (row threshold divisor z p : List Bool) :
    renameCfg divisionBank divisionLabels divisionControls
      (liftCfg (some (.inr Admin.counter)) ((false, false), (0, false))
        (![threshold] : Fin 1 → List Bool)
        (MatrixUnaryDivision.cfg l false row divisor [] z p [])) =
      cfg (l.elim (some (.inr (.inr .counter))) (fun l => some (.inr (.inl l))))
        ((false, false), false, (0, false)) row threshold divisor z p := by
  cases l <;> apply congrArg (fun S => (⟨_, ((false, false), false, (0, false)), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem dispatch_source (row threshold divisor : List Bool) :
    TM2.step program (cfg (some (.inr (.inr .dispatch)))
      ((true, false), false, (0, false)) row threshold divisor [] []) =
      some (cfg none ((true, false), false, (0, false)) row threshold divisor [] []) := rfl

private theorem dispatch_template (row threshold divisor : List Bool) :
    TM2.step program (cfg (some (.inr (.inr .dispatch)))
      ((false, false), false, (0, false)) row threshold divisor [] []) =
      some (cfg (some (.inr (.inl .start)))
        ((false, false), false, (0, false)) row threshold divisor [] []) := rfl

private theorem counter_cons (s : MatrixUnaryCut.Control) (b q : Bool) (p : Fin 4)
    (row threshold divisor z rest : List Bool) :
    TM2.step program (cfg (some (.inr (.inr .counter)))
      (s, b, p, q) row threshold divisor z (true :: rest)) =
      some (cfg (some (.inr (.inr .counter)))
        (s, b, p + 1, true) row threshold divisor z rest) := by
  apply congrArg (fun S => some (⟨_, (s, b, p + 1, true), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem counter_nil (s : MatrixUnaryCut.Control) (b q : Bool) (p : Fin 4)
    (row threshold divisor z : List Bool) :
    TM2.step program (cfg (some (.inr (.inr .counter)))
      (s, b, p, q) row threshold divisor z []) =
      some (cfg none (s, b, p, false) row threshold divisor z []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

theorem counter_run (n : ℕ) (s : MatrixUnaryCut.Control) (b q : Bool) (p : Fin 4)
    (row threshold divisor z : List Bool) :
    run (n + 1) (cfg (some (.inr (.inr .counter)))
      (s, b, p, q) row threshold divisor z (List.replicate n true)) =
      cfg none (s, b, p + Fin.ofNat 4 n, false) row threshold divisor z [] := by
  induction n generalizing p q with
  | zero => simpa using run_succ (counter_nil s b q p row threshold divisor z) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (counter_cons _ _ _ _ _ _ _ _ _) (n + 1), ih]
      have he : p + 1 + Fin.ofNat 4 n = p + Fin.ofNat 4 (n + 1) := by
        apply Fin.ext
        simp only [Fin.val_add, Fin.val_one, Fin.val_ofNat]
        omega
      rw [he]

theorem source_run (N₂ i : ℕ) :
    ∃ t ≤ 12 * N₂ + 4,
      run t (cfg (some (.inl .scan)) ((false, true), false, (0, false))
        (List.replicate (4 * N₂ + i) true) (List.replicate (4 * N₂) true)
        (List.replicate N₂ true) [] []) =
        cfg none ((true, false), false, (0, false))
          (List.replicate i true) (List.replicate (4 * N₂) true)
          (List.replicate N₂ true) [] [] := by
  have hr := MatrixUnaryCut.source_run (4 * N₂) i
  have hh : (((advance MatrixUnaryCut.program)^[3 * (4 * N₂) + 3])
      (MatrixUnaryCut.cfg (some .scan) (false, true)
        (List.replicate (4 * N₂ + i) true) (List.replicate (4 * N₂) true) [] [])).l = none := by
    change (MatrixUnaryCut.run _ _).l = none
    rw [hr]
    rfl
  obtain ⟨t, ht, hrun⟩ := lift_outputs_renamed cutBank (Equiv.refl _) (Equiv.refl _)
    MatrixUnaryCut.program program (some (.inr Admin.dispatch)) (fun _ => rfl)
    (false, (0, false)) (![List.replicate N₂ true, [], []] : Fin 3 → List Bool)
    (MatrixUnaryCut.cfg (some .scan) (false, true)
      (List.replicate (4 * N₂ + i) true) (List.replicate (4 * N₂) true) [] []) _ hh
  change (((advance MatrixUnaryCut.program)^[_]) _) = _ at hr
  rw [hr, cut_cfg, cut_cfg] at hrun
  refine ⟨t + 1, by omega, ?_⟩
  exact (run_add hrun 1).trans (run_succ (dispatch_source _ _ _) 0)

theorem template_run (N₂ : ℕ) (p : Fin 4) (z : Fin N₂) :
    let x := z.val + N₂ * p.val
    ∃ t ≤ 12 * x + 4 * N₂ + 16,
      run t (cfg (some (.inl .scan)) ((false, true), false, (0, false))
        (List.replicate x true) (List.replicate (4 * N₂) true)
        (List.replicate N₂ true) [] []) =
        cfg none ((false, false), false, (p, false)) []
          (List.replicate (4 * N₂) true) (List.replicate N₂ true)
          (List.replicate z.val true) [] := by
  dsimp only
  let x := z.val + N₂ * p.val
  have hp := p.isLt
  have hz := z.isLt
  have hn : 0 < N₂ := by omega
  have hx : x < 4 * N₂ := by dsimp [x]; nlinarith
  have hr := MatrixUnaryCut.template_run x (4 * N₂) hx
  have hh : (((advance MatrixUnaryCut.program)^[3 * x + 4])
      (MatrixUnaryCut.cfg (some .scan) (false, true)
        (List.replicate x true) (List.replicate (4 * N₂) true) [] [])).l = none := by
    change (MatrixUnaryCut.run _ _).l = none
    rw [hr]
    rfl
  obtain ⟨t₀, ht₀, hrun₀⟩ := lift_outputs_renamed cutBank (Equiv.refl _) (Equiv.refl _)
    MatrixUnaryCut.program program (some (.inr Admin.dispatch)) (fun _ => rfl)
    (false, (0, false)) (![List.replicate N₂ true, [], []] : Fin 3 → List Bool)
    (MatrixUnaryCut.cfg (some .scan) (false, true)
      (List.replicate x true) (List.replicate (4 * N₂) true) [] []) _ hh
  change (((advance MatrixUnaryCut.program)^[_]) _) = _ at hr
  rw [hr, cut_cfg, cut_cfg] at hrun₀
  have hrdiv := MatrixUnaryDivision.division_total_run x N₂
  have hhdiv : (((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime x N₂])
      (MatrixUnaryDivision.cfg (some .start) false
        (List.replicate x true) (List.replicate N₂ true) [] [] [] [])).l = none := by
    change (MatrixUnaryDivision.run _ _).l = none
    rw [hrdiv]
    rfl
  obtain ⟨t₁, ht₁, hrun₁⟩ := lift_outputs_renamed divisionBank divisionLabels divisionControls
    MatrixUnaryDivision.program program (some (.inr Admin.counter)) (fun _ => rfl)
    ((false, false), (0, false)) (![List.replicate (4 * N₂) true] : Fin 1 → List Bool)
    (MatrixUnaryDivision.cfg (some .start) false
      (List.replicate x true) (List.replicate N₂ true) [] [] [] []) _ hhdiv
  change (((advance MatrixUnaryDivision.program)^[_]) _) = _ at hrdiv
  rw [hrdiv, division_cfg, division_cfg] at hrun₁
  have hxdiv : x / N₂ = p.val := by
    dsimp [x]
    rw [Nat.add_mul_div_left _ _ hn]
    simp [Nat.div_eq_of_lt hz]
  have hxmod : x % N₂ = z.val := by dsimp [x]; simp [Nat.mod_eq_of_lt hz]
  rw [hxdiv, hxmod] at hrun₁
  have hrcount := counter_run p.val (false, false) false false 0 []
    (List.replicate (4 * N₂) true) (List.replicate N₂ true) (List.replicate z.val true)
  simp only [zero_add, Fin.ofNat_val_eq_self] at hrcount
  refine ⟨t₀ + 1 + t₁ + (p.val + 1), ?_, ?_⟩
  · have hb := MatrixUnaryDivision.totalTime_bound x N₂
    omega
  · exact (run_add ((run_add ((run_add hrun₀ 1).trans
      (run_succ (dispatch_template _ _ _) 0)) t₁).trans hrun₁) (p.val + 1)).trans hrcount

def sourceIndex {N₂ n : ℕ} : (Fin 4 × Fin N₂) ⊕ Fin n → ℕ
  | .inl _ => 0
  | .inr i => i.val

def templateIndex {N₂ n : ℕ} : (Fin 4 × Fin N₂) ⊕ Fin n → ℕ
  | .inl (_, z) => z.val
  | .inr _ => 0

def rowControl {N₂ n : ℕ} : (Fin 4 × Fin N₂) ⊕ Fin n → Control
  | .inl (p, _) => ((false, false), false, (p, false))
  | .inr _ => ((true, false), false, (0, false))

/-- Uniform row-code theorem. The source/template bit and the four-way
template selector are returned in finite control, not supplied to the run. -/
theorem row_run {N₂ n : ℕ} (r : (Fin 4 × Fin N₂) ⊕ Fin n) :
    let x := (MatrixMaterialization.rowCode N₂ n r).val
    ∃ t ≤ 12 * x + 16 * N₂ + 16,
      run t (cfg (some (.inl .scan)) ((false, true), false, (0, false))
        (List.replicate x true) (List.replicate (4 * N₂) true)
        (List.replicate N₂ true) [] []) =
        cfg none (rowControl r) (List.replicate (sourceIndex r) true)
          (List.replicate (4 * N₂) true) (List.replicate N₂ true)
          (List.replicate (templateIndex r) true) [] := by
  rcases r with ⟨p, z⟩ | i
  · obtain ⟨t, ht, hr⟩ := template_run N₂ p z
    refine ⟨t, ?_, hr⟩
    change t ≤ 12 * (z.val + N₂ * p.val) + 16 * N₂ + 16
    omega
  · obtain ⟨t, ht, hr⟩ := source_run N₂ i.val
    refine ⟨t, ?_, hr⟩
    change t ≤ 12 * (4 * N₂ + i.val) + 16 * N₂ + 16
    omega

end EthInapproximability.CurrentPaper.MatrixRowDecode
