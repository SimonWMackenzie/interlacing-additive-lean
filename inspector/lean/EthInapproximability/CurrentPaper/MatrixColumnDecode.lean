import EthInapproximability.CurrentPaper.MatrixUnaryDivision
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming
import EthInapproximability.CurrentPaper.MatrixColumnDigitArithmetic

/-!
# Literal successive division for column labels

Source: locked v8 `thm:paper-materialization`, quotient/remainder decoding
of input labels. Four actual divisions extract the selector digits, four
more divisions split each into its coordinate and family index, and a finite
eight-state counter emits the three tail bits. All calls compose into one
fixed controller. Alternating quotient registers avoid hidden transfers.

`Full.column_run` identifies every output with the actual column equivalence.
The input is a unary column number together with the unary base and family
count. Binary parsing and computation of the base remain separate operations.
-/

namespace EthInapproximability.CurrentPaper.MatrixColumnDecode

open Turing BitMachineEncoding BitMachineComposition BitMachineSubroutine
open BitMachineSubroutineRenaming

namespace BaseFour

abbrev DLabel := MatrixUnaryDivision.Label
abbrev Label := DLabel ⊕ (DLabel ⊕ (DLabel ⊕ DLabel))
abbrev Control := Bool × (Bool × (Bool × Bool))
abbrev Config := TM2.Cfg (fun _ : Fin 9 => Bool) Label Control

def bank₁ : Fin 6 ⊕ Fin 3 ≃ Fin 9 := finSumFinEquiv

private def perm₂ : Fin 9 ≃ Fin 9 where
  toFun i := ![4, 1, 2, 6, 0, 5, 3, 7, 8] i
  invFun i := ![4, 1, 2, 6, 0, 5, 3, 7, 8] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def perm₃ : Fin 9 ≃ Fin 9 where
  toFun i := ![0, 1, 2, 7, 4, 5, 3, 6, 8] i
  invFun i := ![0, 1, 2, 6, 4, 5, 7, 3, 8] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def perm₄ : Fin 9 ≃ Fin 9 where
  toFun i := ![4, 1, 2, 8, 0, 5, 3, 6, 7] i
  invFun i := ![4, 1, 2, 6, 0, 5, 7, 8, 3] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def bank₂ : Fin 6 ⊕ Fin 3 ≃ Fin 9 := bank₁.trans perm₂
def bank₃ : Fin 6 ⊕ Fin 3 ≃ Fin 9 := bank₁.trans perm₃
def bank₄ : Fin 6 ⊕ Fin 3 ≃ Fin 9 := bank₁.trans perm₄

def labels₂ : Label ≃ Label where
  toFun := Sum.elim (fun l => .inr (.inl l))
    (Sum.elim Sum.inl (fun l => .inr (.inr l)))
  invFun := Sum.elim (fun l => .inr (.inl l))
    (Sum.elim Sum.inl (fun l => .inr (.inr l)))
  left_inv l := by rcases l with l | (l | l) <;> rfl
  right_inv l := by rcases l with l | (l | l) <;> rfl

def labels₃ : Label ≃ Label where
  toFun
    | .inl l => .inr (.inr (.inl l))
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inl l)
    | .inr (.inr (.inr l)) => .inr (.inr (.inr l))
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inr (.inr (.inl l))
    | .inr (.inr (.inl l)) => .inl l
    | .inr (.inr (.inr l)) => .inr (.inr (.inr l))
  left_inv l := by rcases l with l | (l | (l | l)) <;> rfl
  right_inv l := by rcases l with l | (l | (l | l)) <;> rfl

def labels₄ : Label ≃ Label where
  toFun
    | .inl l => .inr (.inr (.inr l))
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inl l)
    | .inr (.inr (.inr l)) => .inr (.inr (.inl l))
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inr (.inr (.inl l))
    | .inr (.inr (.inl l)) => .inr (.inr (.inr l))
    | .inr (.inr (.inr l)) => .inl l
  left_inv l := by rcases l with l | (l | (l | l)) <;> rfl
  right_inv l := by rcases l with l | (l | (l | l)) <;> rfl

def controls₂ : Control ≃ Control where
  toFun s := (s.2.1, s.1, s.2.2)
  invFun s := (s.2.1, s.1, s.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def controls₃ : Control ≃ Control where
  toFun s := (s.2.1, s.2.2.1, s.1, s.2.2.2)
  invFun s := (s.2.2.1, s.1, s.2.1, s.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def controls₄ : Control ≃ Control where
  toFun s := (s.2.1, s.2.2.1, s.2.2.2, s.1)
  invFun s := (s.2.2.2, s.1, s.2.1, s.2.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def program : Label → TM2.Stmt (fun _ : Fin 9 => Bool) Label Control
  | .inl l => renameStmt bank₁ (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixUnaryDivision.Label.start)) (MatrixUnaryDivision.program l))
  | .inr (.inl l) => renameStmt bank₂ labels₂ controls₂
      (liftStmt (some (.inr (.inl MatrixUnaryDivision.Label.start))) (MatrixUnaryDivision.program l))
  | .inr (.inr (.inl l)) => renameStmt bank₃ labels₃ controls₃
      (liftStmt (some (.inr (.inr MatrixUnaryDivision.Label.start))) (MatrixUnaryDivision.program l))
  | .inr (.inr (.inr l)) => renameStmt bank₄ labels₄ controls₄
      (liftStmt none (MatrixUnaryDivision.program l))

def cfg (l : Option Label) (input divisor rem₀ quotient rem₁ rem₂ rem₃ : List Bool) : Config :=
  ⟨l, (false, false, false, false), ![input, divisor, [], rem₀, quotient, [], rem₁, rem₂, rem₃]⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem cfg₁ (l : Option DLabel) (input divisor rem₀ quotient rem₁ rem₂ rem₃ : List Bool) :
    renameCfg bank₁ (Equiv.refl _) (Equiv.refl _)
      (liftCfg (some (.inl MatrixUnaryDivision.Label.start)) (false, false, false)
        (![rem₁, rem₂, rem₃] : Fin 3 → List Bool)
        (MatrixUnaryDivision.cfg l false input divisor [] rem₀ quotient [])) =
      cfg (l.elim (some (.inr (.inl .start))) (fun l => some (.inl l)))
        input divisor rem₀ quotient rem₁ rem₂ rem₃ := by
  cases l <;> apply congrArg (fun S => (⟨_, (false, false, false, false), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem cfg₂ (l : Option DLabel) (input divisor rem₀ quotient rem₁ rem₂ rem₃ : List Bool) :
    renameCfg bank₂ labels₂ controls₂
      (liftCfg (some (.inr (.inl MatrixUnaryDivision.Label.start))) (false, false, false)
        (![rem₀, rem₂, rem₃] : Fin 3 → List Bool)
        (MatrixUnaryDivision.cfg l false input divisor [] rem₁ quotient [])) =
      cfg (l.elim (some (.inr (.inr (.inl .start)))) (fun l => some (.inr (.inl l))))
        quotient divisor rem₀ input rem₁ rem₂ rem₃ := by
  cases l <;> apply congrArg (fun S => (⟨_, (false, false, false, false), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem cfg₃ (l : Option DLabel) (input divisor rem₀ quotient rem₁ rem₂ rem₃ : List Bool) :
    renameCfg bank₃ labels₃ controls₃
      (liftCfg (some (.inr (.inr MatrixUnaryDivision.Label.start))) (false, false, false)
        (![rem₀, rem₁, rem₃] : Fin 3 → List Bool)
        (MatrixUnaryDivision.cfg l false input divisor [] rem₂ quotient [])) =
      cfg (l.elim (some (.inr (.inr (.inr .start)))) (fun l => some (.inr (.inr (.inl l)))))
        input divisor rem₀ quotient rem₁ rem₂ rem₃ := by
  cases l <;> apply congrArg (fun S => (⟨_, (false, false, false, false), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem cfg₄ (l : Option DLabel) (input divisor rem₀ quotient rem₁ rem₂ rem₃ : List Bool) :
    renameCfg bank₄ labels₄ controls₄
      (liftCfg none (false, false, false) (![rem₀, rem₁, rem₂] : Fin 3 → List Bool)
        (MatrixUnaryDivision.cfg l false input divisor [] rem₃ quotient [])) =
      cfg (l.map (fun l => .inr (.inr (.inr l))))
        quotient divisor rem₀ input rem₁ rem₂ rem₃ := by
  cases l <;> apply congrArg (fun S => (⟨_, (false, false, false, false), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

/-- Four real divisions produce four literal base digits and the remaining
quotient. This statement includes zero divisors with Lean's total conventions. -/
theorem digits_run (n base : ℕ) :
    ∃ t ≤ 4 * (8 * n + 3 * base + 4),
      run t (cfg (some (.inl .start)) (List.replicate n true)
        (List.replicate base true) [] [] [] [] []) =
      cfg none (List.replicate (n / base / base / base / base) true)
        (List.replicate base true) (List.replicate (n % base) true) []
        (List.replicate (n / base % base) true)
        (List.replicate (n / base / base % base) true)
        (List.replicate (n / base / base / base % base) true) := by
  have dh (x : ℕ) : (((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime x base])
      (MatrixUnaryDivision.cfg (some .start) false (List.replicate x true)
        (List.replicate base true) [] [] [] [])).l = none := by
    change (MatrixUnaryDivision.run _ _).l = none
    rw [MatrixUnaryDivision.division_total_run]
    rfl
  have dr (x : ℕ) := MatrixUnaryDivision.division_total_run x base
  change ∀ x, (((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime x base]) _) = _ at dr
  obtain ⟨t₁, ht₁, hr₁⟩ := lift_outputs_renamed bank₁ (Equiv.refl _) (Equiv.refl _)
    MatrixUnaryDivision.program program (some (.inl MatrixUnaryDivision.Label.start)) (fun _ => rfl)
    (false, false, false) (![( [] : List Bool), [], []] : Fin 3 → List Bool)
    (MatrixUnaryDivision.cfg (some .start) false (List.replicate n true)
      (List.replicate base true) [] [] [] []) _ (dh n)
  rw [dr n, cfg₁, cfg₁] at hr₁
  obtain ⟨t₂, ht₂, hr₂⟩ := lift_outputs_renamed bank₂ labels₂ controls₂
    MatrixUnaryDivision.program program
    (some (.inr (.inl MatrixUnaryDivision.Label.start))) (fun _ => rfl)
    (false, false, false) (![List.replicate (n % base) true, [], []] : Fin 3 → List Bool)
    (MatrixUnaryDivision.cfg (some .start) false (List.replicate (n / base) true)
      (List.replicate base true) [] [] [] []) _ (dh (n / base))
  rw [dr (n / base), cfg₂, cfg₂] at hr₂
  obtain ⟨t₃, ht₃, hr₃⟩ := lift_outputs_renamed bank₃ labels₃ controls₃
    MatrixUnaryDivision.program program
    (some (.inr (.inr MatrixUnaryDivision.Label.start))) (fun _ => rfl)
    (false, false, false)
    (![List.replicate (n % base) true, List.replicate (n / base % base) true, []] : Fin 3 → List Bool)
    (MatrixUnaryDivision.cfg (some .start) false (List.replicate (n / base / base) true)
      (List.replicate base true) [] [] [] []) _ (dh (n / base / base))
  rw [dr (n / base / base), cfg₃, cfg₃] at hr₃
  obtain ⟨t₄, ht₄, hr₄⟩ := lift_outputs_renamed bank₄ labels₄ controls₄
    MatrixUnaryDivision.program program none (fun _ => rfl)
    (false, false, false)
    (![List.replicate (n % base) true, List.replicate (n / base % base) true,
      List.replicate (n / base / base % base) true] : Fin 3 → List Bool)
    (MatrixUnaryDivision.cfg (some .start) false (List.replicate (n / base / base / base) true)
      (List.replicate base true) [] [] [] []) _ (dh (n / base / base / base))
  rw [dr (n / base / base / base), cfg₄, cfg₄] at hr₄
  refine ⟨t₁ + t₂ + t₃ + t₄, ?_, ?_⟩
  · have hb₁ := MatrixUnaryDivision.totalTime_bound n base
    have hb₂ := MatrixUnaryDivision.totalTime_bound (n / base) base
    have hb₃ := MatrixUnaryDivision.totalTime_bound (n / base / base) base
    have hb₄ := MatrixUnaryDivision.totalTime_bound (n / base / base / base) base
    have h₁ := Nat.div_le_self n base
    have h₂ := Nat.div_le_self (n / base) base
    have h₃ := Nat.div_le_self (n / base / base) base
    omega
  · exact (run_add ((run_add ((run_add hr₁ t₂).trans hr₂) t₃).trans hr₃) t₄).trans hr₄

end BaseFour

namespace Selectors

abbrev Label := BaseFour.Label
abbrev Control := BaseFour.Control
abbrev Config := TM2.Cfg (fun _ : Fin 12 => Bool) Label Control

def bank₁ : Fin 6 ⊕ Fin 6 ≃ Fin 12 := finSumFinEquiv

private def perm₂ : Fin 12 ≃ Fin 12 where
  toFun i := ![6, 1, 2, 0, 9, 5, 3, 4, 7, 8, 10, 11] i
  invFun i := ![3, 1, 2, 6, 7, 5, 0, 8, 9, 4, 10, 11] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def perm₃ : Fin 12 ≃ Fin 12 where
  toFun i := ![7, 1, 2, 6, 10, 5, 0, 3, 4, 8, 9, 11] i
  invFun i := ![6, 1, 2, 7, 8, 5, 3, 0, 9, 10, 4, 11] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private def perm₄ : Fin 12 ≃ Fin 12 where
  toFun i := ![8, 1, 2, 7, 11, 5, 0, 3, 4, 6, 9, 10] i
  invFun i := ![6, 1, 2, 7, 8, 5, 9, 3, 0, 10, 11, 4] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def bank₂ : Fin 6 ⊕ Fin 6 ≃ Fin 12 := bank₁.trans perm₂
def bank₃ : Fin 6 ⊕ Fin 6 ≃ Fin 12 := bank₁.trans perm₃
def bank₄ : Fin 6 ⊕ Fin 6 ≃ Fin 12 := bank₁.trans perm₄

def program : Label → TM2.Stmt (fun _ : Fin 12 => Bool) Label Control
  | .inl l => renameStmt bank₁ (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixUnaryDivision.Label.start)) (MatrixUnaryDivision.program l))
  | .inr (.inl l) => renameStmt bank₂ BaseFour.labels₂ BaseFour.controls₂
      (liftStmt (some (.inr (.inl MatrixUnaryDivision.Label.start))) (MatrixUnaryDivision.program l))
  | .inr (.inr (.inl l)) => renameStmt bank₃ BaseFour.labels₃ BaseFour.controls₃
      (liftStmt (some (.inr (.inr MatrixUnaryDivision.Label.start))) (MatrixUnaryDivision.program l))
  | .inr (.inr (.inr l)) => renameStmt bank₄ BaseFour.labels₄ BaseFour.controls₄
      (liftStmt none (MatrixUnaryDivision.program l))

def cfg (l : Option Label)
    (s₀ divisor r₀ q₀ s₆ s₇ s₈ q₁ q₂ q₃ : List Bool) : Config :=
  ⟨l, (false, false, false, false), ![s₀, divisor, [], r₀, q₀, [], s₆, s₇, s₈, q₁, q₂, q₃]⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem cfg₁ (l : Option MatrixUnaryDivision.Label)
    (s₀ divisor r₀ q₀ s₆ s₇ s₈ q₁ q₂ q₃ : List Bool) :
    renameCfg bank₁ (Equiv.refl _) (Equiv.refl _)
      (liftCfg (some (.inl MatrixUnaryDivision.Label.start)) (false, false, false)
        (![s₆, s₇, s₈, q₁, q₂, q₃] : Fin 6 → List Bool)
        (MatrixUnaryDivision.cfg l false s₀ divisor [] r₀ q₀ [])) =
      cfg (l.elim (some (.inr (.inl .start))) (fun l => some (.inl l)))
        s₀ divisor r₀ q₀ s₆ s₇ s₈ q₁ q₂ q₃ := by
  cases l <;> apply congrArg (fun S => (⟨_, (false, false, false, false), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem cfg₂ (l : Option MatrixUnaryDivision.Label)
    (s₀ divisor r₀ q₀ s₆ s₇ s₈ q₁ q₂ q₃ : List Bool) :
    renameCfg bank₂ BaseFour.labels₂ BaseFour.controls₂
      (liftCfg (some (.inr (.inl MatrixUnaryDivision.Label.start))) (false, false, false)
        (![r₀, q₀, s₇, s₈, q₂, q₃] : Fin 6 → List Bool)
        (MatrixUnaryDivision.cfg l false s₆ divisor [] s₀ q₁ [])) =
      cfg (l.elim (some (.inr (.inr (.inl .start)))) (fun l => some (.inr (.inl l))))
        s₀ divisor r₀ q₀ s₆ s₇ s₈ q₁ q₂ q₃ := by
  cases l <;> apply congrArg (fun S => (⟨_, (false, false, false, false), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem cfg₃ (l : Option MatrixUnaryDivision.Label)
    (s₀ divisor r₀ q₀ s₆ s₇ s₈ q₁ q₂ q₃ : List Bool) :
    renameCfg bank₃ BaseFour.labels₃ BaseFour.controls₃
      (liftCfg (some (.inr (.inr MatrixUnaryDivision.Label.start))) (false, false, false)
        (![s₀, r₀, q₀, s₈, q₁, q₃] : Fin 6 → List Bool)
        (MatrixUnaryDivision.cfg l false s₇ divisor [] s₆ q₂ [])) =
      cfg (l.elim (some (.inr (.inr (.inr .start)))) (fun l => some (.inr (.inr (.inl l)))))
        s₀ divisor r₀ q₀ s₆ s₇ s₈ q₁ q₂ q₃ := by
  cases l <;> apply congrArg (fun S => (⟨_, (false, false, false, false), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem cfg₄ (l : Option MatrixUnaryDivision.Label)
    (s₀ divisor r₀ q₀ s₆ s₇ s₈ q₁ q₂ q₃ : List Bool) :
    renameCfg bank₄ BaseFour.labels₄ BaseFour.controls₄
      (liftCfg none (false, false, false) (![s₀, r₀, q₀, s₆, q₁, q₂] : Fin 6 → List Bool)
        (MatrixUnaryDivision.cfg l false s₈ divisor [] s₇ q₃ [])) =
      cfg (l.map (fun l => .inr (.inr (.inr l))))
        s₀ divisor r₀ q₀ s₆ s₇ s₈ q₁ q₂ q₃ := by
  cases l <;> apply congrArg (fun S => (⟨_, (false, false, false, false), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

/-- Split four actual unary selector digits into coordinate and family
indices by four physical divisions, preserving their shared divisor. -/
theorem selectors_run (d₀ d₁ d₂ d₃ families : ℕ) :
    ∃ t ≤ 8 * (d₀ + d₁ + d₂ + d₃) + 12 * families + 16,
      run t (cfg (some (.inl .start)) (List.replicate d₀ true)
        (List.replicate families true) [] [] (List.replicate d₁ true)
        (List.replicate d₂ true) (List.replicate d₃ true) [] [] []) =
      cfg none (List.replicate (d₁ % families) true) (List.replicate families true)
        (List.replicate (d₀ % families) true) (List.replicate (d₀ / families) true)
        (List.replicate (d₂ % families) true) (List.replicate (d₃ % families) true) []
        (List.replicate (d₁ / families) true) (List.replicate (d₂ / families) true)
        (List.replicate (d₃ / families) true) := by
  have dh (x : ℕ) : (((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime x families])
      (MatrixUnaryDivision.cfg (some .start) false (List.replicate x true)
        (List.replicate families true) [] [] [] [])).l = none := by
    change (MatrixUnaryDivision.run _ _).l = none
    rw [MatrixUnaryDivision.division_total_run]
    rfl
  have dr (x : ℕ) := MatrixUnaryDivision.division_total_run x families
  change ∀ x, (((advance MatrixUnaryDivision.program)^[MatrixUnaryDivision.totalTime x families]) _) = _ at dr
  obtain ⟨t₀, ht₀, hr₀⟩ := lift_outputs_renamed bank₁ (Equiv.refl _) (Equiv.refl _)
    MatrixUnaryDivision.program program (some (.inl MatrixUnaryDivision.Label.start)) (fun _ => rfl)
    (false, false, false)
    (![List.replicate d₁ true, List.replicate d₂ true, List.replicate d₃ true, [], [], []] :
      Fin 6 → List Bool)
    (MatrixUnaryDivision.cfg (some .start) false (List.replicate d₀ true)
      (List.replicate families true) [] [] [] []) _ (dh d₀)
  rw [dr d₀, cfg₁, cfg₁] at hr₀
  obtain ⟨t₁, ht₁, hr₁⟩ := lift_outputs_renamed bank₂ BaseFour.labels₂ BaseFour.controls₂
    MatrixUnaryDivision.program program
    (some (.inr (.inl MatrixUnaryDivision.Label.start))) (fun _ => rfl)
    (false, false, false)
    (![List.replicate (d₀ % families) true, List.replicate (d₀ / families) true,
      List.replicate d₂ true, List.replicate d₃ true, [], []] : Fin 6 → List Bool)
    (MatrixUnaryDivision.cfg (some .start) false (List.replicate d₁ true)
      (List.replicate families true) [] [] [] []) _ (dh d₁)
  rw [dr d₁, cfg₂, cfg₂] at hr₁
  obtain ⟨t₂, ht₂, hr₂⟩ := lift_outputs_renamed bank₃ BaseFour.labels₃ BaseFour.controls₃
    MatrixUnaryDivision.program program
    (some (.inr (.inr MatrixUnaryDivision.Label.start))) (fun _ => rfl)
    (false, false, false)
    (![List.replicate (d₁ % families) true, List.replicate (d₀ % families) true,
      List.replicate (d₀ / families) true, List.replicate d₃ true,
      List.replicate (d₁ / families) true, []] : Fin 6 → List Bool)
    (MatrixUnaryDivision.cfg (some .start) false (List.replicate d₂ true)
      (List.replicate families true) [] [] [] []) _ (dh d₂)
  rw [dr d₂, cfg₃, cfg₃] at hr₂
  obtain ⟨t₃, ht₃, hr₃⟩ := lift_outputs_renamed bank₄ BaseFour.labels₄ BaseFour.controls₄
    MatrixUnaryDivision.program program none (fun _ => rfl)
    (false, false, false)
    (![List.replicate (d₁ % families) true, List.replicate (d₀ % families) true,
      List.replicate (d₀ / families) true, List.replicate (d₂ % families) true,
      List.replicate (d₁ / families) true, List.replicate (d₂ / families) true] : Fin 6 → List Bool)
    (MatrixUnaryDivision.cfg (some .start) false (List.replicate d₃ true)
      (List.replicate families true) [] [] [] []) _ (dh d₃)
  rw [dr d₃, cfg₄, cfg₄] at hr₃
  refine ⟨t₀ + t₁ + t₂ + t₃, ?_, ?_⟩
  · have hb₀ := MatrixUnaryDivision.totalTime_bound d₀ families
    have hb₁ := MatrixUnaryDivision.totalTime_bound d₁ families
    have hb₂ := MatrixUnaryDivision.totalTime_bound d₂ families
    have hb₃ := MatrixUnaryDivision.totalTime_bound d₃ families
    omega
  · exact (run_add ((run_add ((run_add hr₀ t₁).trans hr₁) t₂).trans hr₂) t₃).trans hr₃

end Selectors

namespace Combined

abbrev Label := BaseFour.Label ⊕ Selectors.Label
abbrev Control := BaseFour.Control × Selectors.Control
abbrev Config := TM2.Cfg (fun _ : Fin 14 => Bool) Label Control

def baseBank : Fin 9 ⊕ Fin 5 ≃ Fin 14 := finSumFinEquiv

private def selectorPerm : Fin 14 ≃ Fin 14 where
  toFun i := ![3, 9, 2, 4, 10, 5, 6, 7, 8, 11, 12, 13, 0, 1] i
  invFun i := ![12, 13, 2, 0, 3, 5, 6, 7, 8, 1, 4, 9, 10, 11] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def selectorBank : Fin 12 ⊕ Fin 2 ≃ Fin 14 := finSumFinEquiv.trans selectorPerm

def program : Label → TM2.Stmt (fun _ : Fin 14 => Bool) Label Control
  | .inl l => renameStmt baseBank (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inl MatrixUnaryDivision.Label.start)) (BaseFour.program l))
  | .inr l => renameStmt selectorBank (Equiv.sumComm _ _) (Equiv.prodComm _ _)
      (liftStmt none (Selectors.program l))

def cfg (l : Option Label)
    (tail base d₀ r₀ d₁ d₂ d₃ families q₀ q₁ q₂ q₃ : List Bool) : Config :=
  ⟨l, ((false, false, false, false), (false, false, false, false)),
    ![tail, base, [], d₀, r₀, [], d₁, d₂, d₃, families, q₀, q₁, q₂, q₃]⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem base_cfg (l : Option BaseFour.Label)
    (tail base d₀ d₁ d₂ d₃ families q₀ q₁ q₂ q₃ : List Bool) :
    renameCfg baseBank (Equiv.refl _) (Equiv.refl _)
      (liftCfg (some (.inl MatrixUnaryDivision.Label.start)) (false, false, false, false)
        (![families, q₀, q₁, q₂, q₃] : Fin 5 → List Bool)
        (BaseFour.cfg l tail base d₀ [] d₁ d₂ d₃)) =
      cfg (l.elim (some (.inr (.inl .start))) (fun l => some (.inl l)))
        tail base d₀ [] d₁ d₂ d₃ families q₀ q₁ q₂ q₃ := by
  cases l <;> apply congrArg (fun S =>
    (⟨_, ((false, false, false, false), (false, false, false, false)), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem selector_cfg (l : Option Selectors.Label)
    (tail base d₀ r₀ d₁ d₂ d₃ families q₀ q₁ q₂ q₃ : List Bool) :
    renameCfg selectorBank (Equiv.sumComm _ _) (Equiv.prodComm _ _)
      (liftCfg none (false, false, false, false) (![tail, base] : Fin 2 → List Bool)
        (Selectors.cfg l d₀ families r₀ q₀ d₁ d₂ d₃ q₁ q₂ q₃)) =
      cfg (l.map Sum.inr) tail base d₀ r₀ d₁ d₂ d₃ families q₀ q₁ q₂ q₃ := by
  cases l <;> apply congrArg (fun S =>
    (⟨_, ((false, false, false, false), (false, false, false, false)), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

/-- Starting with the literal column number, base, and family count, a single
controller extracts all eight unary selector fields and retains the tail
quotient. No selector digit is precomputed or supplied. -/
theorem decode_run (n base families : ℕ) :
    let d₀ := n % base
    let d₁ := n / base % base
    let d₂ := n / base / base % base
    let d₃ := n / base / base / base % base
    ∃ t ≤ 4 * (8 * n + 3 * base + 4) + 8 * (d₀ + d₁ + d₂ + d₃) + 12 * families + 16,
      run t (cfg (some (.inl (.inl .start))) (List.replicate n true)
        (List.replicate base true) [] [] [] [] [] (List.replicate families true) [] [] [] []) =
      cfg none (List.replicate (n / base / base / base / base) true)
        (List.replicate base true) (List.replicate (d₁ % families) true)
        (List.replicate (d₀ % families) true) (List.replicate (d₂ % families) true)
        (List.replicate (d₃ % families) true) [] (List.replicate families true)
        (List.replicate (d₀ / families) true) (List.replicate (d₁ / families) true)
        (List.replicate (d₂ / families) true) (List.replicate (d₃ / families) true) := by
  dsimp only
  obtain ⟨kb, hkb, hrb⟩ := BaseFour.digits_run n base
  have hhb : (((advance BaseFour.program)^[kb])
      (BaseFour.cfg (some (.inl .start)) (List.replicate n true)
        (List.replicate base true) [] [] [] [] [])).l = none := by
    change (BaseFour.run kb _).l = none
    rw [hrb]
    rfl
  obtain ⟨tb, htb, hrunb⟩ := lift_outputs_renamed baseBank (Equiv.refl _) (Equiv.refl _)
    BaseFour.program program (some (.inl MatrixUnaryDivision.Label.start)) (fun _ => rfl)
    (false, false, false, false)
    (![List.replicate families true, [], [], [], []] : Fin 5 → List Bool)
    (BaseFour.cfg (some (.inl .start)) (List.replicate n true)
      (List.replicate base true) [] [] [] [] []) kb hhb
  change (((advance BaseFour.program)^[kb]) _) = _ at hrb
  rw [hrb, base_cfg, base_cfg] at hrunb
  obtain ⟨ks, hks, hrs⟩ := Selectors.selectors_run (n % base) (n / base % base)
    (n / base / base % base) (n / base / base / base % base) families
  have hhs : (((advance Selectors.program)^[ks])
      (Selectors.cfg (some (.inl .start)) (List.replicate (n % base) true)
        (List.replicate families true) [] [] (List.replicate (n / base % base) true)
        (List.replicate (n / base / base % base) true)
        (List.replicate (n / base / base / base % base) true) [] [] [])).l = none := by
    change (Selectors.run ks _).l = none
    rw [hrs]
    rfl
  obtain ⟨ts, hts, hruns⟩ := lift_outputs_renamed selectorBank
    (Equiv.sumComm _ _) (Equiv.prodComm _ _) Selectors.program program none (fun _ => rfl)
    (false, false, false, false)
    (![List.replicate (n / base / base / base / base) true, List.replicate base true] : Fin 2 → List Bool)
    (Selectors.cfg (some (.inl .start)) (List.replicate (n % base) true)
      (List.replicate families true) [] [] (List.replicate (n / base % base) true)
      (List.replicate (n / base / base % base) true)
      (List.replicate (n / base / base / base % base) true) [] [] []) ks hhs
  change (((advance Selectors.program)^[ks]) _) = _ at hrs
  rw [hrs, selector_cfg, selector_cfg] at hruns
  refine ⟨tb + ts, ?_, (run_add hrunb ts).trans hruns⟩
  omega

end Combined

namespace Tail

open Turing.TM2.Stmt

abbrev Control := Fin 8 × Bool
abbrev Config := TM2.Cfg (fun _ : Fin 2 => Bool) Unit Control

def increment (r : Fin 8) : Fin 8 := ⟨(r.val + 1) % 8, Nat.mod_lt _ (by decide)⟩
def count (r : Fin 8) (n : ℕ) : Fin 8 := ⟨(r.val + n) % 8, Nat.mod_lt _ (by decide)⟩

def bits (r : Fin 8) : List Bool :=
  [decide (r.val / 4 % 2 = 1), decide (r.val / 2 % 2 = 1), decide (r.val % 2 = 1)]

/-- The only arithmetic in finite control is an eight-entry transition table.
All unary-input symbols are still consumed by separate literal transitions. -/
def program : Unit → TM2.Stmt (fun _ : Fin 2 => Bool) Unit Control
  | () => pop 0 (fun s b => (if b.isSome then increment s.1 else s.1, b.isSome))
      (branch Prod.snd (goto (fun _ => ()))
        (push 1 (fun s => decide (s.1.val % 2 = 1))
          (push 1 (fun s => decide (s.1.val / 2 % 2 = 1))
            (push 1 (fun s => decide (s.1.val / 4 % 2 = 1))
              (load (fun _ => (0, false)) halt)))))

def cfg (l : Option Unit) (r : Fin 8) (flag : Bool) (input out : List Bool) : Config :=
  ⟨l, (r, flag), ![input, out]⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_cons (r : Fin 8) (flag : Bool) (input out : List Bool) :
    TM2.step program (cfg (some ()) r flag (true :: input) out) =
      some (cfg (some ()) (increment r) true input out) := by
  apply congrArg (fun S => some (⟨some (), (increment r, true), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem step_nil (r : Fin 8) (flag : Bool) (out : List Bool) :
    TM2.step program (cfg (some ()) r flag [] out) =
      some (cfg none 0 false [] (bits r ++ out)) := by
  apply congrArg (fun S => some (⟨none, (0, false), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem count_increment (r : Fin 8) (n : ℕ) : count (increment r) n = count r (n + 1) := by
  apply Fin.ext
  simp only [count, increment]
  omega

theorem count_zero (r : Fin 8) : count r 0 = r := by
  apply Fin.ext
  simp only [count, Nat.add_zero, Nat.mod_eq_of_lt r.isLt]

theorem count_run (n : ℕ) (r : Fin 8) (flag : Bool) (out : List Bool) :
    run (n + 1) (cfg (some ()) r flag (List.replicate n true) out) =
      cfg none 0 false [] (bits (count r n) ++ out) := by
  induction n generalizing r flag with
  | zero => simpa only [count_zero] using run_succ (step_nil r flag out) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (step_cons _ _ _ _) _]
      simpa only [count_increment] using ih (increment r) true

theorem tail_run (r : Fin 8) (out : List Bool) :
    run (r.val + 1) (cfg (some ()) 0 false (List.replicate r.val true) out) =
      cfg none 0 false [] (bits r ++ out) := by
  have h : count 0 r.val = r := by
    apply Fin.ext
    simp only [count, Fin.val_zero, Nat.zero_add, Nat.mod_eq_of_lt r.isLt]
  simpa only [h] using count_run r.val 0 false out

theorem bits_eq_decoded (r : Fin 8) :
    bits r = List.ofFn (MatrixMaterialization.tailCode.symm r) := by
  fin_cases r <;> rfl

theorem bits_encoded (tail : Fin 3 → Bool) :
    bits (MatrixMaterialization.tailCode tail) = List.ofFn tail := by
  rw [bits_eq_decoded, Equiv.symm_apply_apply]

end Tail

namespace Full

abbrev Label := Combined.Label ⊕ Unit
abbrev Control := Combined.Control × Tail.Control
abbrev Config := TM2.Cfg (fun _ : Fin 15 => Bool) Label Control

def fieldsBank : Fin 14 ⊕ Fin 1 ≃ Fin 15 := finSumFinEquiv

private def tailPerm : Fin 15 ≃ Fin 15 where
  toFun i := ![0, 14, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] i
  invFun i := ![0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 1] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def tailBank : Fin 2 ⊕ Fin 13 ≃ Fin 15 := finSumFinEquiv.trans tailPerm

def program : Label → TM2.Stmt (fun _ : Fin 15 => Bool) Label Control
  | .inl l => renameStmt fieldsBank (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some ()) (Combined.program l))
  | .inr () => renameStmt tailBank (Equiv.sumComm _ _) (Equiv.prodComm _ _)
      (liftStmt none (Tail.program ()))

def cfg (l : Option Label)
    (tail base d₀ r₀ d₁ d₂ d₃ families q₀ q₁ q₂ q₃ tailBits : List Bool) : Config :=
  ⟨l, (((false, false, false, false), (false, false, false, false)), (0, false)),
    ![tail, base, [], d₀, r₀, [], d₁, d₂, d₃, families, q₀, q₁, q₂, q₃, tailBits]⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem fields_cfg (l : Option Combined.Label)
    (tail base d₀ r₀ d₁ d₂ d₃ families q₀ q₁ q₂ q₃ tailBits : List Bool) :
    renameCfg fieldsBank (Equiv.refl _) (Equiv.refl _)
      (liftCfg (some ()) (0, false) (fun _ : Fin 1 => tailBits)
        (Combined.cfg l tail base d₀ r₀ d₁ d₂ d₃ families q₀ q₁ q₂ q₃)) =
      cfg (l.elim (some (.inr ())) (fun l => some (.inl l)))
        tail base d₀ r₀ d₁ d₂ d₃ families q₀ q₁ q₂ q₃ tailBits := by
  cases l <;> apply congrArg (fun S =>
    (⟨_, (((false, false, false, false), (false, false, false, false)), (0, false)), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

private theorem tail_cfg (l : Option Unit)
    (tail base d₀ r₀ d₁ d₂ d₃ families q₀ q₁ q₂ q₃ tailBits : List Bool) :
    renameCfg tailBank (Equiv.sumComm _ _) (Equiv.prodComm _ _)
      (liftCfg none ((false, false, false, false), (false, false, false, false))
        (![base, [], d₀, r₀, [], d₁, d₂, d₃, families, q₀, q₁, q₂, q₃] : Fin 13 → List Bool)
        (Tail.cfg l 0 false tail tailBits)) =
      cfg (l.map Sum.inr) tail base d₀ r₀ d₁ d₂ d₃ families q₀ q₁ q₂ q₃ tailBits := by
  cases l <;> apply congrArg (fun S =>
    (⟨_, (((false, false, false, false), (false, false, false, false)), (0, false)), S⟩ : Config)) <;>
    funext k <;> fin_cases k <;> rfl

/-- Eight selector fields and all three tail bits are extracted from the
literal unary column number by one fixed finite controller. -/
theorem decode_run (n base families : ℕ) (htail : n / base / base / base / base < 8) :
    let d₀ := n % base
    let d₁ := n / base % base
    let d₂ := n / base / base % base
    let d₃ := n / base / base / base % base
    ∃ t ≤ 4 * (8 * n + 3 * base + 4) + 8 * (d₀ + d₁ + d₂ + d₃) + 12 * families + 24,
      run t (cfg (some (.inl (.inl (.inl .start)))) (List.replicate n true)
        (List.replicate base true) [] [] [] [] [] (List.replicate families true) [] [] [] [] []) =
      cfg none [] (List.replicate base true) (List.replicate (d₁ % families) true)
        (List.replicate (d₀ % families) true) (List.replicate (d₂ % families) true)
        (List.replicate (d₃ % families) true) [] (List.replicate families true)
        (List.replicate (d₀ / families) true) (List.replicate (d₁ / families) true)
        (List.replicate (d₂ / families) true) (List.replicate (d₃ / families) true)
        (Tail.bits ⟨n / base / base / base / base, htail⟩) := by
  dsimp only
  let tail : Fin 8 := ⟨n / base / base / base / base, htail⟩
  obtain ⟨kf, hkf, hrf⟩ := Combined.decode_run n base families
  have hhf : (((advance Combined.program)^[kf])
      (Combined.cfg (some (.inl (.inl .start))) (List.replicate n true)
        (List.replicate base true) [] [] [] [] [] (List.replicate families true) [] [] [] [])).l = none := by
    change (Combined.run kf _).l = none
    rw [hrf]
    rfl
  obtain ⟨tf, htf, hrunf⟩ := lift_outputs_renamed fieldsBank (Equiv.refl _) (Equiv.refl _)
    Combined.program program (some ()) (fun _ => rfl) (0, false) (fun _ : Fin 1 => [])
    (Combined.cfg (some (.inl (.inl .start))) (List.replicate n true)
      (List.replicate base true) [] [] [] [] [] (List.replicate families true) [] [] [] []) kf hhf
  change (((advance Combined.program)^[kf]) _) = _ at hrf
  rw [hrf, fields_cfg, fields_cfg] at hrunf
  have hrt := Tail.tail_run tail []
  simp only [List.append_nil] at hrt
  have hht : (((advance Tail.program)^[tail.val + 1])
      (Tail.cfg (some ()) 0 false (List.replicate tail.val true) [])).l = none := by
    change (Tail.run _ _).l = none
    rw [hrt]
    rfl
  obtain ⟨tt, htt, hrunt⟩ := lift_outputs_renamed tailBank (Equiv.sumComm _ _) (Equiv.prodComm _ _)
    Tail.program program none (fun _ => rfl)
    ((false, false, false, false), (false, false, false, false))
    (![List.replicate base true, [], List.replicate ((n / base % base) % families) true,
      List.replicate ((n % base) % families) true, [],
      List.replicate ((n / base / base % base) % families) true,
      List.replicate ((n / base / base / base % base) % families) true, [],
      List.replicate families true, List.replicate ((n % base) / families) true,
      List.replicate ((n / base % base) / families) true,
      List.replicate ((n / base / base % base) / families) true,
      List.replicate ((n / base / base / base % base) / families) true] : Fin 13 → List Bool)
    (Tail.cfg (some ()) 0 false (List.replicate tail.val true) []) (tail.val + 1) hht
  change (((advance Tail.program)^[tail.val + 1]) _) = _ at hrt
  rw [hrt, tail_cfg, tail_cfg] at hrunt
  refine ⟨tf + tt, ?_, (run_add hrunf tt).trans hrunt⟩
  have hb := tail.isLt
  omega

/-- The decoded fields are the exact selectors and tail of the finite
column equivalence used by the matrix definition. -/
theorem column_run {d N₁ : ℕ} (code : Fin (8 * (d * N₁) ^ 4)) :
    let c := (MatrixMaterialization.columnCode d N₁).symm code
    ∃ t ≤ 64 * code.val + 12 * (d * N₁) + 12 * N₁ + 40,
      run t (cfg (some (.inl (.inl (.inl .start)))) (List.replicate code.val true)
        (List.replicate (d * N₁) true) [] [] [] [] [] (List.replicate N₁ true) [] [] [] [] []) =
      cfg none [] (List.replicate (d * N₁) true)
        (List.replicate (c.2 2).2.val true) (List.replicate (c.2 3).2.val true)
        (List.replicate (c.2 1).2.val true) (List.replicate (c.2 0).2.val true) []
        (List.replicate N₁ true) (List.replicate (c.2 3).1.val true)
        (List.replicate (c.2 2).1.val true) (List.replicate (c.2 1).1.val true)
        (List.replicate (c.2 0).1.val true) (List.ofFn c.1) := by
  let c := (MatrixMaterialization.columnCode d N₁).symm code
  have htail := MatrixColumnDigitArithmetic.tail_index code
  have ht : code.val / (d * N₁) / (d * N₁) / (d * N₁) / (d * N₁) < 8 := by
    rw [← htail]
    exact (MatrixMaterialization.tailCode c.1).isLt
  obtain ⟨t, htime, hr⟩ := decode_run code.val (d * N₁) N₁ ht
  have he : (⟨code.val / (d * N₁) / (d * N₁) / (d * N₁) / (d * N₁), ht⟩ : Fin 8) =
      MatrixMaterialization.tailCode c.1 := Fin.ext htail.symm
  rw [he, Tail.bits_encoded] at hr
  have hc₀ := MatrixColumnDigitArithmetic.coordinate code 0
  have hc₁ := MatrixColumnDigitArithmetic.coordinate code 1
  have hc₂ := MatrixColumnDigitArithmetic.coordinate code 2
  have hc₃ := MatrixColumnDigitArithmetic.coordinate code 3
  have hf₀ := MatrixColumnDigitArithmetic.family_index code 0
  have hf₁ := MatrixColumnDigitArithmetic.family_index code 1
  have hf₂ := MatrixColumnDigitArithmetic.family_index code 2
  have hf₃ := MatrixColumnDigitArithmetic.family_index code 3
  rw [MatrixColumnDigitArithmetic.digit_zero] at hc₀ hf₀
  rw [MatrixColumnDigitArithmetic.digit_one] at hc₁ hf₁
  rw [MatrixColumnDigitArithmetic.digit_two] at hc₂ hf₂
  rw [MatrixColumnDigitArithmetic.digit_three] at hc₃ hf₃
  rw [← hc₀, ← hc₁, ← hc₂, ← hc₃, ← hf₀, ← hf₁, ← hf₂, ← hf₃] at hr
  refine ⟨t, ?_, hr⟩
  have hq₁ := Nat.div_le_self code.val (d * N₁)
  have hq₂ := Nat.div_le_self (code.val / (d * N₁)) (d * N₁)
  have hq₃ := Nat.div_le_self (code.val / (d * N₁) / (d * N₁)) (d * N₁)
  have hd₀ := Nat.mod_le code.val (d * N₁)
  have hd₁ := Nat.mod_le (code.val / (d * N₁)) (d * N₁)
  have hd₂ := Nat.mod_le (code.val / (d * N₁) / (d * N₁)) (d * N₁)
  have hd₃ := Nat.mod_le (code.val / (d * N₁) / (d * N₁) / (d * N₁)) (d * N₁)
  omega

end Full

end EthInapproximability.CurrentPaper.MatrixColumnDecode
