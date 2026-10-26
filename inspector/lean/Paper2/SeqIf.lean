import EthInapproximability.CurrentPaper.BitMachineInline

/-! Conditional sequential composition on one physical bank.

After the first program halts, one administrative transition inspects a
fixed Boolean function of its *actual* final finite control. If it is
`true`, the control is reset to fixed values and the second program starts;
otherwise the composite halts with the first program's final control kept
intact. The branch is read from finite control, not supplied. Every
transition is charged. This mirrors `BitMachineRawSequence` exactly, with
the one extra conditional. -/

namespace Paper2.SeqIf

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

variable {K LA LB VA VB : Type*} [DecidableEq K]

abbrev Label (LA LB : Type*) := LA ⊕ (Unit ⊕ LB)
abbrev Control (VA VB : Type*) := VA × VB

def leftLabel (l : LA) : Label LA LB := .inl l
def rightLabel (l : LB) : Label LA LB := .inr (.inr l)
def test : Label LA LB := .inr (.inl ())

def program (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA) (ok : VA → Bool)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB)
    (b₀ : LB) (v₀ : VA) (w₀ : VB) :
    Label LA LB → TM2.Stmt (fun _ : K => Bool) (Label LA LB) (Control VA VB)
  | .inl l => BitMachineInline.stmt leftLabel (fun v => (v, w₀)) Prod.fst
      (some test) (A l)
  | .inr (.inl _) => .branch (fun v => ok v.1)
      (.load (fun _ => (v₀, w₀)) (.goto (fun _ => rightLabel b₀))) .halt
  | .inr (.inr l) => BitMachineInline.stmt rightLabel (fun w => (v₀, w))
      Prod.snd none (B l)

theorem test_true (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA) (ok : VA → Bool)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB) (b₀ : LB) (v₀ v : VA) (w₀ : VB)
    (S : K → List Bool) (h : ok v = true) :
    advance (program A ok B b₀ v₀ w₀)
      (⟨some test, (v, w₀), S⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label LA LB) (Control VA VB)) =
      ⟨some (rightLabel b₀), (v₀, w₀), S⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, test, h]

theorem test_false (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA) (ok : VA → Bool)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB) (b₀ : LB) (v₀ v : VA) (w₀ : VB)
    (S : K → List Bool) (h : ok v = false) :
    advance (program A ok B b₀ v₀ w₀)
      (⟨some test, (v, w₀), S⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label LA LB) (Control VA VB)) =
      ⟨none, (v, w₀), S⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, test, h]

theorem halted (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA) (ok : VA → Bool)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB) (b₀ : LB) (v₀ : VA) (w₀ : VB)
    (c : Control VA VB) (S : K → List Bool) (n : Nat) :
    ((advance (program A ok B b₀ v₀ w₀))^[n])
      (⟨none, c, S⟩ : TM2.Cfg (fun _ : K => Bool) (Label LA LB) (Control VA VB)) =
      ⟨none, c, S⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- First phase to its test point, from any start control of `A`. -/
theorem first_phase (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA) (ok : VA → Bool)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB) (b₀ : LB) (v₀ : VA) (w₀ : VB)
    (a₀ : LA) (u v₁ : VA) (S T : K → List Bool) (ta : Nat)
    (ha : ((advance A)^[ta]) (⟨some a₀, u, S⟩ : TM2.Cfg (fun _ : K => Bool) LA VA) =
      ⟨none, v₁, T⟩) :
    ∃ a ≤ ta, ((advance (program A ok B b₀ v₀ w₀))^[a])
      (⟨some (leftLabel a₀), (u, w₀), S⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label LA LB) (Control VA VB)) =
      ⟨some test, (v₁, w₀), T⟩ := by
  have hah : (((advance A)^[ta])
      (⟨some a₀, u, S⟩ : TM2.Cfg (fun _ : K => Bool) LA VA)).l = none := by rw [ha]
  obtain ⟨a, hat, har⟩ := BitMachineInline.outputs leftLabel (fun v => (v, w₀)) Prod.fst
    (fun _ => rfl) (some test) A (program A ok B b₀ v₀ w₀) (fun _ => rfl)
    (⟨some a₀, u, S⟩ : TM2.Cfg (fun _ : K => Bool) LA VA) ta hah
  rw [ha] at har
  exact ⟨a, hat, by simpa only [BitMachineInline.cfg] using har⟩

/-- Both phases when the test is `true`. -/
theorem runs_ok (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA) (ok : VA → Bool)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB) (b₀ : LB) (v₀ : VA) (w₀ : VB)
    (a₀ : LA) (u v₁ : VA) (w₁ : VB) (S T U : K → List Bool) (ta tb : Nat)
    (ha : ((advance A)^[ta]) (⟨some a₀, u, S⟩ : TM2.Cfg (fun _ : K => Bool) LA VA) =
      ⟨none, v₁, T⟩)
    (hok : ok v₁ = true)
    (hb : ((advance B)^[tb]) (⟨some b₀, w₀, T⟩ : TM2.Cfg (fun _ : K => Bool) LB VB) =
      ⟨none, w₁, U⟩) :
    ∃ t ≤ ta + tb + 1, ((advance (program A ok B b₀ v₀ w₀))^[t])
      (⟨some (leftLabel a₀), (u, w₀), S⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label LA LB) (Control VA VB)) =
      ⟨none, (v₀, w₁), U⟩ := by
  obtain ⟨a, hat, har⟩ := first_phase A ok B b₀ v₀ w₀ a₀ u v₁ S T ta ha
  have hbh : (((advance B)^[tb])
      (⟨some b₀, w₀, T⟩ : TM2.Cfg (fun _ : K => Bool) LB VB)).l = none := by rw [hb]
  obtain ⟨b, hbt, hbr⟩ := BitMachineInline.outputs rightLabel (fun w => (v₀, w)) Prod.snd
    (fun _ => rfl) none B (program A ok B b₀ v₀ w₀) (fun _ => rfl)
    (⟨some b₀, w₀, T⟩ : TM2.Cfg (fun _ : K => Bool) LB VB) tb hbh
  rw [hb] at hbr
  simp only [BitMachineInline.cfg] at hbr
  refine ⟨a + 1 + b, by omega, ?_⟩
  rw [show a + 1 + b = b + (a + 1) by omega, Function.iterate_add_apply,
    Function.iterate_succ_apply', har, test_true A ok B b₀ v₀ v₁ w₀ T hok]
  exact hbr

/-- The composite halts right after the test when it is `false`, keeping the
first program's actual final control. -/
theorem runs_stop (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA) (ok : VA → Bool)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB) (b₀ : LB) (v₀ : VA) (w₀ : VB)
    (a₀ : LA) (u v₁ : VA) (S T : K → List Bool) (ta : Nat)
    (ha : ((advance A)^[ta]) (⟨some a₀, u, S⟩ : TM2.Cfg (fun _ : K => Bool) LA VA) =
      ⟨none, v₁, T⟩)
    (hok : ok v₁ = false) :
    ∃ t ≤ ta + 1, ((advance (program A ok B b₀ v₀ w₀))^[t])
      (⟨some (leftLabel a₀), (u, w₀), S⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label LA LB) (Control VA VB)) =
      ⟨none, (v₁, w₀), T⟩ := by
  obtain ⟨a, hat, har⟩ := first_phase A ok B b₀ v₀ w₀ a₀ u v₁ S T ta ha
  refine ⟨a + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply', har, test_false A ok B b₀ v₀ v₁ w₀ T hok]

#print axioms runs_ok
#print axioms runs_stop
#print axioms halted

end Paper2.SeqIf
