import EthInapproximability.CurrentPaper.BitMachineInline

/-!
# Sequential composition on one physical Boolean-stack bank

Source: frozen v8 `06-eth.tex` and `B-effectivity-details.tex`, implementation
of fixed sequences of arithmetic and output subroutines. Both instruction
tables are inlined literally; one administrative transition resets the second
finite control. All stack contents survive that handoff unchanged.
-/

namespace EthInapproximability.CurrentPaper.BitMachineRawSequence

open Turing BitMachineEncoding

variable {K LA LB VA VB : Type*} [DecidableEq K]

abbrev Label (LA LB : Type*) := LA ⊕ (Unit ⊕ LB)
abbrev Control (VA VB : Type*) := VA × VB

def leftLabel (l : LA) : Label LA LB := .inl l
def rightLabel (l : LB) : Label LA LB := .inr (.inr l)
def handoff : Label LA LB := .inr (.inl ())

def program (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB)
    (b₀ : LB) (v₀ : VA) (w₀ : VB) :
    Label LA LB → TM2.Stmt (fun _ : K => Bool) (Label LA LB) (Control VA VB)
  | .inl l => BitMachineInline.stmt leftLabel (fun v => (v, w₀)) Prod.fst
      (some handoff) (A l)
  | .inr (.inl _) => .load (fun _ => (v₀, w₀)) (.goto (fun _ => rightLabel b₀))
  | .inr (.inr l) => BitMachineInline.stmt rightLabel (fun w => (v₀, w)) Prod.snd none (B l)

theorem handoff_step (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB)
    (b₀ : LB) (v₀ v : VA) (w₀ w : VB) (S : K → List Bool) :
    advance (program A B b₀ v₀ w₀)
      (⟨some handoff, (v, w), S⟩ : TM2.Cfg (fun _ : K => Bool) (Label LA LB) (Control VA VB)) =
      ⟨some (rightLabel b₀), (v₀, w₀), S⟩ := rfl

/-- A concrete pair of raw runs is executed on the same stacks, in at most
their summed times plus one. The conclusion includes the entire final bank.
The hypotheses are component computations, not the desired composite run. -/
theorem runs (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB)
    (a₀ : LA) (b₀ : LB) (v₀ v₁ : VA) (w₀ w₁ : VB)
    (S T U : K → List Bool) (ta tb : ℕ)
    (ha : ((advance A)^[ta]) (⟨some a₀, v₀, S⟩ : TM2.Cfg (fun _ : K => Bool) LA VA) =
      ⟨none, v₁, T⟩)
    (hb : ((advance B)^[tb]) (⟨some b₀, w₀, T⟩ : TM2.Cfg (fun _ : K => Bool) LB VB) =
      ⟨none, w₁, U⟩) :
    ∃ t ≤ ta + tb + 1,
      ((advance (program A B b₀ v₀ w₀))^[t])
        (⟨some (leftLabel a₀), (v₀, w₀), S⟩ :
          TM2.Cfg (fun _ : K => Bool) (Label LA LB) (Control VA VB)) =
        ⟨none, (v₀, w₁), U⟩ := by
  have hah : (((advance A)^[ta])
      (⟨some a₀, v₀, S⟩ : TM2.Cfg (fun _ : K => Bool) LA VA)).l = none := by rw [ha]
  have hbh : (((advance B)^[tb])
      (⟨some b₀, w₀, T⟩ : TM2.Cfg (fun _ : K => Bool) LB VB)).l = none := by rw [hb]
  obtain ⟨a, hat, har⟩ := BitMachineInline.outputs leftLabel (fun v => (v, w₀)) Prod.fst
    (fun _ => rfl) (some handoff) A (program A B b₀ v₀ w₀) (fun _ => rfl)
    (⟨some a₀, v₀, S⟩ : TM2.Cfg (fun _ : K => Bool) LA VA) ta hah
  obtain ⟨b, hbt, hbr⟩ := BitMachineInline.outputs rightLabel (fun w => (v₀, w)) Prod.snd
    (fun _ => rfl) none B (program A B b₀ v₀ w₀) (fun _ => rfl)
    (⟨some b₀, w₀, T⟩ : TM2.Cfg (fun _ : K => Bool) LB VB) tb hbh
  rw [ha] at har
  rw [hb] at hbr
  simp only [BitMachineInline.cfg] at har hbr
  refine ⟨a + 1 + b, by omega, ?_⟩
  rw [show a + 1 + b = b + (a + 1) by omega,
    Function.iterate_add_apply, Function.iterate_succ_apply', har, handoff_step]
  exact hbr

end EthInapproximability.CurrentPaper.BitMachineRawSequence
