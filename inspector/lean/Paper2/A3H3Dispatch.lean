import EthInapproximability.CurrentPaper.BitMachineInline
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-!
# Unit 3 endpoint (H_A3 closure), segment 3 (composition only): a two-way bit dispatch

Lane `owner:a-h-a3-assembly-3` (private, 26 September 2026).

The composition itself, no new machine: one administrative transition peeks the head of a flag cell
(no stack is changed) and enters the literally inlined table `P₁` (head `true`) or `P₂` (head `false`),
resetting the finite control to the chosen table's start control. Both tables are inlined with the
admitted `BitMachineInline.stmt`, exactly as in the admitted `BitMachineValidityDispatch` gate (whose reject
branch halts; here both branches continue). The whole bank survives the transition. Each run is charged
exactly one extra step.
-/

namespace Paper2.A3Assembly.Dispatch

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

variable {K L₁ L₂ V₁ V₂ : Type*} [DecidableEq K]

abbrev Label (L₁ L₂ : Type*) := Unit ⊕ (L₁ ⊕ L₂)
abbrev Control (V₁ V₂ : Type*) := Option Bool × (V₁ × V₂)

def lab₁ (l : L₁) : Label L₁ L₂ := .inr (.inl l)
def lab₂ (l : L₂) : Label L₁ L₂ := .inr (.inr l)
def emb₁ (w₂ : V₂) (v : V₁) : Control V₁ V₂ := (some true, (v, w₂))
def emb₂ (w₁ : V₁) (v : V₂) : Control V₁ V₂ := (some false, (w₁, v))

/-- The dispatch table: label `.inl ()` peeks `flag` and jumps; the two branch tables are inlined. -/
def program (flag : K) (P₁ : L₁ → TM2.Stmt (fun _ : K => Bool) L₁ V₁) (s₁ : L₁)
    (P₂ : L₂ → TM2.Stmt (fun _ : K => Bool) L₂ V₂) (s₂ : L₂) (w₁ : V₁) (w₂ : V₂) :
    Label L₁ L₂ → TM2.Stmt (fun _ : K => Bool) (Label L₁ L₂) (Control V₁ V₂)
  | .inl () => .peek flag (fun _ b => (b, (w₁, w₂)))
      (.branch (fun v => v.1 == some true) (.goto (fun _ => lab₁ s₁)) (.goto (fun _ => lab₂ s₂)))
  | .inr (.inl l) => BitMachineInline.stmt lab₁ (emb₁ w₂) (fun c => c.2.1) none (P₁ l)
  | .inr (.inr l) => BitMachineInline.stmt lab₂ (emb₂ w₁) (fun c => c.2.2) none (P₂ l)

theorem step_true (flag : K) (P₁ : L₁ → TM2.Stmt (fun _ : K => Bool) L₁ V₁) (s₁ : L₁)
    (P₂ : L₂ → TM2.Stmt (fun _ : K => Bool) L₂ V₂) (s₂ : L₂) (w₁ : V₁) (w₂ : V₂)
    (S : K → List Bool) (c₀ : Control V₁ V₂) (hf : (S flag).head? = some true) :
    advance (program flag P₁ s₁ P₂ s₂ w₁ w₂)
      (⟨some (.inl ()), c₀, S⟩ : TM2.Cfg (fun _ : K => Bool) (Label L₁ L₂) (Control V₁ V₂)) =
      ⟨some (lab₁ s₁), emb₁ w₂ w₁, S⟩ := by
  simp [advance, program, TM2.step, TM2.stepAux, hf, emb₁]

theorem step_false (flag : K) (P₁ : L₁ → TM2.Stmt (fun _ : K => Bool) L₁ V₁) (s₁ : L₁)
    (P₂ : L₂ → TM2.Stmt (fun _ : K => Bool) L₂ V₂) (s₂ : L₂) (w₁ : V₁) (w₂ : V₂)
    (S : K → List Bool) (c₀ : Control V₁ V₂) (hf : (S flag).head? = some false) :
    advance (program flag P₁ s₁ P₂ s₂ w₁ w₂)
      (⟨some (.inl ()), c₀, S⟩ : TM2.Cfg (fun _ : K => Bool) (Label L₁ L₂) (Control V₁ V₂)) =
      ⟨some (lab₂ s₂), emb₂ w₁ w₂, S⟩ := by
  simp [advance, program, TM2.step, TM2.stepAux, hf, emb₂]

/-- Head `true`: the supplied run of `P₁` from its start control, plus one charged step. -/
theorem run_true (flag : K) (P₁ : L₁ → TM2.Stmt (fun _ : K => Bool) L₁ V₁) (s₁ : L₁)
    (P₂ : L₂ → TM2.Stmt (fun _ : K => Bool) L₂ V₂) (s₂ : L₂) (w₁ : V₁) (w₂ : V₂)
    (S T : K → List Bool) (u : V₁) (c₀ : Control V₁ V₂) (t : ℕ)
    (hf : (S flag).head? = some true)
    (h : ((advance P₁)^[t]) (⟨some s₁, w₁, S⟩ : TM2.Cfg (fun _ : K => Bool) L₁ V₁) = ⟨none, u, T⟩) :
    ∃ t' ≤ t + 1, ((advance (program flag P₁ s₁ P₂ s₂ w₁ w₂))^[t'])
      (⟨some (.inl ()), c₀, S⟩ : TM2.Cfg (fun _ : K => Bool) (Label L₁ L₂) (Control V₁ V₂)) =
      ⟨none, emb₁ w₂ u, T⟩ := by
  have hh : (((advance P₁)^[t]) (⟨some s₁, w₁, S⟩ : TM2.Cfg (fun _ : K => Bool) L₁ V₁)).l = none := by
    rw [h]
  obtain ⟨n, hn, hr⟩ := BitMachineInline.outputs lab₁ (emb₁ w₂) (fun c => c.2.1) (fun _ => rfl) none
    P₁ (program flag P₁ s₁ P₂ s₂ w₁ w₂) (fun _ => rfl)
    (⟨some s₁, w₁, S⟩ : TM2.Cfg (fun _ : K => Bool) L₁ V₁) t hh
  rw [h] at hr
  simp only [BitMachineInline.cfg] at hr
  refine ⟨n + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply, step_true flag P₁ s₁ P₂ s₂ w₁ w₂ S c₀ hf]
  exact hr

/-- Head `false`: the supplied run of `P₂` from its start control, plus one charged step. -/
theorem run_false (flag : K) (P₁ : L₁ → TM2.Stmt (fun _ : K => Bool) L₁ V₁) (s₁ : L₁)
    (P₂ : L₂ → TM2.Stmt (fun _ : K => Bool) L₂ V₂) (s₂ : L₂) (w₁ : V₁) (w₂ : V₂)
    (S T : K → List Bool) (u : V₂) (c₀ : Control V₁ V₂) (t : ℕ)
    (hf : (S flag).head? = some false)
    (h : ((advance P₂)^[t]) (⟨some s₂, w₂, S⟩ : TM2.Cfg (fun _ : K => Bool) L₂ V₂) = ⟨none, u, T⟩) :
    ∃ t' ≤ t + 1, ((advance (program flag P₁ s₁ P₂ s₂ w₁ w₂))^[t'])
      (⟨some (.inl ()), c₀, S⟩ : TM2.Cfg (fun _ : K => Bool) (Label L₁ L₂) (Control V₁ V₂)) =
      ⟨none, emb₂ w₁ u, T⟩ := by
  have hh : (((advance P₂)^[t]) (⟨some s₂, w₂, S⟩ : TM2.Cfg (fun _ : K => Bool) L₂ V₂)).l = none := by
    rw [h]
  obtain ⟨n, hn, hr⟩ := BitMachineInline.outputs lab₂ (emb₂ w₁) (fun c => c.2.2) (fun _ => rfl) none
    P₂ (program flag P₁ s₁ P₂ s₂ w₁ w₂) (fun _ => rfl)
    (⟨some s₂, w₂, S⟩ : TM2.Cfg (fun _ : K => Bool) L₂ V₂) t hh
  rw [h] at hr
  simp only [BitMachineInline.cfg] at hr
  refine ⟨n + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply, step_false flag P₁ s₁ P₂ s₂ w₁ w₂ S c₀ hf]
  exact hr

/-- The decision program `D` followed (one charged handoff) by the dispatch on `flag`. -/
def seqDispatch {LD VD : Type*} (D : LD → TM2.Stmt (fun _ : K => Bool) LD VD) (vD : VD) (flag : K)
    (P₁ : L₁ → TM2.Stmt (fun _ : K => Bool) L₁ V₁) (s₁ : L₁)
    (P₂ : L₂ → TM2.Stmt (fun _ : K => Bool) L₂ V₂) (s₂ : L₂) (w₁ : V₁) (w₂ : V₂) :=
  BitMachineRawSequence.program D (program flag P₁ s₁ P₂ s₂ w₁ w₂) (.inl ()) vD (none, (w₁, w₂))

end Paper2.A3Assembly.Dispatch

#print axioms Paper2.A3Assembly.Dispatch.run_true
#print axioms Paper2.A3Assembly.Dispatch.run_false
