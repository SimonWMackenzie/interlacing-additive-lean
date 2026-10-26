import CurrentAdditive.GaussPacketSerialize
import CurrentAdditive.GaussTypedIntegratedGetter

/-!
The checked nested getter runs inside a larger fixed 32-stack controller.
Ten banks outside its image can retain operand and cursor backups across a
getter call.  The theorem charges every getter step via the inherited stack
embedding; preparing a fresh row/column request between calls remains a
separate physical stage.
-/

namespace CurrentAdditive.GaussGetterLift32

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 32
abbrev Label := CurrentAdditive.GaussGetterIntegrated.Label
abbrev Control := CurrentAdditive.GaussGetterIntegrated.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def slot : Fin 22 ↪ Stack where
  toFun j := ⟨j.val, by omega⟩
  inj' := by
    intro a b h
    exact Fin.ext (by simpa using congrArg (fun z : Stack => z.val) h)

def program (l : Label) : TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineStackEmbedding.stmt slot id id id none
    (CurrentAdditive.GaussGetterIntegrated.program l)

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

noncomputable def frame (foreign : Stack → List Bool)
    (c : CurrentAdditive.GaussGetterIntegrated.Config) : Config :=
  BitMachineStackEmbedding.cfg slot foreign id id none c

theorem lifted_run (foreign : Stack → List Bool)
    (c : CurrentAdditive.GaussGetterIntegrated.Config) (t : Nat)
    (hhalt : (CurrentAdditive.GaussGetterIntegrated.run t c).l = none) :
    ∃ u ≤ t, run u (frame foreign c) =
      frame foreign (CurrentAdditive.GaussGetterIntegrated.run t c) := by
  simpa only [run, CurrentAdditive.GaussGetterIntegrated.run, frame] using
    BitMachineStackEmbedding.outputs slot foreign id id id
      (by intro v; rfl) none
      CurrentAdditive.GaussGetterIntegrated.program program
      (by intro l; rfl) c t hhalt

theorem frame_inner (foreign : Stack → List Bool)
    (c : CurrentAdditive.GaussGetterIntegrated.Config) (j : Fin 22) :
    (frame foreign c).stk (slot j) = c.stk j := by
  simp only [frame, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  exact BitMachineStackEmbedding.bank_at slot foreign c.stk j

theorem frame_backup (foreign : Stack → List Bool)
    (c : CurrentAdditive.GaussGetterIntegrated.Config)
    (j : Stack) (hj : 22 ≤ j.val) :
    (frame foreign c).stk j = foreign j := by
  simp only [frame, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨i, hi⟩
  have he : i.val = j.val := by
    simpa [slot] using congrArg (fun z : Stack => z.val) hi
  have := i.isLt
  omega

theorem typed_getter_with_backups {m k : Nat}
    (B : Fin m → Fin k → ℚ) (i : Fin m) (j : Fin k)
    (foreign : Stack → List Bool) :
    let init := CurrentAdditive.GaussGetterIntegrated.firstFrame
      (CurrentAdditive.GaussNestedGetter.firstFrame
        (CurrentAdditive.GaussNestedGetter.inputForeign j.val)
        (CurrentAdditive.CylinderContextScanStep.initial
          (CurrentAdditive.GaussPhysical.encodeTypedMatrix B) i.val))
    ∃ t ≤ 140 * ((CurrentAdditive.GaussPhysical.encodeTypedMatrix B).length + 1)^3,
      (run t (frame foreign init)).l = none ∧
      (run t (frame foreign init)).stk 6 =
        CurrentAdditive.CodeDCodec.encodeRawRat
          (CurrentAdditive.GaussPhysical.rawOfRat (B i j)) ∧
      (run t (frame foreign init)).stk 8 =
        CurrentAdditive.GaussPhysical.encodeTypedMatrix B ∧
      (∀ q : Stack, 22 ≤ q.val →
        (run t (frame foreign init)).stk q = foreign q) := by
  dsimp only
  obtain ⟨t, ht, hh, h6, _, h8⟩ :=
    CurrentAdditive.GaussTypedIntegratedGetter.typed_getter_bank6 B i j
  obtain ⟨u, hu, hr⟩ := lifted_run foreign _ t hh
  refine ⟨u, hu.trans ht, ?_, ?_, ?_, ?_⟩
  · rw [hr]
    simp [frame, BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hh]
  · rw [hr]
    change (frame foreign _).stk (slot (6 : Fin 22)) = _
    rw [frame_inner]
    exact h6
  · rw [hr]
    change (frame foreign _).stk (slot (8 : Fin 22)) = _
    rw [frame_inner]
    exact h8
  · intro q hq
    rw [hr]
    exact frame_backup foreign _ q hq

#print axioms lifted_run
#print axioms typed_getter_with_backups

end CurrentAdditive.GaussGetterLift32
