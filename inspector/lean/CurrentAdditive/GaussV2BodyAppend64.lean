import CurrentAdditive.CodeDAppendAtEnd15
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! Embed the checked source-preserving append-at-end controller into Fin64.
The payload must already be a counted-V2 item: `natField raw.length ++ raw`.
The controller itself only concatenates bank 5 after the body on bank 9. -/

namespace CurrentAdditive.GaussV2BodyAppend64

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 64
abbrev Label := CurrentAdditive.CodeDAppendAtEnd15.Label
abbrev Control := CurrentAdditive.CodeDAppendAtEnd15.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def slot : Fin 15 ↪ Stack where
  toFun i := ⟨i.val, by omega⟩
  inj' := by intro i j h; exact Fin.ext (Fin.mk.inj h)

def program (l : Label) : TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineStackEmbedding.stmt slot id id id none
    (CurrentAdditive.CodeDAppendAtEnd15.program l)

def run (t : Nat) (cfg : Config) : Config := ((advance program)^[t]) cfg

def restrict (S : Stack → List Bool) : Fin 15 → List Bool :=
  fun j => S (slot j)

noncomputable def frame (S : Stack → List Bool)
    (cfg : CurrentAdditive.CodeDAppendAtEnd15.Config) : Config :=
  BitMachineStackEmbedding.cfg slot S id id none cfg

theorem frame_initial (S : Stack → List Bool) :
    frame S ⟨some .saveScan, ((), none), restrict S⟩ =
      ⟨some .saveScan, ((), none), S⟩ := by
  unfold frame
  simp only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  congr 1
  exact BitMachineStackEmbedding.bank_restrict slot S

theorem append (S : Stack → List Bool)
    (body payload : List Bool)
    (hbody : S 9 = body) (hpay : S 5 = payload)
    (h11 : S 11 = []) (h14 : S 14 = []) :
    ∃ t ≤ 4 * body.length + 2 * payload.length + 7,
      (run t ⟨some .saveScan, ((), none), S⟩).l = none ∧
      (run t ⟨some .saveScan, ((), none), S⟩).stk 9 =
        body ++ payload ∧
      (run t ⟨some .saveScan, ((), none), S⟩).stk 5 = [] ∧
      (run t ⟨some .saveScan, ((), none), S⟩).stk 8 = S 8 ∧
      (∀ j : Stack, j ≠ 5 → j ≠ 9 → j ≠ 11 → j ≠ 14 →
        (run t ⟨some .saveScan, ((), none), S⟩).stk j = S j) := by
  let F := restrict S
  have hF9 : F 9 = body := hbody
  have hF5 : F 5 = payload := hpay
  have hF11 : F 11 = [] := h11
  have hF14 : F 14 = [] := h14
  have hF : CurrentAdditive.CodeDAppendAtEnd15.initialBank F body payload = F := by
    funext j
    fin_cases j <;> simp [CurrentAdditive.CodeDAppendAtEnd15.initialBank,
      hF9, hF5]
  have hlocal := CurrentAdditive.CodeDAppendAtEnd15.append_run
    F body payload hF11 hF14
  rw [hF] at hlocal
  have hhalt :
      (CurrentAdditive.CodeDAppendAtEnd15.run
        (4 * body.length + 2 * payload.length + 7)
        ⟨some .saveScan, ((), none), F⟩).l = none := by
    rw [show 4 * body.length + 2 * payload.length + 7 =
      (4 * body.length + 2 * payload.length + 6) + 1 by omega,
      CurrentAdditive.CodeDAppendAtEnd15.run,
      Function.iterate_succ_apply']
    change ((advance CurrentAdditive.CodeDAppendAtEnd15.program)
      (CurrentAdditive.CodeDAppendAtEnd15.run
        (4 * body.length + 2 * payload.length + 6)
        ⟨some .saveScan, ((), none), F⟩)).l = none
    rw [hlocal]
    rfl
  let cfg : CurrentAdditive.CodeDAppendAtEnd15.Config :=
    ⟨some .saveScan, ((), none), F⟩
  obtain ⟨t, ht, hEmbed⟩ := BitMachineStackEmbedding.outputs
    slot S id id id (by intro v; rfl) none
    CurrentAdditive.CodeDAppendAtEnd15.program program
    (by intro l; rfl) cfg
    (4 * body.length + 2 * payload.length + 7) hhalt
  have hlocalFull : CurrentAdditive.CodeDAppendAtEnd15.run
      (4 * body.length + 2 * payload.length + 7) cfg =
      ⟨none, ((), none),
        Function.update
          (Function.update
            (Function.update F 9 []) 5 []) 9
            (body ++ payload)⟩ := by
    rw [show 4 * body.length + 2 * payload.length + 7 =
      (4 * body.length + 2 * payload.length + 6) + 1 by omega,
      CurrentAdditive.CodeDAppendAtEnd15.run,
      Function.iterate_succ_apply']
    change advance CurrentAdditive.CodeDAppendAtEnd15.program
      (CurrentAdditive.CodeDAppendAtEnd15.run
        (4 * body.length + 2 * payload.length + 6) cfg) = _
    rw [hlocal]
    rfl
  have hFull : run t ⟨some .saveScan, ((), none), S⟩ =
      frame S (CurrentAdditive.CodeDAppendAtEnd15.run
        (4 * body.length + 2 * payload.length + 7) cfg) := by
    rw [← frame_initial S]
    simpa [run, frame, cfg] using hEmbed
  rw [hlocalFull] at hFull
  refine ⟨t, ht, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hFull]
    rfl
  · rw [hFull]
    change (BitMachineStackEmbedding.bank slot S _) (slot 9) = _
    rw [BitMachineStackEmbedding.bank_at]
    simp [BitMachineInline.cfg, Function.update]
  · rw [hFull]
    change (BitMachineStackEmbedding.bank slot S _) (slot 5) = _
    rw [BitMachineStackEmbedding.bank_at]
    simp [BitMachineInline.cfg, Function.update]
  · rw [hFull]
    change (BitMachineStackEmbedding.bank slot S _) (slot 8) = _
    rw [BitMachineStackEmbedding.bank_at]
    simp only [BitMachineInline.cfg]
    change F 8 = S 8
    rfl
  · intro j hj5 hj9 hj11 hj14
    rw [hFull]
    by_cases hjLow : j.val < 15
    · let i : Fin 15 := ⟨j.val, hjLow⟩
      have hslot : slot i = j := Fin.ext rfl
      rw [← hslot]
      change (BitMachineStackEmbedding.bank slot S _) (slot i) = _
      rw [BitMachineStackEmbedding.bank_at]
      simp only [BitMachineInline.cfg]
      have hi5 : i ≠ (5 : Fin 15) := by
        intro e
        apply hj5
        rw [← hslot, e]
        rfl
      have hi9 : i ≠ (9 : Fin 15) := by
        intro e
        apply hj9
        rw [← hslot, e]
        rfl
      rw [Function.update_of_ne hi9,
        Function.update_of_ne hi5,
        Function.update_of_ne hi9]
      change S (slot i) = S (slot i)
      rfl
    · apply BitMachineStackEmbedding.bank_outside
      rintro ⟨i, hi⟩
      have hv := congrArg Fin.val hi
      have hv' : (slot i).val < 15 := i.isLt
      omega

#print axioms append

end CurrentAdditive.GaussV2BodyAppend64
