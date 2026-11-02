import EthInapproximability.CurrentPaper.MatrixTableInterlaceFirstRestoration

/-!
# Charged exit from the numbered-interlace checkpoint

The row-block controller deliberately exposes a nonhalting `.check`
checkpoint.  Its ordinary finish phase empties the accumulator and writes
its reversal.  This module runs that phase through the three enclosing
fixed controllers, yielding a genuine halt; a following one-pass move can
reverse the word back into a transpose source bank.
-/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceFirstFinish

open Turing BitMachineEncoding BitMachineComposition BitMachineSubroutine
open BitMachineSubroutineRenaming

open MatrixTableInterlaceFirstRestoration


def word (blocks rows cols : ℕ) (f : Fin rows → Fin cols → Bool) : List Bool :=
  MatrixMaterialization.rowMajor
    (MatrixTableInterlaceRowReverse.numberedInterlace blocks rows cols f)

def blockIn (blocks rows cols : ℕ) (f : Fin rows → Fin cols → Bool) :
    SamplerMachineBlockReverse.Config :=
  SamplerMachineBlockReverse.cfg (some .check) SamplerMachineBlockReverse.initial []
    (List.replicate (rows * cols^blocks) true) [] [] (word blocks rows cols f) []

def blockOut (blocks rows cols : ℕ) (f : Fin rows → Fin cols → Bool) :
    SamplerMachineBlockReverse.Config :=
  SamplerMachineBlockReverse.cfg none SamplerMachineBlockReverse.initial []
    (List.replicate (rows * cols^blocks) true) [] [] []
    (word blocks rows cols f).reverse

theorem block_finish (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    SamplerMachineBlockReverse.run ((word blocks rows cols f).length + 2)
      (blockIn blocks rows cols f) = blockOut blocks rows cols f := by
  let w := word blocks rows cols f
  let width := List.replicate (rows * cols^blocks) true
  have hc : SamplerMachineBlockReverse.run 1
      (SamplerMachineBlockReverse.cfg (some .check)
        SamplerMachineBlockReverse.initial [] width [] [] w []) =
      SamplerMachineBlockReverse.cfg (some .finish)
        SamplerMachineBlockReverse.initial [] width [] [] w [] := by
    rfl
  have hf := SamplerMachineBlockReverse.finish_run
    SamplerMachineBlockReverse.initial [] width [] [] w []
  change SamplerMachineBlockReverse.run (w.length+2)
    (SamplerMachineBlockReverse.cfg (some .check)
      SamplerMachineBlockReverse.initial [] width [] [] w []) =
    SamplerMachineBlockReverse.cfg none
      SamplerMachineBlockReverse.initial [] width [] [] [] w.reverse
  rw [show w.length+2 = (w.length+1)+1 by omega]
  simp only [SamplerMachineBlockReverse.run, Function.iterate_add_apply] at hc hf ⊢
  rw [hc, hf]
  simp

def bridgeIn (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) : MatrixTableInterlaceRowBridge.Config :=
  MatrixTableInterlaceRowBridge.rowFrame none (![[],[]] : Fin 2 → List Bool)
    (blockIn blocks rows cols f)

def bridgeOut (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) : MatrixTableInterlaceRowBridge.Config :=
  MatrixTableInterlaceRowBridge.rowFrame none (![[],[]] : Fin 2 → List Bool)
    (blockOut blocks rows cols f)

theorem bridge_finish (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    ∃ t ≤ (word blocks rows cols f).length+2,
      MatrixTableInterlaceRowBridge.run t (bridgeIn blocks rows cols f) =
        bridgeOut blocks rows cols f := by
  have hh : (SamplerMachineBlockReverse.run ((word blocks rows cols f).length+2)
      (blockIn blocks rows cols f)).l = none := by
    rw [block_finish]
    rfl
  obtain ⟨t,ht,he⟩ := lift_outputs_renamed MatrixTableInterlaceRowBridge.rowSlots
    (Equiv.sumComm _ _) (Equiv.prodComm _ _)
    SamplerMachineBlockReverse.program MatrixTableInterlaceRowBridge.program
    none (fun _ => rfl) none
    (![[],[]] : Fin 2 → List Bool) (blockIn blocks rows cols f)
    ((word blocks rows cols f).length+2) hh
  change MatrixTableInterlaceRowBridge.run t (bridgeIn blocks rows cols f) =
    MatrixTableInterlaceRowBridge.rowFrame none
      (![[],[]] : Fin 2 → List Bool)
      (SamplerMachineBlockReverse.run ((word blocks rows cols f).length+2)
        (blockIn blocks rows cols f)) at he
  rw [block_finish] at he
  exact ⟨t,ht,he⟩

def widthForeign (blocks rows cols : ℕ) : Fin 5 → List Bool :=
  ![List.replicate rows true, List.replicate (cols^blocks) true, [], [], []]

def widthIn (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) : MatrixTableInterlaceRowWidth.Config :=
  MatrixTableInterlaceRowWidth.rowFrame false (widthForeign blocks rows cols)
    (bridgeIn blocks rows cols f)

def widthOut (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) : MatrixTableInterlaceRowWidth.Config :=
  MatrixTableInterlaceRowWidth.rowFrame false (widthForeign blocks rows cols)
    (bridgeOut blocks rows cols f)

theorem widthIn_eq_rowEnd (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    widthIn blocks rows cols f =
      MatrixTableInterlaceFirstRestoration.rowEnd blocks rows cols f := by
  unfold widthIn MatrixTableInterlaceRowWidth.rowFrame
    bridgeIn MatrixTableInterlaceRowBridge.rowFrame
    blockIn widthForeign MatrixTableInterlaceFirstRestoration.rowEnd
  apply congrArg (fun S : MatrixTableInterlaceRowWidth.Stack → List Bool =>
    (⟨some (.inr (.inr .check)),
      (false,(none,SamplerMachineBlockReverse.initial)),S⟩ :
      MatrixTableInterlaceRowWidth.Config))
  funext k
  cases k with
  | inl i => fin_cases i <;> rfl
  | inr i => fin_cases i <;> rfl

theorem width_finish (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) :
    ∃ t ≤ (word blocks rows cols f).length+2,
      MatrixTableInterlaceRowWidth.run t (widthIn blocks rows cols f) =
        widthOut blocks rows cols f := by
  obtain ⟨u,hu,he⟩ := bridge_finish blocks rows cols f
  have hh : (MatrixTableInterlaceRowBridge.run u
      (bridgeIn blocks rows cols f)).l = none := by
    rw [he]
    rfl
  obtain ⟨t,ht,hf⟩ := lift_outputs_renamed
    MatrixTableInterlaceRowWidth.rowSlots
    (Equiv.sumComm _ _) (Equiv.prodComm _ _)
    MatrixTableInterlaceRowBridge.program MatrixTableInterlaceRowWidth.program
    none (fun _ => rfl) false (widthForeign blocks rows cols)
    (bridgeIn blocks rows cols f) u hh
  change MatrixTableInterlaceRowWidth.run t (widthIn blocks rows cols f) =
    MatrixTableInterlaceRowWidth.rowFrame false (widthForeign blocks rows cols)
      (MatrixTableInterlaceRowBridge.run u (bridgeIn blocks rows cols f)) at hf
  rw [he] at hf
  exact ⟨t,ht.trans hu,hf⟩

def finalIn (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    MatrixTableInterlaceFirstRestoration.Config :=
  MatrixTableInterlaceFirstRestoration.rowFrame
    (MatrixTableInterlaceSize.initial,v)
    (fun k => MatrixTableInterlaceFirstRestoration.afterBank
      blocks rows cols f v (.inl k))
    (widthIn blocks rows cols f)

def finalOut (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    MatrixTableInterlaceFirstRestoration.Config :=
  MatrixTableInterlaceFirstRestoration.rowFrame
    (MatrixTableInterlaceSize.initial,v)
    (fun k => MatrixTableInterlaceFirstRestoration.afterBank
      blocks rows cols f v (.inl k))
    (widthOut blocks rows cols f)

theorem first_finish (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    ∃ t ≤ (word blocks rows cols f).length+2,
      MatrixTableInterlaceFirstRestoration.run t
        (finalIn blocks rows cols f v) =
          finalOut blocks rows cols f v := by
  obtain ⟨u,hu,he⟩ := width_finish blocks rows cols f
  have hh : (MatrixTableInterlaceRowWidth.run u
      (widthIn blocks rows cols f)).l = none := by
    rw [he]
    rfl
  obtain ⟨t,ht,hf⟩ := lift_outputs_renamed
    (Equiv.sumComm MatrixTableInterlaceRowWidth.Stack
      MatrixTableInterlaceCombined.Stack)
    MatrixTableInterlaceFirstRestoration.rowLabels
    MatrixTableInterlaceFirstRestoration.rowControl
    MatrixTableInterlaceRowWidth.program
    MatrixTableInterlaceFirstRestoration.program
    none (fun _ => rfl) ((MatrixTableInterlaceSize.initial,v),none)
    (fun k => MatrixTableInterlaceFirstRestoration.afterBank
      blocks rows cols f v (.inl k))
    (widthIn blocks rows cols f) u hh
  change MatrixTableInterlaceFirstRestoration.run t
      (finalIn blocks rows cols f v) =
    MatrixTableInterlaceFirstRestoration.rowFrame
      (MatrixTableInterlaceSize.initial,v)
      (fun k => MatrixTableInterlaceFirstRestoration.afterBank
        blocks rows cols f v (.inl k))
      (MatrixTableInterlaceRowWidth.run u (widthIn blocks rows cols f)) at hf
  rw [he] at hf
  exact ⟨t,ht.trans hu,hf⟩

theorem finalOut_halts (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    (finalOut blocks rows cols f v).l = none := by
  rfl

def numberedBound (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool) : ℕ :=
  MatrixTableInterlaceCombined.totalBound blocks rows cols
      (MatrixMaterialization.rowMajor f).length +
    ((rows+1)+((cols^blocks)+1)+
      ((MatrixMaterialization.rowMajor
        (MatrixTableInterlace.interlaced (blocks := blocks) f)).length+1)+
      ((MatrixMaterialization.rowMajor
        (MatrixTableInterlace.interlaced (blocks := blocks) f)).length+1)) +
    (MatrixAddressMachine.exactTime rows (cols^blocks) 0 +
      (2*(MatrixMaterialization.rowMajor
        (MatrixTableInterlace.interlaced (blocks := blocks) f)).length+2 +
        blocks*SamplerMachineBlockReverse.blockStep (rows*(cols^blocks))))

theorem first_interlace_halted_run (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (hwidth : 0 < rows*(cols^blocks)) :
    ∃ t ≤ numberedBound blocks rows cols f +
      (word blocks rows cols f).length+2,
      ∃ v : MatrixTableInterlaceCombined.WControl,
        MatrixTableInterlaceFirstRestoration.run t
          (MatrixTableInterlaceFirstRestoration.combinedFrame
            (false,(none,SamplerMachineBlockReverse.initial))
            MatrixTableInterlaceFirstRestoration.emptyRowBank
            (MatrixTableInterlaceCombined.bridgeCfg
              MatrixTableInterlaceCombined.start blocks rows cols
              (MatrixMaterialization.rowMajor f) [] [] [] [] [])) =
        finalOut blocks rows cols f v := by
  obtain ⟨t₁,ht₁,v,h₁⟩ :=
    MatrixTableInterlaceFirstRestoration.first_interlace_numbered_run
      blocks rows cols f hwidth
  change t₁ ≤ numberedBound blocks rows cols f at ht₁
  rw [← widthIn_eq_rowEnd] at h₁
  change MatrixTableInterlaceFirstRestoration.run t₁ _ =
    finalIn blocks rows cols f v at h₁
  obtain ⟨t₂,ht₂,h₂⟩ := first_finish blocks rows cols f v
  have hsum : MatrixTableInterlaceFirstRestoration.run (t₁+t₂)
      (MatrixTableInterlaceFirstRestoration.combinedFrame
        (false,(none,SamplerMachineBlockReverse.initial))
        MatrixTableInterlaceFirstRestoration.emptyRowBank
        (MatrixTableInterlaceCombined.bridgeCfg
          MatrixTableInterlaceCombined.start blocks rows cols
          (MatrixMaterialization.rowMajor f) [] [] [] [] [])) =
      finalOut blocks rows cols f v := by
    rw [Nat.add_comm t₁ t₂]
    simp only [MatrixTableInterlaceFirstRestoration.run,
      Function.iterate_add_apply] at h₁ h₂ ⊢
    rw [h₁, h₂]
  exact ⟨t₁+t₂, by omega, v, hsum⟩

theorem finalOut_reversed_word (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    (finalOut blocks rows cols f v).stk (.inr (.inr 6)) =
      (word blocks rows cols f).reverse := by
  rfl

theorem finalOut_rowCount (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    (finalOut blocks rows cols f v).stk
      (.inl (.inr (.inr MatrixTableWriter.Extra.rows))) =
      List.replicate (blocks*rows) true := by
  rfl

theorem finalOut_colCount (blocks rows cols : ℕ)
    (f : Fin rows → Fin cols → Bool)
    (v : MatrixTableInterlaceCombined.WControl) :
    (finalOut blocks rows cols f v).stk (.inr (.inl 1)) =
      List.replicate (cols^blocks) true := by
  rfl

end EthInapproximability.CurrentPaper.MatrixTableInterlaceFirstFinish
