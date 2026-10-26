import Paper2.YaoMaterializationTape
import EthInapproximability.CurrentPaper.MatrixWordSliceTotal
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming
import EthInapproximability.CurrentPaper.MatrixReadAt

/-! Physical, source-preserving extraction of a contiguous field from the
actual Yao flat tape. Unary offset/width framing is supplied as input data;
the finite program copies that entire framed input before consuming it. -/

namespace Paper2.YaoPreservedFlatSlice

open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming
open EthInapproximability.CurrentPaper.BitMachineSubroutine
open EthInapproximability.CurrentPaper.BitMachineComposition
open Paper2.YaoLowerBound.Materialization
open Paper2.YaoLowerBound

abbrev Label := BitMachineCopy.Label ⊕ MatrixMaterialization.WordSlice.Label
abbrev Control := Option Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 6 => Bool) Label Control

def copyBank : Fin 3 ⊕ Fin 3 ≃ Fin 6 := finSumFinEquiv

private def slicePerm : Fin 6 ≃ Fin 6 where
  toFun i := ![1, 3, 4, 5, 0, 2] i
  invFun i := ![4, 0, 5, 1, 2, 3] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def sliceBank : Fin 4 ⊕ Fin 2 ≃ Fin 6 := finSumFinEquiv.trans slicePerm

def program : Label → TM2.Stmt (fun _ : Fin 6 => Bool) Label Control
  | .inl l => renameStmt copyBank (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some .countOffset) (BitMachineCopy.program l))
  | .inr l => renameStmt sliceBank (Equiv.sumComm _ _) (Equiv.prodComm _ _)
      (liftStmt none (MatrixMaterialization.WordSlice.program l))

def cfg (l : Option Label) (s : Control)
    (original working copyScratch offset width saved : List Bool) : Config :=
  ⟨l, s, ![original, working, copyScratch, offset, width, saved]⟩

def initial (framed : List Bool) : Config :=
  cfg (some (.inl .scan)) (none, none) framed [] [] [] [] []

def run (n : ℕ) (c : Config) : Config := ((advance program)^[n]) c

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem copy_input (framed : List Bool) :
    renameCfg copyBank (Equiv.refl _) (Equiv.refl _)
      (liftCfg (some .countOffset) none
        (fun _ : Fin 3 => [])
        (BitMachineCopy.cfg (some .scan) none framed [] [])) =
      initial framed := by
  apply congrArg (fun S => (⟨some (.inl .scan), (none, none), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem copy_output (framed : List Bool) :
    renameCfg copyBank (Equiv.refl _) (Equiv.refl _)
      (liftCfg (some .countOffset) none
        (fun _ : Fin 3 => [])
        (BitMachineCopy.cfg none none framed framed [])) =
      cfg (some (.inr .countOffset)) (none, none) framed framed [] [] [] [] := by
  apply congrArg (fun S => (⟨some (.inr .countOffset), (none, none), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem slice_input (framed : List Bool) :
    renameCfg sliceBank (Equiv.sumComm _ _) (Equiv.prodComm _ _)
      (liftCfg none none (fun k : Fin 2 => if k = 0 then framed else [])
        (MatrixMaterialization.WordSlice.cfg (some .countOffset) none framed [] [] [])) =
      cfg (some (.inr .countOffset)) (none, none) framed framed [] [] [] [] := by
  apply congrArg (fun S => (⟨some (.inr .countOffset), (none, none), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem slice_output (framed output : List Bool) :
    renameCfg sliceBank (Equiv.sumComm _ _) (Equiv.prodComm _ _)
      (liftCfg none none (fun k : Fin 2 => if k = 0 then framed else [])
        (MatrixMaterialization.WordSlice.cfg none none output [] [] [])) =
      cfg none (none, none) framed output [] [] [] [] := by
  apply congrArg (fun S => (⟨none, (none, none), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

/-- The fixed six-stack controller physically copies and then slices the
framed input. Original source and all work-bank states are exact. -/
theorem preserved_slice (offset width : ℕ) (flat : List Bool) :
    ∃ steps ≤ 2 * (MatrixMaterialization.WordSlice.encodeInput offset width flat).length + 2 +
        MatrixMaterialization.WordSlice.exactTime offset width flat,
      run steps (initial (MatrixMaterialization.WordSlice.encodeInput offset width flat)) =
        cfg none (none, none)
          (MatrixMaterialization.WordSlice.encodeInput offset width flat)
          (MatrixMaterialization.WordSlice.padded width (flat.drop offset)) [] [] [] [] := by
  let framed := MatrixMaterialization.WordSlice.encodeInput offset width flat
  have hc := BitMachineCopy.run_correct none framed []
  simp only [BitMachineCopy.run, List.append_nil] at hc
  have hch : (((advance BitMachineCopy.program)^[2 * framed.length + 2])
      (BitMachineCopy.cfg (some .scan) none framed [] [])).l = none := by
    rw [hc]; rfl
  obtain ⟨tc, htc, hrc⟩ := lift_outputs_renamed copyBank (Equiv.refl _) (Equiv.refl _)
    BitMachineCopy.program program (some .countOffset) (fun _ => rfl)
    none (fun _ : Fin 3 => [])
    (BitMachineCopy.cfg (some .scan) none framed [] []) (2 * framed.length + 2) hch
  rw [hc, copy_input, copy_output] at hrc
  have hs := MatrixMaterialization.WordSlice.run_correct offset width flat
  change ((advance MatrixMaterialization.WordSlice.program)^[
      MatrixMaterialization.WordSlice.exactTime offset width flat])
      (MatrixMaterialization.WordSlice.cfg (some .countOffset) none framed [] [] []) =
    MatrixMaterialization.WordSlice.cfg none none
      (MatrixMaterialization.WordSlice.padded width (flat.drop offset)) [] [] [] at hs
  have hsh : (((advance MatrixMaterialization.WordSlice.program)^[
      MatrixMaterialization.WordSlice.exactTime offset width flat])
      (MatrixMaterialization.WordSlice.cfg (some .countOffset) none framed [] [] [])).l = none := by
    rw [hs]; rfl
  obtain ⟨ts, hts, hrs⟩ := lift_outputs_renamed sliceBank (Equiv.sumComm _ _)
    (Equiv.prodComm _ _) MatrixMaterialization.WordSlice.program program none
    (fun _ => rfl) none (fun k : Fin 2 => if k = 0 then framed else [])
    (MatrixMaterialization.WordSlice.cfg (some .countOffset) none framed [] [] [])
    (MatrixMaterialization.WordSlice.exactTime offset width flat) hsh
  rw [hs, slice_input, slice_output] at hrs
  refine ⟨tc + ts, ?_, ?_⟩
  · dsimp [framed] at htc
    omega
  · exact (run_add hrc ts).trans hrs

theorem preserved_slice_linear (offset width : ℕ) (flat : List Bool) :
    ∃ steps ≤ 5 * (MatrixMaterialization.WordSlice.encodeInput offset width flat).length + 2,
      run steps (initial (MatrixMaterialization.WordSlice.encodeInput offset width flat)) =
        cfg none (none, none)
          (MatrixMaterialization.WordSlice.encodeInput offset width flat)
          (MatrixMaterialization.WordSlice.padded width (flat.drop offset)) [] [] [] [] := by
  obtain ⟨steps, ht, hr⟩ := preserved_slice offset width flat
  refine ⟨steps, ?_, hr⟩
  have hs := MatrixMaterialization.WordSlice.exactTime_le offset width flat
  omega

/-- The first bit of one selector word in the actual serialized tape. -/
def selectorOffset (t b lambda : ℕ)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1))) : ℕ :=
  (z.val * 2 ^ (t - 1) + g.val) * b

theorem selector_slice_eq (t b lambda : ℕ)
    (bits : SerializedTape t b lambda)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1))) :
    MatrixMaterialization.WordSlice.padded b
      (bits.val.drop (selectorOffset t b lambda z g)) =
      List.ofFn (fun k : Fin b => readTape t b lambda bits (.inl (z, g, k))) := by
  rw [MatrixMaterialization.WordSlice.padded_eq_ofFn]
  congr 1
  funext k
  rw [readTape_selector]
  have hk : (z.val * 2 ^ (t - 1) + g.val) * b + k.val < bits.val.length := by
    rw [bits.property]
    exact selector_offset_lt t b lambda z g k
  simp only [selectorOffset, List.getElem?_drop]
  rw [List.getElem?_eq_getElem hk]
  rfl

/-- One complete selector bit block is physically extracted from the *real*
flat Yao tape, while the whole framed input (including that tape) is
preserved. Its supplied unary offset is proved to be the true layout
coordinate. The block remains little-endian, as in the source tape. -/
theorem physical_selector_block (t b lambda : ℕ)
    (bits : SerializedTape t b lambda)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1))) :
    ∃ steps ≤
      2 * (MatrixMaterialization.WordSlice.encodeInput
          (selectorOffset t b lambda z g) b bits.val).length + 2 +
        MatrixMaterialization.WordSlice.exactTime
          (selectorOffset t b lambda z g) b bits.val,
      run steps (initial (MatrixMaterialization.WordSlice.encodeInput
        (selectorOffset t b lambda z g) b bits.val)) =
        cfg none (none, none)
          (MatrixMaterialization.WordSlice.encodeInput
            (selectorOffset t b lambda z g) b bits.val)
          (List.ofFn (fun k : Fin b => readTape t b lambda bits (.inl (z, g, k))))
          [] [] [] [] := by
  obtain ⟨steps, ht, hr⟩ := preserved_slice
    (selectorOffset t b lambda z g) b bits.val
  refine ⟨steps, ht, ?_⟩
  simpa only [selector_slice_eq] using hr

/-- The flat offset of one payload bit. Fixed-position payload slices are
strided by `K+1`, so they are not contiguous blocks of the serialized tape. -/
def payloadOffset (t b lambda : ℕ)
    (l : Fin (payloadCount t b lambda))
    (h : Fin (2 ^ b)) (j : Fin (2 ^ t * 2 ^ t + 1)) : ℕ :=
  selectorCount t b lambda * 2 ^ (t - 1) * b +
    (l.val * 2 ^ b + h.val) * (2 ^ t * 2 ^ t + 1) + j.val

/-- One actual payload cell is read by a fixed seven-stack program. Both
the unary offset and the *whole* literal flat tape are preserved, while
all working banks are cleared and the exact Yao bit is pushed on output. -/
theorem physical_payload_cell (t b lambda : ℕ)
    (bits : SerializedTape t b lambda)
    (l : Fin (payloadCount t b lambda))
    (h : Fin (2 ^ b)) (j : Fin (2 ^ t * 2 ^ t + 1)) (out : List Bool) :
    ∃ steps ≤ 3 * payloadOffset t b lambda l h j +
        3 * bits.val.length + 8,
      MatrixReadAt.run steps
        (MatrixReadAt.initial
          (List.replicate (payloadOffset t b lambda l h j) true) bits.val out) =
        MatrixReadAt.cfg none
          (none, none, (false, false), (false, false))
          (List.replicate (payloadOffset t b lambda l h j) true) [] bits.val []
          (readTape t b lambda bits (.inr (l, h, j)) :: out) := by
  obtain ⟨steps, ht, hr⟩ := MatrixReadAt.readAt_run
    (payloadOffset t b lambda l h j) bits.val out
  refine ⟨steps, ht, ?_⟩
  have hk : payloadOffset t b lambda l h j < bits.val.length := by
    rw [bits.property]
    exact payload_offset_lt t b lambda l h j
  have hv : bits.val[payloadOffset t b lambda l h j]?.getD false =
      readTape t b lambda bits (.inr (l, h, j)) := by
    rw [readTape_payload]
    change bits.val[payloadOffset t b lambda l h j]?.getD false =
      bits.val[payloadOffset t b lambda l h j]
    rw [List.getElem?_eq_getElem hk]
    rfl
  simpa only [hv] using hr

/-- The big-endian word expected by the physical decoder has exactly the
opposite bit order from the contiguous little-endian tape block. This is
an equality of encodings, not a physical reversal certificate. -/
theorem reversed_selector_value (t b lambda : ℕ)
    (bits : SerializedTape t b lambda)
    (z : Fin (selectorCount t b lambda)) (g : Fin (2 ^ (t - 1))) :
    MatrixBinaryAddress.valueFrom 0
      (List.ofFn (fun i : Fin b => readTape t b lambda bits (.inl (z, g, i.rev)))) =
      (Paper2.CappedSampler.bitsTicketEquiv b
        (fun i => readTape t b lambda bits (.inl (z, g, i)))).val := by
  rw [MatrixBinaryAddress.valueFrom_ofFn, Paper2.CappedSampler.bitsTicketEquiv_value]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.rev_rev]
  cases readTape t b lambda bits (.inl (z, g, i)) <;> rfl

#print axioms preserved_slice
#print axioms preserved_slice_linear
#print axioms selector_slice_eq
#print axioms physical_selector_block
#print axioms physical_payload_cell
#print axioms reversed_selector_value

end Paper2.YaoPreservedFlatSlice
