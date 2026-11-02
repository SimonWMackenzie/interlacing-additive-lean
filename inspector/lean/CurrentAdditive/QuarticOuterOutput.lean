import CurrentAdditive.QuarticCutOutputCopies
import Paper2.ClearAll
import EthInapproximability.CurrentPaper.U4PostFrame

/-! A separate three-cell output area followed by the v27 front/cutter work
bank.  Clearing the work suffix makes the serialized bank exactly the desired
three-field packet followed by fixed blank bits. -/

namespace Paper2.CurrentAdditive.QuarticOuterOutput

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2 Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticFrontLift
open Paper2.CurrentAdditive.QuarticCutOutputCopies

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

abbrev J := Fin ((Lift.a FS + 3) + 3)

def inC : K ↪ J :=
  ⟨fun x => ⟨x.val + 3, by have := x.isLt; omega⟩, by
    intro x y h
    exact Fin.ext (by have := congrArg Fin.val h; simp only at this; omega)⟩

def outC (i : Fin 3) : J := ⟨i.val, by have := i.isLt; omega⟩
def srcC (i : Fin 3) : J := inC (QuarticCutOutputCopies.srcC i)
def scratchC : J := inC QuarticCutOutputCopies.scratchC

def outerBank (S : K → List Bool) : J → List Bool :=
  fun j => if h : j.val < 3 then [] else S ⟨j.val - 3, by have := j.isLt; omega⟩

theorem outer_at (S : K → List Bool) (x : K) : outerBank S (inC x) = S x := by
  simp [outerBank, inC]

theorem outer_out_blank (S : K → List Bool) (i : Fin 3) :
    outerBank S (outC i) = [] := by
  simp [outerBank, outC, i.isLt]

theorem outer_pull (T S : K → List Bool) :
    bank inC (outerBank T) S = outerBank S := by
  funext j
  by_cases hj : j.val < 3
  · rw [bank_outside]
    · simp only [outerBank, dif_pos hj]
    · rintro ⟨x, hx⟩
      have hv := congrArg Fin.val hx
      change x.val + 3 = j.val at hv
      omega
  · let x : K := ⟨j.val - 3, by have := j.isLt; omega⟩
    have he : inC x = j := Fin.ext (by simp [inC, x]; omega)
    rw [← he, bank_at, outer_at]

theorem outer_start (P : Fin 3 → List Bool) :
    outerBank (Wrap.widen (Lift.a FS) P) =
      Wrap.widen (Lift.a FS + 3) P := by
  funext j
  by_cases hA : Lift.a FS + 3 ≤ j.val
  · have h3 : ¬ j.val < 3 := by omega
    have ha : Lift.a FS ≤ j.val - 3 := by omega
    simp only [outerBank, Wrap.widen, dif_neg h3, dif_pos ha, dif_pos hA]
    have hi : (⟨j.val - 3 - Lift.a FS, by omega⟩ : Fin 3) =
        (⟨j.val - (Lift.a FS + 3), by omega⟩ : Fin 3) := by
      apply Fin.ext
      change j.val - 3 - Lift.a FS = j.val - (Lift.a FS + 3)
      omega
    exact congrArg P hi
  · by_cases h3 : j.val < 3
    · simp only [outerBank, Wrap.widen, dif_pos h3, dif_neg hA]
    · have ha : ¬ Lift.a FS ≤ j.val - 3 := by omega
      simp only [outerBank, Wrap.widen, dif_neg h3, dif_neg ha, dif_neg hA]

def copies (i : Fin 3) : Fin 3 ↪ J :=
  ⟨![srcC i, outC i, scratchC], by
    intro x y h
    fin_cases x <;> fin_cases y
    · rfl
    · have hv := congrArg Fin.val h; simp [srcC, inC, outC] at hv; omega
    · exact False.elim (QuarticCutOutputCopies.src_ne_scratch i
        (inC.injective (by simpa [srcC, scratchC] using h)))
    · have hv := congrArg Fin.val h; simp [srcC, inC, outC] at hv; omega
    · rfl
    · have hv := congrArg Fin.val h; simp [scratchC, inC, outC] at hv; omega
    · exact False.elim (QuarticCutOutputCopies.src_ne_scratch i
        (inC.injective (by simpa [srcC, scratchC] using h.symm)))
    · have hv := congrArg Fin.val h; simp [scratchC, inC, outC] at hv; omega
    · rfl⟩

theorem src_ne_dst (i j : Fin 3) : copies i 0 ≠ copies j 1 := by
  intro h
  have hv := congrArg Fin.val h
  simp [copies, srcC, inC, outC] at hv
  omega

theorem scratch_ne_dst (i j : Fin 3) : copies i 2 ≠ copies j 1 := by
  intro h
  have hv := congrArg Fin.val h
  simp [copies, scratchC, inC, outC] at hv
  omega

theorem dst_injective (i j : Fin 3)
    (h : copies i 1 = copies j 1) : i = j := by
  exact Fin.ext (by have hv := congrArg Fin.val h; simpa [copies, outC] using hv)

theorem copy_run (S : K → List Bool)
    (hScratch : S QuarticCutOutputCopies.scratchC = []) :
    ∃ t ≤ 3 * (2 * (BitMachineBankCodec.encode (outerBank S)).length + 3) + 1,
      ∃ v,
      ((advance (CopyAll.prog copies))^[t])
        (⟨some (.inl ⟨0, by omega⟩), none, outerBank S⟩ :
          TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, v, CopyAll.done copies 3 (outerBank S)⟩ := by
  apply CopyAll.all_run copies src_ne_dst scratch_ne_dst dst_injective
    (outerBank S) (fun _ => by simpa [copies, scratchC, outer_at] using hScratch)
    (BitMachineBankCodec.encode (outerBank S)).length
    (fun i => BitMachineBankCodec.word_length_le_encode (outerBank S) (srcC i)) none

def clearCells (i : Fin (Lift.a FS + 3)) : J := inC i

theorem clearCells_inj : Function.Injective clearCells := inC.injective

def outputBank (Y : Fin 3 → List Bool) : J → List Bool :=
  fun j => if h : j.val < 3 then Y ⟨j.val, h⟩ else []

theorem copied_out (S : K → List Bool) (Y : Fin 3 → List Bool)
    (hSrc : ∀ i : Fin 3, S (QuarticCutOutputCopies.srcC i) = Y i)
    (i : Fin 3) :
    CopyAll.done copies 3 (outerBank S) (outC i) = Y i := by
  have h := CopyAll.done_dst copies dst_injective (outerBank S) i
  change CopyAll.done copies 3 (outerBank S) (outC i) =
    outerBank S (inC (QuarticCutOutputCopies.srcC i)) ++ outerBank S (outC i) at h
  rw [outer_at, hSrc i, outer_out_blank, List.append_nil] at h
  exact h

theorem cleared_output (S : K → List Bool) (Y : Fin 3 → List Bool)
    (hSrc : ∀ i : Fin 3, S (QuarticCutOutputCopies.srcC i) = Y i) :
    ClearAll.clearFrom clearCells 0
      (CopyAll.done copies 3 (outerBank S)) = outputBank Y := by
  funext j
  by_cases hj : j.val < 3
  · let i : Fin 3 := ⟨j.val, hj⟩
    have he : outC i = j := Fin.ext rfl
    have hn : ¬ ∃ x : Fin (Lift.a FS + 3),
        0 ≤ x.val ∧ clearCells x = j := by
      rintro ⟨x, -, hx⟩
      have hv := congrArg Fin.val hx
      simp [clearCells, inC] at hv
      omega
    simp only [ClearAll.clearFrom, outputBank, dif_pos hj]
    rw [if_neg hn]
    have hc := copied_out S Y hSrc i
    simpa only [he] using hc
  · let x : Fin (Lift.a FS + 3) := ⟨j.val - 3, by have := j.isLt; omega⟩
    have he : clearCells x = j := Fin.ext (by simp [clearCells, inC, x]; omega)
    have hp : ∃ x : Fin (Lift.a FS + 3),
        0 ≤ x.val ∧ clearCells x = j := ⟨x, Nat.zero_le _, he⟩
    simp only [ClearAll.clearFrom, outputBank, dif_neg hj]
    rw [if_pos hp]

theorem clear_run (S : K → List Bool) :
    let T := CopyAll.done copies 3 (outerBank S)
    ∃ t ≤ (Lift.a FS + 3) *
        ((BitMachineBankCodec.encode T).length + 1) + 1,
      ∃ v,
      ((advance (ClearAll.prog clearCells))^[t])
        (⟨some ⟨0, by omega⟩, none, T⟩ :
          TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, v, ClearAll.clearFrom clearCells 0 T⟩ := by
  intro T
  apply ClearAll.all_run clearCells clearCells_inj
    (BitMachineBankCodec.encode T).length T
    (fun j => BitMachineBankCodec.word_length_le_encode T (clearCells j)) none

theorem encode_outputBank (Y : Fin 3 → List Bool) :
    BitMachineBankCodec.encode (outputBank Y) =
      BitMachineBankCodec.encode Y ++ List.replicate (Lift.a FS + 3) false := by
  rw [Unit4Post.encode_cast
    (show (Lift.a FS + 3) + 3 = 3 + (Lift.a FS + 3) by omega),
    Unit4Post.encode_split 3 (Lift.a FS + 3)]
  have h1 : (fun i : Fin 3 => outputBank Y
      (Fin.cast (show (Lift.a FS + 3) + 3 = 3 + (Lift.a FS + 3) by omega).symm
        (i.castLE (Nat.le_add_right 3 (Lift.a FS + 3))))) = Y := by
    funext i
    simp only [outputBank, Fin.val_cast, Fin.val_castLE]
    rw [dif_pos i.isLt]
  have h2 : (fun j : Fin (Lift.a FS + 3) => outputBank Y
      (Fin.cast (show (Lift.a FS + 3) + 3 = 3 + (Lift.a FS + 3) by omega).symm
        (j.natAdd 3))) = fun _ => ([] : List Bool) := by
    funext j
    simp only [outputBank, Fin.val_cast, Fin.val_natAdd]
    rw [dif_neg (by omega)]
  rw [h1, h2, Unit4Post.encode_nil]

#print axioms copy_run
#print axioms cleared_output
#print axioms clear_run
#print axioms encode_outputBank

end
end Paper2.CurrentAdditive.QuarticOuterOutput
