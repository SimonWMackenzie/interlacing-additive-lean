import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.MatrixBinaryAddress
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! A physical row-address stage: copy a binary row label to scratch, convert
the copy to unary, and preserve the original label and every other cell. -/

namespace Paper2.GenericBitvectorRowAddress

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)

def cp : Fin 3 ↪ Fin 14 := ⟨![0, 1, 2], by decide⟩
def bin : Fin 3 ↪ Fin 14 := ⟨![1, 3, 4], by decide⟩

def copy := MatrixStage4ScalarPreparationOps.copyProgram cp
def decode := fun l => stackStmt bin (MatrixBinaryAddress.program l)
def program := BitMachineRawSequence.program copy decode
  MatrixBinaryAddress.Label.readBit (none : Option Bool) (false, false)

theorem decode_run (S : Fin 14 → List Bool) (q : List Bool)
    (h1 : S 1 = q) (h3 : S 3 = []) (h4 : S 4 = []) :
    ((advance decode)^[MatrixBinaryAddress.workFrom 0 q])
      (⟨some .readBit, (false, false), S⟩ : TM2.Cfg (fun _ : Fin 14 => Bool) _ _) =
      ⟨none, (false, false), Function.update S 1
        (List.replicate (MatrixBinaryAddress.valueFrom 0 q) true)⟩ := by
  let B := MatrixBinaryAddress.stackContents q [] []
  have hB : ∀ k, B k = S (bin k) := by
    intro k
    fin_cases k <;> simp [B, MatrixBinaryAddress.stackContents, bin, h1, h3, h4]
  have hb := MatrixBinaryAddress.run_correct q 0 (false, false)
  simp only [List.replicate_zero] at hb
  unfold MatrixBinaryAddress.run at hb
  have hs := BitMachineStackRun.run bin S MatrixBinaryAddress.program
    (MatrixBinaryAddress.cfg (some .readBit) (false, false) q [] [])
    (MatrixBinaryAddress.workFrom 0 q)
  rw [hb] at hs
  have hstart : stackCfg bin S
      (MatrixBinaryAddress.cfg (some .readBit) (false, false) q [] []) =
      (⟨some .readBit, (false, false), S⟩ : TM2.Cfg (fun _ : Fin 14 => Bool) _ _) := by
    simp only [stackCfg, MatrixBinaryAddress.cfg]
    congr 1
    exact bank_eq_self bin S B hB
  rw [hstart] at hs
  have hend : stackCfg bin S
      (MatrixBinaryAddress.cfg none (false, false)
        (List.replicate (MatrixBinaryAddress.valueFrom 0 q) true) [] []) =
      (⟨none, (false, false), Function.update S 1
        (List.replicate (MatrixBinaryAddress.valueFrom 0 q) true)⟩ :
          TM2.Cfg (fun _ : Fin 14 => Bool) _ _) := by
    simp only [stackCfg, MatrixBinaryAddress.cfg]
    congr 1
    have hloc : MatrixBinaryAddress.stackContents
        (List.replicate (MatrixBinaryAddress.valueFrom 0 q) true) [] [] =
        Function.update B 0
          (List.replicate (MatrixBinaryAddress.valueFrom 0 q) true) := by
      funext k
      fin_cases k <;> simp [B, MatrixBinaryAddress.stackContents]
    rw [hloc, bank_update, bank_eq_self bin S B hB]
    rfl
  simpa only [decode, hend] using hs

theorem row_address_run (S : Fin 14 → List Bool) (q : List Bool)
    (h0 : S 0 = q) (h1 : S 1 = []) (h2 : S 2 = [])
    (h3 : S 3 = []) (h4 : S 4 = []) :
    ∃ t ≤ 2 * q.length + 2 + MatrixBinaryAddress.workFrom 0 q + 1,
      ((advance program)^[t])
        (⟨some (leftLabel BitMachineCopy.Label.scan),
          ((none : Option Bool), (false, false)), S⟩ :
            TM2.Cfg (fun _ : Fin 14 => Bool) _ _) =
        ⟨none, ((none : Option Bool), (false, false)),
          Function.update S 1
            (List.replicate (MatrixBinaryAddress.valueFrom 0 q) true)⟩ := by
  have hc := MatrixStage4ScalarPreparationOps.copy_run cp S h2
  have hcopy : S (cp 0) = q := h0
  have hdst : S (cp 1) = [] := h1
  simp only [hcopy, hdst, List.append_nil] at hc
  let W := Function.update S 1 q
  have hd := decode_run W q (by simp [W])
    (by simp [W, h3]) (by simp [W, h4])
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs copy decode
    BitMachineCopy.Label.scan MatrixBinaryAddress.Label.readBit
    (none : Option Bool) (none : Option Bool)
    (false, false) (false, false) S W _
    (2 * q.length + 2) (MatrixBinaryAddress.workFrom 0 q) hc hd
  refine ⟨t, ht, ?_⟩
  simpa only [program, W, Function.update_idem] using h

#print axioms decode_run
#print axioms row_address_run

end Paper2.GenericBitvectorRowAddress
