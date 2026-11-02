import EthInapproximability.CurrentPaper.SamplerWriterSecondInit
import EthInapproximability.CurrentPaper.BitMachineCopy

/-!
# Physical source-preserving copies for the second sampler call

The two retained second-call input banks are copied into the cleared sampler
degree and length cells. The alphabet width is copied from scalar cell 24
into the block-reverser's width cell 32. Each phase uses the same actual
three-stack copy controller, with a fixed stack injection.
-/

namespace EthInapproximability.CurrentPaper.SamplerWriterSecondCopy

open Turing BitMachineEncoding

abbrev Stack := SamplerWriterSecondInit.Stack

def degreeSlots : Fin 3 ↪ Stack :=
  ⟨![SamplerWriterSecondInit.nextDegree,
     SamplerWriterSecondInit.degreeCell,
     .inl (.inl (.inl (.inl 37)))], by decide⟩

def lengthSlots : Fin 3 ↪ Stack :=
  ⟨![SamplerWriterSecondInit.nextLength,
     SamplerWriterSecondInit.lengthCell,
     .inl (.inl (.inl (.inl 38)))], by decide⟩

def widthSlots : Fin 3 ↪ Stack :=
  ⟨![.inl (.inl (.inl (.inl 24))),
     .inl SamplerWriterPayloadFrame.reverseWidthCell,
     .inl (.inl (.inl (.inl 39)))], by decide⟩

def program (ι : Fin 3 ↪ Stack) (l : BitMachineCopy.Label) :
    TM2.Stmt (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool) :=
  BitMachineStackEmbedding.stmt ι id id id none (BitMachineCopy.program l)

private theorem inlineCfg_id (q : TM2.Cfg (fun _ : Fin 3 => Bool)
    BitMachineCopy.Label (Option Bool)) :
    BitMachineInline.cfg id id none q = q := by
  cases q with
  | mk l v S => cases l <;> rfl

theorem copy_run (ι : Fin 3 ↪ Stack) (S : Stack → List Bool) (bits : List Bool)
    (hsource : S (ι 0) = bits) (htarget : S (ι 1) = [])
    (hscratch : S (ι 2) = []) :
    ∃ u ≤ 2 * bits.length + 2,
      ((advance (program ι))^[u])
        (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : Stack => Bool)
          BitMachineCopy.Label (Option Bool)) =
        ⟨none, none, Function.update S (ι 1) bits⟩ := by
  let c := BitMachineCopy.cfg (some .scan) none bits [] []
  have hbank : BitMachineStackEmbedding.bank ι S c.stk = S := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    fin_cases k <;> simp [c, BitMachineCopy.cfg, BitMachineCopy.stackContents,
      hsource, htarget, hscratch]
  have hr := BitMachineCopy.run_correct none bits []
  have hh : (((advance BitMachineCopy.program)^[2 * bits.length + 2]) c).l = none := by
    change (BitMachineCopy.run (2 * bits.length + 2) c).l = none
    rw [hr]
    rfl
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs ι S
    id id id (by intro v; rfl) none
    BitMachineCopy.program (program ι) (by intro l; rfl)
    c (2 * bits.length + 2) hh
  change ((advance (program ι))^[u])
      (BitMachineStackEmbedding.cfg ι S id id none c) =
      BitMachineStackEmbedding.cfg ι S id id none
        (BitMachineCopy.run (2 * bits.length + 2) c) at he
  rw [hr] at he
  simp only [List.append_nil] at he
  have hf : (BitMachineCopy.cfg none none bits bits []).stk =
      Function.update c.stk 1 bits := by
    funext k
    fin_cases k <;> rfl
  simp only [BitMachineStackEmbedding.cfg, inlineCfg_id] at he
  refine ⟨u, hu, ?_⟩
  simpa only [BitMachineStackEmbedding.stackCfg, hf,
    BitMachineStackEmbedding.bank_update, hbank] using he

end EthInapproximability.CurrentPaper.SamplerWriterSecondCopy
