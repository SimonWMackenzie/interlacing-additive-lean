import EthInapproximability.CurrentPaper.GenericPrefixLoopEndpoint
import EthInapproximability.CurrentPaper.BitMachineCopy

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixCopy

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanPrefix
open scoped Classical

abbrev Stack :=
  (PrefixLoopMachine.Stack ⊕ PairVertexLoopMachine.Stack) ⊕ Fin 1

def atEmbedding : PrefixLoopMachine.Stack ↪ Stack :=
  Function.Embedding.inl.trans Function.Embedding.inl

def pairEmbedding : PairVertexLoopMachine.Stack ↪ Stack :=
  Function.Embedding.inr.trans Function.Embedding.inl

def scratch : Stack := .inr 0

noncomputable def copySlots (src dst : Stack)
    (hs : src ≠ dst) (hx : src ≠ scratch) (hy : dst ≠ scratch) :
    Fin 3 ↪ Stack where
  toFun
    | 0 => src
    | 1 => dst
    | 2 => scratch
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [hs,hx,hy,Ne.symm hs,Ne.symm hx,Ne.symm hy]

noncomputable def copyProgram (src dst : Stack)
    (hs : src ≠ dst) (hx : src ≠ scratch) (hy : dst ≠ scratch) :=
  fun l => stackStmt (copySlots src dst hs hx hy) (BitMachineCopy.program l)

theorem copy_run (src dst : Stack)
    (hs : src ≠ dst) (hx : src ≠ scratch) (hy : dst ≠ scratch)
    (B : Stack → List Bool) (word : List Bool)
    (hsrc : B src = word) (hdst : B dst = [])
    (hw : B scratch = []) :
    ((advance (copyProgram src dst hs hx hy))^[2*word.length+2])
      (⟨some .scan,none,B⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,none,Function.update B dst word⟩ := by
  let C := BitMachineCopy.cfg (some .scan) none word [] []
  have hbank : bank (copySlots src dst hs hx hy) B C.stk = B := by
    apply bank_eq_self
    intro i
    fin_cases i
    · exact hsrc.symm
    · exact hdst.symm
    · exact hw.symm
  have hc : ((advance BitMachineCopy.program)^[2*word.length+2]) C =
      BitMachineCopy.cfg none none word word [] := by
    simpa [C,BitMachineCopy.run] using
      BitMachineCopy.run_correct none word []
  have he := BitMachineStackRun.run (copySlots src dst hs hx hy) B
    BitMachineCopy.program C (2*word.length+2)
  rw [hc] at he
  have hf : (BitMachineCopy.cfg none none word word []).stk =
      Function.update C.stk 1 word := by
    funext i
    fin_cases i <;> rfl
  simp only [stackCfg,hf,bank_update,hbank] at he
  simpa only [copyProgram,copySlots] using he

#print axioms copy_run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixCopy
