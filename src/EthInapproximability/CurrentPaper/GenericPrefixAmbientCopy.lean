import EthInapproximability.CurrentPaper.GenericPrefixCompositeEndpoint
import EthInapproximability.CurrentPaper.SourceCSPFirstRowController

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixAmbientCopy

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

abbrev Stack (q : Nat) :=
  (SourceCSPFirstRowController.Stack q ⊕ PrefixCopy.Stack) ⊕ Fin 1

def rawEmbedding (q : Nat) :
    SourceCSPFirstRowController.Stack q ↪ Stack q :=
  Function.Embedding.inl.trans Function.Embedding.inl

def workEmbedding (q : Nat) : PrefixCopy.Stack ↪ Stack q :=
  Function.Embedding.inr.trans Function.Embedding.inl

def scratch (q : Nat) : Stack q := .inr 0

noncomputable def copySlots {q : Nat} (src dst : Stack q)
    (hs : src ≠ dst) (hx : src ≠ scratch q) (hy : dst ≠ scratch q) :
    Fin 3 ↪ Stack q where
  toFun
    | 0 => src
    | 1 => dst
    | 2 => scratch q
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [hs,hx,hy,Ne.symm hs,Ne.symm hx,Ne.symm hy]

noncomputable def copyProgram {q : Nat} (src dst : Stack q)
    (hs : src ≠ dst) (hx : src ≠ scratch q) (hy : dst ≠ scratch q) :=
  fun l => stackStmt (copySlots src dst hs hx hy) (BitMachineCopy.program l)

theorem copy_run {q : Nat} (src dst : Stack q)
    (hs : src ≠ dst) (hx : src ≠ scratch q) (hy : dst ≠ scratch q)
    (B : Stack q → List Bool) (word : List Bool)
    (hsrc : B src = word) (hdst : B dst = [])
    (hw : B (scratch q) = []) :
    ((advance (copyProgram src dst hs hx hy))^[2*word.length+2])
      (⟨some .scan,none,B⟩ : TM2.Cfg (fun _ : Stack q => Bool) _ _) =
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

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PrefixAmbientCopy
