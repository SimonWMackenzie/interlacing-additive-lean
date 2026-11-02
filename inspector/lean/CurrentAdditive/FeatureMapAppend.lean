import CurrentAdditive.FeatureMapInvoke
import CurrentAdditive.CodeDAppendAtEnd15

/-! The physical per-item context mapper. It clears the getter's unary
length scratch, loads the actual context/item packet, invokes the globally
fixed evaluator, optionally frames the answer, and appends it in order. -/

namespace CurrentAdditive.FeatureMapAppend

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.FeatureMapPairLoader
open CurrentAdditive.FeatureMapInvoke
open CurrentAdditive.MinimumRatioContext

noncomputable section

variable (M : BitMachine.Machine) (framed : Bool)

def appendSlots : Fin 15 ↪ Bank M framed where
 toFun j := ⟨j.val, by have := j.isLt; change j.val < 32 + count M framed; omega⟩
 inj' := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun j : Bank M framed => j.val) h

def appendProgram (l : CodeDAppendAtEnd15.Label) :=
 BitMachineStackEmbedding.stackStmt (appendSlots M framed)
   (CodeDAppendAtEnd15.program l)

theorem append_run (S : Bank M framed → List Bool) (output payload : List Bool)
 (h9 : S (low 9) = output) (h5 : S (low 5) = payload)
 (h11 : S (low 11) = []) (h14 : S (low 14) = []) :
 ((advance (appendProgram M framed))^[4 * output.length + 2 * payload.length + 7])
   (⟨some .saveScan, ((),none), S⟩ : TM2.Cfg (fun _ : Bank M framed => Bool) _ _) =
   ⟨none, ((),none),
     Function.update (Function.update S (low 5) []) (low 9) (output ++ payload)⟩ := by
 let old := fun k => S (appendSlots M framed k)
 have hinit : CodeDAppendAtEnd15.initialBank old output payload = old := by
   funext k
   by_cases h : k = 9
   · subst k; simpa [CodeDAppendAtEnd15.initialBank, old, appendSlots, low] using h9.symm
   by_cases h' : k = 5
   · subst k; simpa [CodeDAppendAtEnd15.initialBank, old, appendSlots, low] using h5.symm
   simp [CodeDAppendAtEnd15.initialBank, h, h']
 have hr := CodeDAppendAtEnd15.append_run old output payload
   (by simpa [old, appendSlots, low] using h11)
   (by simpa [old, appendSlots, low] using h14)
 rw [hinit] at hr
 have hrhalt : ((advance CodeDAppendAtEnd15.program)^[4*output.length+2*payload.length+7])
   (⟨some .saveScan,((),none),old⟩ : CodeDAppendAtEnd15.Config) =
   ⟨none,((),none),Function.update (Function.update old 5 []) 9 (output++payload)⟩ := by
   have htime : 4*output.length+2*payload.length+7 =
       (4*output.length+2*payload.length+6)+1 := by omega
   rw [htime, Function.iterate_succ_apply']
   change advance CodeDAppendAtEnd15.program (CodeDAppendAtEnd15.run _ _) = _
   rw [hr]
   change (⟨none,((),none),_⟩ : CodeDAppendAtEnd15.Config) = _
   congr 1
   funext k
   by_cases h : k = 9 <;> by_cases h' : k = 5 <;>
     simp [Function.update_apply,h,h']
 have h := WeightedRawWords.region_run (appendSlots M framed)
   CodeDAppendAtEnd15.program _ _ _ hrhalt S (by intro k;rfl)
 change ((advance (appendProgram M framed))^[_]) _ = _ at h
 refine h.trans ?_
 congr 1
 change BitMachineStackEmbedding.bank (appendSlots M framed) S
   (Function.update (Function.update old 5 []) 9 (output++payload)) = _
 rw [BitMachineStackEmbedding.bank_update,BitMachineStackEmbedding.bank_update]
 change Function.update (Function.update
   (BitMachineStackEmbedding.bank (appendSlots M framed) S
      (fun k => S (appendSlots M framed k))) (low 5) []) (low 9) _ = _
 rw [BitMachineStackEmbedding.bank_restrict]

def coreProgram := BitMachineRawSequence.program
 (loadedProgram M framed) (appendProgram M framed) .saveScan
 (loadedControl M framed) ((),none)

abbrev CoreLabel := BitMachineRawSequence.Label (LoadedLabel M framed) CodeDAppendAtEnd15.Label
abbrev CoreControl := LoadedControl M framed × (Unit × Option Bool)
def coreStart : CoreLabel M framed := BitMachineRawSequence.leftLabel (loadedStart M framed)
def coreControl : CoreControl M framed := (loadedControl M framed,((),none))

def finalBank (S : Bank M framed → List Bool) (context item output answer : List Bool) :=
 Function.update (Function.update (prepared S (packet context item)) (low 5) [])
   (low 9) (output ++ piece framed answer)

def coreBudget (context item output answer : List Bool) (T : Nat) : Nat :=
 loadedBudget M framed context item answer T +
   (4 * output.length + 2 * (piece framed answer).length + 7) + 1

theorem core_run (S : Bank M framed → List Bool)
 (context item output answer : List Bool) (T : Nat)
 (h12 : S (low 12) = context) (h6 : S (low 6) = item)
 (h7 : S (low 7) = []) (h4 : S (low 4) = []) (h5 : S (low 5) = [])
 (h9 : S (low 9) = output) (h11 : S (low 11) = []) (h14 : S (low 14) = [])
 (hblank : ∀ i, S (machineSlots M framed i) = [])
 (hM : M.OutputsWithin (packet context item) answer T) :
 ∃ t ≤ coreBudget M framed context item output answer T,
 ((advance (coreProgram M framed))^[t])
   (⟨some (coreStart M framed), coreControl M framed, S⟩ :
     TM2.Cfg (fun _ : Bank M framed => Bool) _ _) =
   ⟨none, coreControl M framed, finalBank M framed S context item output answer⟩ := by
 obtain ⟨a,ha,hr⟩ := loaded_run M framed S context item answer T
   h12 h6 h7 h4 h5 h11 h14 hblank hM
 let U := Function.update (prepared S (packet context item)) (low 5) (piece framed answer)
 have h9' : U (low 9) = output := by simpa [U,prepared,low,Fin.ext_iff] using h9
 have h11' : U (low 11) = [] := by simpa [U,prepared,low,Fin.ext_iff] using h11
 have h14' : U (low 14) = [] := by simpa [U,prepared,low,Fin.ext_iff] using h14
 have hs := append_run M framed U output (piece framed answer) h9'
   (by simp [U]) h11' h14'
 obtain ⟨t,ht,he⟩ := BitMachineRawSequence.runs
   (loadedProgram M framed) (appendProgram M framed)
   (loadedStart M framed) .saveScan
   (loadedControl M framed) (loadedControl M framed) ((),none) ((),none)
   S U _ a _ hr hs
 refine ⟨t,by dsimp [coreBudget];omega,?_⟩
 simpa [coreProgram,coreStart,coreControl,finalBank,U,Function.update_idem] using he

inductive Label where
 | clear5 | core (l : CoreLabel M framed)
 deriving Fintype

noncomputable instance : DecidableEq (Label M framed) := Classical.decEq _

abbrev Control := CoreControl M framed × Option Bool
def initial : Control M framed := (coreControl M framed,none)

def program : Label M framed →
 TM2.Stmt (fun _ : Bank M framed => Bool) (Label M framed) (Control M framed)
 | .clear5 => BitMachineClearBank.clearStep (low 5) .clear5 (.core (coreStart M framed))
 | .core l => BitMachineInline.stmt Label.core (fun v => (v,none)) Prod.fst none
     (coreProgram M framed l)

def callbackBudget (S : Bank M framed → List Bool)
 (context item output answer : List Bool) (T : Nat) : Nat :=
 (S (low 5)).length+1 + coreBudget M framed context item output answer T

theorem callback_run (S : Bank M framed → List Bool)
 (context item output answer : List Bool) (T : Nat)
 (h12 : S (low 12) = context) (h6 : S (low 6) = item)
 (h7 : S (low 7) = []) (h4 : S (low 4) = [])
 (h9 : S (low 9) = output) (h11 : S (low 11) = []) (h14 : S (low 14) = [])
 (hblank : ∀ i, S (machineSlots M framed i) = [])
 (hM : M.OutputsWithin (packet context item) answer T) :
 ∃ t ≤ callbackBudget M framed S context item output answer T,
 ((advance (program M framed))^[t])
   (⟨some .clear5, initial M framed, S⟩ :
     TM2.Cfg (fun _ : Bank M framed => Bool) _ _) =
   ⟨none, initial M framed, finalBank M framed S context item output answer⟩ := by
 let U := Function.update S (low 5) []
 have hc := BitMachineClearBank.clear_one_run (program M framed) (low 5)
   (.clear5 : Label M framed) (.core (coreStart M framed)) rfl (coreControl M framed) S
 obtain ⟨a,ha,hr⟩ := core_run M framed U context item output answer T
   (by simpa [U,low,Fin.ext_iff] using h12)
   (by simpa [U,low,Fin.ext_iff] using h6)
   (by simpa [U,low,Fin.ext_iff] using h7)
   (by simpa [U,low,Fin.ext_iff] using h4) (by simp [U])
   (by simpa [U,low,Fin.ext_iff] using h9)
   (by simpa [U,low,Fin.ext_iff] using h11)
   (by simpa [U,low,Fin.ext_iff] using h14)
   (by intro i
       have hn : machineSlots M framed i ≠ low 5 := by
         intro h;have hh := congrArg Fin.val h;change 32+i.val=5 at hh;omega
       simpa [U,Function.update_of_ne hn] using hblank i) hM
 obtain ⟨b,hb,he⟩ := BitMachineInline.outputs
   (Label.core : CoreLabel M framed → Label M framed)
   (fun v => (v,none)) Prod.fst (by intro v;rfl) none
   (coreProgram M framed) (program M framed) (by intro l;rfl)
   (⟨some (coreStart M framed), coreControl M framed,U⟩ :
     TM2.Cfg (fun _ : Bank M framed => Bool) _ _) a (by rw [hr])
 rw [hr] at he
 simp only [BitMachineInline.cfg] at he
 refine ⟨(S (low 5)).length+1+b,by dsimp [callbackBudget];omega,?_⟩
 dsimp only [initial]
 rw [show (S (low 5)).length+1+b=b+((S (low 5)).length+1) by omega,
   Function.iterate_add_apply,hc]
 have hf : finalBank M framed U context item output answer =
     finalBank M framed S context item output answer := by
   funext k
   by_cases h5 : k = low 5 <;> by_cases h9 : k = low 9 <;>
     by_cases h7 : k = low 7 <;> by_cases h6 : k = low 6 <;>
     by_cases h4 : k = low 4 <;>
     simp [finalBank,prepared,U,Function.update_apply,h5,h9,h7,h6,h4,
       low,Fin.ext_iff] at * <;> simp_all
 rw [hf] at he
 exact he

#print axioms append_run
#print axioms callback_run

end
end CurrentAdditive.FeatureMapAppend
