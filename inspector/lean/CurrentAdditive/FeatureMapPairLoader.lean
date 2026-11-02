import CurrentAdditive.CodeDPairSerializerClear
import CurrentAdditive.MachineInvokeFull
import EthInapproximability.CurrentPaper.WeightedRawWordsFuel

/-! Physical preparation of the two-field context/item packet. The context
on bank 12 is retained. Item bank 6 is consumed once into the packet, bank 4
receives the packet, and every foreign bank is preserved. -/

namespace CurrentAdditive.FeatureMapPairLoader

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext

abbrev Stack (N : Nat) := MachineInvokeCore.StackN N
variable {N : Nat}

def low (n : Fin 32) : Stack N := n.castAdd N

@[simp] theorem low_val (n : Fin 32) : (low (N := N) n).val = n.val := rfl

theorem low_injective : Function.Injective (low (N := N)) := by
 intro a b h
 apply Fin.ext
 have hh : (low (N := N) a).val = (low (N := N) b).val := congrArg Fin.val h
 exact hh

def copySlots : Fin 3 ↪ Stack N where
 toFun := ![low 12, low 7, low 14]
 inj' := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [low, Fin.ext_iff]

def copyProgram := ExactParameterBranchInstall.copyProgram (copySlots (N := N))

def pairSlots : BitMachineBankSerialize.Stack 2 ↪ Stack N where
 toFun
  | .inl i => ![low 7, low 6] i
  | .inr i => ![low 14, low 11, low 4] i
 inj' := by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => fin_cases a <;> fin_cases b <;> simp_all [low, Fin.ext_iff]
    | inr b => fin_cases a <;> fin_cases b <;> simp_all [low, Fin.ext_iff]
  | inr a => cases b with
    | inl b => fin_cases a <;> fin_cases b <;> simp_all [low, Fin.ext_iff]
    | inr b => fin_cases a <;> fin_cases b <;> simp_all [low, Fin.ext_iff]

def pairProgram (l : BitMachineBankSerialize.Label 2) :=
 BitMachineStackEmbedding.stackStmt (pairSlots (N := N))
   (BitMachineBankSerialize.program 2 l)

def packet (context item : List Bool) : List Bool :=
 BitMachineBankCodec.encode (![context,item] : Fin 2 → List Bool)

theorem packet_eq (context item : List Bool) :
 packet context item = EncodedCommunication.field context ++ EncodedCommunication.field item := by
 rw [packet, BitMachineBankCodec.encode_eq_list]
 simp

theorem packet_length (context item : List Bool) :
 (packet context item).length = 2 * context.length + 2 * item.length + 2 := by
 rw [packet_eq, List.length_append, EncodedCommunication.field_length,
   EncodedCommunication.field_length]
 omega

def prepared (S : Stack N → List Bool) (item : List Bool) : Stack N → List Bool :=
 Function.update (Function.update (Function.update S (low 7) []) (low 6) [])
   (low 4) item

theorem pair_run (S : Stack N → List Bool) (context item : List Bool)
 (h7 : S (low 7) = context) (h6 : S (low 6) = item)
 (h4 : S (low 4) = []) (h11 : S (low 11) = []) (h14 : S (low 14) = []) :
 ∃ t ≤ 2 * (packet context item).length + 2,
 ((advance (pairProgram (N := N)))^[t])
   (⟨some (.emit 0), none, S⟩ : TM2.Cfg (fun _ : Stack N => Bool) _ _) =
   ⟨none, none, prepared S (packet context item)⟩ := by
 let words := CodeDPairSerializerClear.words context item
 let t := context.length + 1 + (item.length + 1) +
   ((EncodedCommunication.field context ++ EncodedCommunication.field item).length + 2)
 have hr := CodeDPairSerializerClear.serialize_cleared context item
 have hin : ∀ k, (BitMachineBankSerialize.cfg (some (.emit 0)) none words [] [] []).stk k =
     S (pairSlots k) := by
  intro k
  cases k with
  | inl k => fin_cases k <;> simp [words, CodeDPairSerializerClear.words,
      BitMachineBankSerialize.cfg, BitMachineBankSerialize.contents, pairSlots, h7, h6]
  | inr k => fin_cases k <;> simp [BitMachineBankSerialize.cfg,
      BitMachineBankSerialize.contents, pairSlots, h4, h11, h14]
 have h := WeightedRawWords.region_run (pairSlots (N := N))
   (BitMachineBankSerialize.program 2) _ _ _ hr S hin
 refine ⟨t, ?_, ?_⟩
 · dsimp [t]
   rw [packet_eq]
   simp only [List.length_append, EncodedCommunication.field_length]
   omega
 · change ((advance (pairProgram (N := N)))^[t]) _ = _ at h
   refine h.trans ?_
   simp only [BitMachineBankSerialize.cfg, BitMachineStackEmbedding.stackCfg]
   congr 1
   funext j
   have hb : BitMachineBankSerialize.contents (CodeDPairSerializerClear.cleared words)
       [] [] (EncodedCommunication.field context ++ EncodedCommunication.field item) =
       Function.update (Function.update (Function.update
         (fun k => S (pairSlots k)) (.inl 0) []) (.inl 1) [])
         (.inr 2) (packet context item) := by
     funext k
     cases k with
     | inl k =>
       fin_cases k <;>
         change [] = _ <;>
         simp [Function.update_apply]
     | inr k =>
       fin_cases k
       · change [] = _
         simp [pairSlots, h14, Function.update_apply]
       · change [] = _
         simp [pairSlots, h11, Function.update_apply]
       · change EncodedCommunication.field context ++ EncodedCommunication.field item = _
         simp [packet_eq, Function.update_apply]
   rw [hb, BitMachineStackEmbedding.bank_update,
     BitMachineStackEmbedding.bank_update, BitMachineStackEmbedding.bank_update,
     BitMachineStackEmbedding.bank_restrict]
   rfl

def program := BitMachineRawSequence.program
 (copyProgram (N := N)) (pairProgram (N := N)) (.emit 0) none none

def start : BitMachineRawSequence.Label BitMachineCopy.Label (BitMachineBankSerialize.Label 2) :=
 BitMachineRawSequence.leftLabel .scan

theorem load_run (S : Stack N → List Bool) (context item : List Bool)
 (h12 : S (low 12) = context) (h6 : S (low 6) = item)
 (h7 : S (low 7) = []) (h4 : S (low 4) = [])
 (h11 : S (low 11) = []) (h14 : S (low 14) = []) :
 ∃ t ≤ (2 * context.length + 2) + (2 * (packet context item).length + 2) + 1,
 ((advance (program (N := N)))^[t])
   (⟨some start, (none,none), S⟩ : TM2.Cfg (fun _ : Stack N => Bool) _ _) =
   ⟨none, (none,none), prepared S (packet context item)⟩ := by
 obtain ⟨a,ha,hr⟩ := ExactParameterBranchInstall.copy_run copySlots S context
   (by simpa [copySlots] using h12) (by simpa [copySlots] using h7)
   (by simpa [copySlots] using h14)
 obtain ⟨b,hb,hs⟩ := pair_run (Function.update S (low 7) context) context item
   (by simp) (by simpa [low, Fin.ext_iff] using h6)
   (by simpa [low, Fin.ext_iff] using h4)
   (by simpa [low, Fin.ext_iff] using h11)
   (by simpa [low, Fin.ext_iff] using h14)
 obtain ⟨t,ht,he⟩ := BitMachineRawSequence.runs copyProgram pairProgram
   BitMachineCopy.Label.scan (.emit 0) none none none none S
   (Function.update S (low 7) context) _ a b hr hs
 refine ⟨t,by omega,?_⟩
 simpa [program, start, prepared, Function.update_idem] using he

#print axioms load_run
#print axioms pair_run

end CurrentAdditive.FeatureMapPairLoader
