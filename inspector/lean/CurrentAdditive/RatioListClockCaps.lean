import CurrentAdditive.RatioListClockBounds

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
noncomputable section
namespace CurrentAdditive.RatioListClockCaps
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout MinimumRatioContext CurrentAdditive.GaussListContext
open RatioListClockBounds EntryClockPoly

def invokeCap (M : BitMachine.Machine) (L T : Nat) : Nat :=
  (2*L+2)+T+(2*(L+T*M.pushBound)+2)+
    (M.stackCount*(L+T*M.pushBound)+M.stackCount+2)+3
def lookupCap (L : Nat) := 50*(L+1)^3+2*L+12
def massCap (L : Nat) := invokeCap RatioMassProjection.W L (8*(L+1))
def outputCap (L : Nat) := 100*(L+1)^2
def wordCap (L : Nat) := 6*L+3
def appendCap (L : Nat) :=
  invokeCap V2FieldContext.W (wordCap L)
    ((UnaryBinaryEncoding.coefficient+7)*(wordCap L+1)^2) +
  (4*outputCap L+2*(3*wordCap L+1)+7)+1+(wordCap L+2)+1
def itemCap (L : Nat) := lookupCap L+massCap L+20*L+30+appendCap L

theorem invoke_le (M : BitMachine.Machine) (word : List Bool) (T L U : Nat)
    (hL : word.length ≤ L) (hT : T ≤ U) :
    MachineInvokeFull.uniformBound M word T ≤ invokeCap M L U := by
  unfold MachineInvokeFull.uniformBound invokeCap
  gcongr

theorem append_le (output word : List Bool) (L : Nat)
    (hout : output.length ≤ outputCap L) (hword : word.length ≤ wordCap L) :
    RatioV2Append.clock output word ≤ appendCap L := by
  have hf : (V2FieldContext.field word).length ≤ 3*wordCap L+1 := by
    have hn := EncodedGraph.natField_length_upper word.length
    simp only [V2FieldContext.field,List.length_append]
    omega
  have hi := invoke_le V2FieldContext.W word
    ((UnaryBinaryEncoding.coefficient+7)*(word.length+1)^2) (wordCap L)
    ((UnaryBinaryEncoding.coefficient+7)*(wordCap L+1)^2) hword (by gcongr)
  unfold RatioV2Append.clock V2FieldContext.clock appendCap
  omega

theorem lookup_le (cs pre : List (List Bool)) (c : List Bool) (tail : List (List Bool))
    (hsplit : pre ++ c :: tail=cs) (L : Nat)
    (hL : (SourceListEncoding.encode cs).length ≤ L) :
    RatioCoefficientLookup.clock pre c tail ≤ lookupCap L := by
  have hg := StatefulListScheduler.getterBudget_cubic pre c tail
  rw [hsplit] at hg
  have hc := (word_le_packet cs c (by rw [← hsplit]; simp)).trans hL
  have ht : (SourceListEncoding.fields tail).length ≤ L := by
    have hf := hL
    rw [← hsplit] at hf
    simp only [SourceListEncoding.encode,IndexedV2Clock.fields_append,
      SourceListEncoding.fields,List.length_append] at hf
    omega
  unfold RatioCoefficientLookup.clock lookupCap
  have hh : 50*((SourceListEncoding.encode cs).length+1)^3 ≤ 50*(L+1)^3 := by gcongr
  omega

theorem request_cut_cap (xs cs : List (List Bool)) (lambda : List Bool)
    (hlen : cs.length=xs.length) (pre : List (List Bool)) (word : List Bool)
    (tail : List (List Bool)) (hsplit : pre ++ word :: tail=xs) :
    RatioUpdateAppendItem.clock (cs.take pre.length)
      (RatioRequestListSpec.coefficient cs pre.length) (cs.drop (pre.length+1)) word lambda
      (RatioRequestListSpec.outputAt xs.length cs lambda pre) ≤
      itemCap (inputLength xs cs lambda) := by
  let L := inputLength xs cs lambda
  have hpre : pre.length < cs.length := by rw [hlen,← hsplit]; simp
  have hcoefsplit := RatioRequestListSpec.coefficient_split cs pre.length hpre
  have hlookup := lookup_le cs _ _ _ hcoefsplit L (by dsimp [L,inputLength]; omega)
  have hw : word.length ≤ L :=
    (word_le_packet xs word (by rw [← hsplit]; simp)).trans (by dsimp [L,inputLength]; omega)
  have hc : (RatioRequestListSpec.coefficient cs pre.length).length ≤ L :=
    (coefficient_le cs pre.length).trans (by dsimp [L,inputLength]; omega)
  have hl : lambda.length ≤ L := by dsimp [L,inputLength]; omega
  have hout := request_prefix_bound xs cs pre lambda
    (by intro w hw; rw [← hsplit]; simp [hw]) (by rw [← hsplit]; simp)
  have hrequest : (RatioRequestSerializer.bytes word lambda
      (RatioRequestListSpec.coefficient cs pre.length)).length ≤ wordCap L := by
    rw [request_length]
    unfold wordCap
    omega
  have happend := append_le _ _ L hout hrequest
  unfold RatioUpdateAppendItem.clock RatioUpdateItem.clock itemCap
  have hrlen := request_length word lambda (RatioRequestListSpec.coefficient cs pre.length)
  dsimp only [L] at *
  omega

theorem pair_cut_cap (xs cs : List (List Bool))
    (hlen : cs.length=xs.length) (pre : List (List Bool)) (word : List Bool)
    (tail : List (List Bool)) (hsplit : pre ++ word :: tail=xs) :
    RatioPairItem.clock (cs.take pre.length)
      (RatioPairListSpec.coefficient cs pre.length) (cs.drop (pre.length+1)) word
      (RatioPairListSpec.outputAt xs.length cs pre) ≤ itemCap (inputLength xs cs []) := by
  let L := inputLength xs cs []
  have hpre : pre.length < cs.length := by rw [hlen,← hsplit]; simp
  have hcoefsplit := RatioPairListSpec.coefficient_split cs pre.length hpre
  have hlookup := lookup_le cs _ _ _ hcoefsplit L (by dsimp [L,inputLength]; omega)
  have hw : word.length ≤ L :=
    (word_le_packet xs word (by rw [← hsplit]; simp)).trans (by dsimp [L,inputLength]; omega)
  have hc : (RatioPairListSpec.coefficient cs pre.length).length ≤ L :=
    (coefficient_le cs pre.length).trans (by dsimp [L,inputLength]; omega)
  have hm : (RatioPairItem.massWord word).length ≤ L :=
    (BankFieldProjection.result_length (1 : Fin 2) word).trans hw
  have hmass := invoke_le RatioMassProjection.W word (8*(word.length+1)) L
    (8*(L+1)) hw (by omega)
  have hout := pair_prefix_bound xs cs pre
    (by intro w hw; rw [← hsplit]; simp [hw]) (by rw [← hsplit]; simp)
  have hpair : (RatioPairItem.pairWord word
      (RatioPairListSpec.coefficient cs pre.length)).length ≤ wordCap L := by
    simp only [RatioPairItem.pairWord,RatioPairSerializer.bytes,List.length_append,
      EncodedCommunication.field_length]
    unfold wordCap
    omega
  have hpairlen : (RatioPairItem.pairWord word
      (RatioPairListSpec.coefficient cs pre.length)).length ≤ 4*L+2 := by
    simp only [RatioPairItem.pairWord,RatioPairSerializer.bytes,List.length_append,
      EncodedCommunication.field_length]
    omega
  have happend := append_le _ _ L hout hpair
  unfold RatioPairItem.clock itemCap massCap
  dsimp only [RatioMassProjection.clock,L] at *
  omega

#print axioms request_cut_cap
#print axioms pair_cut_cap
end CurrentAdditive.RatioListClockCaps
