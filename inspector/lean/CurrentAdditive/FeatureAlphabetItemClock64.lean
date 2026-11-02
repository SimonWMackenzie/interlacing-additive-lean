import CurrentAdditive.FeatureAlphabetClockBounds64

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 100
noncomputable section
namespace CurrentAdditive.FeatureAlphabetItemClock64
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open EthInapproximability.CurrentPaper.EncodedCommunication
open CylinderFeatureCodec FeatureInnerAlphabetRun64 FeatureBoundedAlphabet64
open GaussListContext Wide64ContextListScheduler FeatureAlphabetClockBounds64

def itemCap (n : Nat) := FeatureExtensionPolynomial64.coefficient*(64*(n+1)+1)^4

theorem itemClock_le (j : Nat) (c : List (Nat × Nat)) (ys : List Nat)
    (body : List Bool) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (hsplit : pre++word::suffix=original ys) :
    itemClock j c pre word suffix (body++joined (piece j c) pre) ≤
      itemCap (inputSize j c ys body) := by
  obtain ⟨y,_,hword⟩ := label_from_split ys pre word suffix hsplit
  subst word
  let L := inputSize j c ys body
  let N := 64*(L+1)
  obtain ⟨hp,ht,hw,hf,hcount⟩ := split_bounds ys pre y.bits suffix hsplit
  obtain ⟨hpre,hframe⟩ := extension_split_bounds j c ys pre y.bits suffix hsplit
  have hb := selected_bankSize j c ys body pre y.bits suffix hsplit
  have hLN : L ≤ N := by dsimp [N]; omega
  have hbody : (body++joined (piece j c) pre).length ≤ L := by
    dsimp only [L,inputSize]
    simp only [List.length_append]
    omega
  have hfr : (EncodedCommunication.natField
      (FeatureExtensionCompose64.raw j y c).length++FeatureExtensionCompose64.raw j y c).length ≤ L := by
    have hh : (piece j c y.bits).length ≤ L := by dsimp [L,inputSize]; omega
    simpa only [piece,FeatureExtensionCompose64.raw,bitsValue_bits] using hh
  have hraw : (FeatureExtensionCompose64.raw j y c).length ≤ L := by
    simp only [List.length_append] at hfr
    omega
  change FeatureBoundedExtension64.clock _ j (bitsValue y.bits) c _ ≤ _
  rw [bitsValue_bits]
  apply FeatureExtensionPolynomial64.clock_le _ j y c _ N
  · exact hb.trans (Nat.mul_le_mul_left 64 (Nat.le_succ L))
  · unfold FeaturePreparedCallback.preparedSize
    dsimp only [L,inputSize,N]
    omega
  · exact hraw.trans hLN
  · exact hbody.trans hLN
  · exact hfr.trans hLN

def growth := BitMachineStackGrowth.perStep FeatureExtensionCompose64.cleanedProgram

theorem state_length_le (j : Nat) (c : List (Nat × Nat)) (ys : List Nat)
    (body : List Bool) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (hsplit : pre++word::suffix=original ys) (k : Fin 64) :
    ((contract j c ys body).state pre word suffix k).length ≤
      inputSize j c ys body+growth*itemCap (inputSize j c ys body) := by
  let C := contract j c ys body
  let S := selected j c pre word suffix (body++joined (piece j c) pre)
  have hr := C.callback_run pre word suffix hsplit
  have hr' : ((advance FeatureExtensionCompose64.cleanedProgram)^[C.time pre word suffix])
      (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel FeaturePairRaw64.start)),
        ((FeaturePairRaw64.control,(((),none),
          (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,((),none)))),((),none)),S⟩ :
          TM2.Cfg (fun _ : Fin 64 => Bool) _ _) =
      ⟨none,C.control pre word suffix,C.state pre word suffix⟩ := by
    simpa only [S,selected,hsplit] using hr
  have hg := BitMachineStackGrowth.run_growth FeatureExtensionCompose64.cleanedProgram
    (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel FeaturePairRaw64.start)),
        ((FeaturePairRaw64.control,(((),none),
          (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,((),none)))),((),none)),S⟩ :
          TM2.Cfg (fun _ : Fin 64 => Bool) _ _) (C.time pre word suffix) k
  rw [hr'] at hg
  have htime : C.time pre word suffix ≤ itemCap (inputSize j c ys body) :=
    (contract_time_le j c ys body pre word suffix hsplit).trans
      (itemClock_le j c ys body pre word suffix hsplit)
  obtain ⟨hp,ht,hw,hf,_⟩ := split_bounds ys pre word suffix hsplit
  obtain ⟨hpre,_⟩ := extension_split_bounds j c ys pre word suffix hsplit
  have hs : (S k).length ≤ inputSize j c ys body := by
    apply selected_length
    all_goals dsimp only [inputSize]
    · rw [hsplit]; omega
    · omega
    · omega
    · omega
    · omega
    · simp only [List.length_append]; omega
    · omega
    · omega
  exact hg.trans (Nat.add_le_add hs (Nat.mul_le_mul_left growth htime))

#print axioms itemClock_le
#print axioms state_length_le
end CurrentAdditive.FeatureAlphabetItemClock64
