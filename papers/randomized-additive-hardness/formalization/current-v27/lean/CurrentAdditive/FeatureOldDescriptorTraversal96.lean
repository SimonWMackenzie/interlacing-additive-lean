import CurrentAdditive.FeatureOldDescriptorFrame96

/-! The changing-count outer descriptor scan, constructed from the actual
guarded callback. Its final theorem has no callback/run premise. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 2048
namespace CurrentAdditive.FeatureOldDescriptorTraversal96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.Wide96ContextListScheduler
open CurrentAdditive.FeatureOldDescriptorFrame96
open CurrentAdditive.MovingContextScheduler96

structure Data where
  j : Nat
  ys : List Nat
  cs : List (List (Nat × Nat))
  qfuel : List Bool
  jUnary : List Bool
  carry : List Bool
  body : List Bool
  count : List Bool

def Data.original (D : Data) := words D.cs
def Data.piece (D : Data) := FeatureOldDescriptorFrame96.piece D.j D.ys
def Data.context (D : Data) := FeatureOldDescriptorFrame96.context D.count D.ys
def Data.extra (D : Data) := FeatureOldDescriptorFrame96.extra D.j D.ys D.qfuel D.jUnary D.carry

noncomputable def Data.selected (D : Data) (pre : List (List Bool))
    (word : List Bool) (suffix : List (List Bool)) : Fin 96 → List Bool :=
  FeatureOldDescriptorFrame96.selected D.j D.ys D.qfuel D.jUnary D.carry
    pre word suffix (D.body++joined D.piece pre) (D.context pre)

def Data.wordClock (D : Data) (pre : List (List Bool)) (word : List Bool) : Nat :=
  match CylinderFeatureCodec.decodeFeature word with
  | none => 0
  | some c => FeatureGuardedDescriptor96.clock D.j c D.ys
      (D.body++joined D.piece pre)

theorem descriptor_from_split (D : Data) (pre : List (List Bool))
    (word : List Bool) (suffix : List (List Bool))
    (hsplit : pre++word::suffix=D.original) :
    ∃ c∈D.cs, word=CylinderFeatureCodec.encodeFeature c := by
  have hm : word∈words D.cs := by
    change word∈D.original
    rw [← hsplit]
    simp
  obtain ⟨c,hc,he⟩ := List.mem_map.mp hm
  exact ⟨c,hc,he.symm⟩

theorem reachable (D : Data) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (hsplit : pre++word::suffix=D.original) :
    ∃ t≤D.wordClock pre word,
      let z := ((advance FeatureGuardedDescriptor96.program)^[t])
        (⟨some FeatureGuardedDescriptor96.start,FeatureGuardedDescriptor96.control,
          D.selected pre word suffix⟩ : TM2.Cfg (fun _ : Fin 96 => Bool) _ _)
      z.l=none ∧ z.stk 9=(D.body++joined D.piece pre)++D.piece word ∧
      z.stk 12=D.context (pre++[word]) ∧
      z.stk 8=SourceListEncoding.encode D.original ∧
      z.stk 10=List.replicate pre.length true ∧
      z.stk 13=List.replicate suffix.length true ∧
      (∀ k : Fin 96, 15≤k.val → z.stk k=D.extra k) := by
  obtain ⟨c,_,hw⟩ := descriptor_from_split D pre word suffix hsplit
  subst word
  let S := D.selected pre (CylinderFeatureCodec.encodeFeature c) suffix
  obtain ⟨h6,h8,h9,h10,h12,h13⟩ := selected_banks D.j D.ys D.qfuel D.jUnary D.carry
    pre (CylinderFeatureCodec.encodeFeature c) suffix
    (D.body++joined D.piece pre) (D.context pre)
  have he (k : Fin 96) (hk : 15≤k.val) : S k=D.extra k :=
    selected_extra D.j D.ys D.qfuel D.jUnary D.carry pre
      (CylinderFeatureCodec.encodeFeature c) suffix
      (D.body++joined D.piece pre) (D.context pre) k hk
  obtain ⟨t,ht,hh,ho,hc,hp,hclear⟩ := FeatureGuardedDescriptor96.run S D.j c D.ys
    (D.body++joined D.piece pre) (D.context pre)
    (by rw [he 30 (by decide)]; simp [Data.extra,extra]) h9 h12
    (by rw [he 15 (by decide)]; simp [Data.extra,extra])
    (by rw [he 31 (by decide)]; simp [Data.extra,extra]) h6
    (by rw [he 16 (by decide)]; simp [Data.extra,extra])
    (by
      intro k hklo hkhi
      rw [he k (by omega)]
      have h15 : k≠15 := by intro h; subst k; omega
      have h17 : k≠17 := by intro h; subst k; omega
      have h18 : k≠18 := by intro h; subst k; omega
      have h29 : k≠29 := by intro h; subst k; omega
      have h30 : k≠30 := by intro h; subst k; omega
      have h31 : k≠31 := by intro h; subst k; omega
      simp [Data.extra,extra,h15,h17,h18,h29,h30,h31])
    (by
      intro k hk
      rw [he k (by omega)]
      have h15 : k≠15 := by intro h; subst k; omega
      have h17 : k≠17 := by intro h; subst k; omega
      have h18 : k≠18 := by intro h; subst k; omega
      have h29 : k≠29 := by intro h; subst k; omega
      have h30 : k≠30 := by intro h; subst k; omega
      have h31 : k≠31 := by intro h; subst k; omega
      simp [Data.extra,extra,h15,h17,h18,h29,h30,h31])
  refine ⟨t,by simpa [Data.wordClock] using ht,hh,?_,?_,?_,?_,?_,?_⟩
  · by_cases hc : c.length<8192 <;>
      simpa [FeatureGuardedDescriptor96.output,Data.piece,piece,hc,S] using ho
  · rw [Data.context,context_step]
    simpa [countStep,eligible,FeatureGuardedDescriptor96.newCount] using hc
  · exact (hp 8 (by decide) (by decide) (by decide)).trans (h8.trans (by rw [hsplit]))
  · exact (hp 10 (by decide) (by decide) (by decide)).trans h10
  · exact (hp 13 (by decide) (by decide) (by decide)).trans h13
  · intro k hk
    by_cases hlo : k.val<32
    · exact (hp k hlo (by intro h; subst k; omega) (by intro h; subst k; omega)).trans (he k hk)
    · rw [hclear k (by omega)]
      have h15 : k≠15 := by intro h; subst k; omega
      have h17 : k≠17 := by intro h; subst k; omega
      have h18 : k≠18 := by intro h; subst k; omega
      have h29 : k≠29 := by intro h; subst k; omega
      have h30 : k≠30 := by intro h; subst k; omega
      have h31 : k≠31 := by intro h; subst k; omega
      simp [Data.extra,extra,h15,h17,h18,h29,h30,h31]

private def chosenTime (D : Data) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) : Nat :=
  if h : pre++word::suffix=D.original then Classical.choose (reachable D pre word suffix h) else 0

private def result (D : Data) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) :=
  ((advance FeatureGuardedDescriptor96.program)^[chosenTime D pre word suffix])
    (⟨some FeatureGuardedDescriptor96.start,FeatureGuardedDescriptor96.control,
      D.selected pre word suffix⟩ : TM2.Cfg (fun _ : Fin 96 => Bool) _ _)

private theorem result_spec (D : Data) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (hsplit : pre++word::suffix=D.original) :
    chosenTime D pre word suffix≤D.wordClock pre word ∧
    (result D pre word suffix).l=none ∧
    (result D pre word suffix).stk 9=(D.body++joined D.piece pre)++D.piece word ∧
    (result D pre word suffix).stk 12=D.context (pre++[word]) ∧
    (result D pre word suffix).stk 8=SourceListEncoding.encode D.original ∧
    (result D pre word suffix).stk 10=List.replicate pre.length true ∧
    (result D pre word suffix).stk 13=List.replicate suffix.length true ∧
    (∀ k : Fin 96, 15≤k.val → (result D pre word suffix).stk k=D.extra k) := by
  dsimp only [result,chosenTime]
  rw [dif_pos hsplit]
  exact Classical.choose_spec (reachable D pre word suffix hsplit)

def contract (D : Data) : MovingContextScheduler96.SourceCallbackContract
    FeatureGuardedDescriptor96.program FeatureGuardedDescriptor96.start
    FeatureGuardedDescriptor96.control D.piece D.body D.context D.original where
  extra := D.extra
  time := chosenTime D
  control := fun pre word suffix => (result D pre word suffix).var
  state := fun pre word suffix => (result D pre word suffix).stk
  callback_run := by
    intro pre word suffix hsplit
    have hh := (result_spec D pre word suffix hsplit).2.1
    have hz : result D pre word suffix=
        ⟨none,(result D pre word suffix).var,(result D pre word suffix).stk⟩ := by
      cases h : result D pre word suffix with
      | mk l v T => cases l with
        | none => rfl
        | some l => simp [h] at hh
    simpa only [result,Data.selected,FeatureOldDescriptorFrame96.selected,
      Data.extra,hsplit] using hz
  post := by
    intro pre word suffix hsplit
    obtain ⟨_,_,h9,h12,h8,h10,h13,he⟩ := result_spec D pre word suffix hsplit
    have hp := CylinderSchedulerPost96.callback_post pre word suffix
      (D.body++joined D.piece pre) (D.context (pre++[word])) D.extra
      (result D pre word suffix).stk (D.piece word)
      (by simpa only [hsplit] using h8) h9 h10 h12 h13 he
    simpa only [joined_append_one,List.append_assoc,hsplit] using hp

theorem time_le (D : Data) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (hsplit : pre++word::suffix=D.original) :
    (contract D).time pre word suffix≤D.wordClock pre word :=
  (result_spec D pre word suffix hsplit).1

theorem run (D : Data) :
    ∃ t≤MovingContextScheduler96.remainingBudget
      FeatureGuardedDescriptor96.program FeatureGuardedDescriptor96.start
      FeatureGuardedDescriptor96.control D.piece D.body D.context D.original
      (contract D) [] D.original,
      ∃ v,
      Wide96ContextListScheduler.run FeatureGuardedDescriptor96.program
        FeatureGuardedDescriptor96.start FeatureGuardedDescriptor96.control t
        ⟨some (.inr (.inr .check)),
          Wide96ContextListScheduler.getterControl FeatureGuardedDescriptor96.control
            (CylinderContextScanStep.copyControl ((),none)),
          (Wide96ContextPreservingScan.frame
            (foreignBank D.body (D.context []) D.original.length D.extra)
            (CylinderContextScanStep.initial (SourceListEncoding.encode D.original) 0)).stk⟩ =
        ⟨none,v,(Wide96ContextPreservingScan.frame
          (foreignBank (D.body++joined D.piece D.original)
            (D.context D.original) 0 D.extra)
          (CylinderContextScanStep.initial (SourceListEncoding.encode D.original)
            D.original.length)).stk⟩ := by
  classical
  have h := MovingContextScheduler96.run_remaining
    FeatureGuardedDescriptor96.program FeatureGuardedDescriptor96.start
    FeatureGuardedDescriptor96.control D.piece D.body D.context D.original
    (contract D) [] D.original (by simp)
    (Wide96ContextListScheduler.getterControl FeatureGuardedDescriptor96.control
      (CylinderContextScanStep.copyControl ((),none)))
  simpa only [List.nil_append,List.length_nil,joined,List.flatMap_nil,List.append_nil] using h

#print axioms contract
#print axioms run
end CurrentAdditive.FeatureOldDescriptorTraversal96
