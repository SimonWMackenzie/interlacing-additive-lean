import CurrentAdditive.MinimumRatioCallbackSemantic
import CurrentAdditive.MinimumRatioFoldSemanticJoin
import CurrentAdditive.StatefulFoldClock

set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 100
set_option maxRecDepth 4096

/-! Selected v39 appendix support: a physical scan of every ordered ratio pair.
The concrete arithmetic callback is instantiated below, never assumed. -/

namespace CurrentAdditive.RatioPhysicalFold

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout CurrentAdditive.GaussListContext

noncomputable abbrev N := MinimumRatioCallbackLayout.extraCount

@[simp] theorem castAdd_literal (j : Fin 32) :
    j.castAdd extraCount = Fin.ofNat (32 + extraCount) j.val := by
  apply Fin.ext
  simp [Fin.ofNat, Nat.mod_eq_of_lt (show j.val < 32 + extraCount by have := j.isLt; omega)]

@[simp] theorem low_literal (j : Fin 32) : low j = (Fin.ofNat (32 + extraCount) j.val : Stack) := by
  apply Fin.ext
  simp [low, Fin.ofNat, Nat.mod_eq_of_lt (show j.val < 32 + extraCount by have := j.isLt; omega)]

@[simp] theorem small_mod (n : Nat) (hn : n < 32) :
    n % (32 + extraCount) = n := Nat.mod_eq_of_lt (by omega)

noncomputable def blank : Bank := fun _ => []

noncomputable def boundary (source output context : List Bool)
    (index fuel : Nat) : Bank :=
  Function.update
    (StatefulListScheduler.initialBank source output context fuel blank)
    10 (List.replicate index true)

noncomputable def selected (source suffix word output context : List Bool)
    (index fuel : Nat) : Bank :=
  Function.update
    (Function.update
      (Function.update (boundary source output context index fuel)
        0 suffix)
      5 (List.replicate word.length true)) 6 word

private theorem frame_eq (output context : List Bool) (fuel : Nat)
    (S : CylinderContextScanStep.Stack → List Bool) (target : Bank)
    (hat : ∀ j, S j = target (StatefulPreservingScan.locate j))
    (hout : ∀ j, (¬ ∃ k, StatefulPreservingScan.locate k = j) →
      StatefulListScheduler.foreignBank output context fuel blank j = target j) :
    (StatefulPreservingScan.frame
      (StatefulListScheduler.foreignBank output context fuel blank)
      (⟨none, CylinderContextScanStep.copyControl ((), none), S⟩ :
        CylinderContextScanStep.Config)).stk = target := by
  funext j
  by_cases hj : ∃ k, StatefulPreservingScan.locate k = j
  · obtain ⟨k, rfl⟩ := hj
    rw [StatefulPreservingScan.frame_bank]
    exact hat k
  · rw [StatefulPreservingScan.frame_foreign _ _ _ hj]
    exact hout j hj

theorem frame_initial (source output context : List Bool)
    (index fuel : Nat) :
    (StatefulPreservingScan.frame
      (StatefulListScheduler.foreignBank output context fuel blank)
      (CylinderContextScanStep.initial source index)).stk =
      boundary source output context index fuel := by
  apply frame_eq
  · intro j
    fin_cases j <;>
      simp [CylinderContextScanStep.initial, CylinderContextScanStep.initialBank, boundary,
        StatefulListScheduler.initialBank, StatefulPreservingScan.locate,
        LargeContextPreservingScan.locate, blank, Function.update_apply,
        Fin.ext_iff, low, Fin.ofNat]
  · intro j hj
    have hh (k : CylinderContextScanStep.Stack) :
        j ≠ StatefulPreservingScan.locate k := by
      intro he; exact hj ⟨k, he.symm⟩
    have h8 : j ≠ (8 : Stack) := by simpa [StatefulPreservingScan.locate,
      LargeContextPreservingScan.locate] using hh 8
    have h10 : j ≠ (10 : Stack) := by simpa [StatefulPreservingScan.locate,
      LargeContextPreservingScan.locate] using hh 10
    simp [boundary, StatefulListScheduler.initialBank,
      StatefulListScheduler.foreignBank, Function.update_apply, h8, h10]

theorem frame_selected (source suffix word output context : List Bool)
    (index fuel : Nat) :
    (StatefulPreservingScan.frame
      (StatefulListScheduler.foreignBank output context fuel blank)
      (⟨none,
       CylinderContextScanStep.getterControl
         (PreservingV2Program.v2Control
           (IndexedV2Program.indexControl
             (SourceListMachineFields.coreControl (some true, false), none))),
       CylinderContextScanStep.selectedBank source suffix word index⟩ :
        CylinderContextScanStep.Config)).stk =
      selected source suffix word output context index fuel := by
  apply frame_eq
  · intro j
    fin_cases j <;>
      simp [CylinderContextScanStep.selectedBank, selected, boundary,
        StatefulListScheduler.initialBank, StatefulPreservingScan.locate,
        LargeContextPreservingScan.locate, blank, Function.update_apply,
        Fin.ext_iff, low, Fin.ofNat]
  · intro j hj
    have hh (k : CylinderContextScanStep.Stack) :
        j ≠ StatefulPreservingScan.locate k := by
      intro he; exact hj ⟨k, he.symm⟩
    have h0 : j ≠ (0 : Stack) := by simpa [StatefulPreservingScan.locate,
      LargeContextPreservingScan.locate] using hh 0
    have h5 : j ≠ (5 : Stack) := by simpa [StatefulPreservingScan.locate,
      LargeContextPreservingScan.locate] using hh 5
    have h6 : j ≠ (6 : Stack) := by simpa [StatefulPreservingScan.locate,
      LargeContextPreservingScan.locate] using hh 6
    have h8 : j ≠ (8 : Stack) := by simpa [StatefulPreservingScan.locate,
      LargeContextPreservingScan.locate] using hh 8
    have h10 : j ≠ (10 : Stack) := by simpa [StatefulPreservingScan.locate,
      LargeContextPreservingScan.locate] using hh 10
    simp [selected, boundary, StatefulListScheduler.initialBank,
      StatefulListScheduler.foreignBank, Function.update_apply,
      h0, h5, h6, h8, h10]

theorem selected_six (source suffix word output context : List Bool)
    (index fuel : Nat) :
    selected source suffix word output context index fuel (low 6) = word := by
  simp [selected, Function.update_apply, Fin.ext_iff, low, Fin.ofNat]

theorem selected_nine (source suffix word output context : List Bool)
    (index fuel : Nat) :
    selected source suffix word output context index fuel (low 9) = output := by
  simp [selected, boundary, StatefulListScheduler.initialBank,
    Function.update_apply, Fin.ext_iff, low, Fin.ofNat]

theorem selected_high (source suffix word output context : List Bool)
    (index fuel : Nat) (j : Stack) (hj : 15 ≤ j.val) :
    selected source suffix word output context index fuel j = [] := by
  have hn (n : Nat) (hn : n < 15) :
      j ≠ Fin.ofNat (32 + extraCount) n := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.ofNat, Fin.val_mk, Nat.mod_eq_of_lt (show n < 32 + extraCount by omega)] at hh
    omega
  have h0 : j ≠ (0 : Stack) := hn 0 (by decide)
  have h5 : j ≠ (5 : Stack) := hn 5 (by decide)
  have h6 : j ≠ (6 : Stack) := hn 6 (by decide)
  have h8 : j ≠ (8 : Stack) := hn 8 (by decide)
  have h9 : j ≠ (9 : Stack) := hn 9 (by decide)
  have h10 : j ≠ (10 : Stack) := hn 10 (by decide)
  have h12 : j ≠ (12 : Stack) := hn 12 (by decide)
  have h13 : j ≠ (13 : Stack) := hn 13 (by decide)
  simp [selected, boundary, StatefulListScheduler.initialBank, blank,
    Function.update_of_ne, h0, h5, h6, h8, h9, h10, h12, h13]

theorem selected_scratch (source suffix word output context : List Bool)
    (index fuel : Nat) :
    MinimumRatioCallbackFull.ScratchEmpty
      (selected source suffix word output context index fuel) := by
  constructor
  · intro j hj
    apply selected_high
    simpa only [low, Fin.val_castAdd] using hj
  · intro j hj
    exact selected_high _ _ _ _ _ _ _ j (by omega)

private theorem cleared_update_inside {n : Nat} (b : Fin n → Stack)
    (S : Bank) (i : Fin n) (word : List Bool) :
    BitMachineClearBank.cleared b (Function.update S (b i) word) =
      BitMachineClearBank.cleared b S := by
  funext j
  by_cases hj : ∃ k, b k = j
  · simp [BitMachineClearBank.cleared, hj]
  · have hn : j ≠ b i := by intro he; exact hj ⟨i, he.symm⟩
    simp [BitMachineClearBank.cleared, hj, Function.update_of_ne hn]

private theorem cleared_update_outside {n : Nat} (b : Fin n → Stack)
    (S : Bank) (j : Stack) (word : List Bool)
    (hj : ∀ i, b i ≠ j) :
    BitMachineClearBank.cleared b (Function.update S j word) =
      Function.update (BitMachineClearBank.cleared b S) j word := by
  funext k
  by_cases hk : k = j
  · subst k
    simp [BitMachineClearBank.cleared, hj]
  · simp only [Function.update_of_ne hk, BitMachineClearBank.cleared]

private theorem cleanup_boundary (source output context : List Bool)
    (index fuel : Nat) :
    BitMachineClearBank.cleared StatefulListScheduler.cleanBank
      (boundary source output context index fuel) =
      boundary source output context index fuel := by
  funext j
  by_cases hj : ∃ i, StatefulListScheduler.cleanBank i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [BitMachineClearBank.cleared_bank]
    symm
    fin_cases i <;>
      simp [StatefulListScheduler.cleanBank, LargeContextListScheduler.cleanBank,
        boundary, StatefulListScheduler.initialBank, Function.update_apply,
        Fin.ext_iff, Fin.ofNat, blank]
  · simp [BitMachineClearBank.cleared, hj]

theorem cleanup_selected (source suffix word output next context : List Bool)
    (index fuel : Nat) :
    BitMachineClearBank.cleared StatefulListScheduler.cleanBank
      (Function.update (selected source suffix word output context index fuel)
        (low 9) next) = boundary source next context index fuel := by
  have h9 : ∀ i, StatefulListScheduler.cleanBank (N := N) i ≠ low 9 := by
    intro i
    fin_cases i <;>
      simp [StatefulListScheduler.cleanBank, LargeContextListScheduler.cleanBank,
        Fin.ext_iff, low, Fin.ofNat]
  rw [cleared_update_outside _ _ _ _ h9]
  unfold selected
  have h0 : StatefulListScheduler.cleanBank (N := N) 0 = (0 : Stack) := rfl
  have h5 : StatefulListScheduler.cleanBank (N := N) 5 = (5 : Stack) := by
    apply Fin.ext; simp [StatefulListScheduler.cleanBank,
      LargeContextListScheduler.cleanBank, Fin.ofNat]
  have h6 : StatefulListScheduler.cleanBank (N := N) 6 = (6 : Stack) := by
    apply Fin.ext; simp [StatefulListScheduler.cleanBank,
      LargeContextListScheduler.cleanBank, Fin.ofNat]
  rw [← h6, cleared_update_inside, ← h5, cleared_update_inside,
    ← h0, cleared_update_inside, cleanup_boundary]
  funext j
  by_cases hj : j = (9 : Stack)
  · subst j
    simp [boundary, StatefulListScheduler.initialBank, Function.update_apply,
      Fin.ext_iff, low, Fin.ofNat]
  · simp [boundary, StatefulListScheduler.initialBank, Function.update_apply,
      low_literal, hj]

theorem increment_boundary (source output context : List Bool)
    (index fuel : Nat) :
    Function.update (boundary source output context index fuel) 10
      (true :: boundary source output context index fuel 10) =
    boundary source output context (index+1) fuel := by
  funext j
  by_cases hj : j = (10 : Stack)
  · subst j
    simp [boundary, List.replicate_succ]
  · simp [boundary, Function.update_of_ne, hj]

noncomputable def selectedCut (context : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) : Bank :=
  selected (SourceListEncoding.encode (pre ++ word :: suffix))
    (SourceListEncoding.fields suffix) word
    (pre.foldl MinimumRatioStepSpec.step []) context pre.length suffix.length

noncomputable def callbackBound (S : Bank) (word best : List Bool) : Nat :=
  MinimumRatioCallbackPhysical.itemClock S word best +
    (∑ j : Fin 17,
      ((MinimumRatioCallbackPhysical.postItemBank S word best)
        (MinimumRatioExtraClear.extraBank j)).length) + 20

theorem cut_callback (context : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) :
    ∃ u ≤ callbackBound (selectedCut context pre word suffix) word
        (pre.foldl MinimumRatioStepSpec.step []),
      ((advance MinimumRatioCallbackPhysical.program)^[u])
        (⟨some MinimumRatioCallbackPhysical.start,
          MinimumRatioCallbackPhysical.control,
          selectedCut context pre word suffix⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, MinimumRatioCallbackPhysical.control,
          Function.update (selectedCut context pre word suffix) (low 9)
            (MinimumRatioStepSpec.step
              (pre.foldl MinimumRatioStepSpec.step []) word)⟩ := by
  exact MinimumRatioCallbackPhysical.callback_run _ word _
    (selected_six _ _ _ _ _ _ _)
    (selected_nine _ _ _ _ _ _ _)
    (selected_scratch _ _ _ _ _ _ _)

noncomputable def cutTime (context : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) : Nat :=
  Classical.choose (cut_callback context pre word suffix)

noncomputable def contract (context : List Bool) :
    StatefulListScheduler.CallbackContract
      MinimumRatioCallbackPhysical.program MinimumRatioCallbackPhysical.start
      MinimumRatioCallbackPhysical.control MinimumRatioStepSpec.step [] context where
  extra := blank
  time := cutTime context
  control := fun _ _ _ => MinimumRatioCallbackPhysical.control
  state := fun pre word suffix =>
    Function.update (selectedCut context pre word suffix) (low 9)
      (MinimumRatioStepSpec.step
        (pre.foldl MinimumRatioStepSpec.step []) word)
  callback_run := by
    intro pre word suffix
    have h := (Classical.choose_spec (cut_callback context pre word suffix)).2
    simpa only [frame_selected, selectedCut, StatefulListScheduler.folded]
      using h
  post := by
    intro pre word suffix
    simp only [selectedCut, cleanup_selected, increment_boundary,
      frame_initial, StatefulListScheduler.folded, List.foldl_append,
      List.foldl_cons, List.foldl_nil, List.length_append,
      List.length_singleton]

noncomputable def program :=
  StatefulListScheduler.program MinimumRatioCallbackPhysical.program
    MinimumRatioCallbackPhysical.start MinimumRatioCallbackPhysical.control

noncomputable def clock (context : List Bool) (xs : List (List Bool)) : Nat :=
  StatefulListScheduler.remainingBudget MinimumRatioCallbackPhysical.program
    MinimumRatioCallbackPhysical.start MinimumRatioCallbackPhysical.control
    MinimumRatioStepSpec.step [] context (contract context) [] xs

theorem runs (context : List Bool) (xs : List (List Bool)) :
    ∃ t ≤ clock context xs,
      ∃ v,
      ((advance program)^[t])
        (⟨some (.inr (.inr .check)),
          StatefulListScheduler.getterControl MinimumRatioCallbackPhysical.control
            (CylinderContextScanStep.copyControl ((), none)),
          boundary (SourceListEncoding.encode xs) [] context 0 xs.length⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, v,
          boundary (SourceListEncoding.encode xs)
            (xs.foldl MinimumRatioStepSpec.step []) context xs.length 0⟩ := by
  classical
  have h := StatefulListScheduler.run_remaining
    MinimumRatioCallbackPhysical.program MinimumRatioCallbackPhysical.start
    MinimumRatioCallbackPhysical.control MinimumRatioStepSpec.step [] context
    (contract context) [] xs
    (StatefulListScheduler.getterControl MinimumRatioCallbackPhysical.control
      (CylinderContextScanStep.copyControl ((), none)))
  simpa only [clock, program, StatefulListScheduler.run,
    StatefulListScheduler.folded, List.nil_append, List.foldl_nil,
    List.length_nil, contract, frame_initial] using h

def pairWords (xs : List (CodeDCodec.RawRat × CodeDCodec.RawRat)) :
    List (List Bool) :=
  xs.map (fun p => CodeDPairProductTargetV2.pairBytes p.1 p.2)

theorem fold_pairWords (xs : List (CodeDCodec.RawRat × CodeDCodec.RawRat))
    (hvalid : ∀ p ∈ xs, p.1.Valid ∧ p.2.Valid) (best : Option ℚ) :
    (pairWords xs).foldl MinimumRatioStepSpec.step
        (MinimumRatioStepSpec.bestPacket best) =
      MinimumRatioStepSpec.bestPacket
        (xs.foldl (fun b p =>
          MinimumRatioStepSpec.semanticStep b p.1.value p.2.value) best) := by
  induction xs generalizing best with
  | nil => rfl
  | cons p xs ih =>
      simp only [pairWords, List.map_cons, List.foldl_cons]
      rw [MinimumRatioStepSpec.step_pair _ _ _
        (hvalid p (by simp)).1 (hvalid p (by simp)).2]
      exact ih (by intro a ha; exact hvalid a (by simp [ha])) _

theorem exact_minimum_runs (weights coeff : Array ℚ) (context : List Bool) :
    let xs := pairWords (MinimumRatioFoldSemanticJoin.pairs weights coeff)
    ∃ t ≤ clock context xs,
      ∃ v,
      ((advance program)^[t])
        (⟨some (.inr (.inr .check)),
          StatefulListScheduler.getterControl MinimumRatioCallbackPhysical.control
            (CylinderContextScanStep.copyControl ((), none)),
          boundary (SourceListEncoding.encode xs) [] context 0 xs.length⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, v,
          boundary (SourceListEncoding.encode xs)
            (MinimumRatioStepSpec.bestPacket
              (SequentialCode.minimumRatio weights coeff))
            context xs.length 0⟩ := by
  dsimp only
  have he := fold_pairWords (MinimumRatioFoldSemanticJoin.pairs weights coeff)
    (MinimumRatioFoldSemanticJoin.pairs_valid weights coeff) none
  change (pairWords (MinimumRatioFoldSemanticJoin.pairs weights coeff)).foldl
      MinimumRatioStepSpec.step [] =
    MinimumRatioStepSpec.bestPacket
      (MinimumRatioFoldSemanticJoin.semanticFold
        (MinimumRatioFoldSemanticJoin.pairs weights coeff)) at he
  rw [MinimumRatioFoldSemanticJoin.semanticFold_eq_minimumRatio] at he
  simpa only [he] using runs context
    (pairWords (MinimumRatioFoldSemanticJoin.pairs weights coeff))

theorem cutTime_le (context : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) :
    cutTime context pre word suffix ≤
      callbackBound (selectedCut context pre word suffix) word
        (pre.foldl MinimumRatioStepSpec.step []) :=
  (Classical.choose_spec (cut_callback context pre word suffix)).1

/-- A clock expressed using actual item words and physical scratch contents.
It has no chosen run times, assumed callback bounds or assumed output values. -/
noncomputable def planClock (context : List Bool)
    (pre suffix : List (List Bool)) : Nat :=
  match suffix with
  | [] => 1
  | word :: tail =>
    1 + StatefulListScheduler.getterBudget pre word tail +
      callbackBound (selectedCut context pre word tail) word
        (pre.foldl MinimumRatioStepSpec.step []) +
      (∑ i : Fin 10,
        ((Function.update (selectedCut context pre word tail) (low 9)
          (MinimumRatioStepSpec.step
            (pre.foldl MinimumRatioStepSpec.step []) word))
          (StatefulListScheduler.cleanBank i)).length) + 15 +
      planClock context (pre ++ [word]) tail

theorem remaining_le_plan (context : List Bool)
    (pre suffix : List (List Bool)) :
    StatefulListScheduler.remainingBudget MinimumRatioCallbackPhysical.program
      MinimumRatioCallbackPhysical.start MinimumRatioCallbackPhysical.control
      MinimumRatioStepSpec.step [] context (contract context) pre suffix ≤
        planClock context pre suffix := by
  induction suffix generalizing pre with
  | nil => simp [StatefulListScheduler.remainingBudget, planClock]
  | cons word tail ih =>
      have ht := cutTime_le context pre word tail
      have hr := ih (pre ++ [word])
      simp only [contract] at hr
      simp only [StatefulListScheduler.remainingBudget,
        StatefulListScheduler.cycleBudget, StatefulListScheduler.folded,
        contract, planClock]
      omega

theorem exact_minimum_explicit_clock (weights coeff : Array ℚ)
    (context : List Bool) :
    let xs := pairWords (MinimumRatioFoldSemanticJoin.pairs weights coeff)
    ∃ t ≤ planClock context [] xs,
      ∃ v,
      ((advance program)^[t])
        (⟨some (.inr (.inr .check)),
          StatefulListScheduler.getterControl MinimumRatioCallbackPhysical.control
            (CylinderContextScanStep.copyControl ((), none)),
          boundary (SourceListEncoding.encode xs) [] context 0 xs.length⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, v,
          boundary (SourceListEncoding.encode xs)
            (MinimumRatioStepSpec.bestPacket
              (SequentialCode.minimumRatio weights coeff))
            context xs.length 0⟩ := by
  dsimp only
  obtain ⟨t, ht, v, hr⟩ := exact_minimum_runs weights coeff context
  exact ⟨t, ht.trans (remaining_le_plan context [] _), v, hr⟩

#print axioms exact_minimum_explicit_clock
#print axioms contract
#print axioms runs
#print axioms exact_minimum_runs

end CurrentAdditive.RatioPhysicalFold
