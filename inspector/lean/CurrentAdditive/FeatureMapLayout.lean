import CurrentAdditive.FeatureMapPairLoader
import CurrentAdditive.FeatureMapSourceScheduler
import CurrentAdditive.FeatureMapInputParser

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

/-! Canonical full-bank equalities for the generic contextual list map.
Only layout/cleanup facts are adapted from the checked ratio fold; no ratio
semantics or arithmetic callbacks are imported. -/

namespace CurrentAdditive.FeatureMapLayout

open EthInapproximability.CurrentPaper Turing BitMachineEncoding
open CurrentAdditive.GaussListContext
open CurrentAdditive.FeatureMapPairLoader

variable {N : Nat}
local notation "Stack" => StatefulListScheduler.StackN N
local notation "Bank" => StatefulListScheduler.StackN N → List Bool
local notation "low" => FeatureMapPairLoader.low (N := N)

@[simp] theorem castAdd_literal (j : Fin 32) :
    j.castAdd N = Fin.ofNat (32 + N) j.val := by
  apply Fin.ext
  simp [Fin.ofNat, Nat.mod_eq_of_lt (show j.val < 32 + N by have := j.isLt; omega)]

@[simp] theorem low_literal (j : Fin 32) : low j = (Fin.ofNat (32 + N) j.val : Stack) := by
  apply Fin.ext
  simp [FeatureMapPairLoader.low, Fin.ofNat, Nat.mod_eq_of_lt (show j.val < 32 + N by have := j.isLt; omega)]

@[simp] theorem small_mod (n : Nat) (hn : n < 32) :
    n % (32 + N) = n := Nat.mod_eq_of_lt (by omega)

noncomputable def blank : Bank := fun _ => []
local notation "blank" => blank (N := N)

noncomputable def boundary (source output context : List Bool)
    (index fuel : Nat) : Bank :=
  Function.update
    (StatefulListScheduler.initialBank source output context fuel blank)
    10 (List.replicate index true)
local notation "boundary" => boundary (N := N)

noncomputable def selected (source suffix word output context : List Bool)
    (index fuel : Nat) : Bank :=
  Function.update
    (Function.update
      (Function.update (boundary source output context index fuel)
        0 suffix)
      5 (List.replicate word.length true)) 6 word
local notation "selected" => selected (N := N)

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
      simp [CylinderContextScanStep.initial, CylinderContextScanStep.initialBank, FeatureMapLayout.boundary,
        StatefulListScheduler.initialBank, StatefulPreservingScan.locate,
        LargeContextPreservingScan.locate, FeatureMapLayout.blank, Function.update_apply,
        Fin.ext_iff, FeatureMapPairLoader.low, Fin.ofNat]
  · intro j hj
    have hh (k : CylinderContextScanStep.Stack) :
        j ≠ StatefulPreservingScan.locate k := by
      intro he; exact hj ⟨k, he.symm⟩
    have h8 : j ≠ (8 : Stack) := by simpa [StatefulPreservingScan.locate,
      LargeContextPreservingScan.locate] using hh 8
    have h10 : j ≠ (10 : Stack) := by simpa [StatefulPreservingScan.locate,
      LargeContextPreservingScan.locate] using hh 10
    simp [FeatureMapLayout.boundary, StatefulListScheduler.initialBank,
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
      simp [CylinderContextScanStep.selectedBank, FeatureMapLayout.selected, FeatureMapLayout.boundary,
        StatefulListScheduler.initialBank, StatefulPreservingScan.locate,
        LargeContextPreservingScan.locate, FeatureMapLayout.blank, Function.update_apply,
        Fin.ext_iff, FeatureMapPairLoader.low, Fin.ofNat]
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
    simp [FeatureMapLayout.selected, FeatureMapLayout.boundary, StatefulListScheduler.initialBank,
      StatefulListScheduler.foreignBank, Function.update_apply,
      h0, h5, h6, h8, h10]

theorem selected_six (source suffix word output context : List Bool)
    (index fuel : Nat) :
    selected source suffix word output context index fuel (low 6) = word := by
  simp [FeatureMapLayout.selected, Function.update_apply, Fin.ext_iff, FeatureMapPairLoader.low, Fin.ofNat]

theorem selected_nine (source suffix word output context : List Bool)
    (index fuel : Nat) :
    selected source suffix word output context index fuel (low 9) = output := by
  simp [FeatureMapLayout.selected, FeatureMapLayout.boundary, StatefulListScheduler.initialBank,
    Function.update_apply, Fin.ext_iff, FeatureMapPairLoader.low, Fin.ofNat]

theorem selected_high (source suffix word output context : List Bool)
    (index fuel : Nat) (j : Stack) (hj : 15 ≤ j.val) :
    selected source suffix word output context index fuel j = [] := by
  have hn (n : Nat) (hn : n < 15) :
      j ≠ Fin.ofNat (32 + N) n := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.ofNat, Fin.val_mk, Nat.mod_eq_of_lt (show n < 32 + N by omega)] at hh
    omega
  have h0 : j ≠ (0 : Stack) := hn 0 (by decide)
  have h5 : j ≠ (5 : Stack) := hn 5 (by decide)
  have h6 : j ≠ (6 : Stack) := hn 6 (by decide)
  have h8 : j ≠ (8 : Stack) := hn 8 (by decide)
  have h9 : j ≠ (9 : Stack) := hn 9 (by decide)
  have h10 : j ≠ (10 : Stack) := hn 10 (by decide)
  have h12 : j ≠ (12 : Stack) := hn 12 (by decide)
  have h13 : j ≠ (13 : Stack) := hn 13 (by decide)
  simp [FeatureMapLayout.selected, FeatureMapLayout.boundary, StatefulListScheduler.initialBank, FeatureMapLayout.blank,
    Function.update_of_ne, h0, h5, h6, h8, h9, h10, h12, h13]

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
        FeatureMapLayout.boundary, StatefulListScheduler.initialBank, Function.update_apply,
        Fin.ext_iff, Fin.ofNat, FeatureMapLayout.blank]
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
        Fin.ext_iff, FeatureMapPairLoader.low, Fin.ofNat]
  rw [cleared_update_outside _ _ _ _ h9]
  unfold FeatureMapLayout.selected
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
    simp [FeatureMapLayout.boundary, StatefulListScheduler.initialBank, Function.update_apply,
      Fin.ext_iff, FeatureMapPairLoader.low, Fin.ofNat]
  · simp [FeatureMapLayout.boundary, StatefulListScheduler.initialBank, Function.update_apply,
      low_literal, hj]

theorem increment_boundary (source output context : List Bool)
    (index fuel : Nat) :
    Function.update (boundary source output context index fuel) 10
      (true :: boundary source output context index fuel 10) =
    boundary source output context (index+1) fuel := by
  funext j
  by_cases hj : j = (10 : Stack)
  · subst j
    simp [FeatureMapLayout.boundary, List.replicate_succ]
  · simp [FeatureMapLayout.boundary, Function.update_of_ne, hj]


theorem cleared_prepared (S : Bank) (request : List Bool) :
    BitMachineClearBank.cleared StatefulListScheduler.cleanBank
      (Function.update (FeatureMapPairLoader.prepared S request) (low 5) []) =
    BitMachineClearBank.cleared StatefulListScheduler.cleanBank S := by
  have h5 : StatefulListScheduler.cleanBank (N := N) 5 = low 5 := by
    apply Fin.ext;simp [StatefulListScheduler.cleanBank,LargeContextListScheduler.cleanBank,FeatureMapPairLoader.low,Fin.ofNat]
  have h4 : StatefulListScheduler.cleanBank (N := N) 4 = low 4 := by
    apply Fin.ext;simp [StatefulListScheduler.cleanBank,LargeContextListScheduler.cleanBank,FeatureMapPairLoader.low,Fin.ofNat]
  have h6 : StatefulListScheduler.cleanBank (N := N) 6 = low 6 := by
    apply Fin.ext;simp [StatefulListScheduler.cleanBank,LargeContextListScheduler.cleanBank,FeatureMapPairLoader.low,Fin.ofNat]
  have h7 : StatefulListScheduler.cleanBank (N := N) 7 = low 7 := by
    apply Fin.ext;simp [StatefulListScheduler.cleanBank,LargeContextListScheduler.cleanBank,FeatureMapPairLoader.low,Fin.ofNat]
  unfold FeatureMapPairLoader.prepared
  rw [← h5,cleared_update_inside,← h4,cleared_update_inside,
    ← h6,cleared_update_inside,← h7,cleared_update_inside]

theorem cleanup_mapped (source suffix word output next context request : List Bool)
    (index fuel : Nat) :
    BitMachineClearBank.cleared StatefulListScheduler.cleanBank
      (Function.update
        (Function.update (FeatureMapPairLoader.prepared
          (selected source suffix word output context index fuel) request) (low 5) [])
        (low 9) next) = boundary source next context index fuel := by
  have h9 : ∀ i,StatefulListScheduler.cleanBank (N := N) i ≠ low 9 := by
    intro i;fin_cases i <;>
      simp [StatefulListScheduler.cleanBank,LargeContextListScheduler.cleanBank,
        FeatureMapPairLoader.low,Fin.ext_iff,Fin.ofNat]
  rw [cleared_update_outside _ _ _ _ h9,cleared_prepared,
    ← cleared_update_outside _ _ _ _ h9]
  exact cleanup_selected source suffix word output next context index fuel

#print axioms frame_initial
#print axioms frame_selected
#print axioms cleanup_mapped

theorem selected_five (source suffix word output context : List Bool)
    (index fuel : Nat) : selected source suffix word output context index fuel (low 5) =
      List.replicate word.length true := by
  have h5 : (low 5 : Stack) = 5 := by
    apply Fin.ext
    norm_num [FeatureMapPairLoader.low,Fin.ofNat,small_mod]
  rw [h5]
  norm_num [FeatureMapLayout.selected,Function.update_apply,Fin.ext_iff,Fin.ofNat,small_mod]

theorem cleanup_sum_generic (source suffix word output next context request : List Bool)
    (index fuel : Nat) :
    (∑ i : Fin 10, ((Function.update
      (Function.update (FeatureMapPairLoader.prepared
        (selected source suffix word output context index fuel) request) (low 5) [])
      (low 9) next) (StatefulListScheduler.cleanBank i)).length) =
      suffix.length+request.length := by
  have hi (i : Fin 10) :
      (Function.update
        (Function.update (FeatureMapPairLoader.prepared
          (selected source suffix word output context index fuel) request) (low 5) [])
        (low 9) next) (StatefulListScheduler.cleanBank i) =
        (if i=0 then suffix else if i=4 then request else []) := by
    fin_cases i <;>
      norm_num [FeatureMapPairLoader.prepared,FeatureMapLayout.selected,
        FeatureMapLayout.boundary,StatefulListScheduler.initialBank,FeatureMapLayout.blank,
        StatefulListScheduler.cleanBank,LargeContextListScheduler.cleanBank,
        Function.update_apply,FeatureMapPairLoader.low,Fin.ext_iff,Fin.ofNat,small_mod]
  simp_rw [hi]
  have hl (i : Fin 10) : (if i=0 then suffix else if i=4 then request else []).length =
      (if i=0 then suffix.length else 0)+(if i=4 then request.length else 0) := by
    by_cases h0:i=0
    · subst i
      have h04 : (0 : Fin 10) ≠ 4 := by decide
      simp [h04]
    · by_cases h4:i=4 <;> simp [h0,h4]
  simp_rw [hl]
  rw [Finset.sum_add_distrib]
  simp

theorem initialize_bank_eq (S : Bank) (context source header : List Bool) (fuel : Nat)
    (hs : Function.update S (low 15) [] = blank) :
    Function.update (Function.update (FeatureMapInputParser.output S context source)
      (low 13) (List.replicate fuel true)) (low 9) header =
      boundary source header context 0 fuel := by
  unfold FeatureMapInputParser.output
  rw [hs]
  funext k
  by_cases h8:k=low 8 <;> by_cases h9:k=low 9 <;>
    by_cases h12:k=low 12 <;> by_cases h13:k=low 13 <;> by_cases h10:k=low 10 <;>
    simp [FeatureMapLayout.boundary,StatefulListScheduler.initialBank,FeatureMapLayout.blank,
      Function.update_apply,FeatureMapPairLoader.low,Fin.ext_iff,Fin.ofNat] at * <;> simp_all

theorem boundary_nine (source output context : List Bool) (index fuel : Nat) :
    boundary source output context index fuel (low 9) = output := by
  have h9 : (low 9 : Stack) = 9 := by
    apply Fin.ext
    norm_num [FeatureMapPairLoader.low,Fin.ofNat,small_mod]
  rw [h9]
  norm_num [FeatureMapLayout.boundary,StatefulListScheduler.initialBank,
    Function.update_apply,Fin.ext_iff,Fin.ofNat,small_mod]

end CurrentAdditive.FeatureMapLayout
