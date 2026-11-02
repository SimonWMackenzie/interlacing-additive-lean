import CurrentAdditive.GaussSearchClock

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace CurrentAdditive.GaussCallbackClock

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussRowZeroCallback
open CurrentAdditive.GaussListContext
open Turing
open BitMachineEncoding

abbrev Stack := Fin 32

theorem selectedLocal_length (pre : List (List Bool))
    (cell : List Bool) (suffix : List (List Bool))
    (j : Fin 10) :
    ((selectedLocal (SourceListEncoding.encode (pre ++ cell :: suffix))
      cell suffix) j).length ≤
      (SourceListEncoding.encode (pre ++ cell :: suffix)).length + 1 := by
  let xs := pre ++ cell :: suffix
  have hfield : (SourceListEncoding.fields suffix).length ≤
      (SourceListEncoding.encode xs).length := by
    have hs : xs = (pre ++ [cell]) ++ suffix := by
      simp [xs, List.append_assoc]
    rw [hs, SourceListEncoding.encode,
      IndexedV2Clock.fields_append]
    simp only [List.length_append]
    omega
  have hcell : cell.length ≤ (SourceListEncoding.encode xs).length := by
    have hm : cell ∈ xs := by simp [xs]
    have hl := IndexedV2Clock.fields_item_length_le xs cell hm
    simp only [SourceListEncoding.encode, List.length_append]
    omega
  have hxs : (SourceListEncoding.encode xs).length =
      (SourceListEncoding.encode (pre ++ cell :: suffix)).length := rfl
  fin_cases j <;> simp [selectedLocal] <;> omega

theorem selectedAfter_preclear_length
    (pre : List (List Bool)) (cell : List Bool)
    (suffix : List (List Bool)) (B : Stack → List Bool)
    (hB : ∀ k : Stack, 24 ≤ k.val → k.val < 30 → B k = [])
    (i : Fin 14) :
    ((selectedAfter B pre cell suffix) (preclearBank i)).length ≤
      (SourceListEncoding.encode (pre ++ cell :: suffix)).length + 1 := by
  by_cases hslot : ∃ j : Fin 10, cellSlot j = preclearBank i
  · obtain ⟨j, hj⟩ := hslot
    rw [← hj]
    unfold selectedAfter
    rw [BitMachineStackEmbedding.bank_at]
    exact selectedLocal_length pre cell suffix j
  · have hsmall : 24 ≤ (preclearBank i).val := by
      fin_cases i <;>
        first | exact False.elim (hslot (by decide)) | decide
    have hlarge : (preclearBank i).val < 30 := by
      fin_cases i <;> decide
    unfold selectedAfter
    rw [BitMachineStackEmbedding.bank_outside cellSlot B _ _ hslot]
    rw [hB _ hsmall hlarge]
    simp

theorem broadcast_scratch (pre : List (List Bool))
    (S : Stack → List Bool)
    (hS : ∀ k : Stack, 24 ≤ k.val → k.val < 30 → S k = [])
    (k : Stack) (hk : 24 ≤ k.val) (hu : k.val < 30) :
    (SourceClausePreservingBroadcast.result 12 24 [23]
      (List.replicate pre.length true) S) k = [] := by
  have h12 : k ≠ 12 := by intro h; have hv := congrArg Fin.val h; omega
  have h23 : k ≠ 23 := by intro h; have hv := congrArg Fin.val h; omega
  by_cases h24 : k = 24
  · subst k
    simp [SourceClausePreservingBroadcast.result]
  · simp [SourceClausePreservingBroadcast.result,
      BitMachineBroadcast.prepend, h12, h23, h24, hS k hk hu]

theorem selectedAfter_preclear_sum (pre : List (List Bool))
    (cell : List Bool) (suffix : List (List Bool))
    (S : Stack → List Bool)
    (hS : ∀ k : Stack, 24 ≤ k.val → k.val < 30 → S k = []) :
    let B := SourceClausePreservingBroadcast.result 12 24 [23]
      (List.replicate pre.length true) S
    let C := selectedAfter B pre cell suffix
    (∑ i : Fin 14, (C (preclearBank i)).length) ≤
      14 * ((SourceListEncoding.encode (pre ++ cell :: suffix)).length + 1) := by
  dsimp only
  have hB := broadcast_scratch pre S hS
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i (_ : i ∈ Finset.univ) =>
      selectedAfter_preclear_length pre cell suffix _ hB i)
  simpa using hsum

theorem selectedAfter_clear_length
    (pre : List (List Bool)) (cell : List Bool)
    (suffix : List (List Bool)) (B : Stack → List Bool)
    (hB : ∀ k : Stack, 24 ≤ k.val → k.val < 30 → B k = [])
    (i : Fin 15) :
    ((selectedAfter B pre cell suffix) (clearBank i)).length ≤
      (SourceListEncoding.encode (pre ++ cell :: suffix)).length + 1 := by
  by_cases hslot : ∃ j : Fin 10, cellSlot j = clearBank i
  · obtain ⟨j, hj⟩ := hslot
    rw [← hj]
    unfold selectedAfter
    rw [BitMachineStackEmbedding.bank_at]
    exact selectedLocal_length pre cell suffix j
  · have hsmall : 24 ≤ (clearBank i).val := by
      fin_cases i <;>
        first | exact False.elim (hslot (by decide)) | decide
    have hlarge : (clearBank i).val < 30 := by
      fin_cases i <;> decide
    unfold selectedAfter
    rw [BitMachineStackEmbedding.bank_outside cellSlot B _ _ hslot]
    rw [hB _ hsmall hlarge]
    simp

theorem cleared_length_le {n : Nat} (bank : Fin n → Stack)
    (S : Stack → List Bool) (k : Stack) :
    ((BitMachineClearBank.cleared bank S) k).length ≤ (S k).length := by
  unfold BitMachineClearBank.cleared
  split <;> simp

theorem zero_run_length (cell : List Bool)
    (j : Fin Z.stackCount) :
    ((Z.run (GaussRawZeroCheck.clock cell) (Z.init cell)).stk j).length ≤
      cell.length + 14 * (cell.length + 1) * Z.pushBound := by
  have hg := BitMachine.run_length Z (Z.init cell) j
    (GaussRawZeroCheck.clock cell)
  have hi : ((Z.init cell).stk j).length ≤ cell.length := by
    simp only [BitMachine.Machine.init]
    split <;> simp
  have ht := GaussRawZeroCheck.clock_le_linear cell
  nlinarith

theorem final_clear_length
    (pre : List (List Bool)) (cell : List Bool)
    (suffix : List (List Bool)) (B : Stack → List Bool)
    (hB : ∀ k : Stack, 24 ≤ k.val → k.val < 30 → B k = [])
    (i : Fin 15) :
    let C := selectedAfter B pre cell suffix
    let D := BitMachineClearBank.cleared preclearBank C
    let E := BitMachineStackEmbedding.bank zeroSlot D
      (Z.run (GaussRawZeroCheck.clock cell) (Z.init cell)).stk
    let b := !((GaussRawZeroCheck.numeratorWord cell).any id)
    let F := Function.update (Function.update E (zeroSlot Z.output) [])
      9 ((!b) :: E 9)
    (F (clearBank i)).length ≤
      (SourceListEncoding.encode (pre ++ cell :: suffix)).length + 1 +
      (cell.length + 14 * (cell.length + 1) * Z.pushBound) := by
  dsimp only
  let C := selectedAfter B pre cell suffix
  let D := BitMachineClearBank.cleared preclearBank C
  let E := BitMachineStackEmbedding.bank zeroSlot D
    (Z.run (GaussRawZeroCheck.clock cell) (Z.init cell)).stk
  have h9 : (clearBank i) ≠ 9 := by
    fin_cases i <;> decide
  rw [Function.update_of_ne h9]
  by_cases hout : clearBank i = zeroSlot Z.output
  · rw [hout]
    simp
  · rw [Function.update_of_ne hout]
    by_cases hslot : ∃ j : Fin Z.stackCount, zeroSlot j = clearBank i
    · obtain ⟨j, hj⟩ := hslot
      rw [← hj]
      change (E (zeroSlot j)).length ≤ _
      dsimp [E]
      rw [BitMachineStackEmbedding.bank_at]
      have hz := zero_run_length cell j
      omega
    · change (E (clearBank i)).length ≤ _
      dsimp [E]
      rw [BitMachineStackEmbedding.bank_outside zeroSlot D _ _ hslot]
      have hc := selectedAfter_clear_length pre cell suffix B hB i
      have hd := cleared_length_le preclearBank C (clearBank i)
      dsimp [D, C]
      dsimp [C] at hd
      omega

theorem final_clear_sum
    (pre : List (List Bool)) (cell : List Bool)
    (suffix : List (List Bool)) (B : Stack → List Bool)
    (hB : ∀ k : Stack, 24 ≤ k.val → k.val < 30 → B k = []) :
    let C := selectedAfter B pre cell suffix
    let D := BitMachineClearBank.cleared preclearBank C
    let E := BitMachineStackEmbedding.bank zeroSlot D
      (Z.run (GaussRawZeroCheck.clock cell) (Z.init cell)).stk
    let b := !((GaussRawZeroCheck.numeratorWord cell).any id)
    let F := Function.update (Function.update E (zeroSlot Z.output) [])
      9 ((!b) :: E 9)
    (∑ i : Fin 15, (F (clearBank i)).length) ≤
      15 * ((SourceListEncoding.encode (pre ++ cell :: suffix)).length + 1 +
        (cell.length + 14 * (cell.length + 1) * Z.pushBound)) := by
  dsimp only
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i (_ : i ∈ Finset.univ) => final_clear_length pre cell suffix B hB i)
  simpa using hsum

theorem callbackCost_bound (pre : List (List Bool))
    (cell : List Bool) (suffix : List (List Bool))
    (S : Stack → List Bool)
    (hS : ∀ k : Stack, 24 ≤ k.val → k.val < 30 → S k = []) :
    callbackCost pre cell suffix S ≤
      1000 * (Z.pushBound + 1) *
        ((SourceListEncoding.encode (pre ++ cell :: suffix)).length + 1)^3 := by
  let Q := (SourceListEncoding.encode (pre ++ cell :: suffix)).length + 1
  let B := SourceClausePreservingBroadcast.result 12 24 [23]
    (List.replicate pre.length true) S
  have hcode := GaussSearchClock.cellCost_bound pre cell suffix
  have h14 := selectedAfter_preclear_sum pre cell suffix S hS
  have h15 := final_clear_sum pre cell suffix B
    (broadcast_scratch pre S hS)
  have hclock := GaussRawZeroCheck.clock_le_linear cell
  have hpre : pre.length ≤ Q := by
    have h := GaussSearchClock.rows_le_code (pre ++ cell :: suffix)
    have hp : pre.length ≤ (pre ++ cell :: suffix).length := by simp
    dsimp [Q]
    omega
  have hcell : cell.length ≤ Q := by
    have hm : cell ∈ pre ++ cell :: suffix := by simp
    have h := IndexedV2Clock.fields_item_length_le
      (pre ++ cell :: suffix) cell hm
    have hlen : (SourceListEncoding.fields (pre ++ cell :: suffix)).length ≤
        (SourceListEncoding.encode (pre ++ cell :: suffix)).length := by
      simp [SourceListEncoding.encode]
    dsimp [Q]
    omega
  have hcell' : cell.length + 1 ≤ 2 * Q := by omega
  have hpQ : 14 * (cell.length + 1) * Z.pushBound ≤
      28 * Q * Z.pushBound := by
    have hh : 14 * (cell.length + 1) ≤ 28 * Q := by omega
    exact Nat.mul_le_mul_right Z.pushBound hh
  have hQ : 1 ≤ Q := by dsimp [Q]; omega
  have hcube : Q ≤ Q^3 := by nlinarith [sq_nonneg ((Q : ℤ) - 1)]
  have hmul := Nat.mul_le_mul_left (900 * (Z.pushBound + 1)) hcube
  change (∑ i : Fin 14,
    ((selectedAfter B pre cell suffix) (preclearBank i)).length) ≤ 14 * Q at h14
  change (∑ i : Fin 15,
    ((Function.update
      (Function.update
        (BitMachineStackEmbedding.bank zeroSlot
          (BitMachineClearBank.cleared preclearBank
            (selectedAfter B pre cell suffix))
          (Z.run (GaussRawZeroCheck.clock cell) (Z.init cell)).stk)
        (zeroSlot Z.output) []) 9
      ((!(!(GaussRawZeroCheck.numeratorWord cell).any id)) ::
        (BitMachineStackEmbedding.bank zeroSlot
          (BitMachineClearBank.cleared preclearBank
            (selectedAfter B pre cell suffix))
          (Z.run (GaussRawZeroCheck.clock cell) (Z.init cell)).stk) 9))
      (clearBank i)).length) ≤
      15 * (Q + (cell.length + 14 * (cell.length + 1) * Z.pushBound)) at h15
  change GaussRowZeroCallback.cellCost pre cell suffix ≤ 50 * Q^3 at hcode
  have hraw : callbackCost pre cell suffix S ≤
      50 * Q^3 + 900 * (Z.pushBound + 1) * Q := by
    unfold callbackCost
    dsimp only
    nlinarith
  change callbackCost pre cell suffix S ≤
    1000 * (Z.pushBound + 1) * Q^3
  nlinarith

theorem typed_callback_time_bound {m k : Nat}
    (B : Fin m → Fin k → ℚ) (j : Fin k)
    (r : List Bool) (state : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool))
    (hsplit : pre ++ word :: suffix =
      CurrentAdditive.GaussTypedGetterBridge.rowWords B) :
    CurrentAdditive.GaussPivotTypedContract.time B j r state
      pre word suffix ≤
      1000 * (Z.pushBound + 1) *
        ((SourceListEncoding.encode
          (CurrentAdditive.GaussTypedGetterBridge.rowWords B)).length + 1)^3 := by
  open CurrentAdditive.GaussPivotTypedContract in
  let d := data B j pre word suffix r state hsplit
  obtain ⟨i, cellPre, cellSuffix, hlen, hword, ht⟩ := d.bound
  let cell := CurrentAdditive.CodeDCodec.encodeRawRat
    (CurrentAdditive.GaussPhysical.rawOfRat (B i j))
  let S := (CurrentAdditive.GaussPivotCallbackFrame.selected pre word suffix
    (GaussPivotTypedScan.reversed (CurrentAdditive.GaussPivotTypedRows.piece j.val) pre)
    (List.replicate j.val true) r state).stk
  have hS : ∀ x : Stack, 24 ≤ x.val → x.val < 30 → S x = [] := by
    intro x hx hu
    exact CurrentAdditive.GaussPivotCallbackFrame.selected_scratch
      pre word suffix _ _ r state x (by omega) hu
  have hcost := callbackCost_bound cellPre cell cellSuffix S hS
  have hwordLen : word.length ≤
      (SourceListEncoding.encode
        (CurrentAdditive.GaussTypedGetterBridge.rowWords B)).length := by
    have hm : word ∈ CurrentAdditive.GaussTypedGetterBridge.rowWords B := by
      rw [← hsplit]
      simp
    have hh := IndexedV2Clock.fields_item_length_le
      (CurrentAdditive.GaussTypedGetterBridge.rowWords B) word hm
    simp only [SourceListEncoding.encode, List.length_append]
    omega
  have hq : (SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)).length + 1 ≤
      (SourceListEncoding.encode
        (CurrentAdditive.GaussTypedGetterBridge.rowWords B)).length + 1 := by
    simpa only [cell, hword] using Nat.add_le_add_right hwordLen 1
  have hpow := Nat.pow_le_pow_left hq 3
  have hmul := Nat.mul_le_mul_left (1000 * (Z.pushBound + 1)) hpow
  change d.t ≤ callbackCost cellPre cell cellSuffix S at ht
  simpa only [CurrentAdditive.GaussPivotTypedContract.time,
    dif_pos hsplit, d] using ht.trans (hcost.trans hmul)

theorem selected_clean_length (pre : List (List Bool))
    (word : List Bool) (suffix : List (List Bool))
    (output context r state : List Bool) (i : Fin 10) :
    ((CurrentAdditive.GaussPivotCallbackFrame.selected
      pre word suffix output context r state).stk
      (LargeContextListScheduler.cleanBank i)).length ≤
      (SourceListEncoding.encode (pre ++ word :: suffix)).length + 1 := by
  let source := SourceListEncoding.encode (pre ++ word :: suffix)
  have hfields : (SourceListEncoding.fields suffix).length ≤ source.length := by
    have hs : pre ++ word :: suffix = (pre ++ [word]) ++ suffix := by
      simp [List.append_assoc]
    dsimp [source]
    rw [hs, SourceListEncoding.encode, IndexedV2Clock.fields_append]
    simp only [List.length_append]
    omega
  have hword : word.length ≤ source.length := by
    have hm : word ∈ pre ++ word :: suffix := by simp
    have hl := IndexedV2Clock.fields_item_length_le
      (pre ++ word :: suffix) word hm
    have hsrc : source.length =
        (SourceListEncoding.encode (pre ++ word :: suffix)).length := rfl
    simp only [SourceListEncoding.encode, List.length_append] at hsrc ⊢
    omega
  have hpre : pre.length ≤ source.length := by
    have hl := GaussSearchClock.rows_le_code (pre ++ word :: suffix)
    have hp : pre.length ≤ (pre ++ word :: suffix).length := by simp
    have hsrc : source.length =
        (SourceListEncoding.encode (pre ++ word :: suffix)).length := rfl
    omega
  have hsrc : source.length =
      (SourceListEncoding.encode (pre ++ word :: suffix)).length := rfl
  rw [← CurrentAdditive.GaussPivotCallbackPost.cleanToLocate_eq i]
  unfold CurrentAdditive.GaussPivotCallbackFrame.selected
  rw [LargeContextPreservingScan.frame_bank]
  change ((CylinderContextScanStep.selectedBank source
    (SourceListEncoding.fields suffix) word pre.length)
    (CurrentAdditive.GaussPivotCallbackPost.cleanToLocate i)).length ≤ _
  fin_cases i <;>
    simp [CurrentAdditive.GaussPivotCallbackPost.cleanToLocate,
      CylinderContextScanStep.selectedBank] <;> omega

theorem typed_callback_clean_sum_bound {m k : Nat}
    (B : Fin m → Fin k → ℚ) (j : Fin k)
    (r : List Bool) (state : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool))
    (hsplit : pre ++ word :: suffix =
      CurrentAdditive.GaussTypedGetterBridge.rowWords B) :
    let C := CurrentAdditive.GaussPivotTypedContract.contract B j r state
    (∑ i : Fin 10,
      ((C.state pre word suffix)
        (LargeContextListScheduler.cleanBank i)).length) ≤
      10 * ((SourceListEncoding.encode
        (CurrentAdditive.GaussTypedGetterBridge.rowWords B)).length + 1 +
        BitMachineStackGrowth.perStep GaussRowZeroCallback.program *
          (1000 * (Z.pushBound + 1) *
            ((SourceListEncoding.encode
              (CurrentAdditive.GaussTypedGetterBridge.rowWords B)).length + 1)^3)) := by
  let d := CurrentAdditive.GaussPivotTypedContract.data
    B j pre word suffix r state hsplit
  let S := (CurrentAdditive.GaussPivotCallbackFrame.selected pre word suffix
    (GaussPivotTypedScan.reversed (CurrentAdditive.GaussPivotTypedRows.piece j.val) pre)
    (List.replicate j.val true) r state).stk
  have ht := typed_callback_time_bound B j r state pre word suffix hsplit
  have htime : d.t ≤ 1000 * (Z.pushBound + 1) *
      ((SourceListEncoding.encode
        (CurrentAdditive.GaussTypedGetterBridge.rowWords B)).length + 1)^3 := by
    simpa only [CurrentAdditive.GaussPivotTypedContract.time,
      dif_pos hsplit, d] using ht
  have hbank : ∀ i : Fin 10,
      (d.T (LargeContextListScheduler.cleanBank i)).length ≤
      (SourceListEncoding.encode
        (CurrentAdditive.GaussTypedGetterBridge.rowWords B)).length + 1 +
        BitMachineStackGrowth.perStep GaussRowZeroCallback.program *
          (1000 * (Z.pushBound + 1) *
            ((SourceListEncoding.encode
              (CurrentAdditive.GaussTypedGetterBridge.rowWords B)).length + 1)^3) := by
    intro i
    let c : Turing.TM2.Cfg (fun _ : Fin 32 => Bool) _ _ :=
      ⟨some (GaussRowZeroCallback.bLabel .scan),
       GaussRowZeroCallback.bControl ((),none), S⟩
    have hg := BitMachineStackGrowth.run_growth
      GaussRowZeroCallback.program c d.t
      (LargeContextListScheduler.cleanBank i)
    have hr := d.run_eq
    change ((advance GaussRowZeroCallback.program)^[d.t]) c =
      ⟨none, d.v, d.T⟩ at hr
    rw [hr] at hg
    have hs := selected_clean_length pre word suffix
      (GaussPivotTypedScan.reversed
        (CurrentAdditive.GaussPivotTypedRows.piece j.val) pre)
      (List.replicate j.val true) r state i
    have hsrc : SourceListEncoding.encode (pre ++ word :: suffix) =
      SourceListEncoding.encode
        (CurrentAdditive.GaussTypedGetterBridge.rowWords B) := by rw [hsplit]
    rw [hsrc] at hs
    dsimp [c] at hg
    nlinarith
  dsimp only
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i (_ : i ∈ Finset.univ) => hbank i)
  have hsum' :
      (∑ i : Fin 10, (d.T (LargeContextListScheduler.cleanBank i)).length) ≤
        10 * ((SourceListEncoding.encode
          (CurrentAdditive.GaussTypedGetterBridge.rowWords B)).length + 1 +
          BitMachineStackGrowth.perStep GaussRowZeroCallback.program *
            (1000 * (Z.pushBound + 1) *
              ((SourceListEncoding.encode
                (CurrentAdditive.GaussTypedGetterBridge.rowWords B)).length + 1)^3)) := by
    simpa using hsum
  simpa only [CurrentAdditive.GaussPivotTypedContract.contract,
    CurrentAdditive.GaussPivotTypedContract.state, dif_pos hsplit, d] using hsum'

#print axioms selectedAfter_preclear_length
#print axioms selectedAfter_preclear_sum
#print axioms final_clear_sum
#print axioms callbackCost_bound
#print axioms typed_callback_time_bound
#print axioms typed_callback_clean_sum_bound

end CurrentAdditive.GaussCallbackClock
