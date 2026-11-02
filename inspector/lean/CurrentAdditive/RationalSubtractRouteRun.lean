import CurrentAdditive.RationalSubtractRoute

namespace EthInapproximability.CurrentPaper.RationalSubtractRouteRun

open Turing TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open RationalSubtractRoute

abbrev Bank := RationalSubtractCore.Bank

private theorem compose {L V : Type*} (P : L → TM2.Stmt (fun _ : Fin 32 => Bool) L V)
    {a b c : TM2.Cfg (fun _ : Fin 32 => Bool) L V} {m n : Nat}
    (hab : ((advance P)^[m]) a = b) (hbc : ((advance P)^[n]) b = c) :
    ((advance P)^[m+n]) a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, hab]
  exact hbc

private theorem preserve15 (phase : Fin 7) (S : Bank) :
    copied phase S 15 = S 15 := by
  apply bank_outside (copySlots phase) S _ 15
  fin_cases phase <;> decide

private theorem preserve_input (phase : Fin 7) (S : Bank)
    (j : Fin 32) (hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 6 ∨ j = 7 ∨ j = 8) :
    copied phase S j = S j := by
  by_cases hsrc : j = copySlots phase 0
  · subst j
    rw [copied, bank_at]
    rfl
  · apply bank_outside (copySlots phase) S _ j
    intro ⟨k, hk⟩
    fin_cases phase <;> fin_cases k <;>
      rcases hj with h | h | h | h | h | h <;>
      simp_all [copySlots]

private theorem preserve_sources (phase : Fin 7) (S : Bank) :
    copied phase S 0 = S 0 ∧ copied phase S 1 = S 1 ∧
    copied phase S 2 = S 2 ∧ copied phase S 6 = S 6 ∧
    copied phase S 7 = S 7 ∧ copied phase S 8 = S 8 := by
  exact ⟨preserve_input phase S 0 (by decide),
    preserve_input phase S 1 (by decide),
    preserve_input phase S 2 (by decide),
    preserve_input phase S 6 (by decide),
    preserve_input phase S 7 (by decide),
    preserve_input phase S 8 (by decide)⟩

private theorem source_bound (S : Bank) (j : Fin 32) :
    (S j).length ≤ (BitMachineBankCodec.encode S).length :=
  BitMachineBankCodec.word_length_le_encode S j

noncomputable def routed (S : Bank) : Bank :=
  let S₁ := copied 0 S
  let S₂ := copied 1 S₁
  let S₃ := copied 2 S₂
  let S₄ := copied 3 S₃
  let S₅ := copied 4 S₄
  let S₆ := copied 5 S₅
  let S₇ := copied 6 S₆
  BitMachineClearBank.cleared clearSlots
    (BitMachineBroadcast.contents (2 : Fin 32) 15 S₇ [] (S₇ 2).reverse)

theorem local_run (S : Bank) (h26 : S 26 = []) (h15 : S 15 = []) :
    ∃ t ≤ 21 * (BitMachineBankCodec.encode S).length + 40,
      ((advance program)^[t])
        (⟨some copyStart, initial, S⟩ :
          TM2.Cfg (fun _ : Fin 32 => Bool) Label Control) =
      ⟨none, initial, routed S⟩ := by
  let S₁ := copied 0 S
  let S₂ := copied 1 S₁
  let S₃ := copied 2 S₂
  let S₄ := copied 3 S₃
  let S₅ := copied 4 S₄
  let S₆ := copied 5 S₅
  let S₇ := copied 6 S₆
  obtain ⟨t₀, ht₀, h₀⟩ := copy_run 0 S h26
  obtain ⟨t₁, ht₁, h₁⟩ := copy_run 1 S₁ (copied_scratch 0 S)
  obtain ⟨t₂, ht₂, h₂⟩ := copy_run 2 S₂ (copied_scratch 1 S₁)
  obtain ⟨t₃, ht₃, h₃⟩ := copy_run 3 S₃ (copied_scratch 2 S₂)
  obtain ⟨t₄, ht₄, h₄⟩ := copy_run 4 S₄ (copied_scratch 3 S₃)
  obtain ⟨t₅, ht₅, h₅⟩ := copy_run 5 S₅ (copied_scratch 4 S₄)
  obtain ⟨t₆, ht₆, h₆⟩ := copy_run 6 S₆ (copied_scratch 5 S₅)
  have h15' : S₇ 15 = [] := by
    simp only [S₇, S₆, S₅, S₄, S₃, S₂, S₁, preserve15]
    exact h15
  have hs : ((advance program)^[(S₇ 2).length+1])
      (⟨some .reverseDen, initial, S₇⟩ :
        TM2.Cfg (fun _ : Fin 32 => Bool) Label Control) =
      ⟨some (.clear 0), initial,
        BitMachineBroadcast.contents (2 : Fin 32) 15 S₇ [] (S₇ 2).reverse⟩ := by
    have h := BitMachineBroadcast.scan_run program (2 : Fin 32) 15
      (by decide) .reverseDen (.clear 0) (by rfl) () none (S₇ 2) [] S₇
    have hc : BitMachineBroadcast.contents (2 : Fin 32) 15 S₇ (S₇ 2) [] = S₇ := by
      simp [BitMachineBroadcast.contents, h15']
    rw [hc] at h
    simpa only [BitMachineBroadcast.run, List.append_nil, initial] using h
  let T := BitMachineBroadcast.contents (2 : Fin 32) 15 S₇ [] (S₇ 2).reverse
  let ct := (∑ i : Fin 5, (T (clearSlots i)).length) + 6
  have hclear : ((advance program)^[ct])
      (⟨some (.clear 0), initial, T⟩ :
        TM2.Cfg (fun _ : Fin 32 => Bool) Label Control) =
      ⟨some .done, initial, BitMachineClearBank.cleared clearSlots T⟩ := by
    have h := BitMachineClearBank.clear_bank_run program id .done 5 clearSlots
      (by decide) Label.clear
      (by
        intro i
        simp [program, clearSlots]
        congr 1)
      (by simp [program, BitMachineClearBank.finishStep]) () T
    simpa only [ct, T, initial, id_eq] using h
  have hd : advance program
      (⟨some .done, initial, BitMachineClearBank.cleared clearSlots T⟩ :
        TM2.Cfg (fun _ : Fin 32 => Bool) Label Control) =
      ⟨none, initial, BitMachineClearBank.cleared clearSlots T⟩ := by
    rfl
  have hsum : ((advance program)^[t₀+t₁+t₂+t₃+t₄+t₅+t₆+((S₇ 2).length+1)+ct+1])
      (⟨some copyStart, initial, S⟩ :
        TM2.Cfg (fun _ : Fin 32 => Bool) Label Control) =
      ⟨none, initial, routed S⟩ := by
    have h₀₁ := compose program h₀ h₁
    have h₀₂ := compose program h₀₁ h₂
    have h₀₃ := compose program h₀₂ h₃
    have h₀₄ := compose program h₀₃ h₄
    have h₀₅ := compose program h₀₄ h₅
    have h₀₆ := compose program h₀₅ h₆
    have h₀₇ := compose program h₀₆ hs
    have h₀₈ := compose program h₀₇ hclear
    have h₀₉ := compose program h₀₈
      (show ((advance program)^[1])
        (⟨some .done, initial, BitMachineClearBank.cleared clearSlots T⟩ :
          TM2.Cfg (fun _ : Fin 32 => Bool) Label Control) =
        ⟨none, initial, BitMachineClearBank.cleared clearSlots T⟩
       from by simpa only [Function.iterate_one] using hd)
    simpa only [copyStart, routed, S₁, S₂, S₃, S₄, S₅, S₆, S₇, T] using h₀₉
  have hsrc :
      S₁ 0 = S 0 ∧ S₁ 1 = S 1 ∧ S₁ 2 = S 2 ∧ S₁ 6 = S 6 ∧
      S₁ 7 = S 7 ∧ S₁ 8 = S 8 := preserve_sources 0 S
  have hsrc₂ :
      S₂ 0 = S 0 ∧ S₂ 1 = S 1 ∧ S₂ 2 = S 2 ∧ S₂ 6 = S 6 ∧
      S₂ 7 = S 7 ∧ S₂ 8 = S 8 := by
    have h := preserve_sources 1 S₁
    simp only [hsrc.1, hsrc.2.1, hsrc.2.2.1,
      hsrc.2.2.2.1, hsrc.2.2.2.2.1, hsrc.2.2.2.2.2] at h
    exact h
  have hsrc₃ :
      S₃ 0 = S 0 ∧ S₃ 1 = S 1 ∧ S₃ 2 = S 2 ∧ S₃ 6 = S 6 ∧
      S₃ 7 = S 7 ∧ S₃ 8 = S 8 := by
    have h := preserve_sources 2 S₂
    simp only [hsrc₂.1, hsrc₂.2.1, hsrc₂.2.2.1,
      hsrc₂.2.2.2.1, hsrc₂.2.2.2.2.1, hsrc₂.2.2.2.2.2] at h
    exact h
  have hsrc₄ :
      S₄ 0 = S 0 ∧ S₄ 1 = S 1 ∧ S₄ 2 = S 2 ∧ S₄ 6 = S 6 ∧
      S₄ 7 = S 7 ∧ S₄ 8 = S 8 := by
    have h := preserve_sources 3 S₃
    simp only [hsrc₃.1, hsrc₃.2.1, hsrc₃.2.2.1,
      hsrc₃.2.2.2.1, hsrc₃.2.2.2.2.1, hsrc₃.2.2.2.2.2] at h
    exact h
  have hsrc₅ :
      S₅ 0 = S 0 ∧ S₅ 1 = S 1 ∧ S₅ 2 = S 2 ∧ S₅ 6 = S 6 ∧
      S₅ 7 = S 7 ∧ S₅ 8 = S 8 := by
    have h := preserve_sources 4 S₄
    simp only [hsrc₄.1, hsrc₄.2.1, hsrc₄.2.2.1,
      hsrc₄.2.2.2.1, hsrc₄.2.2.2.2.1, hsrc₄.2.2.2.2.2] at h
    exact h
  have hsrc₆ :
      S₆ 0 = S 0 ∧ S₆ 1 = S 1 ∧ S₆ 2 = S 2 ∧ S₆ 6 = S 6 ∧
      S₆ 7 = S 7 ∧ S₆ 8 = S 8 := by
    have h := preserve_sources 5 S₅
    simp only [hsrc₅.1, hsrc₅.2.1, hsrc₅.2.2.1,
      hsrc₅.2.2.2.1, hsrc₅.2.2.2.2.1, hsrc₅.2.2.2.2.2] at h
    exact h
  have hsrc₇ : S₇ 2 = S 2 := by
    exact (preserve_sources 6 S₆).2.2.1.trans hsrc₆.2.2.1
  have hb0 := source_bound S 0
  have hb1 := source_bound S 1
  have hb2 := source_bound S 2
  have hb6 := source_bound S 6
  have hb7 := source_bound S 7
  have hb8 := source_bound S 8
  refine ⟨_, ?_, hsum⟩
  change t₀ ≤ 2*(S 0).length+2 at ht₀
  change t₁ ≤ 2*(S₁ 6).length+2 at ht₁
  change t₂ ≤ 2*(S₂ 1).length+2 at ht₂
  change t₃ ≤ 2*(S₃ 7).length+2 at ht₃
  change t₄ ≤ 2*(S₄ 2).length+2 at ht₄
  change t₅ ≤ 2*(S₅ 8).length+2 at ht₅
  change t₆ ≤ 2*(S₆ 8).length+2 at ht₆
  rw [hsrc.2.2.2.1] at ht₁
  rw [hsrc₂.2.1] at ht₂
  rw [hsrc₃.2.2.2.2.1] at ht₃
  rw [hsrc₄.2.2.1] at ht₄
  rw [hsrc₅.2.2.2.2.2] at ht₅
  rw [hsrc₆.2.2.2.2.2] at ht₆
  rw [hsrc₇]
  have hct : ct ≤ 5 * (BitMachineBankCodec.encode S).length + 6 := by
    have hct' : ct = (T 0).length + (T 1).length + (T 6).length +
        (T 7).length + (T 8).length + 6 := by
      simp [ct, clearSlots, Fin.sum_univ_succ, Nat.add_assoc]
    rw [hct']
    have hT0 : T 0 = S 0 := by
      change S₇ 0 = S 0
      exact (preserve_sources 6 S₆).1.trans hsrc₆.1
    have hT1 : T 1 = S 1 := by
      change S₇ 1 = S 1
      exact (preserve_sources 6 S₆).2.1.trans hsrc₆.2.1
    have hT6 : T 6 = S 6 := by
      change S₇ 6 = S 6
      exact (preserve_sources 6 S₆).2.2.2.1.trans hsrc₆.2.2.2.1
    have hT7 : T 7 = S 7 := by
      change S₇ 7 = S 7
      exact (preserve_sources 6 S₆).2.2.2.2.1.trans hsrc₆.2.2.2.2.1
    have hT8 : T 8 = S 8 := by
      change S₇ 8 = S 8
      exact (preserve_sources 6 S₆).2.2.2.2.2.trans hsrc₆.2.2.2.2.2
    rw [hT0, hT1, hT6, hT7, hT8]
    omega
  omega

def precleared (S : Bank) : Bank :=
  BitMachineClearBank.cleared preSlots S

theorem preclear_run (S : Bank) :
    ((advance program)^[(S 15).length + (S 26).length + 3])
      (⟨some start, initial, S⟩ :
        TM2.Cfg (fun _ : Fin 32 => Bool) Label Control) =
      ⟨some copyStart, initial, precleared S⟩ := by
  have h := BitMachineClearBank.clear_bank_run program id copyStart 2 preSlots
    (by decide) Label.preclear
    (by
      intro i
      have hi : i.val ≤ 1 := Nat.lt_succ_iff.mp i.isLt
      simp [program, preSlots, hi]
      congr 1)
    (by simp [program, BitMachineClearBank.finishStep]) () S
  simpa [precleared, preSlots, Fin.sum_univ_succ, start, initial] using h

theorem precleared_15 (S : Bank) : precleared S 15 = [] := by
  simpa [precleared, preSlots] using
    BitMachineClearBank.cleared_bank preSlots S (0 : Fin 2)

theorem precleared_26 (S : Bank) : precleared S 26 = [] := by
  simpa [precleared, preSlots] using
    BitMachineClearBank.cleared_bank preSlots S (1 : Fin 2)

theorem precleared_eq (S : Bank) (h15 : S 15 = []) (h26 : S 26 = []) :
    precleared S = S := by
  funext j
  by_cases h : ∃ i : Fin 2, preSlots i = j
  · obtain ⟨i,hi⟩ := h
    subst j
    fin_cases i <;>
      simp [precleared, BitMachineClearBank.cleared, preSlots, h15, h26]
  · simp [precleared, BitMachineClearBank.cleared, h]

theorem precleared_size (S : Bank) :
    (BitMachineBankCodec.encode (precleared S)).length ≤
      (BitMachineBankCodec.encode S).length := by
  rw [BitMachineBankCodec.encode_length, BitMachineBankCodec.encode_length]
  have hsum : (∑ j : Fin 32, (precleared S j).length) ≤
      ∑ j : Fin 32, (S j).length := by
    apply Finset.sum_le_sum
    intro j _
    by_cases h : ∃ i : Fin 2, preSlots i = j
    · simp [precleared, BitMachineClearBank.cleared, h]
    · simp [precleared, BitMachineClearBank.cleared, h]
  omega

theorem full_run (S : Bank) :
    ∃ t ≤ 23 * (BitMachineBankCodec.encode S).length + 45,
      ((advance program)^[t])
        (⟨some start, initial, S⟩ :
          TM2.Cfg (fun _ : Fin 32 => Bool) Label Control) =
      ⟨none, initial, routed (precleared S)⟩ := by
  have hp := preclear_run S
  obtain ⟨tr,htr,hr⟩ := local_run (precleared S)
    (precleared_26 S) (precleared_15 S)
  have hrun := compose program hp hr
  have hsize := precleared_size S
  have h15 := BitMachineBankCodec.word_length_le_encode S (15 : Fin 32)
  have h26 := BitMachineBankCodec.word_length_le_encode S (26 : Fin 32)
  refine ⟨_, ?_, hrun⟩
  omega

end EthInapproximability.CurrentPaper.RationalSubtractRouteRun
