import CurrentAdditive.RationalProductNestedFlat

namespace EthInapproximability.CurrentPaper.RationalNestedFlatClosure

open RationalProductNestedFlat
open BitMachineBankCodec
open BitMachineEncoding
open CurrentAdditive.CodeDCodec
open CurrentAdditive.CodeDPairProductTargetV2

theorem stage_eq_flat (x y : RawRat) :
    stagingBank (rawRatBank x) (rawRatBank y) = flatBank x y := by
  funext i
  fin_cases i <;> simp [stagingBank, flatBank, rawRatBank]

theorem flat_length_le_pair (x y : RawRat) :
    (flatBytes x y).length ≤ (pairBytes x y).length := by
  simp [flatBytes, pairBytes, pairBank, encodeRawRat,
    BitMachineBankCodec.encode_length, flatBank, rawRatBank,
    Fin.sum_univ_succ]
  omega

theorem pair_success (x y : RawRat) :
    ∃ t ≤ 5*((pairBytes x y).length+1) + 1 +
        7*((encodeRawRat x).length+1) + 1 +
        7*((encodeRawRat y).length+1) + 1 +
        2*(flatBytes x y).length+2,
      let c := run t
        (cfg (some (outerLabel (.scan 0))) none (fun _ => [])
          (pairBytes x y) [] [])
      c.l = none ∧ c.stk (.inr 2) = flatBytes x y := by
  let S := pairBank x y
  let X := rawRatBank x
  let Y := rawRatBank y
  have hd₀ : decode 2 (pairBytes x y) = some S := by
    simp [pairBytes, S]
  have hd₁ : decode 3 (S 0) = some X := by
    simp [S, pairBank, X, encodeRawRat]
  have hd₂ : decode 3 (S 1) = some Y := by
    simp [S, pairBank, Y, encodeRawRat]
  obtain ⟨a,ha,h₀⟩ := parse_outer (pairBytes x y) S hd₀
  obtain ⟨b,hb,h₁⟩ := parse_x S X hd₁
  obtain ⟨c,hc,h₂⟩ := parse_y S X Y hd₂
  obtain ⟨d,hd,h₃,h₄⟩ := serialize_stage S X Y
  have hi : cfg (some (outerLabel (.scan 0))) none (fun _ => [])
      (pairBytes x y) [] [] =
      BitMachineStackEmbedding.cfg outerSlots (fun _ => []) outerLabel id
        (some (adminLabel .afterOuter))
        (BitMachineBankCodec.parserCfg (some (.scan 0)) none
          (fun _ => []) (pairBytes x y) [] []) := by
    unfold cfg BitMachineStackEmbedding.cfg
      BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
    congr 1
    funext j
    by_cases h : ∃ k : BitMachineBankCodec.Stack 2, outerSlots k = j
    · obtain ⟨k,rfl⟩ := h
      rw [BitMachineStackEmbedding.bank_at]
      cases k with
      | inl k => fin_cases k <;> simp [outerSlots, BitMachineBankCodec.parserCfg,
          BitMachineBankCodec.contents]
      | inr k => fin_cases k <;> simp [outerSlots, BitMachineBankCodec.parserCfg,
          BitMachineBankCodec.contents]
    · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ h]
      cases j with
      | inl j =>
          have h12 : j ≠ 12 := by
            intro he; subst j; exact h ⟨.inl 0,rfl⟩
          have h13 : j ≠ 13 := by
            intro he; subst j; exact h ⟨.inl 1,rfl⟩
          simp [BitMachineBankCodec.contents]
      | inr j =>
          exfalso
          exact h ⟨.inr j,rfl⟩
  refine ⟨a+1+b+1+c+1+d, ?_, ?_⟩
  · have hflat : BitMachineBankSerialize.encode (List.ofFn (stagingBank X Y)) =
        flatBytes x y := by
      rw [stage_eq_flat]
      simpa [flatBytes] using
        (BitMachineBankCodec.encode_eq_list (flatBank x y)).symm
    rw [hflat] at hd
    have hS₀ : S 0 = encodeRawRat x := by simp [S, pairBank]
    have hS₁ : S 1 = encodeRawRat y := by simp [S, pairBank]
    rw [hS₀] at hb
    rw [hS₁] at hc
    omega
  · change (run (a+1+b+1+c+1+d) _).l = none ∧ _
    rw [run_add, run_add, run_add, run_add, run_add, run_add, hi, h₀]
    have hstep₀ : run 1 (outerState S) = xStart S := by
      simpa [run] using outer_to_x_start S
    have hstep₁ : run 1 (xState S X) = yStart S X := by
      simpa [run] using x_to_y_start S X
    have hstep₂ : run 1 (yState S X Y) = serStart S X Y := by
      simpa [run] using y_to_ser_start S X Y
    rw [hstep₀, h₁, hstep₁, h₂, hstep₂]
    simpa [flatBytes, stage_eq_flat, BitMachineBankCodec.encode_eq_list] using
      And.intro h₃ h₄

theorem initial_cfg (input : List Bool) :
    rawInit (.inr 0 : Stack) (outerLabel (.scan 0)) none input =
      cfg (some (outerLabel (.scan 0))) none (fun _ => []) input [] [] := by
  unfold rawInit cfg BitMachineBankCodec.contents
  congr 1
  funext j
  cases j with
  | inl j => simp
  | inr j => fin_cases j <;> rfl

theorem pair_outputs (x y : RawRat) :
    machine.OutputsWithin (pairBytes x y) (flatBytes x y)
      (40*((pairBytes x y).length+1)) := by
  obtain ⟨t,ht,hh,ho⟩ := pair_success x y
  have hdecode : decode 2 (pairBytes x y) = some (pairBank x y) := by
    simp [pairBytes]
  have hx := BitMachineBankCodec.decoded_word_length hdecode (0 : Fin 2)
  have hy := BitMachineBankCodec.decoded_word_length hdecode (1 : Fin 2)
  have hX : (encodeRawRat x).length ≤ (pairBytes x y).length := by
    simpa [pairBank] using hx
  have hY : (encodeRawRat y).length ≤ (pairBytes x y).length := by
    simpa [pairBank] using hy
  have hf := flat_length_le_pair x y
  apply outputsWithin_of_raw_run (.inr 0 : Stack) (.inr 2)
    (outerLabel (.scan 0)) none program (pairBytes x y)
    (flatBytes x y) t _ (by omega)
  · simpa only [initial_cfg, run] using hh
  · simpa only [initial_cfg, run] using ho

#print axioms pair_outputs

end EthInapproximability.CurrentPaper.RationalNestedFlatClosure
