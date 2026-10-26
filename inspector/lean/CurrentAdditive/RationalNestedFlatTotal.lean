import CurrentAdditive.RationalNestedFlatClosure

namespace EthInapproximability.CurrentPaper.RationalNestedFlatTotal

open RationalProductNestedFlat
open BitMachineBankCodec
open BitMachineEncoding
open Turing

def result (input : List Bool) : List Bool :=
  match decode 2 input with
  | none => []
  | some S =>
    match decode 3 (S 0), decode 3 (S 1) with
    | some X, some Y => BitMachineBankCodec.encode (stagingBank X Y)
    | _, _ => []

theorem initial_embed (input : List Bool) :
    cfg (some (outerLabel (.scan 0))) none (fun _ => []) input [] [] =
      BitMachineStackEmbedding.cfg outerSlots (fun _ => []) outerLabel id
        (some (adminLabel .afterOuter))
        (parserCfg (some (.scan 0)) none (fun _ => []) input [] []) := by
  unfold cfg BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  congr 1
  funext j
  by_cases h : ∃ k : BitMachineBankCodec.Stack 2, outerSlots k = j
  · obtain ⟨k,rfl⟩ := h
    rw [BitMachineStackEmbedding.bank_at]
    cases k with
    | inl k => fin_cases k <;> simp [outerSlots, parserCfg,
        BitMachineBankCodec.contents]
    | inr k => fin_cases k <;> simp [outerSlots, parserCfg,
        BitMachineBankCodec.contents]
  · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ h]
    cases j with
    | inl j => simp [BitMachineBankCodec.contents]
    | inr j => exact False.elim (h ⟨.inr j,rfl⟩)

theorem stage_length_le_input (input : List Bool)
    (S : Bank 2) (X Y : Bank 3)
    (h₀ : decode 2 input = some S)
    (h₁ : decode 3 (S 0) = some X)
    (h₂ : decode 3 (S 1) = some Y) :
    (BitMachineBankCodec.encode (stagingBank X Y)).length ≤ input.length := by
  have ho := BitMachineBankCodec.encode_decode h₀
  have hx := BitMachineBankCodec.encode_decode h₁
  have hy := BitMachineBankCodec.encode_decode h₂
  rw [← ho, BitMachineBankCodec.encode_length]
  rw [BitMachineBankCodec.encode_length]
  have hxlen : (S 0).length =
      2*(∑ i : Fin 3, (X i).length)+3 := by
    rw [← hx, BitMachineBankCodec.encode_length]
  have hylen : (S 1).length =
      2*(∑ i : Fin 3, (Y i).length)+3 := by
    rw [← hy, BitMachineBankCodec.encode_length]
  simp [stagingBank, Fin.sum_univ_succ] at hxlen hylen ⊢
  omega

theorem success_run (input : List Bool) (S : Bank 2) (X Y : Bank 3)
    (h₀ : decode 2 input = some S)
    (h₁ : decode 3 (S 0) = some X)
    (h₂ : decode 3 (S 1) = some Y) :
    ∃ t ≤ 40*(input.length+1),
      let c := run t (cfg (some (outerLabel (.scan 0))) none
        (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) =
        BitMachineBankCodec.encode (stagingBank X Y) := by
  obtain ⟨a,ha,ha'⟩ := parse_outer input S h₀
  obtain ⟨b,hb,hb'⟩ := parse_x S X h₁
  obtain ⟨c,hc,hc'⟩ := parse_y S X Y h₂
  obtain ⟨d,hd,hd₁,hd₂⟩ := serialize_stage S X Y
  refine ⟨a+1+b+1+c+1+d, ?_, ?_⟩
  · have hx := decoded_word_length h₀ (0 : Fin 2)
    have hy := decoded_word_length h₀ (1 : Fin 2)
    have hs := stage_length_le_input input S X Y h₀ h₁ h₂
    have hs' : (BitMachineBankSerialize.encode
        (List.ofFn (stagingBank X Y))).length ≤ input.length := by
      simpa [BitMachineBankSerialize.encode,
        BitMachineBankCodec.encode_eq_list] using hs
    omega
  · change (run (a+1+b+1+c+1+d) _).l = none ∧ _
    rw [run_add, run_add, run_add, run_add, run_add, run_add,
      initial_embed input, ha']
    have hs₀ : run 1 (outerState S) = xStart S := by
      simpa [run] using outer_to_x_start S
    have hs₁ : run 1 (xState S X) = yStart S X := by
      simpa [run] using x_to_y_start S X
    have hs₂ : run 1 (yState S X Y) = serStart S X Y := by
      simpa [run] using y_to_ser_start S X Y
    rw [hs₀,hb',hs₁,hc',hs₂]
    simpa [BitMachineBankCodec.encode_eq_list] using And.intro hd₁ hd₂

theorem admin_reject (a : Admin) (c : Config)
    (hl : c.l = some (adminLabel a)) (hv : c.var = some false)
    (ho : c.stk (.inr 2) = []) :
    (run 1 c).l = none ∧ (run 1 c).stk (.inr 2) = [] := by
  cases c with
  | mk l v S =>
      dsimp at hl hv ho
      subst l
      subst v
      cases a <;>
        simp [run, advance, program, adminLabel, TM2.step, TM2.stepAux, ho]

theorem outer_reject (input : List Bool)
    (hd : decode 2 input = none) :
    ∃ t ≤ 40*(input.length+1),
      let c := run t (cfg (some (outerLabel (.scan 0))) none
        (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) = [] := by
  obtain ⟨t,ht,hl,hv,ho⟩ := parser_embed_failure 2 outerSlots
    outerLabel (adminLabel .afterOuter) (by intro l; rfl)
    (fun _ => []) input hd
  let c := run t (cfg (some (outerLabel (.scan 0))) none
    (fun _ => []) input [] [])
  have hi : c = run t
      (BitMachineStackEmbedding.cfg outerSlots (fun _ => []) outerLabel id
        (some (adminLabel .afterOuter))
        (parserCfg (some (.scan 0)) none (fun _ => []) input [] [])) := by
    simp [c, initial_embed]
  have hr : (run 1 c).l = none ∧ (run 1 c).stk (.inr 2) = [] := by
    apply admin_reject .afterOuter c
    · simpa [hi] using hl
    · simpa [hi] using hv
    · simpa [hi, outerSlots] using ho
  refine ⟨t+1, by omega, ?_⟩
  simpa [run_add, c] using hr

theorem x_reject (input : List Bool) (S : Bank 2)
    (h₀ : decode 2 input = some S)
    (h₁ : decode 3 (S 0) = none) :
    ∃ t ≤ 40*(input.length+1),
      let c := run t (cfg (some (outerLabel (.scan 0))) none
        (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) = [] := by
  obtain ⟨a,ha,ha'⟩ := parse_outer input S h₀
  obtain ⟨b,hb,hl,hv,ho⟩ := parser_embed_failure 3 xSlots
    xLabel (adminLabel .afterX) (by intro l; rfl)
    (outerState S).stk (S 0) h₁
  let c := run b (xStart S)
  have hr : (run 1 c).l = none ∧ (run 1 c).stk (.inr 2) = [] := by
    apply admin_reject .afterX c
    · simpa [c, xStart] using hl
    · simpa [c, xStart] using hv
    · simpa [c, xStart, xSlots] using ho
  have hstep : run 1 (outerState S) = xStart S := by
    simpa [run] using outer_to_x_start S
  refine ⟨a+1+b+1, ?_, ?_⟩
  · have hs := decoded_word_length h₀ (0 : Fin 2)
    omega
  · change (run (a+1+b+1) _).l = none ∧ _
    rw [run_add, run_add, run_add, initial_embed input, ha', hstep]
    simpa [c] using hr

theorem y_reject (input : List Bool) (S : Bank 2) (X : Bank 3)
    (h₀ : decode 2 input = some S)
    (h₁ : decode 3 (S 0) = some X)
    (h₂ : decode 3 (S 1) = none) :
    ∃ t ≤ 40*(input.length+1),
      let c := run t (cfg (some (outerLabel (.scan 0))) none
        (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) = [] := by
  obtain ⟨a,ha,ha'⟩ := parse_outer input S h₀
  obtain ⟨b,hb,hb'⟩ := parse_x S X h₁
  obtain ⟨c,hc,hl,hv,ho⟩ := parser_embed_failure 3 ySlots
    yLabel (adminLabel .afterY) (by intro l; rfl)
    (xState S X).stk (S 1) h₂
  let d := run c (yStart S X)
  have hr : (run 1 d).l = none ∧ (run 1 d).stk (.inr 2) = [] := by
    apply admin_reject .afterY d
    · simpa [d, yStart] using hl
    · simpa [d, yStart] using hv
    · simpa [d, yStart, ySlots] using ho
  have hs₀ : run 1 (outerState S) = xStart S := by
    simpa [run] using outer_to_x_start S
  have hs₁ : run 1 (xState S X) = yStart S X := by
    simpa [run] using x_to_y_start S X
  refine ⟨a+1+b+1+c+1, ?_, ?_⟩
  · have hx := decoded_word_length h₀ (0 : Fin 2)
    have hy := decoded_word_length h₀ (1 : Fin 2)
    omega
  · change (run (a+1+b+1+c+1) _).l = none ∧ _
    rw [run_add, run_add, run_add, run_add, run_add,
      initial_embed input, ha', hs₀, hb', hs₁]
    simpa [d] using hr

theorem total_run (input : List Bool) :
    ∃ t ≤ 40*(input.length+1),
      let c := run t (cfg (some (outerLabel (.scan 0))) none
        (fun _ => []) input [] [])
      c.l = none ∧ c.stk (.inr 2) = result input := by
  cases h₀ : decode 2 input with
  | none =>
      obtain ⟨t,ht,hr⟩ := outer_reject input h₀
      exact ⟨t,ht,by simpa [result,h₀] using hr⟩
  | some S =>
      cases h₁ : decode 3 (S 0) with
      | none =>
          obtain ⟨t,ht,hr⟩ := x_reject input S h₀ h₁
          exact ⟨t,ht,by simpa [result,h₀,h₁] using hr⟩
      | some X =>
          cases h₂ : decode 3 (S 1) with
          | none =>
              obtain ⟨t,ht,hr⟩ := y_reject input S X h₀ h₁ h₂
              exact ⟨t,ht,by simpa [result,h₀,h₁,h₂] using hr⟩
          | some Y =>
              obtain ⟨t,ht,hr⟩ := success_run input S X Y h₀ h₁ h₂
              exact ⟨t,ht,by simpa [result,h₀,h₁,h₂] using hr⟩

theorem outputs (input : List Bool) :
    RationalProductNestedFlat.machine.OutputsWithin input (result input)
      (40*(input.length+1)) := by
  obtain ⟨t,ht,hh,ho⟩ := total_run input
  apply outputsWithin_of_raw_run (.inr 0 : Stack) (.inr 2)
    (outerLabel (.scan 0)) none program input (result input) t _ ht
  · simpa only [RationalNestedFlatClosure.initial_cfg, run] using hh
  · simpa only [RationalNestedFlatClosure.initial_cfg, run] using ho

theorem polytime : BitMachine.Polytime result := by
  refine ⟨RationalProductNestedFlat.machine,40,1,?_⟩
  intro input
  simpa only [pow_one] using outputs input

#print axioms outputs
#print axioms polytime

end EthInapproximability.CurrentPaper.RationalNestedFlatTotal
