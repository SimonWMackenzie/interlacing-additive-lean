import CurrentAdditive.GaussStateRowCount
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! The actual state-to-row-count machine fits on twenty-eight private banks
of the Gauss pivot scheduler. Four other banks remain free for the immutable
state packet, the count output, and the parser's control words. -/

namespace CurrentAdditive.GaussPivotCount32

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 32
noncomputable abbrev M := CurrentAdditive.GaussStateRowCount.machine

theorem stack_cap : M.stackCount ≤ 28 := by decide

noncomputable def slot (j : Fin M.stackCount) : Stack :=
  if h : j.val < 13 then ⟨j.val, by omega⟩
  else if h' : j.val < 27 then ⟨j.val + 1, by omega⟩
  else 29

theorem slot_injective : Function.Injective slot := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  have hc := stack_cap
  simp only [slot] at h
  split_ifs at h with h1 h2 h3 h4 <;>
    have hv := congrArg Fin.val h <;>
    simp at hv <;>
    apply Fin.ext <;> omega

noncomputable def embed : Fin M.stackCount ↪ Stack where
  toFun := slot
  inj' := slot_injective

theorem slot_not_13 (j : Fin M.stackCount) : slot j ≠ 13 := by
  have h := stack_cap
  have hj := j.isLt
  simp [slot]
  split_ifs <;> intro he <;> have hv := congrArg Fin.val he <;> simp at hv <;> omega

theorem slot_not_28 (j : Fin M.stackCount) : slot j ≠ 28 := by
  have h := stack_cap
  have hj := j.isLt
  simp [slot]
  split_ifs <;> intro he <;> have hv := congrArg Fin.val he <;> simp at hv <;> omega

theorem slot_not_30 (j : Fin M.stackCount) : slot j ≠ 30 := by
  have h := stack_cap
  have hj := j.isLt
  simp [slot]
  split_ifs <;> intro he <;> have hv := congrArg Fin.val he <;> simp at hv <;> omega

theorem slot_not_31 (j : Fin M.stackCount) : slot j ≠ 31 := by
  have h := stack_cap
  have hj := j.isLt
  simp [slot]
  split_ifs <;> intro he <;> have hv := congrArg Fin.val he <;> simp at hv <;> omega

abbrev Label := Fin M.labelCount ⊕ Unit
abbrev Control := Fin M.controlCount
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

noncomputable def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt embed Sum.inl id id
      (some (.inr ())) (M.program l)
  | .inr () => .halt

noncomputable def run (n : Nat) (c : Config) : Config := ((advance program)^[n]) c

theorem count_phase {m k : Nat} (s : CurrentAdditive.GaussControlTrace.State m k)
    (S : Stack → List Bool)
    (hS : ∀ j, S (slot j) = (M.init
      (CurrentAdditive.GaussControlTrace.statePacket s)).stk j) :
    ∃ t ≤ CurrentAdditive.GaussStateRowCount.polynomialClock
        (CurrentAdditive.GaussControlTrace.statePacket s).length,
      let out := M.run
        (CurrentAdditive.GaussStateRowCount.polynomialClock
          (CurrentAdditive.GaussControlTrace.statePacket s).length)
        (M.init (CurrentAdditive.GaussControlTrace.statePacket s))
      run t ⟨some (.inl M.start), M.initial, S⟩ =
        ⟨some (.inr ()), out.var,
          BitMachineStackEmbedding.bank embed S out.stk⟩ := by
  let input := CurrentAdditive.GaussControlTrace.statePacket s
  let bound := CurrentAdditive.GaussStateRowCount.polynomialClock input.length
  let c := M.init input
  have hout := BitMachine.outputsWithin_at_bound M
    (CurrentAdditive.GaussStateRowCount.outputs_polynomial s)
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs
    embed S Sum.inl id id (by intro v; rfl) (some (.inr ()))
    M.program program (by intro l; rfl) c bound hout.1
  refine ⟨t, ht, ?_⟩
  change run t (BitMachineStackEmbedding.cfg embed S Sum.inl id
    (some (.inr ())) c) = _ at he
  have hstart : BitMachineStackEmbedding.cfg embed S Sum.inl id
      (some (.inr ())) c = ⟨some (.inl M.start), M.initial, S⟩ := by
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
    congr 1
    exact BitMachineStackEmbedding.bank_eq_self embed S _
      (fun j => (hS j).symm)
  rw [hstart] at he
  have hrun : ((advance M.program)^[bound] c) = M.run bound c := rfl
  rw [hrun] at he
  simpa only [BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    hout.1, input, bound, c] using he

theorem count_output {m k : Nat}
    (s : CurrentAdditive.GaussControlTrace.State m k)
    (S : Stack → List Bool) :
    (BitMachineStackEmbedding.bank embed S
      (M.run (CurrentAdditive.GaussStateRowCount.polynomialClock
        (CurrentAdditive.GaussControlTrace.statePacket s).length)
        (M.init (CurrentAdditive.GaussControlTrace.statePacket s))).stk)
      (slot M.output) = List.replicate m true := by
  change BitMachineStackEmbedding.bank embed S _ (embed M.output) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact (BitMachine.outputsWithin_at_bound M
    (CurrentAdditive.GaussStateRowCount.outputs_polynomial s)).2

theorem ambient_preserved {m k : Nat}
    (s : CurrentAdditive.GaussControlTrace.State m k)
    (S : Stack → List Bool) (j : Stack)
    (hj : j = 13 ∨ j = 28 ∨ j = 30 ∨ j = 31) :
    (BitMachineStackEmbedding.bank embed S
      (M.run (CurrentAdditive.GaussStateRowCount.polynomialClock
        (CurrentAdditive.GaussControlTrace.statePacket s).length)
        (M.init (CurrentAdditive.GaussControlTrace.statePacket s))).stk) j = S j := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨q, hq⟩
  rcases hj with rfl | rfl | rfl | rfl
  · exact slot_not_13 q hq
  · exact slot_not_28 q hq
  · exact slot_not_30 q hq
  · exact slot_not_31 q hq

#print axioms count_phase
#print axioms count_output
#print axioms ambient_preserved

end CurrentAdditive.GaussPivotCount32
