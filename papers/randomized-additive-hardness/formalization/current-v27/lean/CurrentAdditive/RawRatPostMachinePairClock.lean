import CurrentAdditive.RawRatPostMachinePair

namespace CurrentAdditive.RawRatPostMachinePair

open Turing EthInapproximability.CurrentPaper BitMachineEncoding

theorem saved_length_bound (M : BitMachine.Machine)
    (s : Fin M.stackCount) (input : List Bool) (T : Nat) :
    ((M.run T (M.init input)).stk s).length ≤
      input.length + T * M.pushBound := by
  have hr := BitMachine.run_length M (M.init input) s T
  have hi : ((M.init input).stk s).length ≤ input.length := by
    simp only [BitMachine.Machine.init]
    split <;> simp
  exact hr.trans (Nat.add_le_add_right hi _)

theorem post_outputs_input_clock (M : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output)
    (input q saved : List Bool) (T : Nat)
    (hM : M.OutputsWithin input q T)
    (hsv : (M.run T (M.init input)).stk s = saved) :
    ∃ t ≤ T + 6*(2*(input.length + T*M.pushBound)+2)+1,
      let c := ((advance (program M s hs))^[t])
        (⟨some (BitMachineRawSequence.leftLabel M.start),
          (M.initial,asmInitial), initialBank M input⟩ :
          TM2.Cfg (fun _ : Stack M => Bool) _ _)
      c.l = none ∧
      c.stk (.inr 4) = RawRatPairAssembler.pairWord q saved ∧
      c.stk (.inl M.output) = q ∧ c.stk (.inl s) = saved ∧
      (∀ j : Fin M.stackCount, j ≠ M.output → j ≠ s →
        c.stk (.inl j) = (M.run T (M.init input)).stk j) := by
  obtain ⟨t,ht,hr⟩ := post_outputs M s hs input q saved T hM hsv
  have hq := BitMachine.output_length_bound M hM
  have hsave := saved_length_bound M s input T
  rw [hsv] at hsave
  refine ⟨t, ?_, hr⟩
  omega

theorem input_clock_polynomial (n c d B : Nat) :
    c*(n+1)^d + 6*(2*(n+c*(n+1)^d*B)+2)+1 ≤
      (13+c*(12*B+1))*(n+1)^(d+1) := by
  let p := (n+1)^(d+1)
  have hb : 1 ≤ (n+1)^d := by
    have hbase : 0 < n+1 := by omega
    exact pow_pos hbase d
  have hn : n+1 ≤ p := by
    calc
      n+1 = (n+1)*1 := by omega
      _ ≤ (n+1)*(n+1)^d := Nat.mul_le_mul_left _ hb
      _ = p := by simp [p, pow_succ, Nat.mul_comm]
  have hbp : (n+1)^d ≤ p := by
    calc
      (n+1)^d = (n+1)^d*1 := by omega
      _ ≤ (n+1)^d*(n+1) := Nat.mul_le_mul_left _ (by omega)
      _ = p := by simp [p, pow_succ]
  have hcp := Nat.mul_le_mul_left c hbp
  have hterm := Nat.mul_le_mul_right (12*B+1) hcp
  have hp : 1 ≤ p := hb.trans hbp
  have hsmall : 12*n+13 ≤ 13*p := by omega
  calc
    c*(n+1)^d + 6*(2*(n+c*(n+1)^d*B)+2)+1
        = 12*n+13 + (c*(n+1)^d)*(12*B+1) := by ring
    _ ≤ 13*p + (c*p)*(12*B+1) := Nat.add_le_add hsmall hterm
    _ = (13+c*(12*B+1))*p := by ring
    _ = (13+c*(12*B+1))*(n+1)^(d+1) := rfl

theorem post_outputs_polynomial (M : BitMachine.Machine)
    (s : Fin M.stackCount) (hs : s ≠ M.output)
    (f : List Bool → List Bool) (c d : Nat)
    (hM : M.ComputesWithin f (fun n => c*(n+1)^d))
    (input : List Bool) :
    ∃ t ≤ (13+c*(12*M.pushBound+1))*(input.length+1)^(d+1),
      let out := f input
      let saved := (M.run (c*(input.length+1)^d) (M.init input)).stk s
      let cfg := ((advance (program M s hs))^[t])
        (⟨some (BitMachineRawSequence.leftLabel M.start),
          (M.initial,asmInitial), initialBank M input⟩ :
          TM2.Cfg (fun _ : Stack M => Bool) _ _)
      cfg.l = none ∧
      cfg.stk (.inr 4) = RawRatPairAssembler.pairWord out saved ∧
      cfg.stk (.inl M.output) = out ∧ cfg.stk (.inl s) = saved ∧
      (∀ j : Fin M.stackCount, j ≠ M.output → j ≠ s →
        cfg.stk (.inl j) =
          (M.run (c*(input.length+1)^d) (M.init input)).stk j) := by
  let T := c*(input.length+1)^d
  let saved := (M.run T (M.init input)).stk s
  obtain ⟨t,ht,hr⟩ := post_outputs_input_clock M s hs input (f input)
    saved T (hM input) rfl
  refine ⟨t, ht.trans ?_, ?_⟩
  · exact input_clock_polynomial input.length c d M.pushBound
  · simpa only [T, saved] using hr

#print axioms post_outputs_polynomial

end CurrentAdditive.RawRatPostMachinePair
