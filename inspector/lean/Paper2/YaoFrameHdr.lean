import Paper2.HeaderA

/-! Unit 5 segment Y8, part 1 (lane a-yao-owner-3): the EXACT exit bank of the
admitted header stage `Paper2.HeaderA.prog`.

The admitted `HeaderA.header_run` states only the output cell of the final
bank.  Here the whole final local bank is stated: every cell is empty except
the output cell, which holds `natField rows ++ natField cols ++ natField thr ++
table ++ suffix`.  The only new ingredient is `serialize3_exact`, the admitted
serializer `BitMachineBankSerialize.program 3` run with its consumed word bank
stated exactly (built from the admitted `emit_word`, `emit_end`,
`finish_run`); the three conversions are the admitted `HeaderA.conv_run`. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.YaoFrame

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.EncodedCommunication
open Paper2.HeaderA

/-- The admitted three-word serializer with its consumed word bank stated exactly. -/
theorem serialize3_exact (w0 w1 w2 source output : List Bool) :
    ∃ t ≤ 2 * (field w0 ++ field w1 ++ field w2).length + 2,
      BitMachineBankSerialize.run t
        (BitMachineBankSerialize.cfg (some (.emit 0)) none
          (![w0, w1, w2] : BitMachineBankSerialize.Bank 3) source [] output) =
        BitMachineBankSerialize.cfg none none (fun _ => []) source []
          (field w0 ++ field w1 ++ field w2 ++ output) := by
  let S : BitMachineBankSerialize.Bank 3 := ![w0, w1, w2]
  have e0 : BitMachineBankSerialize.run (w0.length + 1)
      (BitMachineBankSerialize.cfg (some (.emit 0)) none S source [] output) =
      BitMachineBankSerialize.cfg (some (.emit 1)) none (Function.update S 0 []) source
        ((field w0).reverse ++ []) output :=
    BitMachineBankSerialize.emit_word (0 : Fin 3) none S w0 source [] output rfl
  have e1 : BitMachineBankSerialize.run (w1.length + 1)
      (BitMachineBankSerialize.cfg (some (.emit 1)) none (Function.update S 0 []) source
        ((field w0).reverse ++ []) output) =
      BitMachineBankSerialize.cfg (some (.emit 2)) none
        (Function.update (Function.update S 0 []) 1 []) source
        ((field w1).reverse ++ ((field w0).reverse ++ [])) output :=
    BitMachineBankSerialize.emit_word (1 : Fin 3) none (Function.update S 0 []) w1 source
      _ output (by simp [S])
  have e2 : BitMachineBankSerialize.run (w2.length + 1)
      (BitMachineBankSerialize.cfg (some (.emit 2)) none
        (Function.update (Function.update S 0 []) 1 []) source
        ((field w1).reverse ++ ((field w0).reverse ++ [])) output) =
      BitMachineBankSerialize.cfg (some (.emit 3)) none
        (Function.update (Function.update (Function.update S 0 []) 1 []) 2 []) source
        ((field w2).reverse ++ ((field w1).reverse ++ ((field w0).reverse ++ []))) output :=
    BitMachineBankSerialize.emit_word (2 : Fin 3) none
      (Function.update (Function.update S 0 []) 1 []) w2 source _ output (by simp [S])
  have hclear : Function.update (Function.update (Function.update S 0 []) 1 []) 2 [] =
      (fun _ => []) := by
    funext j; fin_cases j <;> simp [S]
  rw [hclear] at e2
  set saved := (field w2).reverse ++ ((field w1).reverse ++ ((field w0).reverse ++ []))
    with hsaved
  have e3 : BitMachineBankSerialize.run 1
      (BitMachineBankSerialize.cfg (some (.emit 3)) none (fun _ => []) source saved output) =
      BitMachineBankSerialize.cfg (some .finish) none (fun _ => []) source saved output :=
    BitMachineBankSerialize.emit_end (K := 3) (fun _ => []) source saved output
  have e4 := BitMachineBankSerialize.finish_run none (fun _ => [] : BitMachineBankSerialize.Bank 3)
    source saved output
  have hsl : saved.length = (field w0 ++ field w1 ++ field w2).length := by
    simp [hsaved, List.length_append]; omega
  refine ⟨(w0.length + 1) + ((w1.length + 1) + ((w2.length + 1) + (1 + (saved.length + 1)))),
    ?_, ?_⟩
  · rw [hsl]
    simp only [List.length_append, field_length]
    omega
  · rw [BitMachineBankSerialize.run_add (w0.length + 1)
        ((w1.length + 1) + ((w2.length + 1) + (1 + (saved.length + 1)))), e0,
      BitMachineBankSerialize.run_add (w1.length + 1)
        ((w2.length + 1) + (1 + (saved.length + 1))), e1,
      BitMachineBankSerialize.run_add (w2.length + 1) (1 + (saved.length + 1)), e2,
      BitMachineBankSerialize.run_add 1 (saved.length + 1), e3, e4]
    congr 1
    simp [hsaved, List.reverse_append, List.append_assoc]

/-- The final local bank of the header stage: blank except the output cell. -/
def Hout (rows cols thr : ℕ) (table suffix : List Bool) : HB → List Bool :=
  fun k => if k = outH then natField rows ++ natField cols ++ natField thr ++ table ++ suffix
    else []

/-- The admitted header stage `HeaderA.prog` with its whole exit bank stated. -/
theorem header_run_exact (rows cols thr : ℕ) (table suffix : List Bool) :
    ∃ t ≤ UnaryBinaryEncoding.coefficient * (rows + 1) ^ 2 +
        UnaryBinaryEncoding.coefficient * (cols + 1) ^ 2 +
        UnaryBinaryEncoding.coefficient * (thr + 1) ^ 2 +
        (2 * (natField rows ++ natField cols ++ natField thr).length + 2) + 3,
      ((advance prog)^[t]) (⟨some progStart, progCtl, Hin rows cols thr table suffix⟩ :
          TM2.Cfg (fun _ : HB => Bool) _ _) =
        ⟨none, progCtl, Hout rows cols thr table suffix⟩ := by
  classical
  let S0 := Hin rows cols thr table suffix
  obtain ⟨t0, ht0, r0⟩ := conv_run 0 S0 (List.replicate rows true) rfl
    (by intro k hk; simp [S0, localSlots, hk, Hin])
  let S1 := Function.update (Function.update S0 (fuel 0) []) (binary 0)
    (List.replicate rows true).length.bits
  obtain ⟨t1, ht1, r1⟩ := conv_run 1 S1 (List.replicate cols true)
    (by simp [S1, S0, fuel, binary, Hin])
    (by intro k hk; simp [S1, S0, localSlots, hk, fuel, binary, Hin])
  let S2 := Function.update (Function.update S1 (fuel 1) []) (binary 1)
    (List.replicate cols true).length.bits
  obtain ⟨t2, ht2, r2⟩ := conv_run 2 S2 (List.replicate thr true)
    (by simp [S2, S1, S0, fuel, binary, Hin])
    (by intro k hk; simp [S2, S1, S0, localSlots, hk, fuel, binary, Hin])
  let S3 := Function.update (Function.update S2 (fuel 2) []) (binary 2)
    (List.replicate thr true).length.bits
  obtain ⟨t4, ht4, hr4⟩ := serialize3_exact rows.bits cols.bits thr.bits [] (table ++ suffix)
  have hin : ∀ k : MatrixInstanceEncoding.Stack,
      (MatrixInstanceEncoding.initial rows cols thr [] table suffix).stk k = S3 (headerSlots k) := by
    intro k
    rcases k with j | j
    · fin_cases j <;>
        simp [MatrixInstanceEncoding.initial, BitMachineBankSerialize.cfg,
          BitMachineBankSerialize.contents, MatrixInstanceEncoding.binaryBank, headerSlots,
          headerSlotsF, S3, S2, S1, S0, fuel, binary]
    · fin_cases j <;>
        simp [MatrixInstanceEncoding.initial, BitMachineBankSerialize.cfg,
          BitMachineBankSerialize.contents, headerSlots, headerSlotsF, srcH, tmpH, outH,
          S3, S2, S1, S0, fuel, binary, Hin]
  have hh := BitMachineStackRun.run headerSlots S3 MatrixInstanceEncoding.program
    (MatrixInstanceEncoding.initial rows cols thr [] table suffix) t4
  change ((advance hdrP)^[t4])
      (stackCfg headerSlots S3 (MatrixInstanceEncoding.initial rows cols thr [] table suffix)) =
    stackCfg headerSlots S3
      (MatrixInstanceEncoding.run t4 (MatrixInstanceEncoding.initial rows cols thr [] table suffix))
    at hh
  have hr4' : MatrixInstanceEncoding.run t4
      (MatrixInstanceEncoding.initial rows cols thr [] table suffix) =
      BitMachineBankSerialize.cfg none none (fun _ => []) [] []
        (natField rows ++ natField cols ++ natField thr ++ (table ++ suffix)) := hr4
  rw [hr4'] at hh
  have hs : bank headerSlots S3 (MatrixInstanceEncoding.initial rows cols thr [] table suffix).stk =
      S3 := bank_eq_self _ _ _ hin
  simp only [stackCfg] at hh
  rw [hs] at hh
  have hfinal : bank headerSlots S3 (BitMachineBankSerialize.cfg none none
      (fun _ => [] : BitMachineBankSerialize.Bank 3) [] []
      (natField rows ++ natField cols ++ natField thr ++ (table ++ suffix))).stk =
      Hout rows cols thr table suffix := by
    funext k
    by_cases hk : ∃ m, headerSlots m = k
    · obtain ⟨m, rfl⟩ := hk
      rw [bank_at]
      rcases m with j | j
      · fin_cases j <;> simp [BitMachineBankSerialize.cfg, BitMachineBankSerialize.contents,
          Hout, headerSlots, headerSlotsF, binary, outH]
      · fin_cases j <;> simp [BitMachineBankSerialize.cfg, BitMachineBankSerialize.contents,
          Hout, headerSlots, headerSlotsF, srcH, tmpH, outH, List.append_assoc]
    · rw [bank_outside _ _ _ _ hk]
      have hko : k ≠ outH := by
        intro h; exact hk ⟨.inr 2, by simp [h, headerSlots, headerSlotsF, outH]⟩
      have hkb : ∀ p : Fin 3, k ≠ binary p := by
        intro p h; exact hk ⟨.inl p, by simp [h, headerSlots, headerSlotsF]⟩
      have hks : k ≠ srcH := by
        intro h; exact hk ⟨.inr 0, by simp [h, headerSlots, headerSlotsF, srcH]⟩
      have hkt : k ≠ tmpH := by
        intro h; exact hk ⟨.inr 1, by simp [h, headerSlots, headerSlotsF, tmpH]⟩
      simp only [Hout, hko, if_false, S3, S2, S1, S0]
      rw [Function.update_of_ne (hkb 2), Function.update_apply]
      split_ifs with h2
      · rfl
      rw [Function.update_of_ne (hkb 1), Function.update_apply]
      split_ifs with h1
      · rfl
      rw [Function.update_of_ne (hkb 0), Function.update_apply]
      split_ifs with h0
      · rfl
      rcases k with k | j
      · simp [Hin]
      · fin_cases j
        · exact absurd rfl h0
        · exact absurd rfl h1
        · exact absurd rfl h2
        · exact absurd rfl hks
        · exact absurd rfl hkt
        · exact absurd rfl hko
  rw [hfinal] at hh
  change ((advance hdrP)^[t4]) (⟨some (.emit 0), none, S3⟩ : TM2.Cfg (fun _ : HB => Bool) _ _) =
    ⟨none, none, Hout rows cols thr table suffix⟩ at hh
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs (convP 0) (convP 1) cStart cStart
    idle idle idle idle _ _ _ _ _ r0 r1
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs p01 (convP 2)
    (BitMachineRawSequence.leftLabel cStart) cStart (idle, idle) (idle, idle) idle idle
    _ _ _ _ _ q1 r2
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs p012 hdrP
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel cStart)) (.emit 0)
    ((idle, idle), idle) ((idle, idle), idle) (none : Option Bool) none _ _ _ _ _ q2 hh
  refine ⟨u3, ?_, q3⟩
  simp only [List.length_replicate] at ht0 ht1 ht2
  have h4 : t4 ≤ 2 * (natField rows ++ natField cols ++ natField thr).length + 2 := by
    simpa [natField] using ht4
  omega

end

#print axioms serialize3_exact
#print axioms header_run_exact

end Paper2.YaoFrame
