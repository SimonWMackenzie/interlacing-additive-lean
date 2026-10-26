import Paper2.BindRetainMachine

/-!
# Charged run of the physical retained-suffix split machine

`machine_outputs`: for every word `code`, the fixed machine prints exactly
`pair (pair (f x) (take B t)) (drop B t)` within the explicit clock
`timeBound c d cf df M.pushBound |code|`, where `(x,t)=parseAll code` and
`B=c*(|f x|+1)^d`. The extra clock includes both outer framing and suffix
restoration, not merely the original truncation phases.
`polytime_result`: hence `result c d f` is `BitMachine.Polytime` whenever `f` is.
**No ledger row is closed.**
-/

namespace Paper2.SelectedTape.Bind.Retain

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.Unit4Shell.Loops
open NPOwner1

variable (M : BitMachine.Machine) (c d : ℕ)

/-- The explicit clock, in the input length `N`. -/
def timeBound (cf df pb N : ℕ) : ℕ :=
  (N + 1) + (N + 1) + cf * (N + 1) ^ df + (N + cf * (N + 1) ^ df * pb + 1) + 1 +
    (d + 1) * (3 + c * (N + cf * (N + 1) ^ df * pb + 1) ^ d *
      (3 * (N + cf * (N + 1) ^ df * pb) + 6)) +
    (c * (N + cf * (N + 1) ^ df * pb + 1) ^ d + 1) + (N + 1) + (N + 1) + 1 +
    (N + cf * (N + 1) ^ df * pb + 1) + 1 +
    8 * (N + cf * (N + 1) ^ df * pb +
      c * (N + cf * (N + 1) ^ df * pb + 1) ^ d + 2)

theorem run_helper {code result : List Bool} {n time : ℕ} {v : Control M}
    {S : Stack M → List Bool}
    (h : (advance (program M c d))^[n]
        (rawInit (mainS M) (Sum.inl NL.parse : Label M) ((none, M.initial) : Control M) code) =
      ⟨none, v, S⟩)
    (hs : S (mainS M) = result) (hn : n ≤ time) :
    (machine M c d).OutputsWithin code result time :=
  outputsWithin_of_raw_run (mainS M) (mainS M) (Sum.inl NL.parse : Label M)
    ((none, M.initial) : Control M) (program M c d) code result n time hn
    (by rw [h]) (by rw [h]; exact hs)

theorem machine_outputs (f : List Bool → List Bool) (cf df : ℕ)
    (hf : M.ComputesWithin f (fun n => cf * (n + 1) ^ df)) (code : List Bool) :
    (machine M c d).OutputsWithin code (result c d f code)
      (timeBound c d cf df M.pushBound code.length) := by
  obtain ⟨X, T, hXT⟩ : ∃ X T, parseAll code = (X, T) := ⟨_, _, rfl⟩
  have hlen := parseAll_length code
  rw [hXT] at hlen
  obtain ⟨hXl, hTl⟩ := hlen
  have hMrun := hf X
  have hylen := BitMachine.output_length_bound M hMrun
  obtain ⟨tM, htM, hhalt, hout⟩ := hMrun
  simp only at hXl hTl hylen htM
  -- phase 1: parse
  have hraw : rawInit (mainS M) (Sum.inl NL.parse : Label M) ((none, M.initial) : Control M)
      code = ⟨some (.inl .parse), (none, M.initial), St M code [] [] [] [] [] [] (fun _ => [])⟩ := by
    unfold rawInit
    congr 1
    funext k
    rcases k with i | j
    · fin_cases i <;> rfl
    · rfl
  obtain ⟨n1, o1, hn1, e1⟩ := parse_any (program M c d) (mainS M) (tempS M) (.inl .parse)
    (.inl .load) (ne_main_temp M) rfl code (St M code [] [] [] [] [] [] (fun _ => []))
    none M.initial rfl
  rw [hXT] at e1
  simp only [st_temp, List.append_nil, up_temp, up_main] at e1
  -- phase 2: load
  have e2 := move_loop (program M c d) (tempS M) (.inr M.input) (.inl .load) (.inr M.start)
    (by simp [tempS]) rfl X.reverse (St M T X.reverse [] [] [] [] [] (fun _ => [])) o1
    M.initial rfl
  simp only [List.length_reverse, List.reverse_reverse, st_R, List.append_nil, up_R,
    up_temp] at e2
  have hinit : Function.update (fun _ : Fin M.stackCount => ([] : List Bool)) M.input X =
      (M.init X).stk := by
    funext j
    simp [BitMachine.Machine.init, Function.update_apply]
  rw [hinit] at e2
  -- phase 3: the embedded machine
  have hbank : BitMachineStackEmbedding.bank (mStack M) (St M T [] [] [] [] [] [] (M.init X).stk)
      (M.init X).stk = St M T [] [] [] [] [] [] (M.init X).stk :=
    BitMachineStackEmbedding.bank_eq_self _ _ _ (fun _ => rfl)
  have hentry : (⟨some (.inr M.start), (none, M.initial), St M T [] [] [] [] [] [] (M.init X).stk⟩ :
      TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)) =
      BitMachineStackEmbedding.cfg (mStack M) (St M T [] [] [] [] [] [] (M.init X).stk) Sum.inr
        (embedC M) (some (.inl .move)) (M.init X) := by
    unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    rw [show (BitMachineInline.cfg Sum.inr (embedC M) (some (Sum.inl NL.move))
      (M.init X)).stk = (M.init X).stk from rfl, hbank]
    rfl
  have hh : (((advance M.program)^[tM]) (M.init X)).l = none := hhalt
  obtain ⟨n3, hn3, e3⟩ := BitMachineStackEmbedding.outputs (mStack M)
    (St M T [] [] [] [] [] [] (M.init X).stk) Sum.inr (embedC M)
    Prod.snd (by intro v; rfl) (some (.inl .move)) M.program (program M c d)
    (machine_program_eq M c d) (M.init X) tM hh
  have hcout : (((advance M.program)^[tM]) (M.init X)).stk M.output = f X := hout
  have hexit : BitMachineStackEmbedding.cfg (mStack M) (St M T [] [] [] [] [] [] (M.init X).stk)
      Sum.inr (embedC M) (some (.inl .move)) (((advance M.program)^[tM]) (M.init X)) =
      (⟨some (.inl .move), (none, (((advance M.program)^[tM]) (M.init X)).var),
        St M T [] [] [] [] [] [] (((advance M.program)^[tM]) (M.init X)).stk⟩ :
        TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)) := by
    simp only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
      BitMachineInline.cfg, hh, embedC]
    congr 1
    funext k
    rcases k with i | j
    · rw [BitMachineStackEmbedding.bank_outside]
      · rfl
      · rintro ⟨j, hj⟩
        simp [mStack] at hj
    · exact BitMachineStackEmbedding.bank_at (mStack M) _ _ j
  -- phase 4: move the output of `M` onto `temp`
  have e4 := move_loop (program M c d) (.inr M.output) (tempS M) (.inl .move) (.inl .initU)
    (by simp [tempS]) rfl (f X) (St M T [] [] [] [] [] [] (((advance M.program)^[tM]) (M.init X)).stk)
    none (((advance M.program)^[tM]) (M.init X)).var (by rw [st_R, hcout])
  simp only [st_temp, List.append_nil, up_temp, up_R] at e4
  -- phase 5: initialise the counters
  have e5 := initU_step M c d (none, (((advance M.program)^[tM]) (M.init X)).var) T (f X).reverse
    [] [] [] [] [] (Function.update (((advance M.program)^[tM]) (M.init X)).stk M.output [])
  simp only [List.append_nil] at e5
  -- phase 6: the `d` multiplication levels
  have e6 := levels M c d T (f X).reverse []
    (Function.update (((advance M.program)^[tM]) (M.init X)).stk M.output [])
    (((advance M.program)^[tM]) (M.init X)).var d c none
  rw [List.length_reverse] at e6
  -- phase 7: cut
  obtain ⟨n7, ov7, U7, hn7, e7⟩ := cut_loop (program M c d) (uS M) (mainS M) (outS M)
    (.inl .cut) (.inl .clear) (ne_u_main M) (ne_u_out M) (ne_main_out M) rfl
    (c * ((f X).length + 1) ^ d) T
    (St M T (f X).reverse [] (List.replicate (c * ((f X).length + 1) ^ d) true) [] [] []
      (Function.update (((advance M.program)^[tM]) (M.init X)).stk M.output []))
    none (((advance M.program)^[tM]) (M.init X)).var rfl rfl
  simp only [st_out, List.append_nil, up_out, up_main, up_u] at e7
  -- phase 8: clear the rest of `main`
  have e8 := move_loop (program M c d) (mainS M) (y2S M) (.inl .clear) (.inl .restore)
    (ne_main_y2 M) rfl (T.drop (c * ((f X).length + 1) ^ d))
    (St M (T.drop (c * ((f X).length + 1) ^ d)) (f X).reverse [] U7 []
      (T.take (c * ((f X).length + 1) ^ d)).reverse []
      (Function.update (((advance M.program)^[tM]) (M.init X)).stk M.output []))
    ov7 (((advance M.program)^[tM]) (M.init X)).var rfl
  simp only [st_y2, List.append_nil, up_y2, up_main] at e8
  -- phase 9: restore `take B t` onto `main`
  have e9 := move_loop (program M c d) (outS M) (mainS M) (.inl .restore) (.inl .emit0)
    (ne_main_out M).symm rfl (T.take (c * ((f X).length + 1) ^ d)).reverse
    (St M [] (f X).reverse (T.drop (c * ((f X).length + 1) ^ d)).reverse U7 []
      (T.take (c * ((f X).length + 1) ^ d)).reverse []
      (Function.update (((advance M.program)^[tM]) (M.init X)).stk M.output []))
    none (((advance M.program)^[tM]) (M.init X)).var rfl
  simp only [st_main, List.append_nil, List.reverse_reverse, up_main, up_out,
    List.length_reverse] at e9
  -- phase 10/11: emit `field y`
  have e10 := pushFalse_step (program M c d) (mainS M) (.inl .emit0) (.inl .emit) rfl
    (none, (((advance M.program)^[tM]) (M.init X)).var)
    (St M (T.take (c * ((f X).length + 1) ^ d)) (f X).reverse
      (T.drop (c * ((f X).length + 1) ^ d)).reverse U7 [] [] []
      (Function.update (((advance M.program)^[tM]) (M.init X)).stk M.output []))
  simp only [st_main, up_main] at e10
  have e11 := emit_loop (program M c d) (tempS M) (mainS M) (.inl .emit) (.inl .frameMove)
    (ne_main_temp M).symm rfl (f X).reverse
    (St M (false :: T.take (c * ((f X).length + 1) ^ d)) (f X).reverse
      (T.drop (c * ((f X).length + 1) ^ d)).reverse U7 [] [] []
      (Function.update (((advance M.program)^[tM]) (M.init X)).stk M.output []))
    none (((advance M.program)^[tM]) (M.init X)).var rfl
  simp only [st_main, up_main, up_temp, List.length_reverse, emit_reverse_field] at e11
  let q := EncodedComplexity.pair (f X) (T.take (c * ((f X).length + 1) ^ d))
  let tail := T.drop (c * ((f X).length + 1) ^ d)
  have e12 := move_loop (program M c d) (mainS M) (outS M)
    (.inl .frameMove) (.inl .suffixRestore) (ne_main_out M) rfl q
    (St M q [] tail.reverse U7 [] [] []
      (Function.update (((advance M.program)^[tM]) (M.init X)).stk M.output []))
    none (((advance M.program)^[tM]) (M.init X)).var rfl
  simp only [st_out, List.append_nil, up_out, up_main] at e12
  have e13 := move_loop (program M c d) (y2S M) (mainS M)
    (.inl .suffixRestore) (.inl .outerEmit0) (ne_main_y2 M).symm rfl tail.reverse
    (St M [] [] tail.reverse U7 [] q.reverse []
      (Function.update (((advance M.program)^[tM]) (M.init X)).stk M.output []))
    none (((advance M.program)^[tM]) (M.init X)).var rfl
  simp only [st_main, List.append_nil, List.reverse_reverse, up_main, up_y2,
    List.length_reverse] at e13
  have e14 := pushFalse_step (program M c d) (mainS M)
    (.inl .outerEmit0) (.inl .outerEmit) rfl
    (none, (((advance M.program)^[tM]) (M.init X)).var)
    (St M tail [] [] U7 [] q.reverse []
      (Function.update (((advance M.program)^[tM]) (M.init X)).stk M.output []))
  simp only [st_main, up_main] at e14
  have e15 := emit_loop (program M c d) (outS M) (mainS M)
    (.inl .outerEmit) (.inl .done) (ne_main_out M).symm rfl q.reverse
    (St M (false :: tail) [] [] U7 [] q.reverse []
      (Function.update (((advance M.program)^[tM]) (M.init X)).stk M.output []))
    none (((advance M.program)^[tM]) (M.init X)).var rfl
  simp only [st_main, up_main, up_out, List.length_reverse, emit_reverse_field] at e15
  have e16 := halt_step (program M c d) (.inl .done) rfl
    (none, (((advance M.program)^[tM]) (M.init X)).var)
    (St M (EncodedCommunication.field q ++ tail) [] [] U7 [] [] []
      (Function.update (((advance M.program)^[tM]) (M.init X)).stk M.output []))
  -- chain
  have r2 := iter_chain e1 e2
  have r3 := iter_chain r2 (hentry ▸ e3)
  rw [hexit] at r3
  have r4 := iter_chain r3 e4
  have r5 := iter_chain r4 (it1 e5)
  have r6 := iter_chain r5 e6
  have r7 := iter_chain r6 e7
  have r8 := iter_chain r7 e8
  have r9 := iter_chain r8 e9
  have r10 := iter_chain r9 (it1 e10)
  have r11 := iter_chain r10 e11
  have r12 := iter_chain r11 e12
  have r13 := iter_chain r12 e13
  have r14 := iter_chain r13 (it1 e14)
  have r15 := iter_chain r14 e15
  have r16 := iter_chain r15 (it1 e16)
  have hres : result c d f code = EncodedComplexity.pair q tail := by
    simp [result, hXT, q, tail]
  rw [← hraw] at r16
  refine run_helper M c d r16 (by rw [hres]; rfl) ?_
  -- the clock
  have hlt := levelTime_le (f X).length d c
  have hTd : (T.drop (c * ((f X).length + 1) ^ d)).length ≤ code.length := by
    rw [List.length_drop]; omega
  have hTt : (T.take (c * ((f X).length + 1) ^ d)).length ≤ code.length := by
    rw [List.length_take]; omega
  have hX1 : (X.length + 1) ^ df ≤ (code.length + 1) ^ df := Nat.pow_le_pow_left (by omega) _
  have htM' : tM ≤ cf * (code.length + 1) ^ df :=
    htM.trans (Nat.mul_le_mul_left _ hX1)
  have hy' : (f X).length ≤ code.length + cf * (code.length + 1) ^ df * M.pushBound := by
    have := Nat.mul_le_mul_right M.pushBound (Nat.mul_le_mul_left cf hX1)
    omega
  have hB : c * ((f X).length + 1) ^ d ≤
      c * (code.length + cf * (code.length + 1) ^ df * M.pushBound + 1) ^ d := by
    gcongr
  have hL : (d + 1) * (3 + c * ((f X).length + 1) ^ d * (3 * (f X).length + 6)) ≤
      (d + 1) * (3 + c * (code.length + cf * (code.length + 1) ^ df * M.pushBound + 1) ^ d *
        (3 * (code.length + cf * (code.length + 1) ^ df * M.pushBound) + 6)) := by
    gcongr
  have hq : q.length = 2 * (f X).length + 1 +
      (T.take (c * ((f X).length + 1) ^ d)).length := by
    simp [q, EncodedComplexity.pair_length]
  have hqBound : q.length ≤ 3 * code.length +
      2 * (cf * (code.length + 1) ^ df * M.pushBound) + 1 := by
    omega
  have htailBound : tail.length ≤ code.length := by
    simpa [tail] using hTd
  unfold timeBound
  omega

theorem polytime_result {f : List Bool → List Bool} (hf : BitMachine.Polytime f) (c d : ℕ) :
    BitMachine.Polytime (result c d f) := by
  obtain ⟨M, cf, df, hM⟩ := hf
  have hpoly : Paper2.Unit4Shell.Poly.PolyIn id (timeBound c d cf df M.pushBound) := by
    unfold timeBound
    repeat (first
      | exact Paper2.Unit4Shell.Poly.self
      | exact Paper2.Unit4Shell.Poly.const _
      | apply Paper2.Unit4Shell.Poly.add
      | apply Paper2.Unit4Shell.Poly.mul
      | apply Paper2.Unit4Shell.Poly.pow)
  obtain ⟨C, E, hCE⟩ := hpoly
  exact ⟨machine M c d, C, E, fun code =>
    BitMachine.outputsWithin_mono _ (machine_outputs M c d f cf df hM code)
      (hCE code.length)⟩

#print axioms machine_outputs
#print axioms polytime_result

end Paper2.SelectedTape.Bind.Retain
