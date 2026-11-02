import Paper2.ECutMachine

/-!
# Paper A (lock v12), lane `owner:a-eth-2`, segment 2 sub-step (obstacle B2 / a-eth-owner-1 open edge O2):
# the charged run of the prefix CUTTER, with a clock independent of the unread tape

`Cut.machine M c d` (module `ECutMachine`: the admitted `NPOwner1.Trunc` program with the `clear`
phase bypassed and the output written on the scratch stack `y2`) is ONE fixed finite machine. On the
actual pair encoding `pair x t` it prints exactly `pair (f x) (take B t)`, `B = c·(|f x|+1)^d`,
where `f` is computed by the fixed machine `M` within `cf·(n+1)^df`, and it halts within
`cutTime c d cf df M.pushBound |x|`, a bound in `|x|` ONLY (`cut_outputs`): the unread rest
`drop B t` of the tape stays untouched on the input stack. Every bit of the output is produced by a
literal transition; nothing is inserted.

Sharper parse lemma `parse_field`: the admitted `parseStmt` consumes `field x ++ t` in at most
`|field x| = 2|x| + 1` steps (the admitted `NPOwner1.parse_any` bounds by the whole word).

The run proof is the admitted `NPOwner1.Trunc.machine_outputs` (Paper2/NPTruncRun.lean) with phase 1
replaced by `parse_field`, phase 8 (`clear`) deleted and phases 9-12 retargeted to `y2`.

No ledger row is closed.
-/

namespace Paper2.AEth2.Cut

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.Unit4Shell.Loops
open NPOwner1

theorem field_length (x : List Bool) :
    (EncodedCommunication.field x).length = 2 * x.length + 1 := by
  induction x with
  | nil => simp [EncodedCommunication.field]
  | cons b x ih => simp [EncodedCommunication.field, ih]; omega

/-- **`parseStmt` on `field x ++ t` takes at most `|field x|` steps.** -/
theorem parse_field {K Λ W : Type*} [DecidableEq K]
    (P : Λ → TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W))
    (a b : K) (here next : Λ) (hab : a ≠ b) (hP : P here = parseStmt a b here next) :
    ∀ (x t : List Bool) (S : K → List Bool) (o : Option Bool) (w : W),
      S a = EncodedCommunication.field x ++ t →
      ∃ n o', n ≤ (EncodedCommunication.field x).length ∧ (advance P)^[n] ⟨some here, (o, w), S⟩ =
        ⟨some next, (o', w), Function.update (Function.update S b (x.reverse ++ S b)) a t⟩
  | [], t, S, o, w, hS => by
      have hS' : S a = false :: t := by simpa [EncodedCommunication.field] using hS
      refine ⟨1, some false, by simp [EncodedCommunication.field], ?_⟩
      simp [advance, TM2.step, TM2.stepAux, hP, parseStmt, setBit, hS', Function.update_eq_self]
  | y :: x, t, S, o, w, hS => by
      have hS' : S a = true :: y :: (EncodedCommunication.field x ++ t) := by
        simpa [EncodedCommunication.field] using hS
      have h1 : advance P ⟨some here, (o, w), S⟩ =
          ⟨some here, (some y, w), Function.update (Function.update S a
            (EncodedCommunication.field x ++ t)) b (y :: S b)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, hP, parseStmt, setBit, hS',
          Function.update_of_ne hab.symm]
      obtain ⟨n, o', hn, he⟩ := parse_field P a b here next hab hP x t
        (Function.update (Function.update S a (EncodedCommunication.field x ++ t)) b (y :: S b))
        (some y) w (by rw [Function.update_of_ne hab, Function.update_self])
      refine ⟨n + 1, o', by simp only [EncodedCommunication.field, List.length_cons]; omega, ?_⟩
      rw [Function.iterate_succ_apply, h1, he]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [Function.update_self, Function.update_idem, Function.update_comm hab,
        Function.update_idem]

variable (M : BitMachine.Machine) (c d : ℕ)

theorem ne_out_y2 : outS M ≠ y2S M := by simp [outS, y2S]

/-- **The cutter's clock** in `m = |x|` and the clock `T` of the inner machine on `x` only
(never in the tape length). -/
def cutTimeG (pb m T : ℕ) : ℕ :=
  (2 * m + 1) + (m + 1) + T + (m + T * pb + 1) + 1 +
    (d + 1) * (3 + c * (m + T * pb + 1) ^ d *
      (3 * (m + T * pb) + 6)) +
    (c * (m + T * pb + 1) ^ d + 1) +
    (c * (m + T * pb + 1) ^ d + 1) + 1 +
    (m + T * pb + 1) + 1

/-- The polynomial instance: the inner machine runs within `cf (|x|+1)^df`. -/
def cutTime (cf df pb m : ℕ) : ℕ := cutTimeG c d pb m (cf * (m + 1) ^ df)

/-- **The physical prefix cutter, per-input inner clock.** If the fixed machine `M` prints `f x`
from `x` within `τ x`, then on `pair x t` the fixed cutter prints exactly
`pair (f x) (take (c·(|f x|+1)^d) t)` within `cutTimeG c d M.pushBound |x| (τ x)`, for EVERY `t`
(of any length; the unread rest of `t` is never touched). -/
theorem cut_outputs_gen (f : List Bool → List Bool) (τ : List Bool → ℕ)
    (x : List Bool) (hf : M.OutputsWithin x (f x) (τ x)) (t : List Bool) :
    (machine M c d).OutputsWithin (EncodedComplexity.pair x t)
      (EncodedComplexity.pair (f x) (t.take (c * ((f x).length + 1) ^ d)))
      (cutTimeG c d M.pushBound x.length (τ x)) := by
  have hMrun := hf
  have hylen := BitMachine.output_length_bound M hMrun
  obtain ⟨tM, htM, hhalt, hout⟩ := hMrun
  set code := EncodedComplexity.pair x t with hcode
  -- phase 1: parse (sharp)
  have hraw : rawInit (mainS M) (Sum.inl NL.parse : Label M) ((none, M.initial) : Control M)
      code = ⟨some (.inl .parse), (none, M.initial), St M code [] [] [] [] [] [] (fun _ => [])⟩ := by
    unfold rawInit
    congr 1
    funext k
    rcases k with i | j
    · fin_cases i <;> rfl
    · rfl
  obtain ⟨n1, o1, hn1, e1⟩ := parse_field (program M c d) (mainS M) (tempS M) (.inl .parse)
    (.inl .load) (ne_main_temp M) rfl x t (St M code [] [] [] [] [] [] (fun _ => []))
    none M.initial rfl
  simp only [st_temp, List.append_nil, up_temp, up_main] at e1
  -- phase 2: load
  have e2 := move_loop (program M c d) (tempS M) (.inr M.input) (.inl .load) (.inr M.start)
    (by simp [tempS]) rfl x.reverse (St M t x.reverse [] [] [] [] [] (fun _ => [])) o1
    M.initial rfl
  simp only [List.length_reverse, List.reverse_reverse, st_R, List.append_nil, up_R,
    up_temp] at e2
  have hinit : Function.update (fun _ : Fin M.stackCount => ([] : List Bool)) M.input x =
      (M.init x).stk := by
    funext j
    simp [BitMachine.Machine.init, Function.update_apply]
  rw [hinit] at e2
  -- phase 3: the embedded machine
  have hbank : BitMachineStackEmbedding.bank (mStack M) (St M t [] [] [] [] [] [] (M.init x).stk)
      (M.init x).stk = St M t [] [] [] [] [] [] (M.init x).stk :=
    BitMachineStackEmbedding.bank_eq_self _ _ _ (fun _ => rfl)
  have hentry : (⟨some (.inr M.start), (none, M.initial), St M t [] [] [] [] [] [] (M.init x).stk⟩ :
      TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)) =
      BitMachineStackEmbedding.cfg (mStack M) (St M t [] [] [] [] [] [] (M.init x).stk) Sum.inr
        (embedC M) (some (.inl .move)) (M.init x) := by
    unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    rw [show (BitMachineInline.cfg Sum.inr (embedC M) (some (Sum.inl NL.move))
      (M.init x)).stk = (M.init x).stk from rfl, hbank]
    rfl
  have hh : (((advance M.program)^[tM]) (M.init x)).l = none := hhalt
  obtain ⟨n3, hn3, e3⟩ := BitMachineStackEmbedding.outputs (mStack M)
    (St M t [] [] [] [] [] [] (M.init x).stk) Sum.inr (embedC M)
    Prod.snd (by intro v; rfl) (some (.inl .move)) M.program (program M c d)
    (machine_program_eq M c d) (M.init x) tM hh
  have hcout : (((advance M.program)^[tM]) (M.init x)).stk M.output = f x := hout
  have hexit : BitMachineStackEmbedding.cfg (mStack M) (St M t [] [] [] [] [] [] (M.init x).stk)
      Sum.inr (embedC M) (some (.inl .move)) (((advance M.program)^[tM]) (M.init x)) =
      (⟨some (.inl .move), (none, (((advance M.program)^[tM]) (M.init x)).var),
        St M t [] [] [] [] [] [] (((advance M.program)^[tM]) (M.init x)).stk⟩ :
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
    (by simp [tempS]) rfl (f x) (St M t [] [] [] [] [] [] (((advance M.program)^[tM]) (M.init x)).stk)
    none (((advance M.program)^[tM]) (M.init x)).var (by rw [st_R, hcout])
  simp only [st_temp, List.append_nil, up_temp, up_R] at e4
  -- phase 5: initialise the counters
  have e5 := initU_step M c d (none, (((advance M.program)^[tM]) (M.init x)).var) t (f x).reverse
    [] [] [] [] [] (Function.update (((advance M.program)^[tM]) (M.init x)).stk M.output [])
  simp only [List.append_nil] at e5
  -- phase 6: the `d` multiplication levels
  have e6 := levels M c d t (f x).reverse []
    (Function.update (((advance M.program)^[tM]) (M.init x)).stk M.output [])
    (((advance M.program)^[tM]) (M.init x)).var d c none
  rw [List.length_reverse] at e6
  -- phase 7: cut (next label `restore`: the rest of `t` is NOT cleared)
  obtain ⟨n7, ov7, U7, hn7, e7⟩ := cut_loop (program M c d) (uS M) (mainS M) (outS M)
    (.inl .cut) (.inl .restore) (ne_u_main M) (ne_u_out M) (ne_main_out M) rfl
    (c * ((f x).length + 1) ^ d) t
    (St M t (f x).reverse [] (List.replicate (c * ((f x).length + 1) ^ d) true) [] [] []
      (Function.update (((advance M.program)^[tM]) (M.init x)).stk M.output []))
    none (((advance M.program)^[tM]) (M.init x)).var rfl rfl
  simp only [st_out, List.append_nil, up_out, up_main, up_u] at e7
  -- phase 9: move `take B t` onto the empty scratch stack `y2`
  have e9 := move_loop (program M c d) (outS M) (y2S M) (.inl .restore) (.inl .emit0)
    (ne_out_y2 M) rfl (t.take (c * ((f x).length + 1) ^ d)).reverse
    (St M (t.drop (c * ((f x).length + 1) ^ d)) (f x).reverse [] U7 []
      (t.take (c * ((f x).length + 1) ^ d)).reverse []
      (Function.update (((advance M.program)^[tM]) (M.init x)).stk M.output []))
    ov7 (((advance M.program)^[tM]) (M.init x)).var rfl
  simp only [st_y2, List.append_nil, List.reverse_reverse, up_y2, up_out,
    List.length_reverse] at e9
  -- phase 10/11: emit `field y` onto `y2`
  have e10 := pushFalse_step (program M c d) (y2S M) (.inl .emit0) (.inl .emit) rfl
    (none, (((advance M.program)^[tM]) (M.init x)).var)
    (St M (t.drop (c * ((f x).length + 1) ^ d)) (f x).reverse
      (t.take (c * ((f x).length + 1) ^ d)) U7 [] [] []
      (Function.update (((advance M.program)^[tM]) (M.init x)).stk M.output []))
  simp only [st_y2, up_y2] at e10
  have e11 := emit_loop (program M c d) (tempS M) (y2S M) (.inl .emit) (.inl .done)
    (ne_temp_y2 M) rfl (f x).reverse
    (St M (t.drop (c * ((f x).length + 1) ^ d)) (f x).reverse
      (false :: t.take (c * ((f x).length + 1) ^ d)) U7 [] [] []
      (Function.update (((advance M.program)^[tM]) (M.init x)).stk M.output []))
    none (((advance M.program)^[tM]) (M.init x)).var rfl
  simp only [st_y2, up_y2, up_temp, List.length_reverse, emit_reverse_field] at e11
  have e12 := halt_step (program M c d) (.inl .done) rfl
    (none, (((advance M.program)^[tM]) (M.init x)).var)
    (St M (t.drop (c * ((f x).length + 1) ^ d)) []
      (EncodedCommunication.field (f x) ++ t.take (c * ((f x).length + 1) ^ d)) U7 [] [] []
      (Function.update (((advance M.program)^[tM]) (M.init x)).stk M.output []))
  -- chain
  have r2 := iter_chain e1 e2
  have r3 := iter_chain r2 (hentry ▸ e3)
  rw [hexit] at r3
  have r4 := iter_chain r3 e4
  have r5 := iter_chain r4 (it1 e5)
  have r6 := iter_chain r5 e6
  have r7 := iter_chain r6 e7
  have r9 := iter_chain r7 e9
  have r10 := iter_chain r9 (it1 e10)
  have r11 := iter_chain r10 e11
  have r12 := iter_chain r11 (it1 e12)
  rw [← hraw] at r12
  refine outputsWithin_of_raw_run (mainS M) (y2S M) (Sum.inl NL.parse : Label M)
    ((none, M.initial) : Control M) (program M c d) code _ _ _ ?_ (by rw [r12]) (by rw [r12]; rfl)
  -- the clock
  have hlt := levelTime_le (f x).length d c
  have hfl := field_length x
  have hy' : (f x).length ≤ x.length + τ x * M.pushBound := by
    have := Nat.mul_le_mul_right M.pushBound htM
    omega
  have hB : c * ((f x).length + 1) ^ d ≤
      c * (x.length + τ x * M.pushBound + 1) ^ d := by
    gcongr
  have hL : (d + 1) * (3 + c * ((f x).length + 1) ^ d * (3 * (f x).length + 6)) ≤
      (d + 1) * (3 + c * (x.length + τ x * M.pushBound + 1) ^ d *
        (3 * (x.length + τ x * M.pushBound) + 6)) := by
    gcongr
  have hTt : (t.take (c * ((f x).length + 1) ^ d)).length ≤ c * ((f x).length + 1) ^ d := by
    rw [List.length_take]; omega
  unfold cutTimeG
  omega

/-- **The physical prefix cutter, polynomial inner machine.** -/
theorem cut_outputs (f : List Bool → List Bool) (cf df : ℕ)
    (hf : M.ComputesWithin f (fun n => cf * (n + 1) ^ df)) (x t : List Bool) :
    (machine M c d).OutputsWithin (EncodedComplexity.pair x t)
      (EncodedComplexity.pair (f x) (t.take (c * ((f x).length + 1) ^ d)))
      (cutTime c d cf df M.pushBound x.length) :=
  cut_outputs_gen M c d f (fun x => cf * (x.length + 1) ^ df) x (hf x) t

end Paper2.AEth2.Cut

#print axioms Paper2.AEth2.Cut.parse_field
#print axioms Paper2.AEth2.Cut.cut_outputs_gen
#print axioms Paper2.AEth2.Cut.cut_outputs
