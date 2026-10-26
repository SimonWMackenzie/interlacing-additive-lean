import Paper2.CmpLoops

/-!
# WP-U18a (ii), segment M2 (part 3): the whole run of the comparator on EVERY input `pair w out`

Lane `owner:a-cmp-1` (private, 27 September 2026). Paper A, lock v12, I:73-76, I:120.
`cmp_outputs`: `machine.OutputsWithin (pair w out) [spec w out] (cmpTime |w| |out|)`, where
`spec` is the literal decision function of the program (parse failure prints `false`).
-/

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Paper2.CmpOwner

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.EncodedCommunication (field readField bitsValue field_length
  readField_sound)
open EthInapproximability.CurrentPaper.EncodedComplexity (pair)

/-- The decision printed on `out` when the threshold bits (LSB first) are `mb`. -/
def specOut (mb : List Bool) : List Bool → Bool
  | [] => false
  | s :: bits =>
    match readField bits with
    | none => false
    | some (zs, r1) =>
      if lastOr none zs = some false ∨ (s = true ∧ lastOr none zs = none) then false else
      match readField r1 with
      | none => false
      | some (js, r2) =>
        if lastOr none js = some false then false else
        if r2 ≠ [] then false else
        if s = true then true else cmpF (loopF js (false :: zs)) mb false

/-- The decision printed on `pair w out`. -/
def spec (w out : List Bool) : Bool := specOut (lead w) out

/-- Clock of the output part. -/
def outTime (ol ml : ℕ) : ℕ := 6 * ol + ml + 12 + (ol + 2) * (2 * ol + 3)

/-- Clock of the whole comparator. -/
def cmpTime (wl ol : ℕ) : ℕ := 2 * wl + 2 + outTime ol wl

theorem iter_seq {α : Type*} {f : α → α} {x y z : α} (m n : ℕ) (h1 : f^[m] x = y)
    (h2 : f^[n] y = z) : f^[m + n] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, h1, h2]

theorem iter_one {α : Type*} {f : α → α} {x y : α} (h : f x = y) : f^[1] x = y := by
  rw [Function.iterate_one]; exact h

theorem lead'_length_le : ∀ (m : Mode) (w : List Bool), (lead' m w).length ≤ w.length
  | _, [] => by simp [lead']
  | m, b :: w => by
    have := lead'_length_le (nextMode m (some b)) w
    simp only [lead', List.length_append]
    generalize lead' (nextMode m (some b)) w = L at this ⊢
    by_cases hm : m = .bit <;> simp [hm] <;> omega

theorem loopF_length_le (L Zs : List Bool) : (loopF L Zs).length ≤ Zs.length := by
  rw [loopF_eq]; simp

theorem readField_length {inp bs rest : List Bool} (h : readField inp = some (bs, rest)) :
    2 * bs.length + 1 + rest.length = inp.length := by
  have := readField_sound h
  rw [← this, List.length_append, field_length]

theorem out_part (mb : List Bool) : ∀ (out : List Bool) (S : Stk → List Bool) (v : Ctl),
    S .I = out → S .O = [] → S .M2 = mb → S .Z = [] → S .Z2 = [] → S .J = [] → S .J2 = [] →
    S .T = [] → v.ll = none → v.lt = false →
    ∃ n ≤ outTime out.length mb.length, ∃ (v' : Ctl) (S' : Stk → List Bool),
      ((advance program)^[n]) (⟨some .sgn, v, S⟩ : Cfg) = ⟨none, v', S'⟩ ∧
      S' .O = [specOut mb out]
  | [], S, v, hI, hO, _, _, _, _, _, _, _, _ => by
    refine ⟨1, by simp [outTime], _, _, by rw [Function.iterate_one, sgn_nil S v hI], ?_⟩
    simp [Function.update_apply, hO, specOut]
  | s :: bits, S, v, hI, hO, hM, hZ, hZ2, hJ, hJ2, hT, hll, hlt => by
    have h1 := sgn_cons S v s bits hI
    set S1 := Function.update S .I bits with hS1
    set v1 : Ctl := { v with x := some s, sign := s } with hv1
    have hF1 := field_run program .Z .zchk .zf rfl (by decide) (by decide) bits S1 v1
      (by simp [hS1, Function.update_apply])
    cases hr : readField bits with
    | none =>
      obtain ⟨n, hn, v', S', hrun, hO'⟩ := hF1.2 hr
      refine ⟨1 + n, ?_, v', S', ?_, ?_⟩
      · simp only [outTime, List.length_cons]; nlinarith
      · exact iter_seq _ _ (iter_one h1) hrun
      · rw [hO']; simp [hS1, Function.update_apply, hO, specOut, hr]
    | some p =>
      rcases p with ⟨zs, r1⟩
      have hlen1 := readField_length hr
      obtain ⟨v2, hrun2, hs2, hlt2, hll2⟩ := hF1.1 zs r1 hr
      set S2 := Function.update (Function.update S1 .I r1) .Z (zs.reverse ++ S1 .Z) with hS2
      have hll2' : v2.ll = lastOr none zs := by rw [hll2, hv1]; simp [hll]
      have hs2' : v2.sign = s := by rw [hs2]
      by_cases hbad : v2.ll = some false ∨ (v2.sign = true ∧ v2.ll = none)
      · have h3 := zchk_bad S2 v2 hbad
        refine ⟨1 + (zs.length + 1) + 1, ?_, v2, Function.update S2 .O (false :: S2 .O), ?_, ?_⟩
        · simp only [outTime, List.length_cons]; nlinarith
        · exact iter_seq _ _ (iter_seq _ _ (iter_one h1) hrun2) (iter_one h3)
        · rw [hll2', hs2'] at hbad
          simp [hS2, hS1, Function.update_apply, hO, specOut, hr, hbad]
      · have h3 := zchk_ok S2 v2 hbad
        have hZ2eq : S2 .Z = zs.reverse := by simp [hS2, hS1, Function.update_apply, hZ]
        have h4 := mv_run program .Z .Z2 .jf .revZ rfl (by decide) zs.reverse S2
          { v2 with ll := none } hZ2eq
        set S4 := Function.update (Function.update S2 .Z []) .Z2 (zs.reverse.reverse ++ S2 .Z2)
          with hS4
        set v4 : Ctl := { { v2 with ll := none } with x := none } with hv4
        have hF4 := field_run program .J .jchk .jf rfl (by decide) (by decide) r1 S4 v4
          (by simp [hS4, hS2, hS1, Function.update_apply])
        have hbad' : ¬ (lastOr none zs = some false ∨ (s = true ∧ lastOr none zs = none)) := by
          rw [hll2', hs2'] at hbad; exact hbad
        cases hr1 : readField r1 with
        | none =>
          obtain ⟨n, hn, v', S', hrun, hO'⟩ := hF4.2 hr1
          refine ⟨1 + (zs.length + 1) + 1 + (zs.reverse.length + 1) + n, ?_, v', S', ?_, ?_⟩
          · simp only [outTime, List.length_cons, List.length_reverse] at hn ⊢; nlinarith
          · exact iter_seq _ _ (iter_seq _ _ (iter_seq _ _ (iter_seq _ _ (iter_one h1) hrun2)
              (iter_one h3)) h4) hrun
          · rw [hO']
            simp [hS4, hS2, hS1, Function.update_apply, hO, specOut, hr, hbad', hr1]
        | some q =>
          rcases q with ⟨js, r2⟩
          have hlen2 := readField_length hr1
          obtain ⟨v5, hrun5, hs5, hlt5, hll5⟩ := hF4.1 js r2 hr1
          set S5 := Function.update (Function.update S4 .I r2) .J (js.reverse ++ S4 .J) with hS5
          have hll5' : v5.ll = lastOr none js := by rw [hll5, hv4]
          have hs5' : v5.sign = s := by rw [hs5, hv4]; exact hs2'
          have hlt5' : v5.lt = false := by rw [hlt5, hv4]; simp [hlt2, hv1, hlt]
          have hpre : ∀ n, n = 1 + (zs.length + 1) + 1 + (zs.reverse.length + 1) + (js.length + 1) →
              ((advance program)^[n]) (⟨some .sgn, v, S⟩ : Cfg) = ⟨some .jchk, v5, S5⟩ := by
            intro n hn
            rw [hn]
            exact iter_seq _ _ (iter_seq _ _ (iter_seq _ _ (iter_seq _ _ (iter_one h1) hrun2)
              (iter_one h3)) h4) hrun5
          by_cases hjb : v5.ll = some false
          · have h6 := jchk_bad S5 v5 hjb
            refine ⟨1 + (zs.length + 1) + 1 + (zs.reverse.length + 1) + (js.length + 1) + 1, ?_,
              v5, Function.update S5 .O (false :: S5 .O), ?_, ?_⟩
            · simp only [outTime, List.length_cons, List.length_reverse]; nlinarith
            · exact iter_seq _ _ (hpre _ rfl) (iter_one h6)
            · rw [hll5'] at hjb
              simp [hS5, hS4, hS2, hS1, Function.update_apply, hO, specOut, hr, hbad', hr1, hjb]
          · have hjb' : ¬ lastOr none js = some false := by rw [← hll5']; exact hjb
            have hI5 : S5 .I = r2 := by simp [hS5, Function.update_apply]
            cases r2 with
            | cons c r =>
              have h6 := jchk_cons S5 v5 hjb c r hI5
              refine ⟨1 + (zs.length + 1) + 1 + (zs.reverse.length + 1) + (js.length + 1) + 1, ?_,
                { v5 with x := some c },
                Function.update (Function.update S5 .I r) .O (false :: S5 .O), ?_, ?_⟩
              · simp only [outTime, List.length_cons, List.length_reverse]; nlinarith
              · exact iter_seq _ _ (hpre _ rfl) (iter_one h6)
              · simp [hS5, hS4, hS2, hS1, Function.update_apply, hO, specOut, hr, hbad', hr1, hjb']
            | nil =>
              have h6 := jchk_nil S5 v5 hjb hI5
              set S6 := Function.update S5 .I [] with hS6
              have hJ6 : S6 .J = js.reverse := by
                simp [hS6, hS5, hS4, hS2, hS1, Function.update_apply, hJ]
              have h7 := mv_run program .J .J2 .neg .revJ rfl (by decide) js.reverse S6
                { v5 with x := none } hJ6
              set S7 := Function.update (Function.update S6 .J []) .J2 (js.reverse.reverse ++ S6 .J2)
                with hS7
              have hpre7 : ∀ n, n = 1 + (zs.length + 1) + 1 + (zs.reverse.length + 1) +
                  (js.length + 1) + 1 + (js.reverse.length + 1) →
                  ((advance program)^[n]) (⟨some .sgn, v, S⟩ : Cfg) =
                    ⟨some .neg, { { v5 with x := none } with x := none }, S7⟩ := by
                intro n hn
                rw [hn]
                exact iter_seq _ _ (iter_seq _ _ (hpre _ rfl) (iter_one h6)) h7
              cases s with
              | true =>
                have h8 := neg_true S7 { { v5 with x := none } with x := none } (by simp [hs5'])
                refine ⟨1 + (zs.length + 1) + 1 + (zs.reverse.length + 1) + (js.length + 1) + 1 +
                  (js.reverse.length + 1) + 1, ?_, { { v5 with x := none } with x := none },
                  Function.update S7 .O (true :: S7 .O), ?_, ?_⟩
                · simp only [outTime, List.length_cons, List.length_reverse]; nlinarith
                · exact iter_seq _ _ (hpre7 _ rfl) (iter_one h8)
                · have hb2 := hbad'
                  simp only [true_and, not_or] at hb2
                  simp [hS7, hS6, hS5, hS4, hS2, hS1, Function.update_apply, hO, specOut, hr, hb2,
                    hr1, hjb']
              | false =>
                have h8 := neg_false S7 { { v5 with x := none } with x := none } (by simp [hs5'])
                set S8 := Function.update S7 .Z2 (false :: S7 .Z2) with hS8
                have hJ8 : S8 .J2 = js := by
                  simp [hS8, hS7, hS6, hS5, hS4, hS2, hS1, Function.update_apply, hJ2]
                have hT8 : S8 .T = [] := by
                  simp [hS8, hS7, hS6, hS5, hS4, hS2, hS1, Function.update_apply, hT]
                have hZ8 : S8 .Z2 = false :: zs := by
                  simp [hS8, hS7, hS6, hS5, hS4, hS2, hS1, Function.update_apply, hZ2]
                obtain ⟨nl, hnl, v9, S9, h9, hZ9, hO9, hM9, hlt9⟩ :=
                  loop_run (false :: zs) js S8 { { v5 with x := none } with x := none } hJ8 hT8 hZ8
                obtain ⟨v10, S10, h10, hO10⟩ :=
                  cmp_run (loopF js (false :: zs)) mb S9 v9 hZ9
                    (by rw [hM9]; simp [hS8, hS7, hS6, hS5, hS4, hS2, hS1, Function.update_apply, hM])
                have hlo := loopF_length_le js (false :: zs)
                refine ⟨1 + (zs.length + 1) + 1 + (zs.reverse.length + 1) + (js.length + 1) + 1 +
                  (js.reverse.length + 1) + 1 + nl +
                  (max (loopF js (false :: zs)).length mb.length + 1), ?_, v10, S10, ?_, ?_⟩
                · simp only [outTime, List.length_cons, List.length_reverse] at hnl hlo ⊢
                  have hprod : (zs.length + 1 + 1) * (2 * js.length + 3) ≤
                      (bits.length + 1 + 2) * (2 * (bits.length + 1) + 3) :=
                    Nat.mul_le_mul (by omega) (by omega)
                  have hmax : max (loopF js (false :: zs)).length mb.length ≤
                      (zs.length + 1) + mb.length := by omega
                  nlinarith
                · exact iter_seq _ _ (iter_seq _ _ (iter_seq _ _ (hpre7 _ rfl) (iter_one h8)) h9) h10
                · rw [hO10, hO9, hlt9]
                  have hb2 := hbad'
                  simp only [Bool.false_eq_true, false_and, or_false] at hb2
                  simp [hb2, hS8, hS7, hS6, hS5, hS4, hS2, hS1, Function.update_apply, hO, specOut, hr,
                    hbad', hr1, hjb', hlt5']

/-- **The comparator runs on every input.** On `pair w out` the literal program halts within
`cmpTime |w| |out|` transitions with output stack exactly `[spec w out]`. -/
theorem cmp_outputs (w out : List Bool) :
    machine.OutputsWithin (pair w out) [spec w out] (cmpTime w.length out.length) := by
  set S0 : Stk → List Bool := fun k => if k = Stk.I then pair w out else [] with hS0
  obtain ⟨v1, h1, _, hlt1, hll1⟩ := a_run out w S0 ctl0 (by simp [hS0, pair])
  set S1 := Function.update (Function.update S0 .I out) .M ((lead' ctl0.im w).reverse ++ S0 .M)
    with hS1
  have h2 := mv_run program .M .M2 .sgn .revM rfl (by decide) (lead' ctl0.im w).reverse S1 v1
    (by simp [hS1, hS0, Function.update_apply])
  set S2 := Function.update (Function.update S1 .M []) .M2
    ((lead' ctl0.im w).reverse.reverse ++ S1 .M2) with hS2
  obtain ⟨n, hn, v', S', h3, hO'⟩ := out_part (lead w) out S2 { v1 with x := none }
    (by simp [hS2, hS1, hS0, Function.update_apply])
    (by simp [hS2, hS1, hS0, Function.update_apply])
    (by simp [hS2, hS1, hS0, Function.update_apply, lead, ctl0])
    (by simp [hS2, hS1, hS0, Function.update_apply])
    (by simp [hS2, hS1, hS0, Function.update_apply])
    (by simp [hS2, hS1, hS0, Function.update_apply])
    (by simp [hS2, hS1, hS0, Function.update_apply])
    (by simp [hS2, hS1, hS0, Function.update_apply])
    (by simp [hll1, ctl0]) (by simp [hlt1, ctl0])
  have hlw := lead'_length_le ctl0.im w
  have hlen : (lead w).length ≤ w.length := hlw
  refine outputsWithin_of_raw_run Stk.I Stk.O Lbl.a ctl0 program (pair w out) [spec w out]
    ((w.length + 1) + ((lead' ctl0.im w).reverse.length + 1) + n) _ ?_ ?_ ?_
  · simp only [cmpTime, outTime, List.length_reverse] at hn ⊢
    have : outTime out.length (lead w).length ≤ outTime out.length w.length := by
      simp only [outTime]; omega
    simp only [outTime] at this
    have hl2 : (lead' ctl0.im w).length ≤ w.length := hlw
    omega
  · have hraw : (rawInit Stk.I Lbl.a ctl0 (pair w out) : Cfg) = ⟨some .a, ctl0, S0⟩ := rfl
    rw [hraw, iter_seq _ _ (iter_seq _ _ h1 h2) h3]
  · have hraw : (rawInit Stk.I Lbl.a ctl0 (pair w out) : Cfg) = ⟨some .a, ctl0, S0⟩ := rfl
    rw [hraw, iter_seq _ _ (iter_seq _ _ h1 h2) h3]
    exact hO'

end Paper2.CmpOwner
