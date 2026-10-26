import Paper2.CmpMachine

/-!
# WP-U18a (ii), segment M2 (part 2): single steps, the decrement-and-drop loop, the comparison loop

Lane `owner:a-cmp-1` (private, 27 September 2026). Paper A, lock v12, I:73-76, I:120.
Exact runs of the remaining phases of `Paper2.CmpOwner.program`, with the arithmetic meaning of the
two loops: `loopF L Zs = Zs.drop (bitsValue L)` and
`cmpF as bs lt = decide (val as < val bs ∨ (val as = val bs ∧ lt))`.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Paper2.CmpOwner

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.EncodedCommunication (field readField bitsValue)

/-! ## Single steps -/

theorem sgn_nil (S : Stk → List Bool) (v : Ctl) (hS : S .I = []) :
    advance program (⟨some .sgn, v, S⟩ : Cfg) =
      ⟨none, { v with x := none }, Function.update (Function.update S .I []) .O (false :: S .O)⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, rej, hS, Function.update_apply]

theorem sgn_cons (S : Stk → List Bool) (v : Ctl) (s : Bool) (bits : List Bool)
    (hS : S .I = s :: bits) :
    advance program (⟨some .sgn, v, S⟩ : Cfg) =
      ⟨some .zf, { v with x := some s, sign := s }, Function.update S .I bits⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, hS]

theorem zchk_bad (S : Stk → List Bool) (v : Ctl)
    (h : v.ll = some false ∨ (v.sign = true ∧ v.ll = none)) :
    advance program (⟨some .zchk, v, S⟩ : Cfg) =
      ⟨none, v, Function.update S .O (false :: S .O)⟩ := by
  rcases h with h | ⟨h1, h2⟩
  · simp [advance, TM2.step, TM2.stepAux, program, rej, h]
  · simp [advance, TM2.step, TM2.stepAux, program, rej, h1, h2]

theorem zchk_ok (S : Stk → List Bool) (v : Ctl)
    (h : ¬ (v.ll = some false ∨ (v.sign = true ∧ v.ll = none))) :
    advance program (⟨some .zchk, v, S⟩ : Cfg) = ⟨some .revZ, { v with ll := none }, S⟩ := by
  push Not at h
  obtain ⟨h1, h2⟩ := h
  have : (decide (v.ll = some false) || (v.sign && decide (v.ll = none))) = false := by
    cases hs : v.sign
    · simp [h1]
    · simp [h1, h2 hs]
  simp [advance, TM2.step, TM2.stepAux, program, this]

theorem jchk_bad (S : Stk → List Bool) (v : Ctl) (h : v.ll = some false) :
    advance program (⟨some .jchk, v, S⟩ : Cfg) =
      ⟨none, v, Function.update S .O (false :: S .O)⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, rej, h]

theorem jchk_nil (S : Stk → List Bool) (v : Ctl) (h : v.ll ≠ some false) (hS : S .I = []) :
    advance program (⟨some .jchk, v, S⟩ : Cfg) =
      ⟨some .revJ, { v with x := none }, Function.update S .I []⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, rej, h, hS]

theorem jchk_cons (S : Stk → List Bool) (v : Ctl) (h : v.ll ≠ some false) (c : Bool)
    (r : List Bool) (hS : S .I = c :: r) :
    advance program (⟨some .jchk, v, S⟩ : Cfg) =
      ⟨none, { v with x := some c }, Function.update (Function.update S .I r) .O (false :: S .O)⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, rej, h, hS, Function.update_apply]

theorem neg_true (S : Stk → List Bool) (v : Ctl) (h : v.sign = true) :
    advance program (⟨some .neg, v, S⟩ : Cfg) = ⟨none, v, Function.update S .O (true :: S .O)⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, h]

theorem neg_false (S : Stk → List Bool) (v : Ctl) (h : v.sign = false) :
    advance program (⟨some .neg, v, S⟩ : Cfg) =
      ⟨some .dec, v, Function.update S .Z2 (false :: S .Z2)⟩ := by
  simp [advance, TM2.step, TM2.stepAux, program, h]

/-! ## Binary decrement and the drop loop -/

/-- Binary decrement of an LSB-first word (`none` on a numerically zero word). -/
def decL : List Bool → Option (List Bool)
  | [] => none
  | true :: r => some (false :: r)
  | false :: r => (decL r).map (true :: ·)

theorem decL_zeros_true (r : List Bool) : ∀ k : ℕ,
    decL (List.replicate k false ++ true :: r) = some (List.replicate k true ++ false :: r)
  | 0 => rfl
  | k + 1 => by simp [List.replicate_succ, decL, decL_zeros_true r k]

theorem decL_zeros : ∀ k : ℕ, decL (List.replicate k false) = none
  | 0 => rfl
  | k + 1 => by simp [List.replicate_succ, decL, decL_zeros k]

theorem shape : ∀ L : List Bool,
    (∃ k r, L = List.replicate k false ++ true :: r) ∨ ∃ k, L = List.replicate k false
  | [] => Or.inr ⟨0, rfl⟩
  | true :: r => Or.inl ⟨0, r, rfl⟩
  | false :: r => by
    rcases shape r with ⟨k, r', h⟩ | ⟨k, h⟩
    · exact Or.inl ⟨k + 1, r', by simp [h, List.replicate_succ]⟩
    · exact Or.inr ⟨k + 1, by simp [h, List.replicate_succ]⟩

theorem decL_value : ∀ (L L' : List Bool), decL L = some L' → bitsValue L = bitsValue L' + 1
  | [], _, h => by simp [decL] at h
  | true :: r, L', h => by
    simp only [decL, Option.some.injEq] at h
    subst h
    simp [bitsValue, Nat.bit_val]
  | false :: r, L', h => by
    simp only [decL, Option.map_eq_some_iff] at h
    obtain ⟨r', hr, rfl⟩ := h
    have := decL_value r r' hr
    simp [bitsValue, Nat.bit_val, this]
    omega

theorem decL_none : ∀ (L : List Bool), decL L = none → bitsValue L = 0
  | [], _ => rfl
  | true :: r, h => by simp [decL] at h
  | false :: r, h => by
    simp only [decL, Option.map_eq_none_iff] at h
    simp [bitsValue, Nat.bit_val, decL_none r h]

/-- The drop loop's meaning on (exponent word, magnitude word). -/
def loopF (L : List Bool) : List Bool → List Bool
  | [] => []
  | z :: Zs => match decL L with
    | none => z :: Zs
    | some L' => loopF L' Zs

theorem loopF_eq : ∀ (Zs L : List Bool), loopF L Zs = Zs.drop (bitsValue L)
  | [], L => by simp [loopF]
  | z :: Zs, L => by
    cases hd : decL L with
    | none => simp [loopF, hd, decL_none L hd]
    | some L' => simp [loopF, hd, decL_value L L' hd, loopF_eq Zs L']

theorem dec_zeros (rest : List Bool) : ∀ (k : ℕ) (S : Stk → List Bool) (v : Ctl),
    S .J2 = List.replicate k false ++ rest →
    ∃ v' : Ctl, ((advance program)^[k]) (⟨some .dec, v, S⟩ : Cfg) =
      ⟨some .dec, v', Function.update (Function.update S .J2 rest) .T
        (List.replicate k true ++ S .T)⟩ ∧ v'.sign = v.sign ∧ v'.lt = v.lt
  | 0, S, v, hS => by
    refine ⟨v, ?_, rfl, rfl⟩
    simp only [List.replicate_zero, List.nil_append] at hS
    simp only [Function.iterate_zero, id, List.replicate_zero, List.nil_append]
    congr 1
    funext k
    by_cases hk : k = .T
    · subst hk; simp [Function.update_apply]
    · by_cases hk' : k = .J2
      · subst hk'; simp [Function.update_apply, hS]
      · simp [Function.update_apply, hk, hk']
  | k + 1, S, v, hS => by
    have hstep : advance program (⟨some .dec, v, S⟩ : Cfg) =
        ⟨some .dec, { v with x := some false },
          Function.update (Function.update S .J2 (List.replicate k false ++ rest)) .T
            (true :: S .T)⟩ := by
      simp [advance, TM2.step, TM2.stepAux, program, hS, List.replicate_succ]
    obtain ⟨v', hrun, h1, h2⟩ := dec_zeros rest k
      (Function.update (Function.update S .J2 (List.replicate k false ++ rest)) .T
        (true :: S .T)) { v with x := some false }
      (by simp [Function.update_apply])
    refine ⟨v', ?_, h1, h2⟩
    rw [Function.iterate_succ_apply, hstep, hrun]
    congr 1
    funext j
    by_cases hj : j = .T
    · subst hj; simp [Function.update_apply, List.replicate_succ', List.append_assoc]
    · by_cases hj' : j = .J2
      · subst hj'; simp [Function.update_apply]
      · simp [Function.update_apply, hj, hj']

theorem rst_ones : ∀ (k : ℕ) (S : Stk → List Bool) (v : Ctl),
    S .T = List.replicate k true →
    ∃ v' : Ctl, ((advance program)^[k]) (⟨some .rst, v, S⟩ : Cfg) =
      ⟨some .rst, v', Function.update (Function.update S .T []) .J2
        (List.replicate k true ++ S .J2)⟩ ∧ v'.sign = v.sign ∧ v'.lt = v.lt
  | 0, S, v, hS => by
    refine ⟨v, ?_, rfl, rfl⟩
    simp only [Function.iterate_zero, id, List.replicate_zero, List.nil_append]
    congr 1
    funext k
    by_cases hk : k = .T
    · subst hk; simp [Function.update_apply, hS]
    · by_cases hk' : k = .J2
      · subst hk'; simp [Function.update_apply]
      · simp [Function.update_apply, hk, hk']
  | k + 1, S, v, hS => by
    have hstep : advance program (⟨some .rst, v, S⟩ : Cfg) =
        ⟨some .rst, { v with x := some true },
          Function.update (Function.update S .T (List.replicate k true)) .J2
            (true :: S .J2)⟩ := by
      simp [advance, TM2.step, TM2.stepAux, program, hS, List.replicate_succ]
    obtain ⟨v', hrun, h1, h2⟩ := rst_ones k
      (Function.update (Function.update S .T (List.replicate k true)) .J2
        (true :: S .J2)) { v with x := some true }
      (by simp [Function.update_apply])
    refine ⟨v', ?_, h1, h2⟩
    rw [Function.iterate_succ_apply, hstep, hrun]
    congr 1
    funext j
    by_cases hj : j = .T
    · subst hj; simp [Function.update_apply]
    · by_cases hj' : j = .J2
      · subst hj'; simp [Function.update_apply, List.replicate_succ', List.append_assoc]
      · simp [Function.update_apply, hj, hj']

theorem loop_run : ∀ (Zs L : List Bool) (S : Stk → List Bool) (v : Ctl),
    S .J2 = L → S .T = [] → S .Z2 = Zs →
    ∃ n ≤ (Zs.length + 1) * (2 * L.length + 3), ∃ (v' : Ctl) (S' : Stk → List Bool),
      ((advance program)^[n]) (⟨some .dec, v, S⟩ : Cfg) = ⟨some .cmp, v', S'⟩ ∧
      S' .Z2 = loopF L Zs ∧ S' .O = S .O ∧ S' .M2 = S .M2 ∧ v'.lt = v.lt := by
  intro Zs
  induction Zs with
  | nil =>
    intro L S v hJ hT hZ
    rcases shape L with ⟨k, r, rfl⟩ | ⟨k, rfl⟩
    · obtain ⟨v1, h1, _, hl1⟩ := dec_zeros (true :: r) k S v (by rw [hJ])
      set S1 := Function.update (Function.update S .J2 (true :: r)) .T
        (List.replicate k true ++ S .T) with hS1
      have hstep2 : advance program (⟨some .dec, v1, S1⟩ : Cfg) =
          ⟨some .rst, { v1 with x := some true },
            Function.update (Function.update S1 .J2 r) .J2 (false :: r)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, program, hS1, Function.update_apply]
      set S2 := Function.update (Function.update S1 .J2 r) .J2 (false :: r) with hS2
      obtain ⟨v3, h3, _, hl3⟩ := rst_ones k S2 { v1 with x := some true }
        (by simp [hS2, hS1, Function.update_apply, hT])
      set S3 := Function.update (Function.update S2 .T []) .J2 (List.replicate k true ++ S2 .J2)
        with hS3
      have hZ3 : S3 .Z2 = [] := by simp [hS3, hS2, hS1, Function.update_apply, hZ]
      have hstep4 : advance program (⟨some .rst, v3, S3⟩ : Cfg) =
          ⟨some .cmp, { v3 with x := none }, Function.update (Function.update S3 .T []) .Z2 []⟩ := by
        have hT3 : S3 .T = [] := by simp [hS3, Function.update_apply]
        simp [advance, TM2.step, TM2.stepAux, program, hT3, hZ3]
      refine ⟨k + 1 + k + 1, ?_, { v3 with x := none },
        Function.update (Function.update S3 .T []) .Z2 [], ?_, ?_, ?_, ?_, ?_⟩
      · simp; nlinarith
      · rw [show k + 1 + k + 1 = 1 + (k + (1 + k)) by omega, Function.iterate_add_apply,
          Function.iterate_add_apply, Function.iterate_add_apply]
        simp only [Function.iterate_one, h1, hstep2, h3, hstep4]
      · simp [loopF]
      · simp [hS3, hS2, hS1, Function.update_apply]
      · simp [hS3, hS2, hS1, Function.update_apply]
      · simp [hl3, hl1]
    · obtain ⟨v1, h1, _, hl1⟩ := dec_zeros [] k S v (by rw [hJ]; simp)
      set S1 := Function.update (Function.update S .J2 []) .T (List.replicate k true ++ S .T)
        with hS1
      have hstep2 : advance program (⟨some .dec, v1, S1⟩ : Cfg) =
          ⟨some .cmp, { v1 with x := none }, Function.update S1 .J2 []⟩ := by
        simp [advance, TM2.step, TM2.stepAux, program, hS1, Function.update_apply]
      refine ⟨k + 1, ?_, { v1 with x := none }, Function.update S1 .J2 [], ?_, ?_, ?_, ?_, ?_⟩
      · simp; nlinarith
      · rw [Function.iterate_succ_apply', h1, hstep2]
      · simp [hS1, Function.update_apply, hZ, loopF]
      · simp [hS1, Function.update_apply]
      · simp [hS1, Function.update_apply]
      · simp [hl1]
  | cons z Zs ih =>
    intro L S v hJ hT hZ
    rcases shape L with ⟨k, r, rfl⟩ | ⟨k, rfl⟩
    · obtain ⟨v1, h1, _, hl1⟩ := dec_zeros (true :: r) k S v (by rw [hJ])
      set S1 := Function.update (Function.update S .J2 (true :: r)) .T
        (List.replicate k true ++ S .T) with hS1
      have hstep2 : advance program (⟨some .dec, v1, S1⟩ : Cfg) =
          ⟨some .rst, { v1 with x := some true },
            Function.update (Function.update S1 .J2 r) .J2 (false :: r)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, program, hS1, Function.update_apply]
      set S2 := Function.update (Function.update S1 .J2 r) .J2 (false :: r) with hS2
      obtain ⟨v3, h3, _, hl3⟩ := rst_ones k S2 { v1 with x := some true }
        (by simp [hS2, hS1, Function.update_apply, hT])
      set S3 := Function.update (Function.update S2 .T []) .J2 (List.replicate k true ++ S2 .J2)
        with hS3
      have hZ3 : S3 .Z2 = z :: Zs := by simp [hS3, hS2, hS1, Function.update_apply, hZ]
      have hT3 : S3 .T = [] := by simp [hS3, Function.update_apply]
      have hstep4 : advance program (⟨some .rst, v3, S3⟩ : Cfg) =
          ⟨some .dec, { v3 with x := some z },
            Function.update (Function.update S3 .T []) .Z2 Zs⟩ := by
        simp [advance, TM2.step, TM2.stepAux, program, hT3, hZ3]
      set S4 := Function.update (Function.update S3 .T []) .Z2 Zs with hS4
      have hJ4 : S4 .J2 = List.replicate k true ++ false :: r := by
        simp [hS4, hS3, hS2, hS1, Function.update_apply]
      obtain ⟨n, hn, v5, S5, h5, hZ5, hO5, hM5, hl5⟩ :=
        ih (List.replicate k true ++ false :: r) S4 { v3 with x := some z } hJ4
          (by simp [hS4, Function.update_apply]) (by simp [hS4, Function.update_apply])
      refine ⟨k + 1 + k + 1 + n, ?_, v5, S5, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons, List.length_append, List.length_replicate] at hn ⊢
        nlinarith
      · rw [show k + 1 + k + 1 + n = n + (1 + (k + (1 + k))) by omega, Function.iterate_add_apply,
          Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply]
        simp only [Function.iterate_one, h1, hstep2, h3, hstep4, h5]
      · rw [hZ5]; simp [loopF, decL_zeros_true]
      · rw [hO5]; simp [hS4, hS3, hS2, hS1, Function.update_apply]
      · rw [hM5]; simp [hS4, hS3, hS2, hS1, Function.update_apply]
      · simp [hl5, hl3, hl1]
    · obtain ⟨v1, h1, _, hl1⟩ := dec_zeros [] k S v (by rw [hJ]; simp)
      set S1 := Function.update (Function.update S .J2 []) .T (List.replicate k true ++ S .T)
        with hS1
      have hstep2 : advance program (⟨some .dec, v1, S1⟩ : Cfg) =
          ⟨some .cmp, { v1 with x := none }, Function.update S1 .J2 []⟩ := by
        simp [advance, TM2.step, TM2.stepAux, program, hS1, Function.update_apply]
      refine ⟨k + 1, ?_, { v1 with x := none }, Function.update S1 .J2 [], ?_, ?_, ?_, ?_, ?_⟩
      · simp; nlinarith
      · rw [Function.iterate_succ_apply', h1, hstep2]
      · simp [hS1, Function.update_apply, hZ, loopF, decL_zeros]
      · simp [hS1, Function.update_apply]
      · simp [hS1, Function.update_apply]
      · simp [hl1]

/-! ## The comparison loop -/

/-- Meaning of the comparison loop. -/
def cmpF : List Bool → List Bool → Bool → Bool
  | [], [], lt => lt
  | [], b :: bs, lt => cmpF [] bs (cmpStep none (some b) lt)
  | a :: as, [], lt => cmpF as [] (cmpStep (some a) none lt)
  | a :: as, b :: bs, lt => cmpF as bs (cmpStep (some a) (some b) lt)

theorem bitsValue_cons (a : Bool) (as : List Bool) :
    bitsValue (a :: as) = 2 * bitsValue as + a.toNat := by
  simp [bitsValue, Nat.bit_val]

theorem cmpF_nil_left : ∀ (bs : List Bool) (lt : Bool),
    cmpF [] bs lt = decide (0 < bitsValue bs ∨ (0 = bitsValue bs ∧ lt = true))
  | [], lt => by simp [cmpF, bitsValue]
  | b :: bs, lt => by
    rw [cmpF, cmpF_nil_left bs, bitsValue_cons]
    generalize bitsValue bs = y
    cases b <;> cases lt <;> simp [cmpStep] <;> first | omega | (rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)

theorem cmpF_eq : ∀ (as bs : List Bool) (lt : Bool),
    cmpF as bs lt = decide (bitsValue as < bitsValue bs ∨
      (bitsValue as = bitsValue bs ∧ lt = true))
  | [], bs, lt => by simpa [bitsValue] using cmpF_nil_left bs lt
  | a :: as, [], lt => by
    rw [cmpF, cmpF_eq as [], bitsValue_cons]
    simp only [bitsValue]
    generalize bitsValue as = x
    cases a <;> cases lt <;> simp [cmpStep]
  | a :: as, b :: bs, lt => by
    rw [cmpF, cmpF_eq as bs, bitsValue_cons, bitsValue_cons]
    generalize bitsValue as = x
    generalize bitsValue bs = y
    cases a <;> cases b <;> cases lt <;> simp [cmpStep] <;> first | omega | (rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)

theorem cmp_nil_left : ∀ (bs : List Bool) (S : Stk → List Bool) (v : Ctl),
    S .Z2 = [] → S .M2 = bs →
    ∃ (v' : Ctl) (S' : Stk → List Bool),
      ((advance program)^[bs.length + 1]) (⟨some .cmp, v, S⟩ : Cfg) = ⟨none, v', S'⟩ ∧
      S' .O = cmpF [] bs v.lt :: S .O
  | [], S, v, hZ, hM => by
    refine ⟨{ v with x := none, y := none },
      Function.update (Function.update (Function.update S .Z2 []) .M2 []) .O (v.lt :: S .O), ?_,
      by simp [Function.update_apply, cmpF]⟩
    simp only [List.length_nil, zero_add, Function.iterate_one]
    simp [advance, TM2.step, TM2.stepAux, program, hZ, hM]
  | b :: bs, S, v, hZ, hM => by
    have hstep : advance program (⟨some .cmp, v, S⟩ : Cfg) =
        ⟨some .cmp, { v with x := none, y := some b, lt := cmpStep none (some b) v.lt },
          Function.update (Function.update S .Z2 []) .M2 bs⟩ := by
      simp [advance, TM2.step, TM2.stepAux, program, hZ, hM]
    obtain ⟨v', S', hrun, hO⟩ := cmp_nil_left bs
      (Function.update (Function.update S .Z2 []) .M2 bs) { v with x := none, y := some b, lt := cmpStep none (some b) v.lt }
      (by simp [Function.update_apply]) (by simp [Function.update_apply])
    refine ⟨v', S', ?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, hstep, hrun]
    · rw [hO]; simp [cmpF, Function.update_apply]

theorem cmp_run : ∀ (as bs : List Bool) (S : Stk → List Bool) (v : Ctl),
    S .Z2 = as → S .M2 = bs →
    ∃ (v' : Ctl) (S' : Stk → List Bool),
      ((advance program)^[max as.length bs.length + 1]) (⟨some .cmp, v, S⟩ : Cfg) =
        ⟨none, v', S'⟩ ∧ S' .O = cmpF as bs v.lt :: S .O
  | [], bs, S, v, hZ, hM => by simpa using cmp_nil_left bs S v hZ hM
  | a :: as, [], S, v, hZ, hM => by
    have hstep : advance program (⟨some .cmp, v, S⟩ : Cfg) =
        ⟨some .cmp, { v with x := some a, y := none, lt := cmpStep (some a) none v.lt },
          Function.update (Function.update S .Z2 as) .M2 []⟩ := by
      simp [advance, TM2.step, TM2.stepAux, program, hZ, hM]
    obtain ⟨v', S', hrun, hO⟩ := cmp_run as []
      (Function.update (Function.update S .Z2 as) .M2 []) { v with x := some a, y := none, lt := cmpStep (some a) none v.lt }
      (by simp [Function.update_apply]) (by simp [Function.update_apply])
    refine ⟨v', S', ?_, ?_⟩
    · simp only [List.length_cons, List.length_nil] at hrun ⊢
      rw [show max (as.length + 1) 0 + 1 = (max as.length 0 + 1) + 1 by simp,
        Function.iterate_succ_apply, hstep, hrun]
    · rw [hO]; simp [cmpF, Function.update_apply]
  | a :: as, b :: bs, S, v, hZ, hM => by
    have hstep : advance program (⟨some .cmp, v, S⟩ : Cfg) =
        ⟨some .cmp, { v with x := some a, y := some b, lt := cmpStep (some a) (some b) v.lt },
          Function.update (Function.update S .Z2 as) .M2 bs⟩ := by
      simp [advance, TM2.step, TM2.stepAux, program, hZ, hM]
    obtain ⟨v', S', hrun, hO⟩ := cmp_run as bs
      (Function.update (Function.update S .Z2 as) .M2 bs) { v with x := some a, y := some b, lt := cmpStep (some a) (some b) v.lt }
      (by simp [Function.update_apply]) (by simp [Function.update_apply])
    refine ⟨v', S', ?_, ?_⟩
    · simp only [List.length_cons]
      rw [show max (as.length + 1) (bs.length + 1) + 1 = (max as.length bs.length + 1) + 1 by
        omega, Function.iterate_succ_apply, hstep, hrun]
    · rw [hO]; simp [cmpF, Function.update_apply]

end Paper2.CmpOwner
