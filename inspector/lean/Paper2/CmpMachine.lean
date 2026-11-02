import EthInapproximability.CurrentPaper.BitMachineEncoding
import EthInapproximability.CurrentPaper.EncodedComplexity
import Mathlib.Tactic

/-!
# WP-U18a (ii), segment M2: the dyadic comparator as ONE literal finite program (part 1)

Lane `owner:a-cmp-1` (private, 27 September 2026). Paper A, lock v12, I:73-76 (footnote: "The
numerical output must permit polynomial-time comparison with binary rationals of polynomial
length") and I:120 ("Accept the source exactly when its estimate is below B+k/2").
Decision implemented: D-A3 (ii) (lane a-model's dyadic codec `encodeInteger z ++ natField j`).

The program runs on the input `pair w out = field w ++ out` and a bank of nine Boolean stacks:
* phase `a`: decode `field w` pair by pair; a three-state finite automaton extracts the leading
  field `lead w` of `w` (the threshold numerator `m`, LSB first) onto `M` (reversed);
* `revM`: move `M` to `M2` (so `M2 = lead w`, LSB on top);
* `sgn`, `zf`, `zchk`, `revZ`, `jf`, `jchk`, `revJ`: parse `out` exactly as
  `Paper2.AModel.readDyadic` (sign bit, canonical magnitude field, canonical exponent field,
  nothing after, no negative zero); any failure prints `[false]`;
* `neg`: a negative numerator prints `[true]`; otherwise push one `false` in front of the
  magnitude (the doubling `2z`);
* `dec`/`rst`: binary decrement of the exponent, one magnitude bit dropped per decrement
  (`⌊2z / 2^j⌋`, never forming `2^j`);
* `cmp`: one lockstep LSB-first comparison of the remaining bits with `M2`; print the bit.

Every stack change is a transition; nothing is inserted.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Paper2.CmpOwner

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.EncodedCommunication (field readField bitsValue)

/-- The nine stacks. -/
inductive Stk | I | O | M | M2 | Z | Z2 | J | J2 | T
  deriving DecidableEq, Fintype

/-- The three states of the lead-field automaton inside phase `a`. -/
inductive Mode | tag | bit | done
  deriving DecidableEq, Fintype

/-- Labels. -/
inductive Lbl | a | revM | sgn | zf | zchk | revZ | jf | jchk | revJ | neg | dec | rst | cmp
  deriving DecidableEq, Fintype

/-- Finite control: two popped cells, the automaton state, the sign, the last payload bit of the
field being parsed, and the running comparison bit. -/
structure Ctl where
  x : Option Bool
  y : Option Bool
  im : Mode
  sign : Bool
  ll : Option Bool
  lt : Bool
  deriving DecidableEq, Fintype

abbrev St := TM2.Stmt (fun _ : Stk => Bool) Lbl Ctl
abbrev Cfg := TM2.Cfg (fun _ : Stk => Bool) Lbl Ctl

/-- Initial control. -/
def ctl0 : Ctl := ⟨none, none, .tag, false, none, false⟩

/-- Reject: print `false` and halt. -/
def rej : St := push .O (fun _ => false) halt

/-- Move `src` onto `dst` (reversing), then go to `next`. -/
def mvStmt (src dst : Stk) (next self : Lbl) : St :=
  pop src (fun v b => { v with x := b })
    (branch (fun v => v.x.isSome) (push dst (fun v => v.x.getD false) (goto fun _ => self))
      (goto fun _ => next))

/-- Parse one `field` from `I` onto `dst` (reversed), recording the last payload bit in `ll`. -/
def fieldStmt (dst : Stk) (next self : Lbl) : St :=
  pop .I (fun v b => { v with x := b })
    (branch (fun v => decide (v.x = some true))
      (pop .I (fun v b => { v with x := b })
        (branch (fun v => v.x.isSome)
          (push dst (fun v => v.x.getD false) (load (fun v => { v with ll := v.x })
            (goto fun _ => self)))
          rej))
      (branch (fun v => decide (v.x = some false)) (goto fun _ => next) rej))

/-- One comparison step on the popped cells (LSB first). -/
def cmpStep : Option Bool → Option Bool → Bool → Bool
  | some a, some b, lt => if a = b then lt else (!a && b)
  | some a, none, lt => lt && !a
  | none, some b, lt => lt || b
  | none, none, lt => lt

/-- Next automaton state after reading one bit of `w`. -/
def nextMode (m : Mode) (b : Option Bool) : Mode :=
  match m with
  | .tag => if b = some true then .bit else .done
  | .bit => .tag
  | .done => .done

/-- The comparator program. -/
def program : Lbl → St
  | .a => pop .I (fun v b => { v with x := b })
      (branch (fun v => decide (v.x = some true))
        (pop .I (fun v b => { v with y := b })
          (branch (fun v => decide (v.im = .bit))
            (push .M (fun v => v.y.getD false)
              (load (fun v => { v with im := nextMode v.im v.y }) (goto fun _ => .a)))
            (load (fun v => { v with im := nextMode v.im v.y }) (goto fun _ => .a))))
        (goto fun _ => .revM))
  | .revM => mvStmt .M .M2 .sgn .revM
  | .sgn => pop .I (fun v b => { v with x := b })
      (branch (fun v => v.x.isSome)
        (load (fun v => { v with sign := v.x.getD false }) (goto fun _ => .zf)) rej)
  | .zf => fieldStmt .Z .zchk .zf
  | .zchk => branch (fun v => decide (v.ll = some false) || (v.sign && decide (v.ll = none))) rej
      (load (fun v => { v with ll := none }) (goto fun _ => .revZ))
  | .revZ => mvStmt .Z .Z2 .jf .revZ
  | .jf => fieldStmt .J .jchk .jf
  | .jchk => branch (fun v => decide (v.ll = some false)) rej
      (pop .I (fun v b => { v with x := b })
        (branch (fun v => v.x.isSome) rej (goto fun _ => .revJ)))
  | .revJ => mvStmt .J .J2 .neg .revJ
  | .neg => branch (fun v => v.sign) (push .O (fun _ => true) halt)
      (push .Z2 (fun _ => false) (goto fun _ => .dec))
  | .dec => pop .J2 (fun v b => { v with x := b })
      (branch (fun v => decide (v.x = some false)) (push .T (fun _ => true) (goto fun _ => .dec))
        (branch (fun v => decide (v.x = some true)) (push .J2 (fun _ => false) (goto fun _ => .rst))
          (goto fun _ => .cmp)))
  | .rst => pop .T (fun v b => { v with x := b })
      (branch (fun v => v.x.isSome) (push .J2 (fun _ => true) (goto fun _ => .rst))
        (pop .Z2 (fun v b => { v with x := b })
          (branch (fun v => v.x.isSome) (goto fun _ => .dec) (goto fun _ => .cmp))))
  | .cmp => pop .Z2 (fun v b => { v with x := b }) (pop .M2 (fun v b => { v with y := b })
      (branch (fun v => v.x.isSome || v.y.isSome)
        (load (fun v => { v with lt := cmpStep v.x v.y v.lt }) (goto fun _ => .cmp))
        (push .O (fun v => v.lt) halt)))

/-- The comparator as a production `BitMachine.Machine` (input stack `I`, output stack `O`). -/
noncomputable def machine : BitMachine.Machine := ofFinite Stk.I Stk.O Lbl.a ctl0 program

/-! ## Phase lemmas -/

theorem mv_run (P : Lbl → St) (src dst : Stk) (next self : Lbl)
    (hP : P self = mvStmt src dst next self) (h : src ≠ dst) :
    ∀ (xs : List Bool) (S : Stk → List Bool) (v : Ctl), S src = xs →
    ((advance P)^[xs.length + 1]) (⟨some self, v, S⟩ : Cfg) =
      ⟨some next, { v with x := none },
        Function.update (Function.update S src []) dst (xs.reverse ++ S dst)⟩
  | [], S, v, hS => by
    simp only [List.length_nil, zero_add, Function.iterate_one]
    simp [advance, TM2.step, TM2.stepAux, mvStmt, hP, hS, Function.update_apply, Ne.symm h]
  | b :: xs, S, v, hS => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : advance P (⟨some self, v, S⟩ : Cfg) =
        ⟨some self, { v with x := some b },
          Function.update (Function.update S src xs) dst (b :: S dst)⟩ := by
      simp [advance, TM2.step, TM2.stepAux, mvStmt, hP, hS, Function.update_apply, Ne.symm h]
    rw [hstep, mv_run P src dst next self hP h xs _ _ (by simp [Function.update_apply, h])]
    congr 1
    funext k
    by_cases hk : k = dst
    · subst hk; simp [Function.update_apply, Ne.symm h]
    · by_cases hk' : k = src
      · subst hk'; simp [Function.update_apply, hk]
      · simp [Function.update_apply, hk, hk']

/-- Last payload bit seen (starting from `l`). -/
def lastOr : Option Bool → List Bool → Option Bool
  | l, [] => l
  | _, b :: bs => lastOr (some b) bs

theorem field_run (P : Lbl → St) (dst : Stk) (next self : Lbl)
    (hP : P self = fieldStmt dst next self) (hd : dst ≠ .I) (hdO : dst ≠ .O) :
    ∀ (inp : List Bool) (S : Stk → List Bool) (v : Ctl), S .I = inp →
    (∀ bs rest, readField inp = some (bs, rest) →
      ∃ v' : Ctl, ((advance P)^[bs.length + 1]) (⟨some self, v, S⟩ : Cfg) =
        ⟨some next, v', Function.update (Function.update S .I rest) dst (bs.reverse ++ S dst)⟩ ∧
        v'.sign = v.sign ∧ v'.lt = v.lt ∧ v'.ll = lastOr v.ll bs) ∧
    (readField inp = none → ∃ n ≤ inp.length + 1, ∃ (v' : Ctl) (S' : Stk → List Bool),
      ((advance P)^[n]) (⟨some self, v, S⟩ : Cfg) = ⟨none, v', S'⟩ ∧ S' .O = false :: S .O)
  | [], S, v, hS => by
    refine ⟨fun bs rest h => by simp [readField] at h, fun _ => ⟨1, by simp, ?_⟩⟩
    refine ⟨{ v with x := none }, Function.update (Function.update S .I []) .O (false :: S .O),
      ?_, by simp⟩
    simp [advance, TM2.step, TM2.stepAux, fieldStmt, rej, hP, hS, Function.update_apply]
  | false :: rest, S, v, hS => by
    refine ⟨fun bs rest' h => ?_, fun h => by simp [readField] at h⟩
    simp only [readField, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨{ v with x := some false }, ?_, rfl, rfl, rfl⟩
    simp only [List.length_nil, zero_add, Function.iterate_one]
    simp [advance, TM2.step, TM2.stepAux, fieldStmt, hP, hS, Function.update_apply]
    intro h; exact absurd h hd
  | [true], S, v, hS => by
    refine ⟨fun bs rest h => by simp [readField] at h, fun _ => ⟨1, by simp, ?_⟩⟩
    refine ⟨{ v with x := none },
      Function.update (Function.update (Function.update S .I []) .I []) .O (false :: S .O),
      ?_, by simp⟩
    simp [advance, TM2.step, TM2.stepAux, fieldStmt, rej, hP, hS, Function.update_apply]
  | true :: b :: rest, S, v, hS => by
    have hstep : advance P (⟨some self, v, S⟩ : Cfg) =
        ⟨some self, { v with x := some b, ll := some b },
          Function.update (Function.update S .I rest) dst (b :: S dst)⟩ := by
      simp [advance, TM2.step, TM2.stepAux, fieldStmt, hP, hS, Function.update_apply, hd]
    have ih := field_run P dst next self hP hd hdO rest
      (Function.update (Function.update S .I rest) dst (b :: S dst))
      { v with x := some b, ll := some b } (by simp [Function.update_apply, Ne.symm hd])
    constructor
    · intro bs rest' h
      cases hr : readField rest with
      | none => simp [readField, hr] at h
      | some p =>
        rcases p with ⟨bs0, suf⟩
        simp only [readField, hr, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
          Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨v', hrun, h1, h2, h3⟩ := ih.1 bs0 suf hr
        refine ⟨v', ?_, h1, h2, h3⟩
        rw [List.length_cons, Function.iterate_succ_apply, hstep, hrun]
        congr 1
        funext k
        by_cases hk : k = dst
        · subst hk; simp [Function.update_apply, hd]
        · by_cases hk' : k = .I
          · subst hk'; simp [Function.update_apply, hk]
          · simp [Function.update_apply, hk, hk']
    · intro h
      cases hr : readField rest with
      | some p =>
        rcases p with ⟨bs0, suf⟩
        simp [readField, hr] at h
      | none =>
        obtain ⟨n, hn, v', S', hrun, hO⟩ := ih.2 hr
        refine ⟨n + 1, by simp; omega, v', S', ?_, ?_⟩
        · rw [Function.iterate_succ_apply, hstep, hrun]
        · rw [hO]; simp [Function.update_apply, Ne.symm hdO]

/-- The lead-field automaton: the payload of the leading `field` of `w` (LSB first). -/
def lead' : Mode → List Bool → List Bool
  | _, [] => []
  | m, b :: r => (if m = .bit then [b] else []) ++ lead' (nextMode m (some b)) r

/-- `lead w`: the threshold numerator bits carried by `w` (LSB first). -/
def lead (w : List Bool) : List Bool := lead' .tag w

theorem lead'_done : ∀ w, lead' .done w = []
  | [] => rfl
  | b :: w => by simp [lead', nextMode, lead'_done w]

theorem lead_field (bs rest : List Bool) : lead (field bs ++ rest) = bs := by
  induction bs with
  | nil => simp [lead, field, lead', nextMode, lead'_done]
  | cons b bs ih => simpa [lead, field, lead', nextMode] using ih

theorem a_run (rest : List Bool) : ∀ (w : List Bool) (S : Stk → List Bool) (v : Ctl),
    S .I = field w ++ rest →
    ∃ v' : Ctl, ((advance program)^[w.length + 1]) (⟨some .a, v, S⟩ : Cfg) =
      ⟨some .revM, v', Function.update (Function.update S .I rest) .M
        ((lead' v.im w).reverse ++ S .M)⟩ ∧ v'.sign = v.sign ∧ v'.lt = v.lt ∧ v'.ll = v.ll
  | [], S, v, hS => by
    refine ⟨{ v with x := some false }, ?_, rfl, rfl, rfl⟩
    simp only [List.length_nil, zero_add, Function.iterate_one]
    simp [advance, TM2.step, TM2.stepAux, program, hS, field, lead', Function.update_apply]
  | b :: w, S, v, hS => by
    have hstep : advance program (⟨some .a, v, S⟩ : Cfg) =
        ⟨some .a, { v with x := some true, y := some b, im := nextMode v.im (some b) },
          Function.update (Function.update S .I (field w ++ rest)) .M
            ((if v.im = .bit then [b] else []) ++ S .M)⟩ := by
      by_cases him : v.im = .bit
      · simp [advance, TM2.step, TM2.stepAux, program, hS, field, him, Function.update_apply]
      · simp [advance, TM2.step, TM2.stepAux, program, hS, field, him, Function.update_apply]
    obtain ⟨v', hrun, h1, h2, h3⟩ := a_run rest w
      (Function.update (Function.update S .I (field w ++ rest)) .M
        ((if v.im = .bit then [b] else []) ++ S .M))
      { v with x := some true, y := some b, im := nextMode v.im (some b) }
      (by simp [Function.update_apply])
    refine ⟨v', ?_, h1, h2, h3⟩
    rw [List.length_cons, Function.iterate_succ_apply, hstep, hrun]
    congr 1
    funext k
    by_cases hk : k = .M
    · subst hk
      by_cases him : v.im = .bit
      · simp [Function.update_apply, lead', List.reverse_append, him]
      · simp [Function.update_apply, lead', List.reverse_append, him]
    · by_cases hk' : k = .I
      · subst hk'; simp [Function.update_apply]
      · simp [Function.update_apply, hk, hk']

end Paper2.CmpOwner
