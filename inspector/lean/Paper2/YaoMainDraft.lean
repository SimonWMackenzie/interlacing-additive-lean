import Paper2.YaoEndpoint
import Paper2.YaoT26Size

/-! Unit 5 segment Y13 (lane a-yao-owner-4): T25 `yao:main` (lock v12 Y:26-42,
proof Y:331-337) as a HYP-parametric composition.

* Source (X05 / T26): the admitted DRAFT record `G : GLSourceDraft t` (AD-1, D-A2:
  NOT adopted, never instantiated; `G.L` is the D-A2 language parameter) composed
  with the physical clone machine: `sourceMachine G` / `draft_yao_source`
  (frozen private lane a-yao-clone-owner-1, under root admission wave13b-a26).
* Materialiser (T30): the ONE fixed framed program `yaoFramed t lambda`
  (`physical_yao_framed`, import-only copy `Y4Frame` of lane a-yao-owner-3).
* Composition: ONE fixed program `yaoMain G lambda` on the bank
  `MStack G lambda = Fin (sourceMachine G).stackCount ⊕ FStack t lambda`:
  stage 1 is the source machine's literal program with its stacks placed by the
  injective `srcEmb` (its OUTPUT stack is the materialiser's code cell `sN 0`, so
  the handoff of the code costs nothing extra and is not an inserted value);
  stage 2 is `yaoFramed` on the right summand.  One charged administrative
  handoff (`BitMachineRawSequence.program`).

**D-A1 (author decision, untaken): the randomized-machine model used here is a
marked DRAFT option "two charged input cells".**  The fixed deterministic program
starts with the input word in the source machine's input cell and the random
tape in the materialiser's raw tape cell (the only two nonempty cells); the tape
law is the uniform law on exact-length tapes, `serializedTapeLaw`, i.e. the raw
tape of the materialiser.  Repackaging as the unit-4 DRAFT
`RandomizedAlgorithm` (a `BitMachine.Machine` on `pair input tape`) is NOT done
here (it needs a pair splitter and `Fintype` label/control instances for
`BitMachineEncoding.ofFinite`); see the lane CHECKPOINT.

Scope: valid upstream codes only (R-Y2) is automatic here: the materialiser's
code is produced by the source machine.  The instance format and language are the
R-Y3 DRAFTs `yaoInstanceDraft` / `yaoLanguageDraft`.  No Yao endpoint completion
claim; no ledger row is closed. -/

noncomputable section

namespace Paper2.YaoMainDraft

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open EthInapproximability.CurrentPaper.EncodedCommunication
open Paper2.Yao
open Paper2.YaoLookup
open Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization
open Paper2.YaoMaterialization
open Paper2.YaoSourceCodec
open Paper2.YaoMachine
open Paper2.YaoFrame
open Paper2.YaoX05Draft
open Paper2.YaoT26Draft
open Paper2.YaoCloneSource

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384
set_option linter.unusedSimpArgs false

variable {t : ℕ}

/-- The Yao source printed by the (DRAFT-record) source machine on `input`. -/
def src (G : GLSourceDraft t) (input : List Bool) : YaoSource t :=
  cloneSource t (forbiddenColours t) (G.output input)

/-- The composed bank. -/
abbrev MStack (G : GLSourceDraft t) (lambda : ℕ) :=
  Fin (sourceMachine G).stackCount ⊕ FStack t lambda

instance instDecEqMStack (G : GLSourceDraft t) (lambda : ℕ) : DecidableEq (MStack G lambda) :=
  inferInstanceAs (DecidableEq (Fin (sourceMachine G).stackCount ⊕ FStack t lambda))

/-- The materialiser's code cell (`sN 0`, holding `encode x` in `initBank`). -/
def codeCell {t lambda : ℕ} : FStack t lambda := .inl (sN 0)
/-- The materialiser's raw tape cell. -/
def tapeCell {t lambda : ℕ} : FStack t lambda := .inl (st (.inl (Paper2.YaoEntryControllerJoin.tapeSource t lambda)))

theorem code_ne_tape {t lambda : ℕ} : (codeCell : FStack t lambda) ≠ tapeCell := by
  intro h
  have h1 : (st (.inr (.inr 0)) : WStack t lambda) = st (.inl (Paper2.YaoEntryControllerJoin.tapeSource t lambda)) :=
    Sum.inl.inj h
  exact Sum.inr_ne_inl (st_injective h1)

/-- Placement of the source machine's stacks: its output stack is the code cell. -/
def srcFun (G : GLSourceDraft t) (lambda : ℕ) (k : Fin (sourceMachine G).stackCount) :
    MStack G lambda :=
  if k = (sourceMachine G).output then .inr codeCell else .inl k

theorem srcFun_injective (G : GLSourceDraft t) (lambda : ℕ) :
    Function.Injective (srcFun G lambda) := by
  intro a b h
  by_cases ha : a = (sourceMachine G).output <;> by_cases hb : b = (sourceMachine G).output
  · rw [ha, hb]
  · simp [srcFun, ha, hb] at h
  · simp [srcFun, ha, hb] at h
  · simpa [srcFun, ha, hb] using h

def srcEmb (G : GLSourceDraft t) (lambda : ℕ) :
    Fin (sourceMachine G).stackCount ↪ MStack G lambda :=
  ⟨srcFun G lambda, srcFun_injective G lambda⟩

def frEmb (G : GLSourceDraft t) (lambda : ℕ) : FStack t lambda ↪ MStack G lambda :=
  Function.Embedding.inr

def stage1 (G : GLSourceDraft t) (lambda : ℕ) :=
  fun l => stackStmt (srcEmb G lambda) ((sourceMachine G).program l)
def stage2 (G : GLSourceDraft t) (lambda : ℕ) :=
  fun l => stackStmt (frEmb G lambda) (yaoFramed t lambda l)

/-- **T25 machine (DRAFT D-A1 two-cell option): ONE fixed program per
`(G, lambda)`**, i.e. per `t` once the record `G : GLSourceDraft t` is fixed. -/
def yaoMain (G : GLSourceDraft t) (lambda : ℕ) :=
  BitMachineRawSequence.program (stage1 G lambda) (stage2 G lambda)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel YaoHeaderParser.startLabel))
    (sourceMachine G).initial (framedControl t lambda)

/-- The initial bank: the input word in the source machine's input cell, the
random tape in the raw tape cell, every other cell empty. -/
def mainInit (G : GLSourceDraft t) (lambda : ℕ) (input tape : List Bool) :
    MStack G lambda → List Bool :=
  fun j => if j = srcEmb G lambda (sourceMachine G).input then input
    else if j = .inr tapeCell then tape else []

/-- The exact final bank: the source machine's scratch `S` on its non-output
stacks (the named existential scratch), its output slot empty, and the exact
final bank `framedOut` of the framed materialiser on the right summand. -/
def mainOut (G : GLSourceDraft t) (lambda : ℕ) (S : Fin (sourceMachine G).stackCount → List Bool)
    (x : YaoSource t) (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda) :
    MStack G lambda → List Bool :=
  Sum.elim (fun k => if k = (sourceMachine G).output then [] else S k) (framedOut lambda x bits)

/-- The output cell of the composed machine. -/
def outCell {G : GLSourceDraft t} {lambda : ℕ} : MStack G lambda := .inr (.inl (.inr .output))

theorem mainOut_output (G : GLSourceDraft t) (lambda : ℕ) (S) (x : YaoSource t)
    (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda) :
    mainOut G lambda S x bits outCell = encodeInstance (yaoInstanceDraft t lambda x bits) :=
  framedOut_output lambda x bits

/-- The foreign bank of stage 1: only the tape cell is nonempty. -/
def foreign1 (G : GLSourceDraft t) (lambda : ℕ) (tape : List Bool) : MStack G lambda → List Bool :=
  fun j => if j = .inr tapeCell then tape else []

theorem srcEmb_ne_tape (G : GLSourceDraft t) (lambda : ℕ) (k) :
    srcEmb G lambda k ≠ .inr tapeCell := by
  show srcFun G lambda k ≠ _
  unfold srcFun
  split_ifs
  · exact fun h => code_ne_tape (Sum.inr.inj h)
  · exact Sum.inl_ne_inr

theorem init_bank (G : GLSourceDraft t) (lambda : ℕ) (input tape : List Bool) :
    bank (srcEmb G lambda) (foreign1 G lambda tape) ((sourceMachine G).init input).stk =
      mainInit G lambda input tape := by
  funext j
  by_cases h : ∃ k, srcEmb G lambda k = j
  · obtain ⟨k, rfl⟩ := h
    rw [bank_at]
    simp only [BitMachine.Machine.init, mainInit, (srcEmb G lambda).injective.eq_iff,
      srcEmb_ne_tape, if_false]
  · rw [bank_outside _ _ _ _ h]
    have h1 : j ≠ srcEmb G lambda (sourceMachine G).input := fun he => h ⟨_, he.symm⟩
    simp only [foreign1, mainInit, h1, if_false]

theorem handoff_bank (G : GLSourceDraft t) (lambda : ℕ) (input : List Bool)
    (bits : SerializedTape t (paddedEdgeBits (src G input).2.1) lambda)
    (S : Fin (sourceMachine G).stackCount → List Bool)
    (hS : S (sourceMachine G).output = encode (src G input)) (j : FStack t lambda) :
    framedInit lambda (src G input) bits.val j =
      bank (srcEmb G lambda) (foreign1 G lambda bits.val) S (frEmb G lambda j) := by
  by_cases hj : j = codeCell
  · subst hj
    have : (frEmb G lambda codeCell : MStack G lambda) = srcEmb G lambda (sourceMachine G).output := by
      show (Sum.inr codeCell : MStack G lambda) = srcFun G lambda _
      simp [srcFun]
    rw [this, bank_at, hS]
    simp [framedInit, codeCell, Paper2.YaoMachine.initBank]
  · have hnot : ¬ ∃ k, srcEmb G lambda k = frEmb G lambda j := by
      rintro ⟨k, hk⟩
      change srcFun G lambda k = Sum.inr j at hk
      unfold srcFun at hk
      split_ifs at hk
      · exact hj (Sum.inr.inj hk).symm
    rw [bank_outside _ _ _ _ hnot]
    rcases j with w | h
    · have hw : w ≠ sN 0 := fun he => hj (by rw [he]; rfl)
      by_cases ht : w = st (.inl (Paper2.YaoEntryControllerJoin.tapeSource t lambda))
      · subst ht
        simp [framedInit, Paper2.YaoMachine.initBank, foreign1, frEmb, tapeCell, hw]
      · have ht' : (Sum.inr (Sum.inl w) : MStack G lambda) ≠ .inr tapeCell := by
          intro he; exact ht (Sum.inl.inj (Sum.inr.inj he))
        simp only [framedInit, Sum.elim_inl, Paper2.YaoMachine.initBank, hw, ht, if_false,
          foreign1, frEmb, Function.Embedding.inr_apply, ht']
    · have ht' : (Sum.inr (Sum.inr h) : MStack G lambda) ≠ .inr tapeCell := by
        intro he; exact Sum.inr_ne_inl (Sum.inr.inj he)
      simp only [framedInit, Sum.elim_inr, foreign1, frEmb, Function.Embedding.inr_apply, ht',
        if_false]

theorem final_bank (G : GLSourceDraft t) (lambda : ℕ) (tape : List Bool)
    (S : Fin (sourceMachine G).stackCount → List Bool) (x : YaoSource t)
    (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda) :
    bank (frEmb G lambda) (bank (srcEmb G lambda) (foreign1 G lambda tape) S)
        (framedOut lambda x bits) = mainOut G lambda S x bits := by
  funext j
  rcases j with k | f
  · have hnot : ¬ ∃ f, frEmb G lambda f = Sum.inl k := by
      rintro ⟨f, hf⟩; exact Sum.inr_ne_inl hf
    rw [bank_outside _ _ _ _ hnot]
    by_cases hk : k = (sourceMachine G).output
    · subst hk
      have hnot2 : ¬ ∃ k', srcEmb G lambda k' = Sum.inl (sourceMachine G).output := by
        rintro ⟨k', hk'⟩
        change srcFun G lambda k' = _ at hk'
        unfold srcFun at hk'
        split_ifs at hk' with h'
        all_goals first
          | exact Sum.inr_ne_inl hk'
          | exact h' (Sum.inl.inj hk')
      rw [bank_outside _ _ _ _ hnot2]
      simp [mainOut, foreign1]
    · have h2 : bank (srcEmb G lambda) (foreign1 G lambda tape) S (Sum.inl k) = S k := by
        have : (Sum.inl k : MStack G lambda) = srcEmb G lambda k := by
          show _ = srcFun G lambda k
          simp [srcFun, hk]
        rw [this, bank_at]
      rw [h2]
      simp [mainOut, hk]
  · have : (Sum.inr f : MStack G lambda) = frEmb G lambda f := rfl
    rw [this, bank_at]
    rfl

/-- **Y13 physical run.**  From the two charged inputs (input word, raw tape) the
ONE fixed program halts with the exact final bank `mainOut`, within the source
clock plus the framed materialiser's clock plus one handoff.  The only
existentials are the final control `c'` and the source machine's scratch `S`. -/
theorem yao_main_run (G : GLSourceDraft t) (lambda : ℕ) (ht : 1 ≤ t) (input : List Bool)
    (bits : SerializedTape t (paddedEdgeBits (src G input).2.1) lambda) :
    ∃ total ≤ sourceTime G input + frameClock lambda (src G input) + 1, ∃ c' S,
      ((advance (yaoMain G lambda))^[total])
        (⟨some (BitMachineRawSequence.leftLabel (sourceMachine G).start),
          ((sourceMachine G).initial, framedControl t lambda),
          mainInit G lambda input bits.val⟩ :
          TM2.Cfg (fun _ : MStack G lambda => Bool) _ _) =
        ⟨none, c', mainOut G lambda S (src G input) bits⟩ := by
  obtain ⟨t1, ht1, hhalt, hout⟩ := (draft_yao_source G input).1
  obtain ⟨t2, ht2, c2, hrun2⟩ := physical_yao_framed t lambda ht (src G input) bits
  set c1 := (sourceMachine G).run t1 ((sourceMachine G).init input) with hc1
  have hA := BitMachineStackRun.run (srcEmb G lambda) (foreign1 G lambda bits.val)
    (sourceMachine G).program ((sourceMachine G).init input) t1
  have hc1eq : ((advance (sourceMachine G).program)^[t1]) ((sourceMachine G).init input) = c1 := rfl
  rw [hc1eq] at hA
  have ha : ((advance (stage1 G lambda))^[t1])
      (⟨some (sourceMachine G).start, (sourceMachine G).initial,
        mainInit G lambda input bits.val⟩ : TM2.Cfg (fun _ : MStack G lambda => Bool) _ _) =
      ⟨none, c1.var, bank (srcEmb G lambda) (foreign1 G lambda bits.val) c1.stk⟩ := by
    rw [← init_bank]
    have h0 : (stackCfg (srcEmb G lambda) (foreign1 G lambda bits.val)
        ((sourceMachine G).init input)) =
        ⟨some (sourceMachine G).start, (sourceMachine G).initial,
          bank (srcEmb G lambda) (foreign1 G lambda bits.val) ((sourceMachine G).init input).stk⟩ :=
      rfl
    rw [← h0]
    refine hA.trans ?_
    simp only [stackCfg]
    rw [hhalt]
  have hB := BitMachineStackRun.run (frEmb G lambda)
    (bank (srcEmb G lambda) (foreign1 G lambda bits.val) c1.stk) (yaoFramed t lambda)
    (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel YaoHeaderParser.startLabel)),
      framedControl t lambda, framedInit lambda (src G input) bits.val⟩ :
      TM2.Cfg (fun _ : FStack t lambda => Bool) _ _) t2
  rw [hrun2] at hB
  have hself : bank (frEmb G lambda) (bank (srcEmb G lambda) (foreign1 G lambda bits.val) c1.stk)
      (framedInit lambda (src G input) bits.val) =
      bank (srcEmb G lambda) (foreign1 G lambda bits.val) c1.stk :=
    bank_eq_self _ _ _ (handoff_bank G lambda input bits c1.stk hout)
  have hb : ((advance (stage2 G lambda))^[t2])
      (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel YaoHeaderParser.startLabel)),
        framedControl t lambda, bank (srcEmb G lambda) (foreign1 G lambda bits.val) c1.stk⟩ :
        TM2.Cfg (fun _ : MStack G lambda => Bool) _ _) =
      ⟨none, c2, mainOut G lambda c1.stk (src G input) bits⟩ := by
    simp only [stackCfg] at hB
    rw [hself, final_bank G lambda bits.val c1.stk] at hB
    exact hB
  obtain ⟨total, htot, hrun⟩ := BitMachineRawSequence.runs (stage1 G lambda) (stage2 G lambda)
    (sourceMachine G).start
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel YaoHeaderParser.startLabel))
    (sourceMachine G).initial c1.var (framedControl t lambda) c2
    (mainInit G lambda input bits.val) _ _ t1 t2 ha hb
  exact ⟨total, by omega, _, c1.stk, hrun⟩

/-! ## Polynomial bounds in `|input|` -/

theorem compose_poly {C d c e v m n : ℕ} (hf : v ≤ C * (m + 1) ^ d)
    (hm : m ≤ c * (n + 1) ^ e) : v ≤ (C * (c + 1) ^ d) * (n + 1) ^ (e * d) := by
  have h1 : m + 1 ≤ (c + 1) * (n + 1) ^ e := by
    have : 1 ≤ (n + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos n)
    nlinarith
  calc v ≤ C * (m + 1) ^ d := hf
    _ ≤ C * ((c + 1) * (n + 1) ^ e) ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 d)
    _ = (C * (c + 1) ^ d) * (n + 1) ^ (e * d) := by rw [mul_pow, ← pow_mul]; ring

theorem pow_le_pow_add (n a b : ℕ) : (n + 1) ^ a ≤ (n + 1) ^ (a + b) :=
  Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_add_right a b)

/-- Polynomial clock, random-bit count and table size of the composed machine, in
`|input|` alone (fixed `G`, `lambda`, hence fixed `t`). -/
theorem yao_main_poly (G : GLSourceDraft t) (lambda : ℕ) (ht : 1 ≤ t) :
    ∃ C d : ℕ, ∀ input : List Bool,
      sourceTime G input + frameClock lambda (src G input) + 1 ≤ C * (input.length + 1) ^ d ∧
      tapeBitCount t (paddedEdgeBits (src G input).2.1) lambda ≤ C * (input.length + 1) ^ d ∧
      (src G input).1 * (16 * Paper2.YaoResources.entryCoefficient t lambda) *
          (max 1 (src G input).2.1) ^ 4 ≤ C * (input.length + 1) ^ d := by
  obtain ⟨c1, d1, h1⟩ := Paper2.YaoT26Size.sourceTime_poly G
  obtain ⟨C2, d2, h2⟩ := Paper2.YaoClockPoly.frameClock_poly t lambda ht
  obtain ⟨C3, d3, h3⟩ := Paper2.YaoClockPoly.poly_tape (t := t) lambda ht
  obtain ⟨c4, d4, h4⟩ := Paper2.YaoT26Size.draft_yao_source_length_poly G
  have hent : Paper2.YaoClockPoly.PolyIn (fun x : YaoSource t =>
      x.1 * (16 * Paper2.YaoResources.entryCoefficient t lambda) * (max 1 x.2.1) ^ 4) := by
    refine Paper2.YaoClockPoly.poly_mono
      (g := fun x : YaoSource t => x.1 * (16 * Paper2.YaoResources.entryCoefficient t lambda) *
        (x.2.1 + 1) ^ 4) (fun x => ?_) ?_
    · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
    · exact Paper2.YaoClockPoly.poly_mul
        (Paper2.YaoClockPoly.poly_mul Paper2.YaoClockPoly.poly_v (Paper2.YaoClockPoly.poly_const _))
        (Paper2.YaoClockPoly.poly_pow
          (Paper2.YaoClockPoly.poly_add Paper2.YaoClockPoly.poly_e (Paper2.YaoClockPoly.poly_const 1)) 4)
  obtain ⟨C5, d5, h5⟩ := hent
  refine ⟨c1 + C2 * (c4 + 1) ^ d2 + 1 + C3 * (c4 + 1) ^ d3 + C5 * (c4 + 1) ^ d5,
    d1 + d4 * d2 + d4 * d3 + d4 * d5, fun input => ?_⟩
  set n := input.length
  set m := (encode (src G input)).length
  have hm : m ≤ c4 * (n + 1) ^ d4 := h4 input
  have hF : frameClock lambda (src G input) ≤ (C2 * (c4 + 1) ^ d2) * (n + 1) ^ (d4 * d2) :=
    compose_poly (h2 (src G input)) hm
  have hT : tapeBitCount t (paddedEdgeBits (src G input).2.1) lambda ≤
      (C3 * (c4 + 1) ^ d3) * (n + 1) ^ (d4 * d3) :=
    compose_poly (h3 (src G input)) hm
  have hE : (src G input).1 * (16 * Paper2.YaoResources.entryCoefficient t lambda) *
      (max 1 (src G input).2.1) ^ 4 ≤ (C5 * (c4 + 1) ^ d5) * (n + 1) ^ (d4 * d5) :=
    compose_poly (h5 (src G input)) hm
  have hS : sourceTime G input ≤ c1 * (n + 1) ^ d1 := h1 input
  set D := d1 + d4 * d2 + d4 * d3 + d4 * d5
  have p1 : (n + 1) ^ d1 ≤ (n + 1) ^ D := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
  have p2 : (n + 1) ^ (d4 * d2) ≤ (n + 1) ^ D := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
  have p3 : (n + 1) ^ (d4 * d3) ≤ (n + 1) ^ D := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
  have p5 : (n + 1) ^ (d4 * d5) ≤ (n + 1) ^ D := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
  have p0 : 1 ≤ (n + 1) ^ D := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have hring : (c1 + C2 * (c4 + 1) ^ d2 + 1 + C3 * (c4 + 1) ^ d3 + C5 * (c4 + 1) ^ d5) *
      (n + 1) ^ D = c1 * (n + 1) ^ D + C2 * (c4 + 1) ^ d2 * (n + 1) ^ D + (n + 1) ^ D +
      C3 * (c4 + 1) ^ d3 * (n + 1) ^ D + C5 * (c4 + 1) ^ d5 * (n + 1) ^ D := by ring
  refine ⟨?_, ?_, ?_⟩
  · have e1 := Nat.mul_le_mul_left c1 p1
    have e2 := Nat.mul_le_mul_left (C2 * (c4 + 1) ^ d2) p2
    have e3 := Nat.zero_le (C3 * (c4 + 1) ^ d3 * (n + 1) ^ D)
    have e4 := Nat.zero_le (C5 * (c4 + 1) ^ d5 * (n + 1) ^ D)
    rw [hring]
    linarith
  · have e3 := Nat.mul_le_mul_left (C3 * (c4 + 1) ^ d3) p3
    have e1 := Nat.zero_le (c1 * (n + 1) ^ D)
    have e2 := Nat.zero_le (C2 * (c4 + 1) ^ d2 * (n + 1) ^ D)
    have e4 := Nat.zero_le (C5 * (c4 + 1) ^ d5 * (n + 1) ^ D)
    rw [hring]
    linarith
  · have e5 := Nat.mul_le_mul_left (C5 * (c4 + 1) ^ d5) p5
    have e1 := Nat.zero_le (c1 * (n + 1) ^ D)
    have e2 := Nat.zero_le (C2 * (c4 + 1) ^ d2 * (n + 1) ^ D)
    have e3 := Nat.zero_le (C3 * (c4 + 1) ^ d3 * (n + 1) ^ D)
    rw [hring]
    linarith

/-! ## T25 (`yao:main`), HYP-parametric in the DRAFT record -/

/-- The printed word of the composed machine on `(input, bits)`. -/
def mainWord (G : GLSourceDraft t) (lambda : ℕ) (input : List Bool)
    (bits : SerializedTape t (paddedEdgeBits (src G input).2.1) lambda) : List Bool :=
  encodeInstance (yaoInstanceDraft t lambda (src G input) bits)

/-- NO-side event identity on the printed word (same object as the admitted
`materialize` table), for any gap `k`. -/
theorem no_event_eq (G : GLSourceDraft t) (lambda : ℕ) (input : List Bool) (k : ℕ) :
    (fun bits : SerializedTape t (paddedEdgeBits (src G input).2.1) lambda =>
        ∃ i, decodeInstance (mainWord G lambda input bits) = some i ∧
          i.threshold + k ≤ Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table)) =
      (fun bits => (2 * paddedEdgeBits (src G input).2.1 + 4 * t + 2) + k ≤
          Dalt .alice (materialize t lambda (src G input).2.2 bits).matrix) := by
  funext bits
  apply propext
  have hv := (draft_yao_source G input).2.1
  rw [mainWord, decode_framed lambda (src G input) hv bits]
  constructor
  · rintro ⟨i, hi, hc⟩
    cases Option.some.inj hi
    simpa only [yaoInstanceDraft, Paper2.EncodedSelectedOutput.tableGame_eq_matrix] using hc
  · intro hc
    refine ⟨yaoInstanceDraft t lambda (src G input) bits, rfl, ?_⟩
    simpa only [yaoInstanceDraft, Paper2.EncodedSelectedOutput.tableGame_eq_matrix] using hc

/-- **T25 `yao:main` (lock v12 Y:26-42), HYP-parametric.**  Fix `g`; put
`t = gapParameter g = max 4 ⌈(g+6)/2⌉` and `lambda = 10` (Y:332).  For every
DRAFT record `G : GLSourceDraft t` (AD-1 / D-A2: NOT adopted, a parameter), the
ONE fixed program `yaoMain G 10` (DRAFT D-A1 two-cell model) satisfies:

* resources: one polynomial `C (n+1)^d` bounds, for every input, the random-bit
  count `tapeBitCount`, the number of printed table entries and the running
  time on EVERY exact-length tape; the run halts with the exact bank `mainOut`
  whose output cell holds `encodeInstance ⟨rows, cols, B, table⟩`, where `table`
  is the admitted `materialize` table of the printed source and
  `B = 2*paddedEdgeBits e + 4t + 2`;
* YES (`input ∈ G.L`, the D-A2 language parameter): on EVERY tape the printed
  word is in the DRAFT language, i.e. `Dalt .alice (M) ≤ B`;
* NO (`input ∉ G.L`): with probability at least `511/512` over the uniform
  exact-length tape law (the raw tape of the materialiser), the printed word
  decodes to an instance with `threshold + g ≤ Dalt .alice (M)`. -/
theorem yao_main_draft (g : ℕ) (G : GLSourceDraft (gapParameter g)) :
    ∃ C d : ℕ, ∀ input : List Bool,
      tapeBitCount (gapParameter g) (paddedEdgeBits (src G input).2.1) 10 ≤
        C * (input.length + 1) ^ d ∧
      (∀ bits : SerializedTape (gapParameter g) (paddedEdgeBits (src G input).2.1) 10,
        (∃ total ≤ C * (input.length + 1) ^ d, ∃ c' S,
          ((advance (yaoMain G 10))^[total])
            (⟨some (BitMachineRawSequence.leftLabel (sourceMachine G).start),
              ((sourceMachine G).initial, framedControl (gapParameter g) 10),
              mainInit G 10 input bits.val⟩ :
              TM2.Cfg (fun _ : MStack G 10 => Bool) _ _) =
            ⟨none, c', mainOut G 10 S (src G input) bits⟩) ∧
        (∀ S, mainOut G 10 S (src G input) bits outCell = mainWord G 10 input bits) ∧
        decodeInstance (mainWord G 10 input bits) =
          some (yaoInstanceDraft (gapParameter g) 10 (src G input) bits) ∧
        (yaoInstanceDraft (gapParameter g) 10 (src G input) bits).threshold =
          2 * paddedEdgeBits (src G input).2.1 + 4 * gapParameter g + 2 ∧
        (yaoInstanceDraft (gapParameter g) 10 (src G input) bits).table =
          (materialize (gapParameter g) 10 (src G input).2.2 bits).bits ∧
        (yaoInstanceDraft (gapParameter g) 10 (src G input) bits).table.length ≤
          C * (input.length + 1) ^ d) ∧
      (input ∈ G.L → ∀ bits : SerializedTape (gapParameter g) (paddedEdgeBits (src G input).2.1) 10,
        mainWord G 10 input bits ∈ yaoLanguageDraft ∧
        Dalt .alice (materialize (gapParameter g) 10 (src G input).2.2 bits).matrix ≤
          2 * paddedEdgeBits (src G input).2.1 + 4 * gapParameter g + 2) ∧
      (input ∉ G.L →
        (511 / 512 : ℝ) ≤
          (serializedTapeLaw (gapParameter g) (paddedEdgeBits (src G input).2.1) 10).prob
            (fun bits => ∃ i, decodeInstance (mainWord G 10 input bits) = some i ∧
              i.threshold + g ≤ Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table))) := by
  have ht4 : 4 ≤ gapParameter g := (gapParameter_admissible g).1
  obtain ⟨C, d, hC⟩ := yao_main_poly G 10 (by omega)
  refine ⟨C, d, fun input => ⟨(hC input).2.1, fun bits => ?_, fun hyes bits => ?_, fun hno => ?_⟩⟩
  · have hv := (draft_yao_source G input).2.1
    obtain ⟨total, htot, c', S, hrun⟩ := yao_main_run G 10 (by omega) input bits
    refine ⟨⟨total, htot.trans (hC input).1, c', S, hrun⟩, fun S' => mainOut_output G 10 S' _ bits,
      decode_framed 10 (src G input) hv bits, rfl, rfl, ?_⟩
    exact (materialize_length_le (gapParameter g) 10 (by omega) (src G input).2.2 bits).trans
      (hC input).2.2
  · have hv := (draft_yao_source G input).2.1
    obtain ⟨colour, hbal⟩ := (draft_yao_source G input).2.2.1 hyes
    refine ⟨?_, materialize_yes_bound (gapParameter g) 10 (by omega) (src G input).2.2 colour
      hbal bits⟩
    have h := Paper2.YaoEndpoint.yao_lift_yes (gapParameter g) 10 ht4 (src G input) hv colour
      hbal bits
    rwa [framedOut_output] at h
  · rw [no_event_eq G 10 input g]
    exact materialize_fixed_gap_success g (src G input).2.2
      ((draft_yao_source G input).2.2.2 hno)

end Paper2.YaoMainDraft

end

#print axioms Paper2.YaoMainDraft.srcFun_injective
#print axioms Paper2.YaoMainDraft.init_bank
#print axioms Paper2.YaoMainDraft.handoff_bank
#print axioms Paper2.YaoMainDraft.final_bank
#print axioms Paper2.YaoMainDraft.yao_main_run
#print axioms Paper2.YaoMainDraft.yao_main_poly
#print axioms Paper2.YaoMainDraft.no_event_eq
#print axioms Paper2.YaoMainDraft.yao_main_draft
