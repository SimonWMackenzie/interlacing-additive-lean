import Paper2.CopyAll
import Paper2.CountedLoop
import EthInapproximability.CurrentPaper.ETHParameterScaleMachineLogCopy
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Unit 3, segment (5): a physical producer of the unary threshold.

Bank `TK = Fin 4 ⊕ (Fin 5 × LS)`, `LS = ETHParameterScaleMachineLogCopy.Stack` (the admitted Paper B
copy-then-clog call): cells `thr`, `X`, `ctr`, `scr` and five private log regions. Start bank
`T0 k v`: `ctr = unary k`, log region `i` holding `unary (v i)` in its source cell, all else blank.

ONE fixed program `thrProg`:
1. five lifted runs of `ETHParameterScaleMachineLogCopy.program` (region `i` computes
   `unary (Nat.clog 2 (v i))`, source kept);
2. five single copies `out 1, out 2, out 1, out 3, out 4 → X` (unary addition);
3. one copy `out 0 → thr` and one push (`+1`);
4. `CountedLoop.loop ctr (copy X → thr)`: `k` times.
Every handoff is one charged step (production `BitMachineRawSequence`).

`thr_run`: the run halts with `thr = unary (clog v₀ + 1 + k * (clog v₁ + clog v₂ + clog v₁ +
clog v₃ + clog v₄))`, `X = unary (clog v₁ + … )`, `ctr = []`, `scr = []`; the five log regions keep
their source and hold the clog output (their internal scratch is the admitted machine's
existential residue). -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.ThrProducer

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)

abbrev LS := ETHParameterScaleMachineLogCopy.Stack
abbrev TK := Fin 4 ⊕ (Fin 5 × LS)

def u (n : ℕ) : List Bool := List.replicate n true

theorem u_app (a b : ℕ) : u a ++ u b = u (a + b) := (List.replicate_add a b true).symm

def thrC : TK := .inl 0
def xC : TK := .inl 1
def ctrC : TK := .inl 2
def scrC : TK := .inl 3

def ιR (i : Fin 5) : LS ↪ TK :=
  ⟨fun x => .inr (i, x), fun a b h => by simpa using h⟩

def srcI (i : Fin 5) : TK := .inr (i, .inl 0)
def outI (i : Fin 5) : TK :=
  .inr (i, ETHParameterScaleMachineLogCopy.logStack
    ETHParameterScaleMachineLogCopy.logMachine.output)

/-- The start bank of log region `i`. -/
def region (n : ℕ) : LS → List Bool := fun x => if x = .inl 0 then u n else []

/-- Producer start bank. -/
def T0 (k : ℕ) (v : Fin 5 → ℕ) : TK → List Bool :=
  Sum.elim ![[], [], u k, []] (fun ix => region (v ix.1) ix.2)

theorem bank_inl (i : Fin 5) (W : TK → List Bool) (S : LS → List Bool) (a : Fin 4) :
    bank (ιR i) W S (.inl a) = W (.inl a) :=
  bank_outside (ιR i) W S (.inl a) (by rintro ⟨k, hk⟩; cases hk)

theorem bank_ne (i j : Fin 5) (W : TK → List Bool) (S : LS → List Bool) (y : LS) (h : j ≠ i) :
    bank (ιR i) W S (.inr (j, y)) = W (.inr (j, y)) :=
  bank_outside (ιR i) W S (.inr (j, y)) (by
    rintro ⟨k, hk⟩
    simp only [ιR, Function.Embedding.coeFn_mk, Sum.inr.injEq, Prod.mk.injEq] at hk
    exact h hk.1.symm)

theorem bank_same (i : Fin 5) (W : TK → List Bool) (S : LS → List Bool) (y : LS) :
    bank (ιR i) W S (.inr (i, y)) = S y := bank_at (ιR i) W S y

theorem start_stk (q : List Bool) :
    (ETHParameterScaleMachineLogCopy.start q).stk = fun x => if x = .inl 0 then q else [] := by
  change BitMachineStackEmbedding.bank ETHParameterScaleMachineLogCopy.copyStack (fun _ => [])
    (BitMachineCopy.cfg (some .scan) none q [] []).stk = _
  funext k
  by_cases hk : ∃ p : Fin 3, ETHParameterScaleMachineLogCopy.copyStack p = k
  · obtain ⟨p, rfl⟩ := hk
    rw [BitMachineStackEmbedding.bank_at]
    fin_cases p <;> simp [ETHParameterScaleMachineLogCopy.copyStack, BitMachineCopy.cfg]
  · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hk]
    have hne : k ≠ (.inl (0 : Fin 1) : LS) := by
      intro he
      exact hk ⟨0, by simpa [ETHParameterScaleMachineLogCopy.copyStack] using he.symm⟩
    simp [hne]

def logL (i : Fin 5) := fun l => stackStmt (ιR i) (ETHParameterScaleMachineLogCopy.program l)

abbrev logCtl := ETHParameterScaleMachineLogCopy.copyControl none

theorem log_lift (i : Fin 5) (W : TK → List Bool) (n : ℕ)
    (hW : ∀ x : LS, W (.inr (i, x)) = region n x) :
    ∃ t ≤ 2 * n + 2 + (UnaryBinaryEncoding.coefficient + 6) * (n + 1) ^ 2,
      ∃ c : ETHParameterScaleMachineLogCopy.logMachine.Config,
      ((advance (logL i))^[t])
          (⟨some (.inl .scan), logCtl, W⟩ : TM2.Cfg (fun _ : TK => Bool) _ _) =
        ⟨none, (none, c.var),
          bank (ιR i) W (ETHParameterScaleMachineLogCopy.afterLog (u n) c).stk⟩ ∧
      bank (ιR i) W (ETHParameterScaleMachineLogCopy.afterLog (u n) c).stk (outI i) =
        u (Nat.clog 2 n) ∧
      bank (ιR i) W (ETHParameterScaleMachineLogCopy.afterLog (u n) c).stk (srcI i) = u n := by
  obtain ⟨t, c, ht, hr, hh, ho⟩ := ETHParameterScaleMachineLogCopy.copied_log_run n
  have hs := BitMachineStackRun.run (ιR i) W ETHParameterScaleMachineLogCopy.program
    (ETHParameterScaleMachineLogCopy.start (u n)) t
  change _ = stackCfg (ιR i) W (ETHParameterScaleMachineLogCopy.run t _) at hs
  have hr' : ETHParameterScaleMachineLogCopy.run t (ETHParameterScaleMachineLogCopy.start (u n)) =
      ETHParameterScaleMachineLogCopy.afterLog (u n) c := hr
  rw [hr'] at hs
  have hb : bank (ιR i) W (ETHParameterScaleMachineLogCopy.start (u n)).stk = W := by
    apply bank_eq_self
    intro x
    rw [start_stk]
    show (if x = .inl 0 then u n else []) = W (.inr (i, x))
    rw [hW]
    rfl
  have hst : stackCfg (ιR i) W (ETHParameterScaleMachineLogCopy.start (u n)) =
      (⟨some (.inl .scan), logCtl, W⟩ : TM2.Cfg (fun _ : TK => Bool) _ _) := by
    simp only [stackCfg]
    rw [hb]
    rfl
  rw [hst] at hs
  have hl : (ETHParameterScaleMachineLogCopy.afterLog (u n) c).l = none := by
    simp [ETHParameterScaleMachineLogCopy.afterLog, BitMachineStackEmbedding.cfg, stackCfg,
      BitMachineInline.cfg, hh]
  refine ⟨t, ht, c, ?_, ?_, ?_⟩
  · refine hs.trans ?_
    simp only [stackCfg]
    rw [hl]
    rfl
  · rw [outI, bank_same]
    exact (ETHParameterScaleMachineLogCopy.afterLog_output n c).trans ho
  · rw [srcI, bank_same]
    exact ETHParameterScaleMachineLogCopy.afterLog_source n c

/-! ### Single copies -/

def cp (a b : TK) (hab : a ≠ b) (ha : a ≠ scrC) (hb : b ≠ scrC) : Fin 1 → (Fin 3 ↪ TK) :=
  fun _ => ⟨![a, b, scrC], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all⟩

theorem cp_run (a b : TK) (hab : a ≠ b) (ha : a ≠ scrC) (hb : b ≠ scrC) (T : TK → List Bool)
    (hz : T scrC = []) :
    ∃ t ≤ 1 * (2 * (T a).length + 3) + 1, ∃ v',
      ((advance (CopyAll.prog (cp a b hab ha hb)))^[t])
          (⟨some (.inl ⟨0, by omega⟩), (none : Option Bool), T⟩ :
            TM2.Cfg (fun _ : TK => Bool) _ _) =
        ⟨none, v', Function.update T b (T a ++ T b)⟩ := by
  obtain ⟨t, ht, v', hr⟩ := CopyAll.all_run (cp a b hab ha hb)
    (by intro i j h; fin_cases i; fin_cases j; exact hab h)
    (by intro i j h; fin_cases i; fin_cases j; exact hb h.symm)
    (by intro i j _; fin_cases i; fin_cases j; rfl) T
    (by intro i; fin_cases i; exact hz) (T a).length
    (by intro i; fin_cases i; exact le_refl _) none
  refine ⟨t, ht, v', ?_⟩
  rw [hr]
  simp [CopyAll.done, cp]

/-! ### The program -/

theorem n01 : outI 1 ≠ xC := by simp [outI, xC]
theorem n02 : outI 2 ≠ xC := by simp [outI, xC]
theorem n03 : outI 3 ≠ xC := by simp [outI, xC]
theorem n04 : outI 4 ≠ xC := by simp [outI, xC]
theorem n00 : outI 0 ≠ thrC := by simp [outI, thrC]
theorem sO (i : Fin 5) : outI i ≠ scrC := by simp [outI, scrC]
theorem sX : xC ≠ scrC := by simp [xC, scrC]
theorem sT : thrC ≠ scrC := by simp [thrC, scrC]
theorem xT : xC ≠ thrC := by simp [xC, thrC]

def c1 := CopyAll.prog (cp (outI 1) xC n01 (sO 1) sX)
def c2 := CopyAll.prog (cp (outI 2) xC n02 (sO 2) sX)
def c3 := CopyAll.prog (cp (outI 1) xC n01 (sO 1) sX)
def c4 := CopyAll.prog (cp (outI 3) xC n03 (sO 3) sX)
def c5 := CopyAll.prog (cp (outI 4) xC n04 (sO 4) sX)
def cT := CopyAll.prog (cp (outI 0) thrC n00 (sO 0) sT)
def cL := CopyAll.prog (cp xC thrC xT sX sT)

def pushT : Unit → TM2.Stmt (fun _ : TK => Bool) Unit (Option Bool) :=
  fun _ => TM2.Stmt.push thrC (fun _ => true) TM2.Stmt.halt

theorem push_run (S : TK → List Bool) (v : Option Bool) :
    ((advance pushT)^[1]) (⟨some (), v, S⟩ : TM2.Cfg (fun _ : TK => Bool) _ _) =
      ⟨none, v, Function.update S thrC (true :: S thrC)⟩ := rfl

def loopP := CountedLoop.loop ctrC cL (.inl ⟨0, by omega⟩) (none : Option Bool)

abbrev oc := (none : Option Bool)
def z0 : CopyAll.Lab 1 := .inl ⟨0, by omega⟩

def p1 := BitMachineRawSequence.program (logL 0) (logL 1) (.inl .scan) logCtl logCtl
def p2 := BitMachineRawSequence.program p1 (logL 2) (.inl .scan) (logCtl, logCtl) logCtl
def p3 := BitMachineRawSequence.program p2 (logL 3) (.inl .scan) ((logCtl, logCtl), logCtl) logCtl
def k3 := (((logCtl, logCtl), logCtl), logCtl)
def p4 := BitMachineRawSequence.program p3 (logL 4) (.inl .scan) k3 logCtl
def k4 := (k3, logCtl)
def p5 := BitMachineRawSequence.program p4 c1 z0 k4 oc
def k5 := (k4, oc)
def p6 := BitMachineRawSequence.program p5 c2 z0 k5 oc
def k6 := (k5, oc)
def p7 := BitMachineRawSequence.program p6 c3 z0 k6 oc
def k7 := (k6, oc)
def p8 := BitMachineRawSequence.program p7 c4 z0 k7 oc
def k8 := (k7, oc)
def p9 := BitMachineRawSequence.program p8 c5 z0 k8 oc
def k9 := (k8, oc)
def p10 := BitMachineRawSequence.program p9 cT z0 k9 oc
def k10 := (k9, oc)
def p11 := BitMachineRawSequence.program p10 pushT () k10 oc
def k11 := (k10, oc)
/-- The threshold producer: ONE fixed program. -/
def thrProg := BitMachineRawSequence.program p11 loopP (.inl ()) k11 (oc, oc)
def thrCtl := (k11, (oc, oc))
def labelOfP {L σ : Type*} {K : Type*} (_P : L → TM2.Stmt (fun _ : K => Bool) L σ)
    (l : L) : L := l
def thrStart := labelOfP thrProg (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
    (.inl .scan)))))))))))))

end

end Paper2.ThrProducer
