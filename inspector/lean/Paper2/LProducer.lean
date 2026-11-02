import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.ETHParameterScaleMachineLogCopy
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Unit 3, segment (2), first part: a physical producer of the `L`-determined raw public counts
`p = LookupSeed.width L`, `s = width L`, `q₁ = width L - 2`, `q₂ = outerWidth L`,
`w = restorationWidth L` from unary `n` (`L = clog₂ n`).

Bank `LK = Fin 16 ⊕ (Fin 2 × LS)`, `LS = ETHParameterScaleMachineLogCopy.Stack` (two regions for the admitted
copy-then-clog call). ONE fixed program `lProg` (twenty parts, production `BitMachineRawSequence` handoffs):
admitted copies (`MatrixStage4ScalarPreparationOps.copyProgram`), two admitted clog calls (`L = clog n`,
`e = clog (L+1)`), two single-step constant pushes, one admitted multiplication (`e * e`), four admitted
unary powers of two, one two-pop step. Every `Fin 16` cell is stated at the exit; the two log regions are the
admitted `afterLog` banks (existential internal configuration, named residue). -/

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

namespace Paper2.LProducer

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)

abbrev LS := ETHParameterScaleMachineLogCopy.Stack
abbrev LK := Fin 16 ⊕ (Fin 2 × LS)

def u (n : ℕ) : List Bool := List.replicate n true

def c (i : Fin 16) : LK := .inl i
def srcR (i : Fin 2) : LK := .inr (i, .inl 0)
def outR (i : Fin 2) : LK := .inr (i, ETHParameterScaleMachineLogCopy.logStack
  ETHParameterScaleMachineLogCopy.logMachine.output)

-- cell names
abbrev nC := c 0
abbrev c1 := c 1
abbrev oe := c 2
abbrev ep := c 3
abbrev es := c 4
abbrev dp := c 5
abbrev dd := c 6
abbrev pC := c 7
abbrev sC := c 8
abbrev q2C := c 9
abbrev wC := c 10
abbrev q1C := c 11
abbrev z := c 12
abbrev x1 := c 13
abbrev x2 := c 14
abbrev x3 := c 15

def ιR (i : Fin 2) : LS ↪ LK :=
  ⟨fun x => .inr (i, x), fun a b h => by simpa using h⟩

theorem bank_inl (i : Fin 2) (W : LK → List Bool) (S : LS → List Bool) (a : Fin 16) :
    bank (ιR i) W S (.inl a) = W (.inl a) :=
  bank_outside (ιR i) W S (.inl a) (by rintro ⟨k, hk⟩; cases hk)

theorem bank_ne (i j : Fin 2) (W : LK → List Bool) (S : LS → List Bool) (y : LS) (h : j ≠ i) :
    bank (ιR i) W S (.inr (j, y)) = W (.inr (j, y)) :=
  bank_outside (ιR i) W S (.inr (j, y)) (by
    rintro ⟨k, hk⟩
    simp only [ιR, Function.Embedding.coeFn_mk, Sum.inr.injEq, Prod.mk.injEq] at hk
    exact h hk.1.symm)

theorem bank_same (i : Fin 2) (W : LK → List Bool) (S : LS → List Bool) (y : LS) :
    bank (ιR i) W S (.inr (i, y)) = S y := bank_at (ιR i) W S y

/-! ### Embeddings -/

def cpE (a b : LK) (hab : a ≠ b) (ha : a ≠ z) (hb : b ≠ z) : Fin 3 ↪ LK :=
  ⟨![a, b, z], by intro x y h; fin_cases x <;> fin_cases y <;> simp_all [eq_comm]⟩

def powF (o e : LK) : MatrixUnaryPower.Stack → LK
  | .inl 0 => o
  | .inl 1 => x1
  | .inl _ => x2
  | .inr () => e

def powE (o e : LK) (h1 : o ≠ x1) (h2 : o ≠ x2) (h3 : o ≠ e) (h4 : e ≠ x1) (h5 : e ≠ x2) :
    MatrixUnaryPower.Stack ↪ LK := ⟨powF o e, by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · fin_cases a <;> fin_cases b <;> simp_all [powF, c]
  · cases b; fin_cases a <;> simp_all [powF, c]
  · cases a; fin_cases b <;> simp_all [powF, c]
  · cases a; cases b; rfl⟩

def ιM : Fin 6 ↪ LK := ⟨![outR 1, dp, x1, x2, x3, dd], by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [outR, c]⟩

/-! ### Parts -/

def logL (i : Fin 2) := fun l => stackStmt (ιR i) (ETHParameterScaleMachineLogCopy.program l)
abbrev logCtl := ETHParameterScaleMachineLogCopy.copyControl none
abbrev powCtl : MatrixUnaryPower.Control := ((false, false), none)

def cp (a b : LK) (hab : a ≠ b) (ha : a ≠ z) (hb : b ≠ z) :=
  MatrixStage4ScalarPreparationOps.copyProgram (cpE a b hab ha hb)
def pw (o e : LK) (h1 : o ≠ x1) (h2 : o ≠ x2) (h3 : o ≠ e) (h4 : e ≠ x1) (h5 : e ≠ x2) :=
  MatrixStage4ScalarPreparationOps.unaryPowerProgram (powE o e h1 h2 h3 h4 h5)

def push1 : Unit → TM2.Stmt (fun _ : LK => Bool) Unit Bool := fun _ =>
  TM2.Stmt.push c1 (fun _ => true) TM2.Stmt.halt

def pushN (a : LK) (k : ℕ) (q : TM2.Stmt (fun _ : LK => Bool) Unit Bool) :
    TM2.Stmt (fun _ : LK => Bool) Unit Bool :=
  match k with
  | 0 => q
  | k + 1 => TM2.Stmt.push a (fun _ => true) (pushN a k q)

def pushC : Unit → TM2.Stmt (fun _ : LK => Bool) Unit Bool := fun _ =>
  pushN ep 6 (pushN es 16 (pushN oe 32 TM2.Stmt.halt))

def pop2 : Unit → TM2.Stmt (fun _ : LK => Bool) Unit Bool := fun _ =>
  TM2.Stmt.pop q1C (fun v _ => v) (TM2.Stmt.pop q1C (fun v _ => v) TM2.Stmt.halt)

def P1 := cp nC (srcR 0) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3])
def P2 := logL 0
def P3 := cp (outR 0) c1 (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3])
def P4 := cp (outR 0) oe (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3])
def P5 := push1
def P6 := cp c1 (srcR 1) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3])
def P7 := logL 1
def P8 := cp (outR 1) ep (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3])
def P9 := cp (outR 1) es (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3])
def P10 := cp (outR 1) dp (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3])
def P11 := cp (outR 1) oe (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3])
def P12 := cp (outR 1) oe (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3])
def P13 := pushC
def P14 := MatrixStage4ScalarPreparationOps.multiplyProgram ιM
def P15 := pw pC ep (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3])
def P16 := pw sC es (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3])
def P17 := pw q2C oe (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3])
def P18 := pw wC dd (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3])
def P19 := cp sC q1C (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3]) (by simp [c, srcR, outR, nC, c1, oe, ep, es, dp, dd, pC, sC, q2C, wC, q1C, z, x1, x2, x3])
def P20 := pop2

abbrev oc := (none : Option Bool)
def s1 := BitMachineRawSequence.program P1 P2 (.inl .scan) oc logCtl
def s2 := BitMachineRawSequence.program s1 P3 BitMachineCopy.Label.scan (oc, logCtl) oc
def s3 := BitMachineRawSequence.program s2 P4 BitMachineCopy.Label.scan ((oc, logCtl), oc) oc
def k3 := (((oc, logCtl), oc), oc)
def s4 := BitMachineRawSequence.program s3 P5 () k3 false
def k4 := (k3, false)
def s5 := BitMachineRawSequence.program s4 P6 BitMachineCopy.Label.scan k4 oc
def k5 := (k4, oc)
def s6 := BitMachineRawSequence.program s5 P7 (.inl .scan) k5 logCtl
def k6 := (k5, logCtl)
def s7 := BitMachineRawSequence.program s6 P8 BitMachineCopy.Label.scan k6 oc
def k7 := (k6, oc)
def s8 := BitMachineRawSequence.program s7 P9 BitMachineCopy.Label.scan k7 oc
def k8 := (k7, oc)
def s9 := BitMachineRawSequence.program s8 P10 BitMachineCopy.Label.scan k8 oc
def k9 := (k8, oc)
def s10 := BitMachineRawSequence.program s9 P11 BitMachineCopy.Label.scan k9 oc
def k10 := (k9, oc)
def s11 := BitMachineRawSequence.program s10 P12 BitMachineCopy.Label.scan k10 oc
def k11 := (k10, oc)
def s12 := BitMachineRawSequence.program s11 P13 () k11 false
def k12 := (k11, false)
def s13 := BitMachineRawSequence.program s12 P14 MatrixAddressMachine.Label.outer k12 false
def k13 := (k12, false)
def s14 := BitMachineRawSequence.program s13 P15 (.inr false) k13 powCtl
def k14 := (k13, powCtl)
def s15 := BitMachineRawSequence.program s14 P16 (.inr false) k14 powCtl
def k15 := (k14, powCtl)
def s16 := BitMachineRawSequence.program s15 P17 (.inr false) k15 powCtl
def k16 := (k15, powCtl)
def s17 := BitMachineRawSequence.program s16 P18 (.inr false) k16 powCtl
def k17 := (k16, powCtl)
def s18 := BitMachineRawSequence.program s17 P19 BitMachineCopy.Label.scan k17 oc
def k18 := (k17, oc)
/-- The `L`-count producer: ONE fixed program. -/
def lProg := BitMachineRawSequence.program s18 P20 () k18 false
def lCtl := (k18, false)
def labelOfP {L σ : Type*} {K : Type*} (_P : L → TM2.Stmt (fun _ : K => Bool) L σ)
    (l : L) : L := l
def lStart := labelOfP lProg (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
    (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan)))))))))))))))))))

/-- Start bank: unary `n` in cell 0, everything else blank. -/
def L0 (n : ℕ) : LK → List Bool := Function.update (fun _ => []) nC (u n)

end

end Paper2.LProducer
