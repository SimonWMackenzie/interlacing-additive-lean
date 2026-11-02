import Paper2.GFront
import Paper2.TMFront
import Paper2.Blank

/-! Unit 3 (lock v12 App. D; T44/U10), lane a-success-table-12, segment (2): the full H_A3 count front.

Bank `JF = J2 ⊕ (JM ⊕ (SuccessOrient.Stack ⊕ (Fin 3 ⊕ Fin 1)))`: the owner-11 graph-byte front bank `J2`, this lane's
threshold / sample-dimension bank `JM` (segment 1), the success start-bank region, the H_A3 input packet
`[EncodedGraph.encode g, unary k, word]` (the packet of `A3Wrap.inputBank`, `word` = the tape word), one copy scratch.
ONE fixed program `full a b Δ` (five parts, four production `BitMachineRawSequence` handoffs):

1. admitted `copyProgram`: the packet's graph bytes into the `J2` input cell `gB` (source kept);
2. owner-11 `CountFront.gfront a b Δ` lifted to `J2` (charged by `CountFront.g_run`: n, m, L, p, s, q₁, q₂, w, Q produced);
3. admitted `CopyAll` of seven copies (unary k from the packet, p, s, q₂, w, Q, L from the produced cells) into the blank
   inputs of segment 1's `TMFront.TM0`;
4. segment 1 `TMFront.tmProg` lifted to `JM` (charged by `TMFront.tm_run`: threshold, mX, mY produced);
5. admitted `CopyAll` of eleven copies (q₂, q₁, s, n, w, Q, p, k, mX, mY, word) into the blank start-bank region.

Start bank: the packet only (everything else blank). Exit bank exact: `J2` = the `g_run` exit, `JM` = the `tm_run` exit,
start-bank region = exactly `SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word` (via owner-11
`StartInstall.startBank_install`/`startBank_cells`/`startBank_off` and this lane's `StartBlank.blank_nil`), packet
unchanged, scratch blank. -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

namespace Paper2.FullFront

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)
open Paper2.CountFront (J1 J2 LK QK jc lc qc gB gfront gStart gfrontCtl G0 LFacts QFacts lqBd g_run)
open Paper2.TMFront (JM TK MK tc mc tmProg tmStart tmCtl TM0 TFacts MFacts thrVal tmBd tm_run)

abbrev SO := SuccessOrient.Stack
abbrev JF := J2 ⊕ (JM ⊕ (SO ⊕ (Fin 3 ⊕ Fin 1)))

instance instDecJ2 : DecidableEq J2 := inferInstance
instance instDecJM : DecidableEq JM := inferInstance
instance instDecR3 : DecidableEq (SO ⊕ (Fin 3 ⊕ Fin 1)) :=
  @instDecidableEqSum _ _ StartInstall.instDecSO inferInstance
instance instDecR2 : DecidableEq (JM ⊕ (SO ⊕ (Fin 3 ⊕ Fin 1))) :=
  @instDecidableEqSum _ _ instDecJM instDecR3
instance instDecJF : DecidableEq JF := @instDecidableEqSum _ _ instDecJ2 instDecR2

def jg (x : J2) : JF := .inl x
def jt (x : JM) : JF := .inr (.inl x)
def so (x : SO) : JF := .inr (.inr (.inl x))
def pk (i : Fin 3) : JF := .inr (.inr (.inr (.inl i)))
def zs : JF := .inr (.inr (.inr (.inr 0)))

def ιG : J2 ↪ JF := ⟨Sum.inl, fun _ _ h => Sum.inl_injective h⟩
def ιT : JM ↪ JF := ⟨fun x => .inr (.inl x), fun a b h => by simpa using h⟩

/-- A copy embedding from three distinct cells. -/
def mkE (x y z : JF) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : Fin 3 ↪ JF :=
  ⟨![x, y, z], by
    intro i j h
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact absurd h hxy | exact absurd h hxz | exact absurd h hyz
      | exact absurd h.symm hxy | exact absurd h.symm hxz | exact absurd h.symm hyz⟩

def e0 : Fin 3 ↪ JF := mkE (pk 0) (jg gB) zs (by simp [pk, jg]) (by simp [pk, zs]) (by simp [jg, zs])

/-! ### The seven copies into the segment-1 inputs -/

def srcB : Fin 7 → JF := ![pk 1, jg (jc (lc LProducer.pC)), jg (jc (lc LProducer.sC)),
  jg (jc (lc LProducer.q2C)), jg (jc (lc LProducer.wC)), jg (jc (qc (.inl 24))),
  jg (jc (lc (LProducer.outR 0)))]
def dB : Fin 7 → JM := ![tc ThrProducer.ctrC, tc (ThrProducer.srcI 0), tc (ThrProducer.srcI 1),
  tc (ThrProducer.srcI 2), tc (ThrProducer.srcI 3), tc (ThrProducer.srcI 4), mc 2]

theorem srcB_ne (i : Fin 7) (x : JM) : srcB i ≠ jt x := by
  fin_cases i <;> simp [srcB, pk, jg, jt]
theorem srcB_zs (i : Fin 7) : srcB i ≠ zs := by
  fin_cases i <;> simp [srcB, pk, jg, zs]
theorem jt_zs (x : JM) : jt x ≠ zs := by simp [jt, zs]

def cpB (i : Fin 7) : Fin 3 ↪ JF :=
  mkE (srcB i) (jt (dB i)) zs (srcB_ne i _) (srcB_zs i) (jt_zs _)

theorem dB_inj : ∀ i j, dB i = dB j → i = j := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [dB, tc, mc, ThrProducer.srcI, ThrProducer.ctrC]

/-! ### The eleven installation copies -/

def srcC : Fin 11 → JF := ![jg (jc (lc LProducer.q2C)), jg (jc (lc LProducer.q1C)), jg (jc (lc LProducer.sC)),
  jg (jc (lc LProducer.nC)), jg (jc (lc LProducer.wC)), jg (jc (qc (.inl 24))), jg (jc (lc LProducer.pC)),
  pk 1, jt (mc 13), jt (mc 10), pk 2]
def dC : Fin 11 → SO := ![StartInstall.pc (SamplerParameterBank.compilerCell 12),
  StartInstall.pc (SamplerParameterBank.compilerCell 16), StartInstall.pc (SamplerParameterBank.compilerCell 17),
  StartInstall.pc (SamplerParameterBank.compilerCell 18), StartInstall.pc (SamplerParameterBank.compilerCell 31),
  StartInstall.pc (SamplerParameterBank.compilerCell 32), StartInstall.pc (SamplerParameterBank.compilerCell 63),
  StartInstall.pc (SamplerParameterBank.compilerCell 64), StartInstall.pc SamplerParameterBank.countXCell,
  StartInstall.pc SamplerParameterBank.countYCell, StartInstall.pc (SamplerParameterBank.drawCell 0)]

theorem srcC_ne (i : Fin 11) (x : SO) : srcC i ≠ so x := by
  fin_cases i <;> simp [srcC, pk, jg, jt, so]
theorem srcC_zs (i : Fin 11) : srcC i ≠ zs := by
  fin_cases i <;> simp [srcC, pk, jg, jt, zs]
theorem so_zs (x : SO) : so x ≠ zs := by simp [so, zs]

def cpC (i : Fin 11) : Fin 3 ↪ JF :=
  mkE (srcC i) (so (dC i)) zs (srcC_ne i _) (srcC_zs i) (so_zs _)

theorem dC_inj : ∀ i j, dC i = dC j → i = j := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [dC, StartInstall.pc, SamplerParameterBank.compilerCell, SamplerParameterBank.countXCell,
      SamplerParameterBank.countYCell, SamplerParameterBank.drawCell, CodeHeaderDraw.d]

/-! ### The program -/

def cq (e : Fin 3 ↪ JF) := MatrixStage4ScalarPreparationOps.copyProgram e
abbrev oc := (none : Option Bool)
def pG (a b Δ : ℕ) := fun l => stackStmt ιG (gfront a b Δ l)
def pTM := fun l => stackStmt ιT (tmProg l)

def r1 (a b Δ : ℕ) := BitMachineRawSequence.program (cq e0) (pG a b Δ) (gStart a b Δ) oc gfrontCtl
def c1 := (oc, gfrontCtl)
def r2 (a b Δ : ℕ) := BitMachineRawSequence.program (r1 a b Δ) (CopyAll.prog cpB) (.inl ⟨0, by omega⟩) c1 oc
def c2 := (c1, oc)
def r3 (a b Δ : ℕ) := BitMachineRawSequence.program (r2 a b Δ) pTM tmStart c2 tmCtl
def c3 := (c2, tmCtl)
/-- The full H_A3 count front: ONE fixed program (machine constants `a b Δ`). -/
def full (a b Δ : ℕ) := BitMachineRawSequence.program (r3 a b Δ) (CopyAll.prog cpC) (.inl ⟨0, by omega⟩) c3 oc
def fullCtl := (c3, oc)
def labelOfP {L σ : Type*} {K : Type*} (_P : L → TM2.Stmt (fun _ : K => Bool) L σ) (l : L) : L := l
def fullStart (a b Δ : ℕ) := labelOfP (full a b Δ)
  (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))

/-! ### The produced values (named; literally the values of `g_run` and `tm_run`) -/

def Lg (g : EncodedGraph.Graph) : ℕ := Nat.clog 2 g.vertices
def eg (g : EncodedGraph.Graph) : ℕ := Nat.clog 2 (Lg g + 1)
def pV (g : EncodedGraph.Graph) : ℕ := 2 ^ (6 + eg g)
def sV (g : EncodedGraph.Graph) : ℕ := 2 ^ (16 + eg g)
def q2V (g : EncodedGraph.Graph) : ℕ := 2 ^ (32 + (eg g + (eg g + Lg g)))
def wV (g : EncodedGraph.Graph) : ℕ := 2 ^ (eg g * eg g)
def q1V (g : EncodedGraph.Graph) : ℕ := 2 ^ (16 + eg g) - 2
def QV (a b Δ : ℕ) (g : EncodedGraph.Graph) : ℕ :=
  2 ^ Nat.clog 2 (max (max (QProducer.C0 (Lg g) (sV g) (wV g))
    (QProducer.A2 a b Δ g.vertices g.edges.length (Lg g) (sV g) (wV g))) (QProducer.A3 a b (Lg g) (sV g) (wV g)))
def vT (a b Δ : ℕ) (g : EncodedGraph.Graph) : Fin 5 → ℕ := ![pV g, sV g, q2V g, wV g, QV a b Δ g]
def bV (a b Δ : ℕ) (g : EncodedGraph.Graph) (k : ℕ) : ℕ := thrVal k (vT a b Δ g)
def Zv (b k : ℕ) : ℕ := 12 + (2 + (2 ^ (b - 1)) * ((2 ^ (b - 1)) + 1)) * (2 ^ (k + b - 1))
def mYV (b k : ℕ) : ℕ := Zv b k + Zv b k
def mXV (b k L : ℕ) : ℕ := (L + Zv b k - 1) / L

/-- The H_A3 input packet `[encode g, unary k, word]` (the shape of `A3Wrap.inputBank`). -/
def X0 (g : EncodedGraph.Graph) (k : ℕ) (word : List Bool) : Fin 3 → List Bool :=
  ![EncodedGraph.encode g, List.replicate k true, word]

/-- Start bank: the packet; everything else blank. -/
def F0 (X : Fin 3 → List Bool) : JF → List Bool :=
  Sum.elim (fun _ => []) (Sum.elim (fun _ => []) (Sum.elim (fun _ => []) (Sum.elim X (fun _ => []))))

/-- The exit bank of the graph-byte front. -/
def gBank (g : EncodedGraph.Graph) (hg : g.Valid) (FL : LK → List Bool) (FQ : QK → List Bool) :
    J2 → List Bool :=
  Sum.elim (Sum.elim FL (Sum.elim FQ (fun _ => [])))
    (Sum.elim (PublicGraphEndpointMachine.resultBank g hg) (fun _ => EncodedGraph.encode g))

/-- The exit bank of the full front, generic in the eleven installed values. -/
def exitBankG (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (word : List Bool)
    (FL : LK → List Bool) (FQ : QK → List Bool) (FT : TK → List Bool) (FM : MK → List Bool)
    (n p s q₁ q₂ w Q mX mY : ℕ) : JF → List Bool :=
  Sum.elim (gBank g hg FL FQ)
    (Sum.elim (Sum.elim FT (Sum.elim FM (fun _ => [])))
      (Sum.elim (SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word)
        (Sum.elim (X0 g k word) (fun _ => []))))

/-- The exact exit bank of the full front (at the produced values). -/
def exitBank (a b Δ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (word : List Bool)
    (FL : LK → List Bool) (FQ : QK → List Bool) (FT : TK → List Bool) (FM : MK → List Bool) :
    JF → List Bool :=
  exitBankG g hg k word FL FQ FT FM g.vertices (pV g) (sV g) (q1V g) (q2V g) (wV g) (QV a b Δ g)
    (mXV (thrVal k ![pV g, sV g, q2V g, wV g, QV a b Δ g]) k (Lg g)) (mYV (thrVal k ![pV g, sV g, q2V g, wV g, QV a b Δ g]) k)

def gBd (a b Δ : ℕ) (g : EncodedGraph.Graph) : ℕ :=
  (2 * (EncodedGraph.encode g).length + 2) + 103 * ((EncodedGraph.encode g).length + 1) ^ 3 +
    (2 * g.vertices + 2) + (2 * g.edges.length + 2) + lqBd a b Δ g.vertices g.edges.length + 4

def LB (a b Δ : ℕ) (g : EncodedGraph.Graph) (k : ℕ) : ℕ :=
  k + pV g + sV g + q2V g + wV g + QV a b Δ g + Lg g
def LC (a b Δ : ℕ) (g : EncodedGraph.Graph) (k : ℕ) (word : List Bool) : ℕ :=
  q2V g + q1V g + sV g + g.vertices + wV g + QV a b Δ g + pV g + k +
    mXV (thrVal k ![pV g, sV g, q2V g, wV g, QV a b Δ g]) k (Lg g) + mYV (thrVal k ![pV g, sV g, q2V g, wV g, QV a b Δ g]) k + word.length

/-- The explicit clock of `full_run`. -/
def fullBd (a b Δ : ℕ) (g : EncodedGraph.Graph) (k : ℕ) (word : List Bool) : ℕ :=
  (2 * (EncodedGraph.encode g).length + 2) + gBd a b Δ g + 1 + (7 * (2 * LB a b Δ g k + 3) + 1) +
    tmBd k ![pV g, sV g, q2V g, wV g, QV a b Δ g] (Lg g) + (11 * (2 * LC a b Δ g k word + 3) + 1) + 3

/-- The bank after the graph-byte front (explicit). -/
def W2 (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (word : List Bool)
    (FL : LK → List Bool) (FQ : QK → List Bool) : JF → List Bool :=
  Sum.elim (gBank g hg FL FQ) (Sum.elim (fun _ => []) (Sum.elim (fun _ => [])
    (Sum.elim (X0 g k word) (fun _ => []))))

/-- The bank after the seven copies (explicit; generic in the producer inputs). -/
def W3 (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (word : List Bool)
    (FL : LK → List Bool) (FQ : QK → List Bool) (v : Fin 5 → ℕ) (L : ℕ) : JF → List Bool :=
  Sum.elim (gBank g hg FL FQ) (Sum.elim (TM0 k v L)
    (Sum.elim (fun _ => []) (Sum.elim (X0 g k word) (fun _ => []))))

/-- The bank after the threshold + sample-dimension producer (explicit). -/
def W4 (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (word : List Bool)
    (FL : LK → List Bool) (FQ : QK → List Bool) (FT : TK → List Bool) (FM : MK → List Bool) :
    JF → List Bool :=
  Sum.elim (gBank g hg FL FQ) (Sum.elim (Sum.elim FT (Sum.elim FM (fun _ => [])))
    (Sum.elim (fun _ => []) (Sum.elim (X0 g k word) (fun _ => []))))

/-- Parts 1-2: bytes copied, graph-byte front run (charged by `g_run`). -/
theorem run12 (a b Δ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (word : List Bool) :
    ∃ t ≤ (2 * (EncodedGraph.encode g).length + 2) + gBd a b Δ g + 1, ∃ vc,
      ∃ FL : LK → List Bool, ∃ FQ : QK → List Bool,
      ((advance (r1 a b Δ))^[t])
          (⟨some (leftLabel BitMachineCopy.Label.scan), c1, F0 (X0 g k word)⟩ :
            TM2.Cfg (fun _ : JF => Bool) _ _) =
        ⟨none, (oc, vc), W2 g hg k word FL FQ⟩ ∧
      LFacts g.vertices FL ∧ QFacts a b Δ g.vertices g.edges.length (Nat.clog 2 g.vertices)
        (2 ^ (16 + (Nat.clog 2 ((Nat.clog 2 g.vertices) + 1))))
        (2 ^ ((Nat.clog 2 ((Nat.clog 2 g.vertices) + 1)) * (Nat.clog 2 ((Nat.clog 2 g.vertices) + 1)))) FQ := by
  obtain ⟨S0, hS0⟩ : ∃ S, S = F0 (X0 g k word) := ⟨_, rfl⟩
  have h1 := MatrixStage4ScalarPreparationOps.copy_run e0 S0 (by rw [hS0]; rfl)
  have l1 : (S0 (e0 0)).length = (EncodedGraph.encode g).length := by rw [hS0]; rfl
  rw [l1] at h1
  obtain ⟨V1, hV1⟩ : ∃ B, B = Function.update S0 (e0 1) (S0 (e0 0) ++ S0 (e0 1)) := ⟨_, rfl⟩
  rw [← hV1] at h1
  have v1_g : ∀ x, V1 (jg x) = G0 g x := by
    intro x
    by_cases hx : x = gB
    · subst hx
      rw [hV1]
      show Function.update S0 (e0 1) _ (e0 1) = _
      rw [Function.update_self, hS0]
      show EncodedGraph.encode g ++ [] = G0 g gB
      rw [List.append_nil]; simp [G0]
    · rw [hV1, Function.update_of_ne (by simpa [e0, mkE, jg] using hx), hS0]
      show [] = G0 g x
      simp [G0, hx]
  have v1_r : ∀ y, V1 (.inr y) = S0 (.inr y) := fun y => by
    rw [hV1, Function.update_of_ne (by simp [e0, mkE, jg])]
  obtain ⟨t2, ht2, vc2, FL, FQ, hrun2, hLF, hQF⟩ := g_run a b Δ g hg
  have hA := BitMachineStackRun.run ιG V1 (gfront a b Δ)
    (⟨some (gStart a b Δ), gfrontCtl, G0 g⟩ : TM2.Cfg (fun _ : J2 => Bool) _ _) t2
  rw [hrun2] at hA
  have hA0 : stackCfg ιG V1 (⟨some (gStart a b Δ), gfrontCtl, G0 g⟩ : TM2.Cfg (fun _ : J2 => Bool) _ _) =
      ⟨some (gStart a b Δ), gfrontCtl, V1⟩ := by
    simp only [stackCfg]
    rw [bank_eq_self ιG V1 (G0 g) (fun x => (v1_g x).symm)]
  rw [hA0] at hA
  have hV2 : bank ιG V1 (gBank g hg FL FQ) = W2 g hg k word FL FQ := by
    funext z
    rcases z with z | y
    · exact bank_at ιG V1 _ z
    · rw [bank_outside ιG _ _ _ (by rintro ⟨w, hw⟩; cases hw), v1_r, hS0]; rfl
  have hA' : ((advance (pG a b Δ))^[t2])
      (⟨some (gStart a b Δ), gfrontCtl, V1⟩ : TM2.Cfg (fun _ : JF => Bool) _ _) =
        ⟨none, vc2, W2 g hg k word FL FQ⟩ := by
    rw [← hV2]; exact hA
  obtain ⟨a2, ha2, R2⟩ := BitMachineRawSequence.runs (cq e0) (pG a b Δ) BitMachineCopy.Label.scan
    (gStart a b Δ) oc oc gfrontCtl _ S0 V1 _ (2 * (EncodedGraph.encode g).length + 2) t2 h1 hA'
  refine ⟨a2, ?_, vc2, FL, FQ, ?_, hLF, hQF⟩
  · have e2 : t2 ≤ gBd a b Δ g := ht2
    clear ht2
    generalize gBd a b Δ g = GB at *
    omega
  · rw [← hS0]; exact R2

#print axioms run12

theorem srcB_val (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (word : List Bool)
    (FL : LK → List Bool) (FQ : QK → List Bool) (p s q₂ w Q L : ℕ)
    (hp' : FL LProducer.pC = List.replicate p true) (hs' : FL LProducer.sC = List.replicate s true)
    (hq2' : FL LProducer.q2C = List.replicate q₂ true) (hw' : FL LProducer.wC = List.replicate w true)
    (hQ' : FQ (.inl 24) = List.replicate Q true)
    (hL' : FL (LProducer.outR 0) = List.replicate L true) (i : Fin 7) :
    W2 g hg k word FL FQ (cpB i 0) = List.replicate (![k, p, s, q₂, w, Q, L] i) true := by
  fin_cases i
  · rfl
  · exact hp'
  · exact hs'
  · exact hq2'
  · exact hw'
  · exact hQ'
  · exact hL'

#print axioms srcB_val

theorem doneB (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (word : List Bool)
    (FL : LK → List Bool) (FQ : QK → List Bool) (p s q₂ w Q L : ℕ)
    (hv : ∀ i, W2 g hg k word FL FQ (cpB i 0) = List.replicate (![k, p, s, q₂, w, Q, L] i) true)
    (hddB : ∀ i j, cpB i 1 = cpB j 1 → i = j) :
    CopyAll.done cpB 7 (W2 g hg k word FL FQ) = W3 g hg k word FL FQ ![p, s, q₂, w, Q] L := by
  funext z
  by_cases hz' : ∃ j, cpB j 1 = z
  · obtain ⟨j, rfl⟩ := hz'
    rw [CopyAll.done_dst cpB hddB _ j, hv j]
    have e2 : W2 g hg k word FL FQ (cpB j 1) = [] := rfl
    rw [e2, List.append_nil]
    change _ = TM0 k ![p, s, q₂, w, Q] L (dB j)
    fin_cases j <;> rfl
  · rw [CopyAll.done_off cpB _ z (fun j h => hz' ⟨j, h⟩)]
    rcases z with z | (y | (y | (y | y)))
    · rfl
    · change [] = TM0 k ![p, s, q₂, w, Q] L y
      rcases y with (a' | ⟨i, x⟩) | (m | f)
      · fin_cases a'
        · rfl
        · rfl
        · exact absurd ⟨0, rfl⟩ hz'
        · rfl
      · by_cases hx : x = .inl 0
        · subst hx
          fin_cases i
          · exact absurd ⟨1, rfl⟩ hz'
          · exact absurd ⟨2, rfl⟩ hz'
          · exact absurd ⟨3, rfl⟩ hz'
          · exact absurd ⟨4, rfl⟩ hz'
          · exact absurd ⟨5, rfl⟩ hz'
        · show [] = (if x = .inl 0 then _ else [])
          rw [if_neg hx]
      · by_cases hm : m = 2
        · subst hm; exact absurd ⟨6, rfl⟩ hz'
        · show [] = Function.update (fun _ => []) (2 : MK) (MProducer.u L) m
          rw [Function.update_of_ne hm]
      · rfl
    · rfl
    · rfl
    · rfl

#print axioms doneB

theorem doneC (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (word : List Bool)
    (FL : LK → List Bool) (FQ : QK → List Bool) (FT : TK → List Bool) (FM : MK → List Bool)
    (n p s q₁ q₂ w Q mX mY : ℕ)
    (hv : ∀ i, W4 g hg k word FL FQ FT FM (cpC i 0) =
      ![List.replicate q₂ true, List.replicate q₁ true, List.replicate s true, List.replicate n true,
        List.replicate w true, List.replicate Q true, List.replicate p true, List.replicate k true,
        List.replicate mX true, List.replicate mY true, word] i)
    (hddC : ∀ i j, cpC i 1 = cpC j 1 → i = j) :
    CopyAll.done cpC 11 (W4 g hg k word FL FQ FT FM) =
      exitBankG g hg k word FL FQ FT FM n p s q₁ q₂ w Q mX mY := by
  obtain ⟨c12, c16, c17, c18, c31, c32, c63, c64, cX, cY, cD⟩ :=
    StartInstall.startBank_cells n p s q₁ q₂ w Q k mX mY word
  funext z
  by_cases hz' : ∃ j, cpC j 1 = z
  · obtain ⟨j, rfl⟩ := hz'
    rw [CopyAll.done_dst cpC hddC _ j, hv j]
    have e4 : W4 g hg k word FL FQ FT FM (cpC j 1) = [] := rfl
    rw [e4, List.append_nil]
    change _ = SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word (dC j)
    fin_cases j
    · exact c12.symm
    · exact c16.symm
    · exact c17.symm
    · exact c18.symm
    · exact c31.symm
    · exact c32.symm
    · exact c63.symm
    · exact c64.symm
    · exact cX.symm
    · exact cY.symm
    · exact cD.symm
  · rw [CopyAll.done_off cpC _ z (fun j h => hz' ⟨j, h⟩)]
    rcases z with z | (y | (y | (y | y)))
    · rfl
    · rfl
    · show [] = SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word y
      have hy : y ∉ StartInstall.cells := by
        intro hmem
        simp only [StartInstall.cells, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h | h | h | h | h | h | h | h | h | h | h <;> subst h
        · exact hz' ⟨0, rfl⟩
        · exact hz' ⟨1, rfl⟩
        · exact hz' ⟨2, rfl⟩
        · exact hz' ⟨3, rfl⟩
        · exact hz' ⟨4, rfl⟩
        · exact hz' ⟨5, rfl⟩
        · exact hz' ⟨6, rfl⟩
        · exact hz' ⟨7, rfl⟩
        · exact hz' ⟨8, rfl⟩
        · exact hz' ⟨9, rfl⟩
        · exact hz' ⟨10, rfl⟩
      rw [StartInstall.startBank_off _ _ _ _ _ _ _ _ _ _ _ y hy, StartBlank.blank_nil]
    · rfl
    · rfl

#print axioms doneC

/-- Parts 3-5 composed after parts 1-2, generic in the produced counts (every count a variable). -/
theorem full_gen (a b Δ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (word : List Bool)
    (FL : LK → List Bool) (FQ : QK → List Bool) (n p s q₁ q₂ w Q L a2 : ℕ) (vc2 : _)
    (R2 : ((advance (r1 a b Δ))^[a2])
          (⟨some (leftLabel BitMachineCopy.Label.scan), c1, F0 (X0 g k word)⟩ :
            TM2.Cfg (fun _ : JF => Bool) _ _) =
        ⟨none, (oc, vc2), W2 g hg k word FL FQ⟩)
    (hn' : FL LProducer.nC = List.replicate n true) (hp' : FL LProducer.pC = List.replicate p true)
    (hs' : FL LProducer.sC = List.replicate s true) (hq2' : FL LProducer.q2C = List.replicate q₂ true)
    (hw' : FL LProducer.wC = List.replicate w true) (hq1' : FL LProducer.q1C = List.replicate q₁ true)
    (hL' : FL (LProducer.outR 0) = List.replicate L true) (hQ' : FQ (.inl 24) = List.replicate Q true) :
    ∃ t ≤ a2 + (7 * (2 * (k + p + s + q₂ + w + Q + L) + 3) + 1) + tmBd k ![p, s, q₂, w, Q] L +
        (11 * (2 * (q₂ + q₁ + s + n + w + Q + p + k + mXV (thrVal k ![p, s, q₂, w, Q]) k L +
          mYV (thrVal k ![p, s, q₂, w, Q]) k + word.length) + 3) + 1) + 3,
      ∃ vc, ∃ FT : TK → List Bool, ∃ FM : MK → List Bool,
      ((advance (full a b Δ))^[t])
          (⟨some (fullStart a b Δ), fullCtl, F0 (X0 g k word)⟩ : TM2.Cfg (fun _ : JF => Bool) _ _) =
        ⟨none, vc, exitBankG g hg k word FL FQ FT FM n p s q₁ q₂ w Q
          (mXV (thrVal k ![p, s, q₂, w, Q]) k L) (mYV (thrVal k ![p, s, q₂, w, Q]) k)⟩ ∧
      TFacts k ![p, s, q₂, w, Q] FT ∧ MFacts (thrVal k ![p, s, q₂, w, Q]) k L FM := by
  obtain ⟨bb, hbb⟩ : ∃ x, x = thrVal k ![p, s, q₂, w, Q] := ⟨_, rfl⟩
  rw [← hbb]
  -- (3) seven copies
  have hvB := srcB_val g hg k word FL FQ p s q₂ w Q L hp' hs' hq2' hw' hQ' hL'
  have hdB : ∀ j, cpB j 1 = jt (dB j) := fun j => rfl
  have hsdB : ∀ i j, cpB i 0 ≠ cpB j 1 := fun i j => by rw [hdB]; exact srcB_ne i _
  have hzdB : ∀ i j, cpB i 2 ≠ cpB j 1 := fun i j => by rw [hdB]; exact (jt_zs _).symm
  have hddB : ∀ i j, cpB i 1 = cpB j 1 → i = j := fun i j h => by
    rw [hdB, hdB] at h; exact dB_inj i j (by simpa [jt] using h)
  obtain ⟨t3, ht3, vc3, h3⟩ := CopyAll.all_run cpB hsdB hzdB hddB (W2 g hg k word FL FQ)
    (fun i => rfl) (k + p + s + q₂ + w + Q + L)
    (fun i => by
      rw [hvB, List.length_replicate]
      fin_cases i <;> simp <;> omega) oc
  rw [doneB g hg k word FL FQ p s q₂ w Q L hvB hddB] at h3
  -- (4) the threshold + sample-dimension producer on JM
  obtain ⟨t4, ht4, vc4, FT, FM, hrun4, hT, hM⟩ := tm_run k ![p, s, q₂, w, Q] L
  rw [← hbb] at hM
  have hB := BitMachineStackRun.run ιT (W3 g hg k word FL FQ ![p, s, q₂, w, Q] L) tmProg
    (⟨some tmStart, tmCtl, TM0 k ![p, s, q₂, w, Q] L⟩ : TM2.Cfg (fun _ : JM => Bool) _ _) t4
  rw [hrun4] at hB
  have hB0 : stackCfg ιT (W3 g hg k word FL FQ ![p, s, q₂, w, Q] L)
      (⟨some tmStart, tmCtl, TM0 k ![p, s, q₂, w, Q] L⟩ : TM2.Cfg (fun _ : JM => Bool) _ _) =
      ⟨some tmStart, tmCtl, W3 g hg k word FL FQ ![p, s, q₂, w, Q] L⟩ := by
    simp only [stackCfg]
    rw [bank_eq_self ιT (W3 g hg k word FL FQ ![p, s, q₂, w, Q] L) (TM0 k ![p, s, q₂, w, Q] L) (fun x => rfl)]
  rw [hB0] at hB
  have hB4 : bank ιT (W3 g hg k word FL FQ ![p, s, q₂, w, Q] L) (Sum.elim FT (Sum.elim FM (fun _ => []))) =
      W4 g hg k word FL FQ FT FM := by
    funext z
    rcases z with z | (y | y)
    · exact bank_outside ιT _ _ _ (by rintro ⟨w, hw⟩; cases hw)
    · exact bank_at ιT _ _ y
    · exact bank_outside ιT _ _ _ (by rintro ⟨w, hw⟩; cases hw)
  have hB' : ((advance pTM)^[t4])
      (⟨some tmStart, tmCtl, W3 g hg k word FL FQ ![p, s, q₂, w, Q] L⟩ : TM2.Cfg (fun _ : JF => Bool) _ _) =
      ⟨none, vc4, W4 g hg k word FL FQ FT FM⟩ := by rw [← hB4]; exact hB
  -- (5) eleven installation copies
  have hTM := hM
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hm10, -, -, hm13, -⟩ := hTM
  obtain ⟨mX, hmX⟩ : ∃ x, x = mXV bb k L := ⟨_, rfl⟩
  obtain ⟨mY, hmY⟩ : ∃ x, x = mYV bb k := ⟨_, rfl⟩
  have hm13' : FM 13 = List.replicate mX true := by rw [hmX]; exact hm13
  have hm10' : FM 10 = List.replicate mY true := by rw [hmY]; exact hm10
  rw [← hmX, ← hmY]
  have hvC : ∀ i, W4 g hg k word FL FQ FT FM (cpC i 0) =
      ![List.replicate q₂ true, List.replicate q₁ true, List.replicate s true, List.replicate n true,
        List.replicate w true, List.replicate Q true, List.replicate p true, List.replicate k true,
        List.replicate mX true, List.replicate mY true, word] i := by
    intro i
    fin_cases i
    · exact hq2'
    · exact hq1'
    · exact hs'
    · exact hn'
    · exact hw'
    · exact hQ'
    · exact hp'
    · rfl
    · exact hm13'
    · exact hm10'
    · rfl
  have hdC : ∀ j, cpC j 1 = so (dC j) := fun j => rfl
  have hsdC : ∀ i j, cpC i 0 ≠ cpC j 1 := fun i j => by rw [hdC]; exact srcC_ne i _
  have hzdC : ∀ i j, cpC i 2 ≠ cpC j 1 := fun i j => by rw [hdC]; exact (so_zs _).symm
  have hddC : ∀ i j, cpC i 1 = cpC j 1 → i = j := fun i j h => by
    rw [hdC, hdC] at h; exact dC_inj i j (by simpa [so] using h)
  obtain ⟨t5, ht5, vc5, h5⟩ := CopyAll.all_run cpC hsdC hzdC hddC (W4 g hg k word FL FQ FT FM)
    (fun i => rfl) (q₂ + q₁ + s + n + w + Q + p + k + mX + mY + word.length)
    (fun i => by
      rw [hvC]
      fin_cases i <;> simp <;> omega) oc
  rw [doneC g hg k word FL FQ FT FM n p s q₁ q₂ w Q mX mY hvC hddC] at h5
  -- (6) the handoffs
  obtain ⟨a3, ha3, R3⟩ := BitMachineRawSequence.runs (r1 a b Δ) (CopyAll.prog cpB)
    (leftLabel BitMachineCopy.Label.scan) (.inl ⟨0, by omega⟩) c1 _ oc _ _ _ _ a2 t3 R2 h3
  obtain ⟨a4, ha4, R4⟩ := BitMachineRawSequence.runs (r2 a b Δ) pTM
    (leftLabel (leftLabel BitMachineCopy.Label.scan)) tmStart c2 _ tmCtl _ _ _ _ a3 t4 R3 hB'
  obtain ⟨a5, ha5, R5⟩ := BitMachineRawSequence.runs (r3 a b Δ) (CopyAll.prog cpC)
    (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))) (.inl ⟨0, by omega⟩) c3 _ oc _
    _ _ _ a4 t5 R4 h5
  refine ⟨a5, ?_, (c3, vc5), FT, FM, R5, hT, hM⟩
  generalize tmBd k ![p, s, q₂, w, Q] L = TB at *
  omega

#print axioms full_gen

/-- **Segment (2).** The full H_A3 count front: ONE fixed program `full a b Δ` from the literal packet
`[encode g, unary k, word]` to exactly `SuccessOrient.startBank n p s q₁ q₂ w Q k mX mY word` (with the produced
counts), the packet preserved, every part and handoff charged, explicit clock. -/
theorem full_run (a b Δ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid) (k : ℕ) (word : List Bool) :
    ∃ t ≤ fullBd a b Δ g k word, ∃ vc, ∃ FL : LK → List Bool, ∃ FQ : QK → List Bool,
      ∃ FT : TK → List Bool, ∃ FM : MK → List Bool,
      ((advance (full a b Δ))^[t])
          (⟨some (fullStart a b Δ), fullCtl, F0 (X0 g k word)⟩ : TM2.Cfg (fun _ : JF => Bool) _ _) =
        ⟨none, vc, exitBank a b Δ g hg k word FL FQ FT FM⟩ ∧
      LFacts g.vertices FL ∧ QFacts a b Δ g.vertices g.edges.length (Nat.clog 2 g.vertices)
        (2 ^ (16 + (Nat.clog 2 ((Nat.clog 2 g.vertices) + 1))))
        (2 ^ ((Nat.clog 2 ((Nat.clog 2 g.vertices) + 1)) * (Nat.clog 2 ((Nat.clog 2 g.vertices) + 1)))) FQ ∧
      TFacts k ![pV g, sV g, q2V g, wV g, QV a b Δ g] FT ∧
      MFacts (thrVal k ![pV g, sV g, q2V g, wV g, QV a b Δ g]) k (Lg g) FM := by
  obtain ⟨a2, ha2, vc2, FL, FQ, R2, hLF, hQF⟩ := run12 a b Δ g hg k word
  have hLF' := hLF
  obtain ⟨hn0, -, -, -, -, -, -, hp, hs, hq2, hw, hq1, -, -, -, -, g0, g1', hr0, -, hout0, -⟩ := hLF'
  have hQF' := hQF
  obtain ⟨cq0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h24, -⟩ := hQF'
  have hn' : FL LProducer.nC = List.replicate g.vertices true := hn0
  have hp' : FL LProducer.pC = List.replicate (pV g) true := hp
  have hs' : FL LProducer.sC = List.replicate (sV g) true := hs
  have hq2' : FL LProducer.q2C = List.replicate (q2V g) true := hq2
  have hw' : FL LProducer.wC = List.replicate (wV g) true := hw
  have hq1' : FL LProducer.q1C = List.replicate (q1V g) true := hq1
  have hL' : FL (LProducer.outR 0) = List.replicate (Lg g) true := (hr0 _).trans hout0
  have hQ' : FQ (.inl 24) = List.replicate (QV a b Δ g) true := h24
  obtain ⟨t, ht, vc, FT, FM, hrun, hT, hM⟩ := full_gen a b Δ g hg k word FL FQ g.vertices (pV g) (sV g)
    (q1V g) (q2V g) (wV g) (QV a b Δ g) (Lg g) a2 vc2 R2 hn' hp' hs' hq2' hw' hq1' hL' hQ'
  refine ⟨t, ?_, vc, FL, FQ, FT, FM, hrun, hLF, hQF, hT, hM⟩
  unfold fullBd LB LC
  generalize tmBd k ![pV g, sV g, q2V g, wV g, QV a b Δ g] (Lg g) = TB at *
  generalize gBd a b Δ g = GB at *
  omega

end

#print axioms full_run

end Paper2.FullFront
