import Paper2.LQFront
import Paper2.PublicGraphEndpointMachine

/-! Unit 3, segment (2), third part: the count front from the literal graph bytes.

Bank `J2 = J1 ⊕ (PS ⊕ Fin 1)` (`J1` = the L -> Q front bank, `PS` = the admitted
`PublicGraphEndpointMachine` bank, one input cell holding the literal bytes `EncodedGraph.encode g`).
ONE fixed program `gfront a b Δ` (five parts, production `BitMachineRawSequence` handoffs):
admitted `copyProgram` (bytes -> endpoint input cell, source kept); the admitted
`PublicGraphEndpointMachine.program` lifted to `PS` (charged: `physical_run_public`, clock
`103 (|encode g| + 1)^3`); two admitted `copyProgram`s (the endpoint's unary vertex count -> LK cell 0,
its unary edge count -> QK cell 1); `CountFront.front a b Δ` lifted to `J1`.
Start bank: only the literal bytes, in the input cell. -/

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

namespace Paper2.CountFront

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)

abbrev PS := PublicGraphEndpointMachine.Stack
abbrev J2 := J1 ⊕ (PS ⊕ Fin 1)

def jc (x : J1) : J2 := .inl x
def pc2 (x : PS) : J2 := .inr (.inl x)
def gB : J2 := .inr (.inr 0)
def gIn : PS := .inl (.inl 0)
def vOut : PS := .inl (.inr 0)
def mOut : PS := .inl (.inr 1)

def ιJ : J1 ↪ J2 := ⟨Sum.inl, fun _ _ h => Sum.inl_injective h⟩
def ιPS : PS ↪ J2 := ⟨fun x => .inr (.inl x), fun a b h => by simpa using h⟩

def k1 : Fin 3 ↪ J2 := ⟨![gB, pc2 gIn, jc sc], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [gB, pc2, jc, sc, gIn]⟩
def k2 : Fin 3 ↪ J2 := ⟨![pc2 vOut, jc (lc LProducer.nC), jc sc], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [pc2, jc, sc, lc, vOut]⟩
def k3 : Fin 3 ↪ J2 := ⟨![pc2 mOut, jc (qc (.inl 1)), jc sc], by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [pc2, jc, sc, qc, mOut]⟩

def graphP := fun l => stackStmt ιPS (PublicGraphEndpointMachine.program l)
def pF (a b Δ : ℕ) := fun l => stackStmt ιJ (front a b Δ l)
def cq (e : Fin 3 ↪ J2) := MatrixStage4ScalarPreparationOps.copyProgram e

def gCtl := ((none : Option Bool), PublicGraphEndpointMachine.parserControl)
def h1 := BitMachineRawSequence.program (cq k1) graphP (leftLabel BitMachineCopy.Label.scan) oc gCtl
def m1 := (oc, gCtl)
def h2 := BitMachineRawSequence.program h1 (cq k2) BitMachineCopy.Label.scan m1 oc
def m2 := (m1, oc)
def h3 := BitMachineRawSequence.program h2 (cq k3) BitMachineCopy.Label.scan m2 oc
def m3 := (m2, oc)
/-- The count front from the literal graph bytes: ONE fixed program (machine constants `a b Δ`). -/
def gfront (a b Δ : ℕ) := BitMachineRawSequence.program h3 (pF a b Δ) (frontStart a b Δ) m3 frontCtl
def gfrontCtl := (m3, frontCtl)
def gStart (a b Δ : ℕ) := labelOfP (gfront a b Δ)
  (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))

/-- Start bank: the literal graph bytes in the input cell; everything else blank. -/
def G0 (g : EncodedGraph.Graph) : J2 → List Bool :=
  Function.update (fun _ => []) gB (EncodedGraph.encode g)

/-- The clock bound of `lq_run`, named. -/
def lqBd (a b Δ n m : ℕ) : ℕ :=
  LProducer.lBd n + (2 * n + 2) + (2 * (Nat.clog 2 n) + 2) + (2 * (2 ^ (16 + (Nat.clog 2 ((Nat.clog 2 n) + 1)))) + 2) + (2 * (2 ^ ((Nat.clog 2 ((Nat.clog 2 n) + 1)) * (Nat.clog 2 ((Nat.clog 2 n) + 1)))) + 2) +
        QProducer.qBd a b Δ n m (Nat.clog 2 n) (2 ^ (16 + (Nat.clog 2 ((Nat.clog 2 n) + 1)))) (2 ^ ((Nat.clog 2 ((Nat.clog 2 n) + 1)) * (Nat.clog 2 ((Nat.clog 2 n) + 1)))) + 5

theorem g_run (a b Δ : ℕ) (g : EncodedGraph.Graph) (hg : g.Valid) :
    ∃ t ≤ (2 * (EncodedGraph.encode g).length + 2) + 103 * ((EncodedGraph.encode g).length + 1) ^ 3 +
        (2 * g.vertices + 2) + (2 * g.edges.length + 2) + lqBd a b Δ g.vertices g.edges.length + 4,
      ∃ vc, ∃ FL : LK → List Bool, ∃ FQ : QK → List Bool,
      ((advance (gfront a b Δ))^[t])
          (⟨some (gStart a b Δ), gfrontCtl, G0 g⟩ : TM2.Cfg (fun _ : J2 => Bool) _ _) =
        ⟨none, vc, Sum.elim (Sum.elim FL (Sum.elim FQ (fun _ => [])))
          (Sum.elim (PublicGraphEndpointMachine.resultBank g hg) (fun _ => EncodedGraph.encode g))⟩ ∧
      LFacts g.vertices FL ∧
      QFacts a b Δ g.vertices g.edges.length (Nat.clog 2 g.vertices)
        (2 ^ (16 + (Nat.clog 2 ((Nat.clog 2 g.vertices) + 1))))
        (2 ^ ((Nat.clog 2 ((Nat.clog 2 g.vertices) + 1)) * (Nat.clog 2 ((Nat.clog 2 g.vertices) + 1)))) FQ := by
  obtain ⟨S0, hS0⟩ : ∃ S, S = G0 g := ⟨_, rfl⟩
  -- (1) bytes -> endpoint input
  have c1 := MatrixStage4ScalarPreparationOps.copy_run k1 S0 (by simp [hS0, G0, k1, gB, jc, sc])
  have l1 : (S0 (k1 0)).length = (EncodedGraph.encode g).length := by simp [hS0, G0, k1]
  rw [l1] at c1
  obtain ⟨S1, hS1⟩ : ∃ S, S = Function.update S0 (k1 1) (S0 (k1 0) ++ S0 (k1 1)) := ⟨_, rfl⟩
  rw [← hS1] at c1
  have hP : bank ιPS S1 (PublicGraphEndpointMachine.initialBank (EncodedGraph.encode g)) = S1 := by
    apply bank_eq_self
    intro x
    by_cases hx : x = gIn
    · subst hx
      have e : S1 (ιPS gIn) = EncodedGraph.encode g := by
        simp [hS1, hS0, G0, k1, gB, pc2, gIn, ιPS]
      rw [e]
      rfl
    · have e : S1 (ιPS x) = [] := by
        have hx' : ιPS x ≠ pc2 gIn := fun h => hx (ιPS.injective h)
        simp only [hS1, k1, Function.Embedding.coeFn_mk, Matrix.cons_val_one, Matrix.cons_val_zero]
        rw [Function.update_of_ne hx', hS0, G0, Function.update_of_ne (by simp [ιPS, gB])]
      rw [e]
      rcases x with (y | y) | y
      · fin_cases y
        · exact absurd rfl hx
        all_goals rfl
      · fin_cases y <;> rfl
      · fin_cases y <;> rfl
  -- (2) the admitted endpoint machine on the side region
  obtain ⟨t2, ht2, hr2⟩ := PublicGraphEndpointMachine.physical_run_public g hg
  have r2 := BitMachineStackRun.run ιPS S1 PublicGraphEndpointMachine.program
    (PublicGraphEndpointMachine.start (EncodedGraph.encode g)) t2
  change _ = stackCfg ιPS S1 (PublicGraphEndpointMachine.run t2 _) at r2
  rw [hr2] at r2
  have hst : stackCfg ιPS S1 (PublicGraphEndpointMachine.start (EncodedGraph.encode g)) =
      ⟨some (leftLabel BitMachineCopy.Label.scan), gCtl, S1⟩ := by
    simp only [stackCfg, PublicGraphEndpointMachine.start]
    rw [hP]
    rfl
  rw [hst] at r2
  obtain ⟨S2, hS2⟩ : ∃ S, S = bank ιPS S1 (PublicGraphEndpointMachine.resultBank g hg) := ⟨_, rfl⟩
  have r2' : ((advance graphP)^[t2])
      (⟨some (leftLabel BitMachineCopy.Label.scan), gCtl, S1⟩ : TM2.Cfg (fun _ : J2 => Bool) _ _) =
      ⟨none, (none, SourceNormalizationMachineDecode.doneControl true), S2⟩ := by rw [hS2]; exact r2
  have s2p : ∀ x, S2 (pc2 x) = PublicGraphEndpointMachine.resultBank g hg x := fun x => by
    rw [hS2]; exact bank_at ιPS S1 _ x
  have s2j : ∀ y, S2 (jc y) = [] := fun y => by
    rw [hS2, bank_outside ιPS _ _ _ (by rintro ⟨k, hk⟩; cases hk), hS1,
      Function.update_of_ne (by simp [k1, jc, pc2]), hS0, G0, Function.update_of_ne (by simp [jc, gB])]
  have s2g : S2 gB = EncodedGraph.encode g := by
    rw [hS2, bank_outside ιPS _ _ _ (by rintro ⟨k, hk⟩; cases hk), hS1,
      Function.update_of_ne (by simp [k1, gB, pc2]), hS0, G0, Function.update_self]
  -- (3) the two counts
  have c2 := MatrixStage4ScalarPreparationOps.copy_run k2 S2 (by simp [k2, s2j])
  have l2 : (S2 (k2 0)).length = g.vertices := by
    show (S2 (pc2 vOut)).length = _
    rw [s2p]; show (List.replicate g.vertices true).length = _; simp
  rw [l2] at c2
  obtain ⟨S3, hS3⟩ : ∃ S, S = Function.update S2 (k2 1) (S2 (k2 0) ++ S2 (k2 1)) := ⟨_, rfl⟩
  rw [← hS3] at c2
  have c3 := MatrixStage4ScalarPreparationOps.copy_run k3 S3
    (by
      show S3 (jc sc) = []
      rw [hS3, Function.update_of_ne (by simp [k2, jc, sc, lc]), s2j])
  have l3 : (S3 (k3 0)).length = g.edges.length := by
    show (S3 (pc2 mOut)).length = _
    rw [hS3, Function.update_of_ne (by simp [k2, pc2, jc]), s2p]
    show (List.replicate g.edges.length true).length = _; simp
  rw [l3] at c3
  obtain ⟨S4, hS4⟩ : ∃ S, S = Function.update S3 (k3 1) (S3 (k3 0) ++ S3 (k3 1)) := ⟨_, rfl⟩
  rw [← hS4] at c3
  have hJ : bank ιJ S4 (J0 g.vertices g.edges.length) = S4 := by
    apply bank_eq_self
    intro x
    show J0 g.vertices g.edges.length x = S4 (jc x)
    rw [hS4, hS3]
    by_cases hx1 : x = qc (.inl 1)
    · subst hx1
      rw [show jc (qc (.inl 1)) = k3 1 from rfl, Function.update_self,
        Function.update_of_ne (show k3 0 ≠ k2 1 by simp [k3, k2, pc2, jc]),
        Function.update_of_ne (show k3 1 ≠ k2 1 by simp [k3, k2, jc, qc, lc])]
      show _ = S2 (pc2 mOut) ++ S2 (jc (qc (.inl 1)))
      rw [s2p, s2j, List.append_nil]
      simp only [J0, Sum.elim_inr, Sum.elim_inl, qc, Function.update_self]
      rfl
    · by_cases hx0 : x = lc LProducer.nC
      · subst hx0
        rw [show jc (lc LProducer.nC) = k2 1 from rfl,
          Function.update_of_ne (show k2 1 ≠ k3 1 by simp [k3, k2, jc, qc, lc]), Function.update_self]
        show _ = S2 (pc2 vOut) ++ S2 (jc (lc LProducer.nC))
        rw [s2p, s2j, List.append_nil]
        simp only [J0, Sum.elim_inl, lc, LProducer.L0, Function.update_self]
        rfl
      · have e1' : jc x ≠ k3 1 := fun h => hx1 (by simpa [k3, jc] using h)
        have e0' : jc x ≠ k2 1 := fun h => hx0 (by simpa [k2, jc] using h)
        rw [Function.update_of_ne e1', Function.update_of_ne e0', s2j]
        rcases x with y | (z | f)
        · show LProducer.L0 g.vertices y = []
          rw [LProducer.L0, Function.update_of_ne (fun h => hx0 (by rw [h]; rfl))]
        · show Function.update (fun _ => []) (.inl 1) (QProducer.u g.edges.length) z = []
          rw [Function.update_of_ne (fun h => hx1 (by rw [h]; rfl))]
        · rfl
  -- (4) the L -> Q front on J1
  obtain ⟨t5, ht5, vc5, FL, FQ, hrun5, hLF, hQF⟩ := lq_run a b Δ g.vertices g.edges.length
  have ht5' : t5 ≤ lqBd a b Δ g.vertices g.edges.length := ht5
  have r5 := BitMachineStackRun.run ιJ S4 (front a b Δ)
    (⟨some (frontStart a b Δ), frontCtl, J0 g.vertices g.edges.length⟩ : TM2.Cfg (fun _ : J1 => Bool) _ _) t5
  rw [hrun5] at r5
  have hst5 : stackCfg ιJ S4
      (⟨some (frontStart a b Δ), frontCtl, J0 g.vertices g.edges.length⟩ : TM2.Cfg (fun _ : J1 => Bool) _ _) =
      ⟨some (frontStart a b Δ), frontCtl, S4⟩ := by
    simp only [stackCfg]
    rw [hJ]
  rw [hst5] at r5
  have r5' : ((advance (pF a b Δ))^[t5])
      (⟨some (frontStart a b Δ), frontCtl, S4⟩ : TM2.Cfg (fun _ : J2 => Bool) _ _) =
      ⟨none, vc5, bank ιJ S4 (Sum.elim FL (Sum.elim FQ (fun _ => [])))⟩ := r5
  obtain ⟨a2, ha2, R2⟩ := BitMachineRawSequence.runs (cq k1) graphP BitMachineCopy.Label.scan
    (leftLabel BitMachineCopy.Label.scan) oc _ gCtl _ _ _ _ (2 * (EncodedGraph.encode g).length + 2) t2 c1 r2'
  obtain ⟨a3, ha3, R3⟩ := BitMachineRawSequence.runs h1 (cq k2) (leftLabel BitMachineCopy.Label.scan)
    BitMachineCopy.Label.scan m1 _ oc _ _ _ _ a2 (2 * g.vertices + 2) R2 c2
  obtain ⟨a4, ha4, R4⟩ := BitMachineRawSequence.runs h2 (cq k3)
    (leftLabel (leftLabel BitMachineCopy.Label.scan)) BitMachineCopy.Label.scan m2 _ oc _ _ _ _ a3
    (2 * g.edges.length + 2) R3 c3
  obtain ⟨a5, ha5, R5⟩ := BitMachineRawSequence.runs h3 (pF a b Δ)
    (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))) (frontStart a b Δ) m3 _ frontCtl _ _ _ _
    a4 t5 R4 r5'
  have hfin : bank ιJ S4 (Sum.elim FL (Sum.elim FQ (fun _ => []))) =
      Sum.elim (Sum.elim FL (Sum.elim FQ (fun _ => [])))
        (Sum.elim (PublicGraphEndpointMachine.resultBank g hg) (fun _ => EncodedGraph.encode g)) := by
    funext x
    rcases x with y | (z | f)
    · exact bank_at ιJ S4 _ y
    · rw [bank_outside ιJ _ _ _ (by rintro ⟨k, hk⟩; cases hk), hS4,
        Function.update_of_ne (by simp [k3, jc]), hS3, Function.update_of_ne (by simp [k2, jc])]
      exact s2p z
    · rw [bank_outside ιJ _ _ _ (by rintro ⟨k, hk⟩; cases hk), hS4,
        Function.update_of_ne (by simp [k3, jc]), hS3, Function.update_of_ne (by simp [k2, jc])]
      have hf : f = 0 := Subsingleton.elim _ _
      subst hf
      exact s2g
  rw [hfin, hS0] at R5
  refine ⟨a5, ?_, _, FL, FQ, R5, hLF, hQF⟩
  generalize lqBd a b Δ g.vertices g.edges.length = QB at *
  generalize 103 * ((EncodedGraph.encode g).length + 1) ^ 3 = PB at *
  omega

end

#print axioms g_run

end Paper2.CountFront
