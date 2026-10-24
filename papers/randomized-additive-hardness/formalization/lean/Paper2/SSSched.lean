import Paper2.FrontClockF

/-! Lane owner:a-sched-space-1, WP-SCHED (rows T44 `lem:parameters` P:64-66 and U10 `eq:schedule` /
`eq:admissibility`, lock v12 appendix C): the public schedule and its checks as ONE standalone fixed machine
per `(Δ, γ)`, split off the admitted H_A3 front at the schedule/dimension boundary.

Bank `KS = CountFront.J2 ⊕ Fin 1`. Program (one production `BitMachineRawSequence` handoff):

  `sched Δ γ = CountFront.gfront a b Δ (lifted by Sum.inl) ; CheckBit.checkProg sA sB sO Δ γ`

with `a = γ.num.toNat`, `b = γ.den` (machine constants), `sA` = the produced unary `n`, `sB` = the produced unary
`m`, `sO` = the flag cell.  This is `FrontLift.front13` with the k-dependent tail of `FullFront.full` (unary `k`
copy, the threshold / sample-dimension machine `TMFront.tmProg`, the start-bank install) REMOVED: the only input is
the literal graph bytes `EncodedGraph.encode g`; there is no `k`, no tape word, no base matrix anywhere.

Every stage is admitted and reused by exact name: `CountFront.g_run` (literal bytes -> n, m, L, p, s, q₁, q₂, w, Q),
`CheckBit.check_run` (the Checks bit), `BitMachineRawSequence.runs`, `BitMachineStackRun.run`, the admitted value
identities `LProducer.p_eq/s_eq/q₂_eq/w_eq`, `QProducer.coverWidth_eq`. -/

namespace SSSched

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2
open Paper2.A3Assembly
open Paper2.CountFront (J2 LK QK jc lc qc gB gfront gStart gfrontCtl G0 LFacts QFacts g_run)

abbrev KS := J2 ⊕ Fin 1
instance instDecKS : DecidableEq KS := @instDecidableEqSum _ _ FullFront.instDecJ2 inferInstance

def ιS : J2 ↪ KS := ⟨Sum.inl, Sum.inl_injective⟩

def sA : KS := .inl (jc (lc LProducer.nC))
def sB : KS := .inl (jc (qc (.inl 1)))
def sO : KS := .inr 0

theorem sA_sB : sA ≠ sB := by simp [sA, sB, jc, lc, qc]
theorem sA_sO : sA ≠ sO := by simp [sA, sO]
theorem sB_sO : sB ≠ sO := by simp [sB, sO]

/-- **The schedule machine**: ONE fixed program per `(Δ, γ)`. -/
def sched (Δ : ℕ) (γ : ℚ) :=
  BitMachineRawSequence.program (Lift.liftP ιS (gfront γ.num.toNat γ.den Δ))
    (CheckBit.checkProg sA sB sO Δ γ) CheckBit.DL.rdA gfrontCtl
    (CheckBit.ctl0 (CheckBit.NA Δ γ) (CheckBit.NB Δ γ))

/-- Start label and control. -/
def schedStart (Δ : ℕ) (γ : ℚ) := FullFront.labelOfP (sched Δ γ)
  (BitMachineRawSequence.leftLabel (gStart γ.num.toNat γ.den Δ))
def schedCtl (Δ : ℕ) (γ : ℚ) := (gfrontCtl, CheckBit.ctl0 (CheckBit.NA Δ γ) (CheckBit.NB Δ γ))

theorem bank_inlS (S : J2 → List Bool) : bank ιS (fun _ => []) S = Sum.elim S (fun _ => []) := by
  funext x
  rcases x with x | x
  · exact bank_at ιS _ S x
  · rw [bank_outside ιS _ S _ (by rintro ⟨y, hy⟩; cases hy)]
    rfl

/-- The exact exit bank of the admitted `g_run` (graph-byte front), for scratch `FL`, `FQ`. -/
def gExit (g : EncodedGraph.Graph) (hg : g.Valid) (FL : LK → List Bool) (FQ : QK → List Bool) :
    J2 → List Bool :=
  Sum.elim (Sum.elim FL (Sum.elim FQ (fun _ => [])))
    (Sum.elim (PublicGraphEndpointMachine.resultBank g hg) (fun _ => EncodedGraph.encode g))

/-- **WP-SCHED run.** From the literal graph bytes alone (start bank: `encode g` in the byte cell, every other cell
blank), the ONE program `sched Δ γ` halts within `gBd + (n + m + 2) + 1` steps in EXACTLY the bank
`Sum.elim (gExit g hg FL FQ) (fun _ => [bit])` with the two consumed unary counts erased; `FL`, `FQ` satisfy the
admitted full cell specifications `LFacts` / `QFacts` (every cell pinned except the named log-machine scratch), the
cells hold the scheduled values in unary (`p`, `s`, `q₁`, `q₂`, `w`, `L`, `Q`), and `bit = true ↔ Checks`. -/
theorem sched_run (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ) :
    ∃ T ≤ FullFront.gBd γ.num.toNat γ.den Δ g + (g.vertices + g.edges.length + 2) + 1,
      ∃ u, ∃ bit : Bool, ∃ FL : LK → List Bool, ∃ FQ : QK → List Bool,
        ((advance (sched Δ γ))^[T])
            (⟨some (schedStart Δ γ), schedCtl Δ γ, Sum.elim (G0 g) (fun _ => [])⟩ :
              TM2.Cfg (fun _ : KS => Bool) _ _) =
          ⟨none, u, Function.update (Function.update
            (Sum.elim (gExit g hg FL FQ) (fun _ => [bit])) sA []) sB []⟩ ∧
        LFacts g.vertices FL ∧
        QFacts γ.num.toNat γ.den Δ g.vertices g.edges.length (Nat.clog 2 g.vertices)
          (2 ^ (16 + (Nat.clog 2 ((Nat.clog 2 g.vertices) + 1))))
          (2 ^ ((Nat.clog 2 ((Nat.clog 2 g.vertices) + 1)) * (Nat.clog 2 ((Nat.clog 2 g.vertices) + 1)))) FQ ∧
        FL LProducer.pC = LProducer.u (LookupSeed.width (Nat.clog 2 g.vertices)) ∧
        FL LProducer.sC = LProducer.u (SourceProfileParameters.width (Nat.clog 2 g.vertices)) ∧
        FL LProducer.q1C = LProducer.u (SourceProfileParameters.width (Nat.clog 2 g.vertices) - 2) ∧
        FL LProducer.q2C = LProducer.u (SourceProfileParameters.outerWidth (Nat.clog 2 g.vertices)) ∧
        FL LProducer.wC = LProducer.u (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices)) ∧
        FQ (.inl 2) = QProducer.u (Nat.clog 2 g.vertices) ∧
        FQ (.inl 24) = QProducer.u
          (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) ∧
        (bit = true ↔ CompletePublicScheduleScratch.Checks (V := Fin g.vertices) (E := Fin g.edges.length)
          (Nat.clog 2 g.vertices) Δ γ) := by
  obtain ⟨hm, -⟩ := CheckBit.pos_of_hyp Δ g hg hn hinc hdeg
  obtain ⟨t1, ht1, vc, FL, FQ, hrun, hLF, hQF⟩ := g_run γ.num.toNat γ.den Δ g hg
  have h1 := BitMachineStackRun.run ιS (fun _ => []) (gfront γ.num.toNat γ.den Δ)
    ⟨some (gStart γ.num.toNat γ.den Δ), gfrontCtl, G0 g⟩ t1
  rw [hrun] at h1
  have hA : bank ιS (fun _ => []) (gExit g hg FL FQ) sA = List.replicate g.vertices true := by
    rw [bank_inlS]; exact hLF.1
  have hQF' := hQF
  obtain ⟨c, -, hq1, -⟩ := hQF'
  have hB : bank ιS (fun _ => []) (gExit g hg FL FQ) sB = List.replicate g.edges.length true := by
    rw [bank_inlS]; exact hq1
  obtain ⟨w, bit, h2, hbit⟩ :=
    CheckBit.check_run sA sB sO sA_sB sA_sO sB_sO Δ γ hγ hΔ g hg hn hinc hdeg _ hA hB
  obtain ⟨T, hT, hr⟩ := BitMachineRawSequence.runs (Lift.liftP ιS (gfront γ.num.toNat γ.den Δ))
    (CheckBit.checkProg sA sB sO Δ γ) (gStart γ.num.toNat γ.den Δ) CheckBit.DL.rdA gfrontCtl vc
    (CheckBit.ctl0 (CheckBit.NA Δ γ) (CheckBit.NB Δ γ)) w _ _ _ t1 (g.vertices + g.edges.length + 2) h1 h2
  -- the exit bank in closed form
  have hex : Function.update (Function.update (Function.update
      (bank ιS (fun _ => []) (gExit g hg FL FQ)) sA []) sB [])
        sO (bit :: bank ιS (fun _ => []) (gExit g hg FL FQ) sO) =
      Function.update (Function.update (Sum.elim (gExit g hg FL FQ) (fun _ => [bit])) sA []) sB [] := by
    rw [bank_inlS]
    funext x
    by_cases hxO : x = sO
    · subst hxO
      rw [Function.update_self, Function.update_of_ne (Ne.symm sB_sO), Function.update_of_ne (Ne.symm sA_sO)]
      rfl
    · rw [Function.update_of_ne hxO]
      by_cases hxB : x = sB
      · subst hxB; rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hxB, Function.update_of_ne hxB]
        by_cases hxA : x = sA
        · subst hxA; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hxA, Function.update_of_ne hxA]
          rcases x with x | x
          · rfl
          · exact absurd (by fin_cases x; rfl) hxO
  have hstart : bank ιS (fun _ => []) (G0 g) = Sum.elim (G0 g) (fun _ => []) := bank_inlS _
  rw [hex] at hr
  change ((advance (sched Δ γ))^[T])
      (⟨some (schedStart Δ γ), schedCtl Δ γ, bank ιS (fun _ => []) (G0 g)⟩ :
        TM2.Cfg (fun _ : KS => Bool) _ _) = _ at hr
  rw [hstart] at hr
  -- the scheduled values (admitted identities, as in `CountFront.lq_run_sched`)
  have hLF' := hLF
  obtain ⟨-, -, -, -, -, -, -, hp, hs, hq2, hw, hq1', -⟩ := hLF'
  have hQF'' := hQF
  obtain ⟨c', -, -, hL2, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h24, -⟩ := hQF''
  have ht1' : t1 ≤ FullFront.gBd γ.num.toNat γ.den Δ g := ht1
  refine ⟨T, by omega, _, bit, FL, FQ, hr, hLF, hQF, ?_, ?_, ?_, ?_, ?_, hL2, ?_, hbit⟩
  · rw [hp, LProducer.p_eq]
  · rw [hs, LProducer.s_eq]
  · rw [hq1', LProducer.s_eq]
  · rw [hq2, LProducer.q₂_eq]
  · rw [hw, LProducer.w_eq]
  · rw [h24, QProducer.coverWidth_eq g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ hγ hΔ hn hm,
      ← LProducer.s_eq, ← LProducer.w_eq]
    rfl

end

end SSSched

#print axioms SSSched.sched_run
