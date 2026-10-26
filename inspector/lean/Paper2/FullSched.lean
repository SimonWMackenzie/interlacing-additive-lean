import Paper2.FullFront

/-! Unit 3, lane a-success-table-12, segment (2) at the H-A3 schedule.

For the fixed machine constants `a = γ.num.toNat`, `b = γ.den`, `Δ`, the ONE program `FullFront.full a b Δ`, started on the
literal packet `[encode g, unary k, word]`, installs EXACTLY
`SuccessOrient.startBank n (LookupSeed.width L) (width L) (width L - 2) (outerWidth L) (restorationWidth L)
  (coverWidth n m L Δ γ) k (sourceRows L r q k) (sourceCols L r q k) word`
with `n = g.vertices`, `m = |E(g)|`, `L = clog₂ n`, `r = restorationDepth L`, `q = coverDepth n m L Δ γ`
(the argument order of `RepJoin.success_run_rep`), under `0 < γ`, `0 < Δ`, `0 < n`, `0 < m` (needed only by the
admitted value identity `QProducer.coverWidth_eq`). Owner-10 `LProducer.p_eq`, `s_eq`, `q₂_eq`, `w_eq`, owner-11
`QProducer.coverWidth_eq`, segment 1 `TMFront.thrVal_sched`, admitted `MProducer.rows_eq`, `cols_eq`, all by exact name. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.FullFront

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.CountFront (LK QK LFacts QFacts)
open Paper2.TMFront (TK MK TFacts MFacts thrVal)

theorem pV_eq (g : EncodedGraph.Graph) : pV g = LookupSeed.width (Nat.clog 2 g.vertices) := by
  rw [LProducer.p_eq]; rfl
theorem sV_eq (g : EncodedGraph.Graph) : sV g = SourceProfileParameters.width (Nat.clog 2 g.vertices) := by
  rw [LProducer.s_eq]; rfl
theorem q1V_eq (g : EncodedGraph.Graph) :
    q1V g = SourceProfileParameters.width (Nat.clog 2 g.vertices) - 2 := by
  rw [LProducer.s_eq]; rfl
theorem q2V_eq (g : EncodedGraph.Graph) :
    q2V g = SourceProfileParameters.outerWidth (Nat.clog 2 g.vertices) := by
  rw [LProducer.q₂_eq]; rfl
theorem wV_eq (g : EncodedGraph.Graph) :
    wV g = ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices) := by
  rw [LProducer.w_eq]; rfl
theorem QV_eq (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ) (g : EncodedGraph.Graph) (hn : 0 < g.vertices)
    (hm : 0 < g.edges.length) :
    QV γ.num.toNat γ.den Δ g =
      ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ := by
  rw [QProducer.coverWidth_eq g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ hγ hΔ hn hm,
    ← sV_eq, ← wV_eq]
  rfl

theorem vec_eq (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ) (g : EncodedGraph.Graph) (hn : 0 < g.vertices)
    (hm : 0 < g.edges.length) :
    ![pV g, sV g, q2V g, wV g, QV γ.num.toNat γ.den Δ g] = TMFront.vS g.vertices g.edges.length Δ γ := by
  rw [pV_eq, sV_eq, q2V_eq, wV_eq, QV_eq Δ γ hγ hΔ g hn hm]
  rfl

theorem budget_sched (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ) (g : EncodedGraph.Graph)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length) (k : ℕ) :
    thrVal k ![pV g, sV g, q2V g, wV g, QV γ.num.toNat γ.den Δ g] =
      SourceRecursiveNoSampling.sourceBudget (Nat.clog 2 g.vertices)
        (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
        (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k := by
  rw [vec_eq Δ γ hγ hΔ g hn hm]
  exact TMFront.thrVal_sched g.vertices g.edges.length Δ γ k

/-- **Segment (2) at the schedule.** -/
theorem full_run_sched (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ) (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length) (k : ℕ) (word : List Bool) :
    ∃ t ≤ fullBd γ.num.toNat γ.den Δ g k word, ∃ vc, ∃ FL : LK → List Bool, ∃ FQ : QK → List Bool,
      ∃ FT : TK → List Bool, ∃ FM : MK → List Bool,
      ((advance (full γ.num.toNat γ.den Δ))^[t])
          (⟨some (fullStart γ.num.toNat γ.den Δ), fullCtl, F0 (X0 g k word)⟩ :
            TM2.Cfg (fun _ : JF => Bool) _ _) =
        ⟨none, vc, exitBankG g hg k word FL FQ FT FM g.vertices
          (LookupSeed.width (Nat.clog 2 g.vertices))
          (SourceProfileParameters.width (Nat.clog 2 g.vertices))
          (SourceProfileParameters.width (Nat.clog 2 g.vertices) - 2)
          (SourceProfileParameters.outerWidth (Nat.clog 2 g.vertices))
          (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices))
          (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ)
          (SourceRecursiveNoSampling.sourceRows (Nat.clog 2 g.vertices)
            (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
            (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k)
          (SourceRecursiveNoSampling.sourceCols (Nat.clog 2 g.vertices)
            (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
            (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k)⟩ ∧
      LFacts g.vertices FL ∧ QFacts γ.num.toNat γ.den Δ g.vertices g.edges.length (Nat.clog 2 g.vertices)
        (2 ^ (16 + (Nat.clog 2 ((Nat.clog 2 g.vertices) + 1))))
        (2 ^ ((Nat.clog 2 ((Nat.clog 2 g.vertices) + 1)) * (Nat.clog 2 ((Nat.clog 2 g.vertices) + 1)))) FQ ∧
      TFacts k (TMFront.vS g.vertices g.edges.length Δ γ) FT ∧
      MFacts (thrVal k (TMFront.vS g.vertices g.edges.length Δ γ)) k (Nat.clog 2 g.vertices) FM := by
  obtain ⟨t, ht, vc, FL, FQ, FT, FM, hr, hL, hQ, hT, hM⟩ := full_run γ.num.toNat γ.den Δ g hg k word
  have eb := budget_sched Δ γ hγ hΔ g hn hm k
  have emX : mXV (thrVal k ![pV g, sV g, q2V g, wV g, QV γ.num.toNat γ.den Δ g]) k (Lg g) =
      SourceRecursiveNoSampling.sourceRows (Nat.clog 2 g.vertices)
        (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
        (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k := by
    rw [eb, MProducer.rows_eq]; rfl
  have emY : mYV (thrVal k ![pV g, sV g, q2V g, wV g, QV γ.num.toNat γ.den Δ g]) k =
      SourceRecursiveNoSampling.sourceCols (Nat.clog 2 g.vertices)
        (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
        (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k := by
    rw [eb, MProducer.cols_eq]; rfl
  have ev := vec_eq Δ γ hγ hΔ g hn hm
  refine ⟨t, ht, vc, FL, FQ, FT, FM, ?_, hL, hQ, ?_, ?_⟩
  · have e : exitBank γ.num.toNat γ.den Δ g hg k word FL FQ FT FM =
        exitBankG g hg k word FL FQ FT FM g.vertices
          (LookupSeed.width (Nat.clog 2 g.vertices))
          (SourceProfileParameters.width (Nat.clog 2 g.vertices))
          (SourceProfileParameters.width (Nat.clog 2 g.vertices) - 2)
          (SourceProfileParameters.outerWidth (Nat.clog 2 g.vertices))
          (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices))
          (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ)
          (SourceRecursiveNoSampling.sourceRows (Nat.clog 2 g.vertices)
            (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
            (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k)
          (SourceRecursiveNoSampling.sourceCols (Nat.clog 2 g.vertices)
            (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
            (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k) := by
      unfold exitBank
      rw [emX, emY, pV_eq, sV_eq, q1V_eq, q2V_eq, wV_eq, QV_eq Δ γ hγ hΔ g hn hm]
    rw [← e]; exact hr
  · rw [← ev]; exact hT
  · rw [← ev]; exact hM

end Paper2.FullFront

#print axioms Paper2.FullFront.QV_eq
#print axioms Paper2.FullFront.budget_sched
#print axioms Paper2.FullFront.full_run_sched
