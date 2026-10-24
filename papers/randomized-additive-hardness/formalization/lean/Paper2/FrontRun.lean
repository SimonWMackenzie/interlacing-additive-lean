import Paper2.FrontLift

/-! Unit 3 (lock v12 App. D; T44/U10), lane a-success-table-13, segment (2) (run): the re-banked front from the widened
H_A3 packet to exactly the Mid1 bank `layoutBank FS X (region FS (startBank …) ![[bit], [], []] Z)`, with
`bit = true ↔ Checks`, clock `fullBd + (n + m + 2) + 1`. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

namespace Paper2.FrontLift

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.FullFront (JF jg jt so pk zs full fullStart fullCtl F0 X0 exitBankG)
open Paper2.A3Assembly
open SourceProfileParameters SourceRecursiveNoSampling

/-- The scheduled start bank (the let-values of `RepMain.success_run_rep` / `Lift.startCanon`, generic word). -/
def stSched (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (k : ℕ) (word : List Bool) : SuccessOrient.Stack → List Bool :=
  SuccessOrient.startBank g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
    (width (Nat.clog 2 g.vertices)) (width (Nat.clog 2 g.vertices) - 2)
    (outerWidth (Nat.clog 2 g.vertices))
    (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices))
    (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k
    (sourceRows (Nat.clog 2 g.vertices)
      (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k)
    (sourceCols (Nat.clog 2 g.vertices)
      (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k)
    word

/-- The front on its own bank `K13`. -/
theorem front13_run (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ)
    (k : ℕ) (word : List Bool) :
    ∃ T ≤ FullFront.fullBd γ.num.toNat γ.den Δ g k word + (g.vertices + g.edges.length + 2) + 1,
      ∃ u, ∃ bit : Bool, ∃ E : JF → List Bool,
        ((advance (front13 Δ γ))^[T])
            (⟨some (sF Δ γ), vF Δ γ, bank ιL (fun _ => []) (F0 (X0 g k word))⟩ :
              TM2.Cfg (fun _ : K13 => Bool) _ _) =
          ⟨none, u, Function.update (Function.update (Function.update (bank ιL (fun _ => []) E) cA []) cB []) cO
            (bit :: bank ιL (fun _ => []) E cO)⟩ ∧
        (∀ x, E (so x) = stSched Δ γ g k word x) ∧ (∀ i, E (pk i) = X0 g k word i) ∧
        (bit = true ↔ CompletePublicScheduleScratch.Checks (V := Fin g.vertices) (E := Fin g.edges.length)
          (Nat.clog 2 g.vertices) Δ γ) := by
  obtain ⟨hm, -⟩ := CheckBit.pos_of_hyp Δ g hg hn hinc hdeg
  obtain ⟨t1, ht1, vc, FL, FQ, FT, FM, hrun, hLF, hQF, -, -⟩ :=
    FullFront.full_run_sched Δ γ hγ hΔ g hg hn hm k word
  have h1 := BitMachineStackRun.run ιL (fun _ => []) (full γ.num.toNat γ.den Δ)
    ⟨some (fullStart γ.num.toNat γ.den Δ), fullCtl, F0 (X0 g k word)⟩ t1
  rw [hrun] at h1
  have hA : bank ιL (fun _ => []) (exitBankG g hg k word FL FQ FT FM g.vertices
      (LookupSeed.width (Nat.clog 2 g.vertices)) (width (Nat.clog 2 g.vertices))
      (width (Nat.clog 2 g.vertices) - 2) (outerWidth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ)
      (sourceRows (Nat.clog 2 g.vertices)
        (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
        (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k)
      (sourceCols (Nat.clog 2 g.vertices)
        (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
        (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k))
      cA = List.replicate g.vertices true := by
    rw [bank_inl]; exact hLF.1
  obtain ⟨c, -, hq1, -⟩ := hQF
  have hB : bank ιL (fun _ => []) (exitBankG g hg k word FL FQ FT FM g.vertices
      (LookupSeed.width (Nat.clog 2 g.vertices)) (width (Nat.clog 2 g.vertices))
      (width (Nat.clog 2 g.vertices) - 2) (outerWidth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.restorationWidth (Nat.clog 2 g.vertices))
      (ParameterizedCanonicalSource.coverWidth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ)
      (sourceRows (Nat.clog 2 g.vertices)
        (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
        (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k)
      (sourceCols (Nat.clog 2 g.vertices)
        (ParameterizedCanonicalSource.restorationDepth (Nat.clog 2 g.vertices))
        (ParameterizedCanonicalSource.coverDepth g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ) k))
      cB = List.replicate g.edges.length true := by
    rw [bank_inl]; exact hq1
  obtain ⟨w, bit, h2, hbit⟩ := CheckBit.check_run cA cB cO cA_cB cA_cO cB_cO Δ γ hγ hΔ g hg hn hinc hdeg _ hA hB
  obtain ⟨T, hT, hr⟩ := BitMachineRawSequence.runs (Lift.liftP ιL (full γ.num.toNat γ.den Δ))
    (CheckBit.checkProg cA cB cO Δ γ) (fullStart γ.num.toNat γ.den Δ) CheckBit.DL.rdA fullCtl vc
    (CheckBit.ctl0 (CheckBit.NA Δ γ) (CheckBit.NB Δ γ)) w _ _ _ t1 (g.vertices + g.edges.length + 2) h1 h2
  exact ⟨T, by omega, _, bit, _, hr, fun x => rfl, fun i => rfl, hbit⟩

/-- **Segment (2)**: the re-banked front on the widened H_A3 bank ends in exactly the Mid1 bank. -/
theorem front_run (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ)
    (k : ℕ) (word : List Bool) :
    ∃ T ≤ FullFront.fullBd γ.num.toNat γ.den Δ g k word + (g.vertices + g.edges.length + 2) + 1,
      ∃ u, ∃ bit : Bool, ∃ Z : FS → List Bool,
        ((advance (front Δ γ))^[T])
            (⟨some (sF Δ γ), vF Δ γ, Wrap.widen (Lift.a FS) (X0 g k word)⟩ :
              TM2.Cfg (fun _ : Fin (Lift.a FS + 3) => Bool) _ _) =
          ⟨none, u, Lift.layoutBank FS (X0 g k word)
            (Lift.region FS (stSched Δ γ g k word) ![[bit], [], []] Z)⟩ ∧
        (bit = true ↔ CompletePublicScheduleScratch.Checks (V := Fin g.vertices) (E := Fin g.edges.length)
          (Nat.clog 2 g.vertices) Δ γ) := by
  obtain ⟨T, hT, u, bit, E, hr, hst, hpk, hbit⟩ := front13_run Δ γ hγ hΔ g hg hn hinc hdeg k word
  have h := BitMachineStackRun.run ιK (fun _ => []) (front13 Δ γ)
    ⟨some (sF Δ γ), vF Δ γ, bank ιL (fun _ => []) (F0 (X0 g k word))⟩ T
  rw [hr] at h
  simp only [stackCfg] at h
  rw [bank_start, bank_exit] at h
  have e1 : (fun i => E (pk i)) = X0 g k word := funext hpk
  have e2 : (fun x => E (so x)) = stSched Δ γ g k word := funext hst
  rw [e1, e2] at h
  exact ⟨T, hT, u, bit, _, h, hbit⟩

end

end Paper2.FrontLift

#print axioms Paper2.FrontLift.front13_run
#print axioms Paper2.FrontLift.front_run
