import Paper2.BrCutMachine
import Paper2.HA3Closed

/-! Lane a-bridge-owner-1, segment 3: the physical output identity.

ONE fixed machine `graphStageMachine` = `cutMachine ; MA` where `MA` is the machine of the
ADMITTED `A3Close.H_A3_closed`. On the literal graph-layout bank word
`encode ![encode g, 1^k, word]` with ANY raw word at least as long as the selected
input-bit count, it prints exactly `EncodedSelectedOutput.outputBits … t` for the typed
selected tape `t` whose bits are the physically retained prefix `word.take inputBits`.
The identification `frontD = inputBits` is the frozen, root-replayed
`FrontPreparedCut.frontD_eq_selected_inputBits` (scheduled branch). -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.ABridge

noncomputable section

open Turing
open EthInapproximability.CurrentPaper

/-- Every physically retained prefix of the right length is the bit word of a typed
selected tape (scheduled branch). -/
theorem exists_tape_of_prefix {n m : ℕ} (hn : 0 < n) (edge : Fin m → Bool → Fin n)
    (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ)
    (word : List Bool)
    (hlen : (TotalFiniteConstructorScratch.select hn edge Δ γ k).inputBits ≤ word.length) :
    ∃ t : (TotalFiniteConstructorScratch.select hn edge Δ γ k).Tape,
      (TotalFiniteConstructorScratch.select hn edge Δ γ k).tapeBits t =
        word.take (TotalFiniteConstructorScratch.select hn edge Δ γ k).inputBits := by
  rw [TotalFiniteConstructorScratch.select_good hn edge Δ γ k hc] at hlen ⊢
  refine ⟨⟨word.take _, ?_⟩, rfl⟩
  rw [List.length_take]
  exact Nat.min_eq_left hlen

/-- The graph stage machine for fixed `Δ, γ`. -/
def graphStageMachine (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) : BitMachine.Machine :=
  BitMachineComposition.composition (cutMachine γ.num.toNat γ.den Δ)
    (Classical.choose (A3Close.H_A3_closed Δ γ hΔ hγ))

def stageCA (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) : ℕ :=
  Classical.choose (Classical.choose_spec (A3Close.H_A3_closed Δ γ hΔ hγ))

def stageEA (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) : ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (A3Close.H_A3_closed Δ γ hΔ hγ)))

/-- The explicit graph-stage clock. -/
def stageClock (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ)
    (g : EncodedGraph.Graph) (k : ℕ) (word : List Bool) : ℕ :=
  cutClock γ.num.toNat γ.den Δ g k word +
    2 * (BitMachineBankCodec.encode
      ![EncodedGraph.encode g, List.replicate k true, word]).length + 2 +
    stageCA Δ γ hΔ hγ * (g.vertices + 2) ^ (stageEA Δ γ hΔ hγ * (k + 1))

/-- **Segment 3: physical output identity.** For every valid graph satisfying the H_A3
hypotheses and the scheduled public checks, every `k ≥ 1` and EVERY raw word at least
`inputBits` long, the fixed graph-stage machine prints on the literal bank word exactly the
canonical `outputBits` of the typed selected tape whose bits are the retained prefix. -/
theorem graph_stage_outputs (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (hm : 0 < g.edges.length) (k : ℕ) (hk : 1 ≤ k)
    (hsurj : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) Δ γ)
    (word : List Bool)
    (hlen : (TotalFiniteConstructorScratch.select hn
      (CanonicalEdgeTape.graphEdge g hg) Δ γ k).inputBits ≤ word.length) :
    ∃ t : (TotalFiniteConstructorScratch.select hn
        (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape,
      (TotalFiniteConstructorScratch.select hn
        (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t =
        word.take (TotalFiniteConstructorScratch.select hn
          (CanonicalEdgeTape.graphEdge g hg) Δ γ k).inputBits ∧
      (graphStageMachine Δ γ hΔ hγ).OutputsWithin
        (BitMachineBankCodec.encode ![EncodedGraph.encode g, List.replicate k true, word])
        (EncodedSelectedOutput.outputBits hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k t)
        (stageClock Δ γ hΔ hγ g k word) := by
  obtain ⟨t, ht⟩ := exists_tape_of_prefix hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k hc word hlen
  refine ⟨t, ht, ?_⟩
  have hA := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (A3Close.H_A3_closed Δ γ hΔ hγ))) g hg hn k hk hsurj hdeg t
  have hcut := cut_machine_outputs γ.num.toNat γ.den Δ g hg k word
  have hD := FrontPreparedCut.frontD_eq_selected_inputBits Δ γ hγ hΔ g hg hn hm k hc
  rw [hD, ← ht] at hcut
  have hC := BitMachineComposition.composition_outputsWithin _ _ hcut hA
  apply BitMachine.outputsWithin_mono _ hC
  have hmid := encode_take_le (EncodedGraph.encode g) (List.replicate k true) word
    (TotalFiniteConstructorScratch.select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).inputBits
  rw [← ht] at hmid
  unfold stageClock stageCA stageEA
  omega

#print axioms exists_tape_of_prefix
#print axioms graph_stage_outputs

end

end Paper2.ABridge
