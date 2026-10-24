import CurrentAdditive.QuarticLayout
import CurrentAdditive.QuarticNoneRun
import Paper2.A3L3None

/-! Retarget the checked physical none printer's input to the literal v27 layout. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.CurrentAdditive.QuarticNoneLift

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2 Paper2.A3Assembly.Lift Paper2.A3Assembly.Lift3
open Paper2.A3Assembly
open Paper2.SourceProfileParameters Paper2.SourceRecursiveNoSampling
open Paper2.CurrentAdditive.QuarticConstructor
open Paper2.CurrentAdditive.QuarticLayout
open Paper2.CurrentAdditive.QuarticDispatchSpec
open Paper2.CurrentAdditive.QuarticDispatchAssembly
open CurrentAdditive.RandomizedSchedule

variable (FS : Type) [Fintype FS] [DecidableEq FS]

/-- The exact entry bank for `NoneOut.progN` with quartic numeric counts and
the selected v27 tape word. -/
def entryCanon27 (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0 < g.vertices) (k : ℕ)
    (t : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :
    NoneOut.JN → List Bool :=
  NoneOut.entryN g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
    (width (Nat.clog 2 g.vertices)) (width (Nat.clog 2 g.vertices) - 2)
    (outerWidth (Nat.clog 2 g.vertices))
    (width27 (Nat.clog 2 g.vertices))
    (Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) γ Δ) k
    (sourceRows (Nat.clog 2 g.vertices)
      (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))
      (q27 (V := Fin g.vertices) (E := Fin g.edges.length)
        (Nat.clog 2 g.vertices) γ Δ) k)
    (sourceCols (Nat.clog 2 g.vertices)
      (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))
      (q27 (V := Fin g.vertices) (E := Fin g.edges.length)
        (Nat.clog 2 g.vertices) γ Δ) k)
    ((select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t)

/-- Every embedded none-machine cell of a v27 post-probe bank has exactly its
canonical physical entry value. The branch needs no copying or value rewrite. -/
theorem entryCanon_layout27 (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph)
    (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ)
    (t : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape)
    (P : Fin 3 → List Bool) (c : Fin 3 → List Bool) (hc : c 2 = [])
    (Z : FS → List Bool) (x : NoneOut.JN) :
    entryCanon27 Δ γ g hg hn k t x =
      layoutBank FS P (region FS (startCanon27 Δ γ g hg hn k t) c Z)
        (ιN FS x) := by
  change _ = layoutBank FS P (region FS (startCanon27 Δ γ g hg hn k t) c Z)
    (pos FS (nMap FS x))
  rcases x with x | x | x | x
  · rw [show nMap FS (.inl x) = .inl (.inr (.inl x)) from rfl, layoutBank_inl]
    rfl
  · rw [show nMap FS (.inr (.inl x)) = .inl (nReg FS (.inl x)) from rfl, layoutBank_inl]
    rfl
  · rw [show nMap FS (.inr (.inr (.inl x))) = .inl (nReg FS (.inr (.inl x))) from rfl,
      layoutBank_inl]
    rfl
  · by_cases h5 : x = 5
    · subst h5
      rw [show nMap FS (.inr (.inr (.inr 5))) = .inl (.inl 2) from rfl, layoutBank_inl]
      change [] = c 2
      rw [hc]
    · rw [show nMap FS (.inr (.inr (.inr x))) = .inl (nReg FS (.inr (.inr x)))
          from if_neg h5, layoutBank_inl]
      rfl

/-- The fixed none-branch printer, lifted without changing any input value to the
common v27 layout. `Checks27` remains an explicit precondition. -/
theorem hNone_spec27 (Δ : ℕ) (γ : ℚ) (CM EM : ℕ) :
    BranchSpec Δ γ (a FS) (nProg FS)
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
          (.inl ⟨0, by omega⟩))))) NoneOut.ctlN (outJ FS)
      (fun g hg hn k t S =>
        (Mid2_27 FS Δ γ CM EM g hg hn k t S ∧
          ChecksCond27 Δ γ g hg hn k t) ∧
        ¬ Good27 Δ γ g hg hn k t)
      (NC FS CM) (max EM Paper2.A3Assembly.Clocks.EN) := by
  intro g hg hn k hH t S hpre
  obtain ⟨⟨⟨⟨b₁, b₂, Z, hS⟩, hsz⟩, hc⟩, hnG⟩ := hpre
  haveI : NeZero g.vertices := ⟨Nat.pos_iff_ne_zero.mp hn⟩
  haveI : NeZero (width (Nat.clog 2 g.vertices)) := ⟨by unfold width; positivity⟩
  haveI : NeZero (width (Nat.clog 2 g.vertices) - 2) :=
    ⟨by have h := SourceProfileParameters.width_admissible (Nat.clog 2 g.vertices); omega⟩
  haveI : NeZero (outerWidth (Nat.clog 2 g.vertices)) :=
    ⟨by unfold outerWidth; positivity⟩
  haveI : NeZero (width27 (Nat.clog 2 g.vertices)) :=
    ⟨by unfold width27; positivity⟩
  haveI : NeZero (Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) γ Δ) := ⟨by
    rw [CurrentAdditive.RandomizedSchedule.Q27_dyadic]
    positivity⟩
  have hres : QuarticProbeOutcome.genOut27 Δ γ g hg hn k hc t = none := by
    by_contra hne
    exact hnG ⟨hc, Option.ne_none_iff_isSome.mp hne⟩
  have key := QuarticConstructor.none_run_canonical27 g hg hn Δ γ k hc t
  have key2 := key hres
  obtain ⟨T, hT, ctl, d, G, F, H, -, hr, -, -, hH⟩ := key2
  have hbank : bank (ιN FS) S (entryCanon27 Δ γ g hg hn k t) = S := by
    apply bank_eq_self
    intro x
    rw [hS]
    exact entryCanon_layout27 FS Δ γ g hg hn k t _ _ rfl Z x
  have hr' : ((advance NoneOut.progN)^[T])
      ⟨some _, NoneOut.ctlN, entryCanon27 Δ γ g hg hn k t⟩ = _ := hr
  have hL := congrArg (stackCfg (ιN FS) S) hr'
  rw [← BitMachineStackRun.run] at hL
  simp only [stackCfg] at hL
  rw [hbank] at hL
  have hN : 1 ≤ g.vertices + 2 := by omega
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q =
      (g.vertices + 2) ^ (max EM Paper2.A3Assembly.Clocks.EN * (k + 1)) := ⟨_, rfl⟩
  have hMQ : (g.vertices + 2) ^ (EM * (k + 1)) ≤ Q := by
    rw [hQdef]
    exact Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _ (le_max_left _ _))
  have hNQ : (g.vertices + 2) ^ (Paper2.A3Assembly.Clocks.EN * (k + 1)) ≤ Q := by
    rw [hQdef]
    exact Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _ (le_max_right _ _))
  have hCN := QuarticClockN.clockN_HA3_27 (n := g.vertices) (m := g.edges.length)
    Δ γ hc k
  have hTk : T ≤ NCk * Q := (hT.trans hCN).trans (Nat.mul_le_mul_left _ hNQ)
  have hsize := size_run (nProg FS) ⟨some (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩))))), NoneOut.ctlN, S⟩ T
  have hr2 : ((advance (nProg FS))^[T]) ⟨some (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩))))), NoneOut.ctlN, S⟩ =
      ⟨none, ctl, _⟩ := hL
  rw [hr2] at hsize
  rw [← hQdef]
  refine ⟨T, _, _, ?_, hr2, ?_, ?_⟩
  · have : NCk ≤ NC FS CM := by unfold NC; omega
    exact hTk.trans (Nat.mul_le_mul_right _ this)
  · rw [← ιN_out, bank_at]
    exact hH
  · have h1 : (BitMachineBankCodec.encode S).length ≤ CM * Q :=
      hsz.trans (Nat.mul_le_mul_left _ hMQ)
    have h2 : 2 * (a FS + 3) * (PSN FS * T) ≤
        2 * (a FS + 3) * PSN FS * NCk * Q := by
      have := Nat.mul_le_mul_left (2 * (a FS + 3))
        (Nat.mul_le_mul_left (PSN FS) hTk)
      calc
        2 * (a FS + 3) * (PSN FS * T) ≤
            2 * (a FS + 3) * (PSN FS * (NCk * Q)) := this
        _ = 2 * (a FS + 3) * PSN FS * NCk * Q := by ring
    have e : NC FS CM * Q = NCk * Q + CM * Q +
        2 * (a FS + 3) * PSN FS * NCk * Q := by
      unfold NC
      ring
    refine le_trans (b := (BitMachineBankCodec.encode S).length +
      2 * (a FS + 3) * (PSN FS * T)) hsize ?_
    rw [e]
    generalize 2 * (a FS + 3) * PSN FS * NCk * Q = X at h2
    generalize 2 * (a FS + 3) * (PSN FS * T) = Y at h2
    generalize NCk * Q = Z'
    omega

#print axioms entryCanon_layout27
#print axioms hNone_spec27

end

end Paper2.CurrentAdditive.QuarticNoneLift
