import Paper2.BrStage
import Paper2.FallbackNoPreloadRun
import Paper2.FrontClockF

/-! Lane a-bridge-owner-1, segment 4: residue-length majorants of the prepared
cut. `fullBd` depends on the raw word only through `22·|word|`, so the admitted
H_A3 front clock (`FrontClock13.frontClock`, evaluated at the typed tape whose bits
are the retained prefix) bounds it; `prepBd` is bounded through the admitted
scheduled atom bounds (`FallbackNoPreloadRun.scheduled_atoms`, `FairBitCap`). -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.ABridge

noncomputable section

open EthInapproximability.CurrentPaper
open Paper2.SourceRecursiveNoSampling Paper2.ParameterizedCanonicalSource

theorem fullBd_word (a b Δ : ℕ) (g : EncodedGraph.Graph) (k : ℕ) (word : List Bool) :
    FullFront.fullBd a b Δ g k word = FullFront.fullBd a b Δ g k [] + 22 * word.length := by
  unfold FullFront.fullBd FullFront.LC
  simp only [List.length_nil]
  ring

/-- `fullBd` on ANY raw word, from the admitted front clock at one typed tape. -/
theorem fullBd_raw_le (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0 < g.vertices) (k : ℕ) (hH : A3Assembly.Run.Hyp Δ g hg k)
    (t : (TotalFiniteConstructorScratch.select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape)
    (word : List Bool) :
    FullFront.fullBd γ.num.toNat γ.den Δ g k word ≤
      2 * (g.vertices + 2) ^ (FrontClock13.cF Δ γ * 266 * 45 * (k + 1)) + 22 * word.length := by
  have h := FrontClock13.frontClock Δ γ g hg hn k hH t
  rw [fullBd_word] at h ⊢
  omega

/-- The per-step constant of the admitted cutter. -/
def cutPS : ℕ := BitMachineStackGrowth.perStep SamplerParameterJoin.cutProgram

def prepConst : ℕ := 8 * FallbackNoPreloadClock.cf + 27100 + 40 + 16 * cutPS

/-- `prepBd` at the exact checked schedule, on any raw word. -/
theorem prepBd_sched_le {n m : ℕ} [NeZero n] (L Δ : ℕ) (γ : ℚ)
    (hc : CompletePublicScheduleScratch.Checks (V := Fin n) (E := Fin m) L Δ γ)
    (k : ℕ) (word : List Bool) :
    FrontPreparedCut.prepBd n (LookupSeed.width L) (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2) (SourceProfileParameters.outerWidth L)
      (restorationWidth L) (coverWidth n m L Δ γ) k
      (sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k)
      (sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k) word ≤
      prepConst * (2 ^ (60 * ((k + 1) * L))) ^ 3 +
        (word.length + 2 * (word.length * cutPS)) := by
  have hclk := FallbackNoPreloadRun.scheduled_atoms (n := n) (m := m) L Δ γ hc k
  dsimp only at hclk
  set Z := 2 ^ (60 * ((k + 1) * L)) with hZ
  set p := LookupSeed.width L
  set s := SourceProfileParameters.width L
  set q₁ := SourceProfileParameters.width L - 2
  set q₂ := SourceProfileParameters.outerWidth L
  set w := restorationWidth L
  set Q := coverWidth n m L Δ γ
  set mX := sourceRows L (restorationDepth L) (coverDepth n m L Δ γ) k
  set mY := sourceCols L (restorationDepth L) (coverDepth n m L Δ γ) k
  let T := (k + 1) * L
  have hL : 16 ≤ L := by
    rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hL, _⟩
    exact hL
  have hT : 1 ≤ T := by
    have hp : 0 < (k + 1) * L := Nat.mul_pos (by omega) (by omega)
    dsimp [T]; omega
  have hZ1 : 1 ≤ Z := Nat.one_le_two_pow
  have mono : ∀ e, e ≤ 60 * T → 2 ^ e ≤ Z := fun e he =>
    pow_le_pow_right₀ (by decide : 1 ≤ (2:Nat)) he
  have hB : SamplerParameterJoin.B n p s q₁ q₂ w Q ≤ Z := by
    have h : SamplerParameterJoin.B n p s q₁ q₂ w Q ≤ 8 * L :=
      FairBitCap.scheduled_alphabet_bitWidth_le L Δ γ hc
    have h2 : 8 * L < 2 ^ (8 * L) := Nat.lt_two_pow_self
    have h3 : 2 ^ (8 * L) ≤ Z := mono _ (by dsimp [T]; nlinarith)
    omega
  have hN60 : SamplerNRProducer.N s q₁ q₂ w Q p k mX mY ≤ 2 ^ (60 * T) := by
    have h := FairBitCap.scheduled_drawCap_le L Δ γ hc k
    exact h.trans (le_of_eq (by dsimp [T]; ring_nf))
  have hN : SamplerNRProducer.N s q₁ q₂ w Q p k mX mY ≤ Z := hN60
  have hR : SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY ≤ Z := by
    have h := FairBitCap.rejectionAttemptCap_le_of_pow _ _ hN60
    have hlin := CodeSamplerScheduledBounds.linear_le_pow T hT
    have h8 : 2 ^ (8 * T) ≤ Z := mono _ (by omega)
    change Paper2.rejectionAttemptCap (SamplerNRProducer.N s q₁ q₂ w Q p k mX mY) ≤ Z
    omega
  unfold FrontPreparedCut.prepBd
  dsimp only
  unfold MatrixAddressMachine.exactTime prepConst cutPS
  generalize BitMachineStackGrowth.perStep SamplerParameterJoin.cutProgram = ps at *
  generalize SamplerParameterJoin.clock n p s q₁ q₂ w Q k mX mY = C at hclk ⊢
  generalize SamplerParameterJoin.B n p s q₁ q₂ w Q = Bv at hB ⊢
  generalize SamplerParameterJoin.R p s q₁ q₂ w Q k mX mY = Rv at hR ⊢
  generalize SamplerNRProducer.N s q₁ q₂ w Q p k mX mY = Nv at hN hN60 ⊢
  generalize word.length = W
  have hRB : Rv * Bv ≤ Z * Z := Nat.mul_le_mul hR hB
  have hD : Nv * (Rv * Bv) ≤ Z * (Z * Z) := Nat.mul_le_mul hN hRB
  have hZ3 : Z ^ 3 = Z * (Z * Z) := by ring
  have hZZ : Z ≤ Z * Z := Nat.le_mul_of_pos_left Z (by omega)
  have hZZZ : Z * Z ≤ Z * (Z * Z) := Nat.le_mul_of_pos_left _ (by omega)
  have hDps : Nv * (Rv * Bv) * ps ≤ Z * (Z * Z) * ps := Nat.mul_le_mul_right ps hD
  have hN0 : 2 * Rv * Bv + 4 * Rv + 2 * 0 + 4 = 2 * (Rv * Bv) + 4 * Rv + 4 := by ring
  have hN1 : 2 * Nv * (Rv * Bv) + 4 * Nv + 2 * 0 + 4 = 2 * (Nv * (Rv * Bv)) + 4 * Nv + 4 := by ring
  have hE : (Nv * (Rv * Bv) + W + 4) * ps = Nv * (Rv * Bv) * ps + W * ps + 4 * ps := by ring
  rw [hN0, hN1, hE]
  rw [hZ3] at hclk ⊢
  have hexp : (8 * FallbackNoPreloadClock.cf + 27100 + 40 + 16 * ps) * (Z * (Z * Z)) =
      (8 * FallbackNoPreloadClock.cf + 27100) * (Z * (Z * Z)) + 40 * (Z * (Z * Z)) +
        16 * (ps * (Z * (Z * Z))) := by ring
  rw [hexp]
  have h1 : 1 ≤ Z * (Z * Z) := hZ1.trans (hZZ.trans hZZZ)
  have hps3 : ps * 1 ≤ ps * (Z * (Z * Z)) := Nat.mul_le_mul_left ps h1
  have hDps' : Nv * (Rv * Bv) * ps ≤ ps * (Z * (Z * Z)) := by
    have := Nat.mul_le_mul_right ps hD
    rw [Nat.mul_comm (Z * (Z * Z)) ps] at this
    exact this
  have hRB3 : Rv * Bv ≤ Z * (Z * Z) := hRB.trans hZZZ
  have hR3 : Rv ≤ Z * (Z * Z) := hR.trans (hZZ.trans hZZZ)
  have hN3 : Nv ≤ Z * (Z * Z) := hN.trans (hZZ.trans hZZZ)
  omega

#print axioms fullBd_raw_le
#print axioms prepBd_sched_le

end

end Paper2.ABridge
