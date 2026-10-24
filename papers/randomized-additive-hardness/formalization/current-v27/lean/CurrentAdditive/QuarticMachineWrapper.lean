import CurrentAdditive.QuarticFrontOnlyMachine
import CurrentAdditive.QuarticDispatchSize
import Paper2.A3Wrap

/-! The physical bit-machine wrapper for the literal v27 selector and output word.
This reuses the general three-stage codec machines, but its statement is about
`select27` and `outputBits27` throughout. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.CurrentAdditive.QuarticMachineWrapper

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2 Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticDispatchSpec

/-- A fixed physical machine prints the literal v27 selected word within an
absolute polynomial bound on every selected tape. -/
def H_A3_27 (Δ : ℕ) (γ : ℚ) : Prop :=
  ∃ (MA : BitMachine.Machine) (CA EA : ℕ),
    ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ),
      Hyp Δ g hg k →
      ∀ t : (QuarticConstructor.select27 hn
          (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape,
        MA.OutputsWithin
          (BitMachineBankCodec.encode (inputBank27 Δ γ g hg hn k t))
          (QuarticConstructor.outputBits27 hn
            (CanonicalEdgeTape.graphEdge g hg) Δ γ k t)
          (CA * (g.vertices + 2) ^ (EA * (k + 1)))

variable {L V : Type} [Fintype L] [Fintype V]

private theorem clock_arith27 (K a C N x w : ℕ) (hN : 1 ≤ N)
    (hx : x ≤ C * N) (hw : w ≤ C * N) :
    a + 1 + 2 * (a + x) + 2 +
        ((2 * K + 1) * (a + x + 1) + C * N + 2 * (C * N) + 4 + 2 * w + 2 +
          (2 * K + 4) * (w + 1)) ≤
      (3 * a + 9 + 2 * C + (2 * K + 1) * (a + 1 + C) + 5 * C +
        (2 * K + 4) * (C + 1)) * N := by
  have h1 : (2 * K + 1) * (a + x + 1) ≤
      (2 * K + 1) * ((a + 1) * N + C * N) := by
    apply Nat.mul_le_mul_left
    have : a + 1 ≤ (a + 1) * N := Nat.le_mul_of_pos_right _ hN
    omega
  have h2 : (2 * K + 4) * (w + 1) ≤ (2 * K + 4) * (C * N + N) :=
    Nat.mul_le_mul_left _ (by omega)
  have h3 : 3 * a + 9 ≤ (3 * a + 9) * N := Nat.le_mul_of_pos_right _ hN
  have hexp : (3 * a + 9 + 2 * C + (2 * K + 1) * (a + 1 + C) + 5 * C +
      (2 * K + 4) * (C + 1)) * N =
      (3 * a + 9) * N + 2 * (C * N) +
        (2 * K + 1) * ((a + 1) * N + C * N) + 5 * (C * N) +
        (2 * K + 4) * (C * N + N) := by ring
  rw [hexp]
  omega

set_option maxHeartbeats 1000000 in
/-- The generic codec wrapper applied to a literal v27 local run. -/
theorem H_A3_27_of_local (Δ : ℕ) (γ : ℚ) (a : ℕ)
    (P : L → TM2.Stmt (fun _ : Fin (a + 3) => Bool) L V) (start : L) (initial : V)
    (j : Fin (a + 3)) (C E : ℕ)
    (hrun : LocalRun27 Δ γ a P start initial j C E)
    (hin : InputSize27 Δ γ C E) :
    H_A3_27 Δ γ := by
  refine ⟨BitMachineComposition.composition (Unit4Post.Pre.machine a)
      (BitMachineComposition.composition (BitMachineBankWrapper.machine P start initial)
        (BankFieldProjection.machine j)),
    3 * a + 9 + 2 * C + (2 * (a + 3) + 1) * (a + 1 + C) + 5 * C +
      (2 * (a + 3) + 4) * (C + 1), E, ?_⟩
  intro g hg hn k hH t
  obtain ⟨X, hX⟩ : ∃ X, X = inputBank27 Δ γ g hg hn k t := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N, N = (g.vertices + 2) ^ (E * (k + 1)) := ⟨_, rfl⟩
  rw [← hX, ← hNdef]
  have hN : 1 ≤ N := by rw [hNdef]; exact Nat.one_le_pow _ _ (by omega)
  obtain ⟨T, c, hT, hr, hl, hj, hsz⟩ := hrun g hg hn k hH t
  have hx := hin g hg hn k hH t
  rw [← hX, ← hNdef] at hx
  rw [← hX] at hr
  rw [← hNdef] at hT hsz
  obtain ⟨T', hT', _, _, hF⟩ := Wrap.finalBank_spec P start initial (Wrap.widen a X) T c hr hl
  have hpre := Unit4Post.Pre.outputs a (BitMachineBankCodec.encode X)
  rw [← Wrap.encode_widen] at hpre
  have hwrap := BitMachineBankWrapper.outputs P start initial (Wrap.finalBank P start initial)
    (BitMachineBankCodec.encode (Wrap.widen a X)) (C * N) (C * N)
    (by
      intro S hd
      rw [BitMachineBankCodec.decode_encode] at hd
      cases Option.some.inj hd
      obtain ⟨T'', hT'', hl'', hs'', _⟩ :=
        Wrap.finalBank_spec P start initial (Wrap.widen a X) T c hr hl
      exact ⟨T'', _, hT''.trans hT, rfl, hl'', hs''⟩)
    (by
      intro S hd
      rw [BitMachineBankCodec.decode_encode] at hd
      cases Option.some.inj hd
      rw [hF]; exact hsz)
  have hres : BitMachineBankWrapper.result (Wrap.finalBank P start initial)
      (BitMachineBankCodec.encode (Wrap.widen a X)) =
      BitMachineBankCodec.encode (Wrap.finalBank P start initial (Wrap.widen a X)) := by
    simp only [BitMachineBankWrapper.result, BitMachineBankCodec.decode_encode]
  rw [hres, hF] at hwrap
  have hproj := BankFieldProjection.outputs j (BitMachineBankCodec.encode c.stk)
  rw [BankFieldProjection.result_encode, hj] at hproj
  have h23 := BitMachineComposition.composition_outputsWithin _ _ hwrap hproj
  have h123 := BitMachineComposition.composition_outputsWithin _ _ hpre h23
  apply BitMachine.outputsWithin_mono _ h123
  have hlen1 : (BitMachineBankCodec.encode (Wrap.widen a X)).length =
      a + (BitMachineBankCodec.encode X).length := by
    rw [Wrap.encode_widen, List.length_append, List.length_replicate]
  rw [hlen1]
  have hclock := clock_arith27 (a + 3) a C N
    (BitMachineBankCodec.encode X).length
    (BitMachineBankCodec.encode c.stk).length hN hx hsz
  exact hclock

theorem inputSize27_mono (Δ : ℕ) (γ : ℚ) (C₀ E₀ C E : ℕ)
    (hin : InputSize27 Δ γ C₀ E₀) (hC : C₀ ≤ C) (hE : E₀ ≤ E) :
    InputSize27 Δ γ C E := by
  intro g hg hn k hH t
  have hbase : 1 ≤ g.vertices + 2 := by omega
  have hpow : (g.vertices + 2) ^ (E₀ * (k + 1)) ≤
      (g.vertices + 2) ^ (E * (k + 1)) :=
    Nat.pow_le_pow_right hbase (Nat.mul_le_mul_right _ hE)
  calc
    (BitMachineBankCodec.encode (inputBank27 Δ γ g hg hn k t)).length ≤
        C₀ * (g.vertices + 2) ^ (E₀ * (k + 1)) := hin g hg hn k hH t
    _ ≤ C₀ * (g.vertices + 2) ^ (E * (k + 1)) := Nat.mul_le_mul_left _ hpow
    _ ≤ C * (g.vertices + 2) ^ (E * (k + 1)) := Nat.mul_le_mul_right _ hC

/-- Once the remaining numeric front is physically realized, the same fixed
program yields the current v27 bit-machine endpoint. -/
theorem H_A3_27_of_front (FS : Type) [Fintype FS] [DecidableEq FS]
    (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ)
    {LF VF : Type} [Fintype LF] [Fintype VF]
    (front : LF → TM2.Stmt (fun _ : Fin (Lift.a FS + 3) => Bool) LF VF)
    (sF : LF) (vF : VF) (CM EM CF EF : ℕ)
    (hFront : QuarticFrontOnlyMachine.FrontSpec27 FS Δ γ front sF vF CM EM CF EF) :
    H_A3_27 Δ γ := by
  let C := CF +
    (Lift.PC FS CM + Lift.SC FS (Lift.PC FS CM) + Lift3.NC FS (Lift.PC FS CM) + 2) +
    QuarticUnschedLift.UC27 FS Δ γ CM + 2
  let E := max EF
    (max (max (Lift.PE EM)
      (max (Lift.SE (Lift.PE EM)) (max (Lift.PE EM) Clocks.EN)))
      (max EM 160))
  have hC : 4 * Δ + 9 ≤ C := by
    have hUC : 4 * Δ + 9 ≤ QuarticUnschedLift.UC27 FS Δ γ CM := by
      unfold QuarticUnschedLift.UC27 QuarticUnschedLift.UCk27
      omega
    dsimp only [C]
    omega
  have hE : 160 ≤ E := by
    dsimp [E]
    exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  have hrun := QuarticFrontOnlyMachine.localRun_of_front27 FS Δ γ hΔ hγ
    front sF vF CM EM CF EF hFront
  exact H_A3_27_of_local Δ γ (Lift.a FS) _ _ _ (Lift.outJ FS) C E
    hrun (inputSize27_mono Δ γ (4 * Δ + 9) 160 C E
      (QuarticDispatchSize.inputSize27 Δ γ) hC hE)

#print axioms H_A3_27_of_local
#print axioms H_A3_27_of_front

end Paper2.CurrentAdditive.QuarticMachineWrapper
