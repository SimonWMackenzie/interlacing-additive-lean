import CurrentAdditive.QuarticFrontComposition
import CurrentAdditive.QuarticDispatchSize

/-! A physical numeric front needs to prove its exact bank and time. A generic
finite-program growth theorem then supplies the encoded exit-bank bound. -/

set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticPrepSize

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2 Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticDispatchSpec
open Paper2.CurrentAdditive.QuarticFrontComposition

variable (FS : Type) [Fintype FS] [DecidableEq FS]

def NumericRun27 (A B : FS) (Δ : ℕ) (γ : ℚ)
    {L V : Type}
    (P : L → TM2.Stmt (fun _ : Fin (Lift.a FS + 3) => Bool) L V)
    (s : L) (v : V) (C E : ℕ) : Prop :=
  ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ),
    Hyp Δ g hg k →
    ∀ t : (QuarticConstructor.select27 hn
      (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape,
      ∃ (T : ℕ) (u : V) (Z : FS → List Bool),
        T ≤ C * (g.vertices + 2) ^ (E * (k + 1)) ∧
        ((advance P)^[T])
          ⟨some s, v, Wrap.widen (Lift.a FS) (inputBank27 Δ γ g hg hn k t)⟩ =
            ⟨none, u, Lift.layoutBank FS (inputBank27 Δ γ g hg hn k t)
              (Lift.region FS (QuarticLayout.startCanon27 Δ γ g hg hn k t)
                ![[], [], []] Z)⟩ ∧
        Z A = List.replicate g.vertices true ∧
        Z B = List.replicate g.edges.length true

noncomputable def sizeCoefficient {L V : Type} [Fintype L]
    (P : L → TM2.Stmt (fun _ : Fin (Lift.a FS + 3) => Bool) L V)
    (Δ C : ℕ) : ℕ :=
  C + Lift.a FS + (4 * Δ + 9) +
    2 * (Lift.a FS + 3) * BitMachineStackGrowth.perStep P * C

def sizeExponent (E : ℕ) : ℕ := max E 160

theorem numeric_prep_of_run27 (A B : FS) (Δ : ℕ) (γ : ℚ)
    {L V : Type} [Fintype L]
    (P : L → TM2.Stmt (fun _ : Fin (Lift.a FS + 3) => Bool) L V)
    (s : L) (v : V) (C E : ℕ)
    (hRun : NumericRun27 FS A B Δ γ P s v C E) :
    NumericPrep27 FS A B Δ γ P s v
      (sizeCoefficient FS P Δ C) (sizeExponent E) := by
  intro g hg hn k hH t
  obtain ⟨T, u, Z, hT, hr, hA, hB⟩ := hRun g hg hn k hH t
  let N := g.vertices + 2
  let Q := N ^ (sizeExponent E * (k + 1))
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hQ : 1 ≤ Q := by dsimp [Q]; exact Nat.one_le_pow _ _ hN
  have hE : N ^ (E * (k + 1)) ≤ Q := by
    dsimp [Q, sizeExponent]
    exact Nat.pow_le_pow_right hN
      (Nat.mul_le_mul_right _ (le_max_left E 160))
  have h160 : N ^ (160 * (k + 1)) ≤ Q := by
    dsimp [Q, sizeExponent]
    exact Nat.pow_le_pow_right hN
      (Nat.mul_le_mul_right _ (le_max_right E 160))
  have hT' : T ≤ C * Q := hT.trans (Nat.mul_le_mul_left C hE)
  let X := inputBank27 Δ γ g hg hn k t
  let S := Lift.layoutBank FS X
    (Lift.region FS (QuarticLayout.startCanon27 Δ γ g hg hn k t)
      ![[], [], []] Z)
  have hInput : (BitMachineBankCodec.encode X).length ≤
      (4 * Δ + 9) * N ^ (160 * (k + 1)) :=
    (QuarticDispatchSize.inputSize27 Δ γ) g hg hn k hH t
  have hInitial : (BitMachineBankCodec.encode
      (Wrap.widen (Lift.a FS) X)).length ≤
        (Lift.a FS + (4 * Δ + 9)) * Q := by
    rw [Wrap.encode_widen, List.length_append, List.length_replicate]
    have hInput' := hInput.trans (Nat.mul_le_mul_left _ h160)
    have hFS : Lift.a FS ≤ Lift.a FS * Q := Nat.le_mul_of_pos_right _ hQ
    nlinarith
  have hGrowth := Lift.size_run P
    (⟨some s, v, Wrap.widen (Lift.a FS) X⟩ :
      TM2.Cfg (fun _ : Fin (Lift.a FS + 3) => Bool) L V) T
  change ((advance P)^[T])
    (⟨some s, v, Wrap.widen (Lift.a FS) X⟩ :
      TM2.Cfg (fun _ : Fin (Lift.a FS + 3) => Bool) L V) =
      ⟨none, u, S⟩ at hr
  rw [hr] at hGrowth
  have hSize : (BitMachineBankCodec.encode S).length ≤
      sizeCoefficient FS P Δ C * Q := by
    have hRunGrowth :
        2 * (Lift.a FS + 3) * (BitMachineStackGrowth.perStep P * T) ≤
        (2 * (Lift.a FS + 3) * BitMachineStackGrowth.perStep P * C) * Q := by
      have h := Nat.mul_le_mul_left
        (2 * (Lift.a FS + 3) * BitMachineStackGrowth.perStep P) hT'
      nlinarith
    have hAll := Nat.add_le_add hInitial hRunGrowth
    unfold sizeCoefficient
    nlinarith
  refine ⟨T, u, Z, ?_, ?_, hA, hB, ?_⟩
  · exact hT'.trans (Nat.mul_le_mul_right Q (by unfold sizeCoefficient; omega))
  · exact hr
  · exact hSize

#print axioms numeric_prep_of_run27

end Paper2.CurrentAdditive.QuarticPrepSize
