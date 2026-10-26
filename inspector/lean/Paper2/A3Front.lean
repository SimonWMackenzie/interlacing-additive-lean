import Paper2.FrontRun

/-! Unit 3 (lock v12 App. D; T44/U10), lane a-success-table-13, segment (4): the `DecideSpec` hFront of
`A3H3Run.H_A3_R12`, exactly in the form the layout lane fixes
(`Run.DecideSpec Δ γ (a FS) front sF vF (flag₁ FS) (Run.IsInput Δ γ (a FS)) (Mid1 FS Δ γ CM EM) (Run.ChecksCond Δ γ) CF EF`),
from ONE named clock premise `FrontClock Δ γ CF EF` (the explicit clock `fullBd + (n + m + 2) + 1` of `front_run`
at the H_A3 word within `CF·(n+2)^(EF(k+1))`). The Mid1 size conjunct is derived (admitted per-step growth via
`Lift.size_run`, `Wrap.encode_widen`, the checked `Size.inputSize`). -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

namespace Paper2.FrontLift

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.FullFront (JF X0)
open Paper2.A3Assembly

set_option synthInstance.maxSize 16384
set_option synthInstance.maxHeartbeats 400000

/-- NAMED PREMISE (the front clock): the explicit clock of `front_run` at the literal H_A3 word. -/
def FrontClock (Δ : ℕ) (γ : ℚ) (C E : ℕ) : Prop :=
  ∀ (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ), Run.Hyp Δ g hg k →
    ∀ t : (TotalFiniteConstructorScratch.select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape,
      FullFront.fullBd γ.num.toNat γ.den Δ g k
          ((TotalFiniteConstructorScratch.select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t) +
        (g.vertices + g.edges.length + 2) + 1 ≤ C * (g.vertices + 2) ^ (E * (k + 1))

/-- The Mid1 size constant. -/
def CM (Δ : ℕ) (γ : ℚ) (C : ℕ) : ℕ :=
  Lift.a FS + (4 * Δ + 9) + 2 * (Lift.a FS + 3) * (BitMachineStackGrowth.perStep (front Δ γ) * C)
/-- The Mid1 size exponent. -/
def EM (E : ℕ) : ℕ := max 160 E

theorem size_arith (N a I D p T C E k : ℕ) (hN : 1 ≤ N)
    (hI : I ≤ D * N ^ (160 * (k + 1))) (hT : T ≤ C * N ^ (E * (k + 1))) :
    a + I + 2 * (a + 3) * (p * T) ≤ (a + D + 2 * (a + 3) * (p * C)) * N ^ (max 160 E * (k + 1)) := by
  have hP : 1 ≤ N ^ (max 160 E * (k + 1)) := Nat.one_le_pow _ _ hN
  have h1 : N ^ (160 * (k + 1)) ≤ N ^ (max 160 E * (k + 1)) :=
    Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _ (le_max_left _ _))
  have h2 : N ^ (E * (k + 1)) ≤ N ^ (max 160 E * (k + 1)) :=
    Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _ (le_max_right _ _))
  have a1 : I ≤ D * N ^ (max 160 E * (k + 1)) := hI.trans (Nat.mul_le_mul_left _ h1)
  have a2 : T ≤ C * N ^ (max 160 E * (k + 1)) := hT.trans (Nat.mul_le_mul_left _ h2)
  have a3 : 2 * (a + 3) * (p * T) ≤ 2 * (a + 3) * (p * (C * N ^ (max 160 E * (k + 1)))) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ a2)
  have a4 : a * 1 ≤ a * N ^ (max 160 E * (k + 1)) := Nat.mul_le_mul_left _ hP
  have e : (a + D + 2 * (a + 3) * (p * C)) * N ^ (max 160 E * (k + 1)) =
      a * N ^ (max 160 E * (k + 1)) + D * N ^ (max 160 E * (k + 1)) +
        2 * (a + 3) * (p * (C * N ^ (max 160 E * (k + 1)))) := by ring
  rw [e]
  omega

/-- **Segment (4)**: the hFront `DecideSpec` of `A3H3Run.H_A3_R12` from the front clock premise. -/
theorem hFront (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ) (C E : ℕ) (hC : FrontClock Δ γ C E) :
    Run.DecideSpec Δ γ (Lift.a FS) (front Δ γ) (sF Δ γ) (vF Δ γ) (Lift.flag₁ FS)
      (Run.IsInput Δ γ (Lift.a FS)) (Lift.Mid1 FS Δ γ (CM Δ γ C) (EM E)) (Run.ChecksCond Δ γ) C E := by
  intro g hg hn k hH t S hS
  obtain ⟨hk, hinc, hdeg⟩ := hH
  obtain ⟨T, hT, u, bit, Z, hr, hbit⟩ := front_run Δ γ hγ hΔ g hg hn hinc hdeg k
    ((TotalFiniteConstructorScratch.select hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t)
  have hTC : T ≤ C * (g.vertices + 2) ^ (E * (k + 1)) := hT.trans (hC g hg hn k ⟨hk, hinc, hdeg⟩ t)
  subst hS
  refine ⟨T, u, _, bit, hTC, hr, ?_, hbit, ?_⟩
  · show (Lift.layoutBank FS _ _ (Lift.pos FS (.inl (.inl 0)))).head? = some bit
    rw [Lift.layoutBank_inl]
    rfl
  · refine ⟨⟨bit, Z, rfl⟩, ?_⟩
    have hg1 := Lift.size_run (front Δ γ)
      (⟨some (sF Δ γ), vF Δ γ, Wrap.widen (Lift.a FS) (Wrap.inputBank Δ γ g hg hn k t)⟩ :
        TM2.Cfg (fun _ : Fin (Lift.a FS + 3) => Bool) _ _) T
    rw [show ((advance (front Δ γ))^[T])
        (⟨some (sF Δ γ), vF Δ γ, Wrap.widen (Lift.a FS) (Wrap.inputBank Δ γ g hg hn k t)⟩ :
          TM2.Cfg (fun _ : Fin (Lift.a FS + 3) => Bool) _ _) = _ from hr] at hg1
    have hin := Size.inputSize Δ γ g hg hn k hk hinc hdeg t
    rw [Wrap.encode_widen, List.length_append, List.length_replicate] at hg1
    exact hg1.trans (size_arith (g.vertices + 2) (Lift.a FS) _ (4 * Δ + 9)
      (BitMachineStackGrowth.perStep (front Δ γ)) T C E k (by omega) hin hTC)

end

end Paper2.FrontLift

#print axioms Paper2.FrontLift.size_arith
#print axioms Paper2.FrontLift.hFront
