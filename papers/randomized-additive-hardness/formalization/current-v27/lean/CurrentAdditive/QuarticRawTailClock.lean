import CurrentAdditive.QuarticPacketClockDensity
import CurrentAdditive.QuarticDimensionsMachine
import CurrentAdditive.QuarticTailClockArithmetic

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536

namespace Paper2.CurrentAdditive.QuarticTMClockRepair

open EthInapproximability.CurrentPaper
open Paper2.CurrentAdditive.QuarticNumericFront
open CurrentAdditive.RandomizedSchedule
open SourceProfileParameters SourceRecursiveNoSampling

noncomputable def rawExponent (Δ : ℕ) (γ : ℚ) : ℕ :=
  max (baseExponent Δ γ)
    (max (Paper2.CurrentAdditive.QuarticPacketClockBound.exponent Δ γ)
      (clockExponent Δ γ)) + 1

noncomputable def growthCoefficient : ℕ :=
  BitMachineStackGrowth.perStep TMFront.tmProg + 2

theorem tail_cost_poly27 (g : EncodedGraph.Graph) (Δ k : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < g.vertices) (hmpos : 0 < g.edges.length)
    (hm : g.edges.length ≤ Δ * g.vertices) (word : List Bool) :
    let B := (g.vertices + 2) ^ (rawExponent Δ γ * (k + 1))
    TailSource27.cost g k Δ γ word ≤
      500 * (growthCoefficient * B + word.length) := by
  let n := g.vertices
  let m := g.edges.length
  let N := n + 2
  let E := rawExponent Δ γ
  let B := N ^ (E * (k + 1))
  let G := BitMachineStackGrowth.perStep TMFront.tmProg
  let Z := growthCoefficient * B + word.length
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hEbase : baseExponent Δ γ ≤ E := by
    dsimp only [E, rawExponent]
    exact (le_max_left _ _).trans (Nat.le_succ _)
  have hEclock : clockExponent Δ γ ≤ E := by
    dsimp only [E, rawExponent]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (Nat.le_succ _))
  have hE1 : 1 ≤ E := by dsimp only [E, rawExponent]; omega
  have hEk : E ≤ E * (k + 1) := Nat.le_mul_of_pos_right E (by omega)
  have hB1 : 1 ≤ B := Nat.one_le_pow _ _ hN
  have hBasePow : N ^ baseExponent Δ γ ≤ B :=
    Nat.pow_le_pow_right hN (hEbase.trans hEk)
  have hClockPow : N ^ (clockExponent Δ γ * (k + 1)) ≤ B :=
    Nat.pow_le_pow_right hN (Nat.mul_le_mul_right _ hEclock)
  have hGle : G ≤ growthCoefficient := by dsimp [G, growthCoefficient]; omega
  have hOneG : 1 ≤ growthCoefficient := by dsimp [growthCoefficient]; omega
  have hBz : B ≤ Z := by
    have h := Nat.mul_le_mul_right B hOneG
    dsimp [Z]
    omega
  have hGBz : G * B ≤ Z := by
    have h := Nat.mul_le_mul_right B hGle
    dsimp [Z]
    omega
  have hZ : 1 ≤ Z := hB1.trans hBz
  have hV : ∀ i, vector27 n m (Nat.clog 2 n) Δ γ i ≤ Z := by
    intro i
    exact (vector_bound27 Δ n m γ hγ hΔ hn hmpos hm i).trans
      (hBasePow.trans hBz)
  have hNpow : N ≤ B := by
    have h1 : N ^ 1 ≤ B :=
      Nat.pow_le_pow_right hN (le_trans hE1 hEk)
    simpa only [pow_one] using h1
  have hnZ : n ≤ Z := by
    have : n ≤ N := by dsimp [N]; omega
    exact this.trans (hNpow.trans hBz)
  have hLZ : Nat.clog 2 n ≤ Z := by
    have hL : Nat.clog 2 n ≤ n :=
      Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
    exact hL.trans hnZ
  have hkZ : k ≤ Z := by
    have hk2 : k ≤ 2 ^ k := (Nat.lt_two_pow_self).le
    have h2N : 2 ≤ N := by dsimp [N]; omega
    have hkN : 2 ^ k ≤ N ^ k := Nat.pow_le_pow_left h2N k
    have hkE : k ≤ E * (k + 1) := by
      have h := Nat.mul_le_mul_right (k + 1) hE1
      omega
    exact hk2.trans (hkN.trans
      ((Nat.pow_le_pow_right hN hkE).trans hBz))
  have hTM : TMFront.tmBd k (vector27 n m (Nat.clog 2 n) Δ γ)
      (Nat.clog 2 n) ≤ B :=
    (tmBd_poly27 Δ n m k γ hγ hΔ hn hmpos hm).trans hClockPow
  have hDim := QuarticDimensionsMachine.dimensions_le_machine_clock
    n m (Nat.clog 2 n) Δ k γ
  have hRows : sourceRows (Nat.clog 2 n)
      (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n))
      (q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ) k ≤ Z :=
    (hDim.1.trans (Nat.mul_le_mul_left _ hTM)).trans hGBz
  have hCols : sourceCols (Nat.clog 2 n)
      (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n))
      (q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ) k ≤ Z :=
    (hDim.2.trans (Nat.mul_le_mul_left _ hTM)).trans hGBz
  have hWord : word.length ≤ Z := by dsimp [Z]; omega
  have hp : LookupSeed.width (Nat.clog 2 n) ≤ Z := by
    simpa only [vector27] using hV (0 : Fin 5)
  have hs : width (Nat.clog 2 n) ≤ Z := by
    simpa only [vector27] using hV (1 : Fin 5)
  have hq₂ : outerWidth (Nat.clog 2 n) ≤ Z := by
    simpa only [vector27] using hV (2 : Fin 5)
  have hw : width27 (Nat.clog 2 n) ≤ Z := by
    simpa only [vector27] using hV (3 : Fin 5)
  have hQ : Q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ ≤ Z := by
    simpa only [vector27] using hV (4 : Fin 5)
  simpa only [Z, B, N, n, m] using
    QuarticTailClockArithmetic.tail_cost_linear g k Δ γ word Z
      hZ hLZ hnZ hkZ hp hs hq₂ hw hQ hRows hCols hWord
      (hTM.trans hBz)

#print axioms tail_cost_poly27

end Paper2.CurrentAdditive.QuarticTMClockRepair
