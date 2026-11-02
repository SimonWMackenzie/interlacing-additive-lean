import CurrentAdditive.QuarticCheckLayout
import CurrentAdditive.QuarticFrontOnlyMachine

/-! Assembly seam for a physical v27 numeric preparer and the checked v27
public-check controller. The numeric premise is an exact local program run,
including its charged clock and final-bank size. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.CurrentAdditive.QuarticFrontComposition

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2 Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticDispatchSpec
open Paper2.CurrentAdditive.QuarticCheckLayout
open Paper2.CurrentAdditive.QuarticCheckBit

variable (FS : Type) [Fintype FS] [DecidableEq FS]

/-- Exact numeric-preparer interface: the fixed program installs the literal
quartic start bank, leaves the first flag blank, retains unary n and m in two
distinct scratch cells, and pays for time and bank size. -/
def NumericPrep27 (A B : FS) (Δ : ℕ) (γ : ℚ)
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
        Z B = List.replicate g.edges.length true ∧
        (BitMachineBankCodec.encode
          (Lift.layoutBank FS (inputBank27 Δ γ g hg hn k t)
            (Lift.region FS (QuarticLayout.startCanon27 Δ γ g hg hn k t)
              ![[], [], []] Z))).length ≤
          C * (g.vertices + 2) ^ (E * (k + 1))

/-- One fixed program: numeric preparation followed by the exact v27 check. -/
noncomputable def frontProg27 (A B : FS) (Δ : ℕ) (γ : ℚ)
    {L V : Type}
    (P : L → TM2.Stmt (fun _ : Fin (Lift.a FS + 3) => Bool) L V)
    (v : V) :=
  BitMachineRawSequence.program P (checkProgLayout27 FS A B Δ γ)
    CheckBit.DL.rdA v (CheckBit.ctl0 (NA27 Δ γ) (NB27 Δ γ))

noncomputable def frontClockC27 (A B : FS) (Δ : ℕ) (γ : ℚ) (C : ℕ) : ℕ :=
  C + Δ + 4 + 2 * (Lift.a FS + 3) *
    BitMachineStackGrowth.perStep (checkProgLayout27 FS A B Δ γ) * (Δ + 3)

def frontClockE27 (E : ℕ) : ℕ := max E 1

theorem front_of_numeric27 (A B : FS) (hAB : A ≠ B)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    {L V : Type} [Fintype L]
    (P : L → TM2.Stmt (fun _ : Fin (Lift.a FS + 3) => Bool) L V)
    (s : L) (v : V) (C E : ℕ)
    (hPrep : NumericPrep27 FS A B Δ γ P s v C E) :
    QuarticFrontOnlyMachine.FrontSpec27 FS Δ γ
      (frontProg27 FS A B Δ γ P v)
      (BitMachineRawSequence.leftLabel s)
      (v, CheckBit.ctl0 (NA27 Δ γ) (NB27 Δ γ))
      (frontClockC27 FS A B Δ γ C) (frontClockE27 E)
      (frontClockC27 FS A B Δ γ C) (frontClockE27 E) := by
  intro g hg hn k hH t S hS
  rcases hH with ⟨hk, hinc, hdeg⟩
  subst S
  obtain ⟨T₁, u, Z, hT₁, hr₁, hA, hB, hsz₁⟩ :=
    hPrep g hg hn k ⟨hk, hinc, hdeg⟩ t
  obtain ⟨w, bit, Z', hr₂, hbit⟩ :=
    check_layout_run27 FS A B hAB Δ γ hγ hΔ g hg hn hinc hdeg
      (inputBank27 Δ γ g hg hn k t)
      (QuarticLayout.startCanon27 Δ γ g hg hn k t) Z hA hB
  let S₁ := Lift.layoutBank FS (inputBank27 Δ γ g hg hn k t)
    (Lift.region FS (QuarticLayout.startCanon27 Δ γ g hg hn k t)
      ![[], [], []] Z)
  let S₂ := Lift.layoutBank FS (inputBank27 Δ γ g hg hn k t)
    (Lift.region FS (QuarticLayout.startCanon27 Δ γ g hg hn k t)
      ![[bit], [], []] Z')
  obtain ⟨T, hT, hr⟩ := BitMachineRawSequence.runs P
    (checkProgLayout27 FS A B Δ γ) s .rdA v u
    (CheckBit.ctl0 (NA27 Δ γ) (NB27 Δ γ)) w _ S₁ S₂
    T₁ (g.vertices + g.edges.length + 2) hr₁ hr₂
  let N := (g.vertices + 2) ^ (frontClockE27 E * (k + 1))
  have hbase : 1 ≤ g.vertices + 2 := by omega
  have hN : 1 ≤ N := by dsimp [N]; exact Nat.one_le_pow _ _ hbase
  have hpow : (g.vertices + 2) ^ (E * (k + 1)) ≤ N := by
    dsimp [N, frontClockE27]
    exact Nat.pow_le_pow_right hbase
      (Nat.mul_le_mul_right _ (le_max_left E 1))
  have hbaseN : g.vertices + 2 ≤ N := by
    have he : 1 ≤ frontClockE27 E * (k + 1) := by
      exact Nat.mul_pos (by
        simp only [frontClockE27]
        exact lt_of_lt_of_le Nat.zero_lt_one (le_max_right E 1)) (by omega)
    simpa using (Nat.pow_le_pow_right hbase he :
      (g.vertices + 2) ^ 1 ≤ N)
  haveI : Nonempty (Fin g.vertices) := ⟨⟨0, hn⟩⟩
  have hm := SourceDensityScheduleScratch.twice_edges_le_degree_vertices
    (V := Fin g.vertices) (E := Fin g.edges.length)
    (CanonicalEdgeTape.graphEdge g hg) Δ hdeg
  simp only [Fintype.card_fin] at hm
  have hT₂ : g.vertices + g.edges.length + 2 ≤ (Δ + 3) * N := by
    have hmul := Nat.mul_le_mul_left (Δ + 3) hbaseN
    nlinarith
  have hT₁' : T₁ ≤ C * N :=
    hT₁.trans (Nat.mul_le_mul_left _ hpow)
  have hsz₁' : (BitMachineBankCodec.encode S₁).length ≤ C * N :=
    hsz₁.trans (Nat.mul_le_mul_left _ hpow)
  have hszRun := Lift.size_run (checkProgLayout27 FS A B Δ γ)
    (⟨some .rdA, CheckBit.ctl0 (NA27 Δ γ) (NB27 Δ γ), S₁⟩ :
      TM2.Cfg (fun _ : Fin (Lift.a FS + 3) => Bool) CheckBit.DL
        (CheckBit.DV (NA27 Δ γ) (NB27 Δ γ)))
    (g.vertices + g.edges.length + 2)
  rw [hr₂] at hszRun
  have hsz₂ : (BitMachineBankCodec.encode S₂).length ≤
      frontClockC27 FS A B Δ γ C * N := by
    have hmul := Nat.mul_le_mul_left
      (2 * (Lift.a FS + 3) *
        BitMachineStackGrowth.perStep (checkProgLayout27 FS A B Δ γ)) hT₂
    dsimp [frontClockC27]
    nlinarith
  have hclock : T ≤ frontClockC27 FS A B Δ γ C * N := by
    have hsum : T ≤ (C + Δ + 4) * N := by
      calc
        T ≤ T₁ + (g.vertices + g.edges.length + 2) + 1 := hT
        _ ≤ C * N + (Δ + 3) * N + N := by omega
        _ = (C + Δ + 4) * N := by ring
    exact hsum.trans (Nat.mul_le_mul_right N (by
      dsimp [frontClockC27]
      omega))
  refine ⟨T, (v, w), S₂, bit, hclock, ?_, ?_, hbit, ?_⟩
  · simpa only [frontProg27] using hr
  · simp [S₂, Lift.flag₁, Lift.layoutBank_inl, Lift.region]
  · exact ⟨⟨bit, Z', rfl⟩, hsz₂⟩

#print axioms front_of_numeric27

end Paper2.CurrentAdditive.QuarticFrontComposition
