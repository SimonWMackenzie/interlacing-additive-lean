import EthInapproximability.CurrentPaper.ActualSourceNames

/-! Level-zero fixed family clock rebased onto the same actual-count envelope.
Structural identities are reused from `EntryClockPoly3TF`; only polynomial
majorization is replayed. -/

noncomputable section

namespace EthInapproximability.CurrentPaper.ActualCountLevel0Clock

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EntryClockPoly3 ActualCountClock ActualCountFamilyClock EntryPrepFamily EntryTailClear

set_option maxHeartbeats 3000000

def A0 (k : L0) : ℕ := A (φ k)

theorem comapA {f : LI → ℕ} (h : PolyIn A f) : PolyIn A0 (fun k => f (φ k)) :=
  PolyIn.comap φ (fun _ => le_refl _) h

theorem hFam0 : PolyIn A0 (fun k => famBound k.G k.n k.c) :=
  PolyIn.mono (fun k => le_of_eq (famBound_eq k)) (comapA ActualCountFamilyClock.famClock_poly)

theorem pb15_eq (k : L0) :
    WeightedLevelFields15.publicBound15 (iP k.G k.n k.c) (gP k.G) (Fintype.card k.E)
      WeightedRawWords.noW (aP k.G k.n k.c) (sP k.G k.n k.c) (qP k.G k.n k.c) (LP k.G k.n k.c)
      (dP k.G k.n k.c).binBase (dP k.G k.n k.c).rawWidth (dP k.G k.n k.c).s = pb15 (φ k) := by
  unfold pb15
  rw [dP_binBase, dP_rawWidth, dP_s, noW_eq]
  dsimp only [φ]

theorem hPb15 : PolyIn A pb15 := by
  unfold pb15
  exact ActualCountFamilyClock.hP15

theorem hGrow0 : PolyIn A0 (fun k => growB k.G k.n k.c) := by
  unfold growB
  refine PolyIn.mul (PolyIn.const _) ?_
  exact PolyIn.mono (fun k => le_of_eq (pb15_eq k)) (comapA hPb15)

theorem pEll0 : PolyIn A0 (fun k => ell3 k.G) :=
  PolyIn.mono (fun k => le_of_eq (phi_facts k).2.2.2.2.1.symm) (comapA ActualCountFamilyClock.pEll)
theorem pND0 : PolyIn A0 (fun k => b0 k.n) :=
  PolyIn.mono (fun k => le_of_eq (phi_facts k).1.symm) (comapA ActualCountFamilyClock.pND)
theorem pY0 : PolyIn A0 (fun k => y0 k.n) :=
  PolyIn.mono (fun k => by rw [(phi_facts k).2.1]; exact Nat.le_add_right _ _) (comapA ActualCountFamilyClock.pCost)
theorem pC0 : PolyIn A0 (fun k => k.c) :=
  PolyIn.mono (fun k => le_of_eq (phi_facts k).2.2.1.symm) (comapA ActualCountFamilyClock.pSC)
theorem pE0 : PolyIn A0 (fun k => Fintype.card k.E) :=
  PolyIn.mono (fun k => le_of_eq (phi_facts k).2.2.2.1.symm) (comapA ActualCountFamilyClock.pE)
theorem pEnc0 : PolyIn A0 (fun k => (EncodedGraph.encode (gP k.G)).length) :=
  PolyIn.mono (fun k => le_of_eq (phi_facts k).2.2.2.2.2.symm) pEll0

theorem hSf0 : PolyIn A0 sfB := by
  unfold sfB
  have h4 := comapA ActualCountFamilyClock.pCy
  have h5 := comapA ActualCountFamilyClock.pRx
  have := pEnc0
  have := pND0
  have := pY0
  have := pE0
  have := pC0
  prActual

theorem hClear0 : PolyIn A0 (fun k => clearB k.G k.n k.c) := by
  have h0 := comapA ActualCountClock.hExB_actual
  have h1 : PolyIn A0 exB0 := PolyIn.mono (fun k => le_of_eq (exB0_eq k)) h0
  have h2 : PolyIn A0 (fun k => sfB k + growB k.G k.n k.c + exB0 k) :=
    PolyIn.add (PolyIn.add hSf0 hGrow0) h1
  have h3 : PolyIn A0 (fun k => nF * (sfB k + growB k.G k.n k.c + exB0 k)) :=
    PolyIn.mul (PolyIn.const _) h2
  exact PolyIn.mono (fun k => clearB_le k) h3

theorem hA0 : PolyIn A0 (fun k => costA k.G) := by
  unfold costA
  have := pEnc0
  prActual

theorem hC0 : PolyIn A0 (fun k => costC k.G k.n k.c) := by
  unfold costC
  have hrx' : PolyIn A0 (fun k => (EntryLevelWords.w0 k.G k.n k.c).rx) :=
    PolyIn.mono (fun k => le_of_eq (w0_fields k).1) (comapA ActualCountFamilyClock.pRx)
  have hcy' : PolyIn A0 (fun k => (EntryLevelWords.w0 k.G k.n k.c).cy) :=
    PolyIn.mono (fun k => le_of_eq (w0_fields k).2.1) (comapA ActualCountFamilyClock.pCy)
  have := pND0
  have := pY0
  have := pE0
  have := pC0
  prActual

theorem hE0 : PolyIn A0 (fun k => costE k.G k.n k.c) := by
  refine PolyIn.mono (fun k => le_of_eq (costE_eq k)) ?_
  have := comapA ActualCountFamilyClock.pL
  have := comapA ActualCountFamilyClock.pQ
  have := comapA ActualCountFamilyClock.pQOne
  have := comapA ActualCountFamilyClock.pRx
  prActual

theorem hS0 : PolyIn A0 (fun k => (EntryLevelWords.w0 k.G k.n k.c).s) :=
  PolyIn.mono (fun k => le_of_eq (w0_fields k).2.2.1) (comapA ActualCountFamilyClock.pS)

theorem TF_poly0 : PolyIn A0 (fun k => TF k.G k.n k.c) := by
  have := hFam0
  have := hClear0
  have := hA0
  have := hC0
  have := hE0
  have := hS0
  unfold TF
  prActual

/-- Level zero has the same actual-count clock as later levels. The premise
names its concrete `φ k` family, not a coarse one-level envelope. -/
theorem TF0_clock_from_source_names : ∃ C : ℕ, ∀ (k : L0) (p : ℕ),
    Nat.clog 2 (k.n + 2) ≤ p → ActualSourceNames.Names (φ k) p →
    TF k.G k.n k.c ≤
      (k.n + ell3 k.G + 2) ^ C + 2 ^ (C * p) := by
  obtain ⟨K, D, hKD⟩ := TF_poly0
  let C := K + 24 * D
  refine ⟨C, fun k p hfloor hnames => ?_⟩
  have hp : 1 ≤ p := by
    have hclog := Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < k.n + 2)
    omega
  let X := k.n + ell3 k.G + 2
  have hX : 2 ≤ X := by dsimp [X]; omega
  have h800 : 800 ≤ 2 ^ (10 * p) := by
    calc
      800 ≤ 2 ^ 10 := by norm_num
      _ ≤ 2 ^ (10 * p) := Nat.pow_le_pow_right (by decide) (by omega)
  have hA : A0 k ≤ 2 ^ (11 * p) * X := by
    calc
      A0 k ≤ 800 * 2 ^ p * (ell3 k.G + 1) := by
        exact ActualSourceNames.actual_counts_source_bound (φ k) p hnames
      _ ≤ 2 ^ (10 * p) * 2 ^ p * (ell3 k.G + 1) := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h800)
      _ = 2 ^ (11 * p) * (ell3 k.G + 1) := by
        rw [← pow_add]
        rw [show 10 * p + p = 11 * p by omega]
      _ ≤ 2 ^ (11 * p) * X := Nat.mul_le_mul_left _ (by dsimp [X]; omega)
  have hab := EntryClockPoly.absorb K D 11 1 X p (A0 k) hX hp (by
    simpa only [pow_one] using hA)
  calc
    TF k.G k.n k.c ≤ K * (A0 k + 1) ^ D := hKD k
    _ ≤ X ^ (K + 2 * D) + 2 ^ ((K + 24 * D) * p) := by
      simpa only [show 2 * 1 * D = 2 * D by omega,
        show 2 * (11 + 1) * D = 24 * D by omega] using hab
    _ ≤ X ^ C + 2 ^ (C * p) :=
      Nat.add_le_add (Nat.pow_le_pow_right (by omega) (by dsimp [C]; omega))
        (by dsimp [C]; exact le_refl _)


#print axioms hFam0
#print axioms hClear0
#print axioms TF_poly0
#print axioms TF0_clock_from_source_names

end EthInapproximability.CurrentPaper.ActualCountLevel0Clock
