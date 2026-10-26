import CurrentAdditive.V42PublicSize
import CurrentAdditive.V39BitGrowth

/-! v42 literal runtime widths and fair-bit resource reservation. The
reservation is proved from the actual recursive sample requests. -/
namespace V42RuntimeSchedule
open CurrentAdditive V42Schedule V42PublicSchedule V42PublicCutoff V42PublicSize
open V38OneStep V39RecursiveGenerator

abbrev ell := V42PublicSchedule.ell
abbrev seedWidth := V42PublicSchedule.seedWidth
def fullS (L : ℕ) := s (fullExponent L)
def fullQ₁ (L : ℕ) := fullS L-2
def fullQ₂ (L : ℕ) := q₂ (fullExponent L) L
theorem fullQ₂_eq_old (L : ℕ) : fullQ₂ L=V38Schedule.fullQ₂ L := by
  simp only [fullQ₂,CurrentAdditive.V42Schedule.q₂,CurrentAdditive.V42PublicSchedule.fullExponent,
    V38Schedule.fullQ₂,V38Schedule.fullS,ell,CurrentAdditive.V42PublicSchedule.ell,V38Schedule.ell]
  rw [←pow_mul,←pow_add]
  congr 1
  omega

def fullW (L : ℕ) := w (fullExponent L)
def fullQ (L : ℕ) := Q (fullExponent L)
abbrev fullOverhead := V42PublicSchedule.fullOverhead
abbrev B := V42PublicSchedule.B
abbrev H := V42PublicSchedule.H
abbrev rankBound := V42PublicSchedule.rankBound
abbrev sampleSide := V42PublicSchedule.sampleSide
def fullWidthExponent (L : ℕ) := 16*L
def fullSampleExponent (L i : ℕ) := 40*(i+1)*L
def fullDrawExponent (L i : ℕ) := sampleExponent (fullWidthExponent L) (fullSampleExponent L i) i
def fullAlphabet (n L : ℕ) := publicA n (fullS L) (fullQ₂ L) (fullW L) (fullQ L) (seedWidth L)
def reservation (L i : ℕ) := 2^fullDrawExponent L i
def precision (n L i : ℕ) := publicBits (fullAlphabet n L) (reservation L i)

theorem fullS_ge_256 (L : ℕ) : 256 ≤ fullS L := by
  change 2^8 ≤ 2^(16+ell L)
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem full_positive_widths (L : ℕ) :
    0<seedWidth L ∧ 0<fullQ₁ L ∧ 0<fullQ₂ L ∧ 0<fullS L ∧
    0<4*fullS L ∧ 0<fullS L-3 ∧ 0<fullW L ∧ 0<fullQ L := by
  have hs := fullS_ge_256 L
  have hp : 0<seedWidth L := by unfold seedWidth; rw [V42PublicSchedule.seedWidth_exact]; positivity
  have hq : 0<fullQ₂ L := q₂_pos _ _
  have hw : 0<fullW L := w_pos _
  have hQ : 0<fullQ L := Q_pos _
  dsimp [fullQ₁]
  omega

instance seedNZ (L : ℕ) : NeZero (seedWidth L) := ⟨ne_of_gt (full_positive_widths L).1⟩
instance q1NZ (L : ℕ) : NeZero (fullQ₁ L) := ⟨ne_of_gt (full_positive_widths L).2.1⟩
instance q2NZ (L : ℕ) : NeZero (fullQ₂ L) := ⟨ne_of_gt (full_positive_widths L).2.2.1⟩
instance sNZ (L : ℕ) : NeZero (fullS L) := ⟨ne_of_gt (full_positive_widths L).2.2.2.1⟩
instance fsNZ (L : ℕ) : NeZero (4*fullS L) := ⟨ne_of_gt (full_positive_widths L).2.2.2.2.1⟩
instance smNZ (L : ℕ) : NeZero (fullS L-3) := ⟨ne_of_gt (full_positive_widths L).2.2.2.2.2.1⟩
instance wNZ (L : ℕ) : NeZero (fullW L) := ⟨ne_of_gt (full_positive_widths L).2.2.2.2.2.2.1⟩
instance QNZ (L : ℕ) : NeZero (fullQ L) := ⟨ne_of_gt (full_positive_widths L).2.2.2.2.2.2.2⟩

theorem full_widths_le_pow (n L : ℕ) (hn : n ≤ 2^L)
    (hL : fullLengthCutoff 0 ≤ L) :
    n ≤ 2^fullWidthExponent L ∧ seedWidth L ≤ 2^fullWidthExponent L ∧
    fullQ₁ L ≤ 2^fullWidthExponent L ∧ fullQ₂ L ≤ 2^fullWidthExponent L ∧
    fullS L ≤ 2^fullWidthExponent L ∧ fullW L ≤ 2^fullWidthExponent L ∧
    fullQ L ≤ 2^fullWidthExponent L := by
  have hb := full_cutoff_bounds 0 L hL
  have hk : 4*fullExponent L ≤ L := hb.2.2.2.2
  have hseed : 6+ell L ≤ 16*L := by change 4*(16+ell L) ≤ L at hk; omega
  have hs : fullS L ≤ 2^fullWidthExponent L :=
    Nat.pow_le_pow_right (by decide) (by unfold fullWidthExponent; omega)
  refine ⟨hn.trans (Nat.pow_le_pow_right (by decide) (by unfold fullWidthExponent; omega)),?_,?_,?_,hs,?_,?_⟩
  · unfold seedWidth; rw [V42PublicSchedule.seedWidth_exact]
    exact Nat.pow_le_pow_right (by decide) hseed
  · exact (Nat.sub_le _ _).trans hs
  · exact Nat.pow_le_pow_right (by decide) (by unfold fullWidthExponent; omega)
  · exact Nat.pow_le_pow_right (by decide) (by unfold fullWidthExponent; omega)
  · exact Nat.pow_le_pow_right (by decide) (by unfold fullWidthExponent; omega)

theorem full_sampleSide_le_pow (L i : ℕ) (hL : fullLengthCutoff 0 ≤ L) :
    sampleSide L i ≤ 2^fullSampleExponent L i := by
  have he := sampleEntries_power_bound 0 L i hL
  have hm : 1 ≤ sampleSide L i := Nat.one_le_two_pow.trans (sampleSide_lower L i)
  exact (show sampleSide L i ≤ sampleEntries L i by unfold sampleEntries; nlinarith).trans he

theorem fullAlphabet_le (n L : ℕ) (hn : n ≤ 2^L) (hL : fullLengthCutoff 0 ≤ L) :
    fullAlphabet n L ≤ 2^(2*fullWidthExponent L+9) := by
  obtain ⟨hn,hp,_,hq,hs,hw,hQ⟩ := full_widths_le_pow n L hn hL
  exact publicA_le_exp n (seedWidth L) (fullQ₂ L) (fullS L) (fullW L) (fullQ L)
    (fullWidthExponent L) hn hp hq hs hw hQ

theorem draw_cap (L i : ℕ) (hL : fullLengthCutoff 0 ≤ L) :
    sampleDrawBudget (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
      (fullW L) (fullQ L) i (sampleSide L i) ≤ reservation L i := by
  obtain ⟨_,hp,hq1,hq2,hs,hw,hQ⟩ := full_widths_le_pow (2^L) L le_rfl hL
  exact sampleDrawBudget_le_exp _ _ _ _ _ _ _ _ _ _ hp hq1 hq2 hs hw hQ
    (full_sampleSide_le_pow L i hL)

theorem budget_exponents_linear (L i : ℕ) (hL : fullLengthCutoff 0 ≤ L) :
    fullDrawExponent L i ≤ 112*(i+1)*L ∧
    2*fullWidthExponent L+fullDrawExponent L i+17 ≤ 160*(i+1)*L ∧
    2*fullWidthExponent L+2*fullDrawExponent L i+17 ≤ 272*(i+1)*L := by
  have h16 := (full_cutoff_bounds 0 L hL).2.1
  have hi := Nat.mul_le_mul_left i h16
  have h : fullDrawExponent L i ≤ 112*(i+1)*L := by
    unfold fullDrawExponent sampleExponent fullWidthExponent fullSampleExponent
    nlinarith only [h16,hi,Nat.zero_le (i*L)]
  refine ⟨h,?_,?_⟩ <;> unfold fullWidthExponent <;> nlinarith

theorem precision_le (n L i : ℕ) (hn : n ≤ 2^L) (hL : fullLengthCutoff 0 ≤ L) :
    precision n L i ≤ 160*(i+1)*L :=
  (publicBits_le_expSum _ _ _ _ (fullAlphabet_le n L hn hL) le_rfl).trans
    (budget_exponents_linear L i hL).2.1

theorem reserved_bits_le (n L i : ℕ) (hn : n ≤ 2^L) (hL : fullLengthCutoff 0 ≤ L) :
    precision n L i*reservation L i ≤ 2^(272*(i+1)*L) :=
  (randomBits_le_expSum _ _ _ _ (fullAlphabet_le n L hn hL) le_rfl).trans
    (Nat.pow_le_pow_right (by decide) (budget_exponents_linear L i hL).2.2)

/-- Runtime premises are numerical only: the unchanged edge-width guards,
plus the new public length cutoff. No sampler or printer run is assumed. -/
def FullTests (cc : ℚ) (L edgeCount : ℕ) (δv ζ : ℚ) : Prop :=
  V38Schedule.FullTests cc L edgeCount δv ζ ∧ fullLengthCutoff 0 ≤ L

theorem fullDrawCap_le (cc : ℚ) (L edgeCount i : ℕ) (δv ζ : ℚ)
    (ht : FullTests cc L edgeCount δv ζ) :
    sampleDrawBudget (seedWidth L) (fullQ₁ L) (fullQ₂ L) (fullS L)
      (fullW L) (fullQ L) i (sampleSide L i) ≤ 2^fullDrawExponent L i :=
  draw_cap L i ht.2
/-- This cutoff is a public integer depending only on the promised source
constants. Its second term discharges the new sampler arithmetic. -/
def sourceCutoff (γ : ℚ) (Δ : ℕ) :=
  max (V39FullCutoff.sourceCutoff γ Δ) (2^fullLengthCutoff 0)

theorem tests_all_large (γ : ℚ) (Δ n edgeCount : ℕ)
    (hγ : 0<γ) (hΔ : 0<Δ) (hn : 0<n)
    (hnm : n ≤ 2*edgeCount) (hdeg : 2*edgeCount ≤ Δ*n)
    (hlarge : sourceCutoff γ Δ ≤ n) :
    FullTests (V38Schedule.fullConstant γ Δ n edgeCount) (Nat.clog 2 n) edgeCount
      (V38Schedule.sourceDeltaV γ Δ n edgeCount) (V38Schedule.sourceZeta γ) := by
  refine ⟨V39FullCutoff.fullPublicTests_all_large γ Δ n edgeCount hγ hΔ hn hnm hdeg
    ((le_max_left _ _).trans hlarge),?_⟩
  have hpow : 2^fullLengthCutoff 0 ≤ n := (le_max_right _ _).trans hlarge
  have hc := Nat.clog_mono_right 2 hpow
  simpa only [Nat.clog_pow 2 _ (by decide)] using hc

#print axioms tests_all_large
#print axioms draw_cap
#print axioms reserved_bits_le
end V42RuntimeSchedule






