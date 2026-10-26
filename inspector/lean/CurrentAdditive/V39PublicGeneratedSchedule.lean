import CurrentAdditive.V39GraphGenerated
import CurrentAdditive.GeneratedCutoffApplications

/-! Bind the actual public first-passing generated schedule to the actual
stored graph constructor. All source widths and the repetition count are
computed here. No passing-size, width-divisibility or source constructor is
an input premise of publicGraphRun. NO/profile and physical clocks remain
separate. The generated analysis parameter is exactly N^-8. -/

namespace CurrentAdditive.V39GeneratedConstruction

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open V38Schedule GeneratedCutoff
open CurrentAdditive.LiteralEdgeEncoder

/-- Fixed rational constants from the source graph promise. No test result,
matrix profile or communication bound is contained in this record. -/
structure SourceConstants where
  gamma : ℚ
  degree : ℕ
  deletion : ℚ
  gamma_pos : 0 < gamma
  degree_pos : 0 < degree
  deletion_pos : 0 < deletion
  deletion_le : deletion ≤
    min 1 (min (gamma/(4*degree)) (sourceZeta gamma/256)) / 2^16

def sourceConstants (γ : ℚ) (Δ : ℕ) (hγ : 0 < γ) (hΔ : 0 < Δ) :
    SourceConstants := by
  let b : ℚ := min 1 (min (γ/(4*Δ)) (sourceZeta γ/256))
  have hb : 0 < b := by
    have hΔq : (0 : ℚ) < Δ := by exact_mod_cast hΔ
    dsimp [b, sourceZeta]
    positivity
  refine ⟨γ, Δ, b/2^17, hγ, hΔ, by positivity, ?_⟩
  change b/2^17 ≤ b/2^16
  norm_num
  linarith

def publicLog (p : SourceConstants) (n m : ℕ)
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n) : ℕ :=
  firstGeneratedExponent p.deletion n m
    (sourceDeltaV p.gamma p.degree n m) (sourceZeta p.gamma)
    (exists_passing p.gamma p.deletion p.degree n m p.gamma_pos p.degree_pos
      p.deletion_pos p.deletion_le hn hlow hdegree)

theorem publicLog_spec (p : SourceConstants) (n m : ℕ)
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n) :
    Nat.clog 2 n ≤ publicLog p n m hn hlow hdegree ∧
      GeneratedTests p.deletion (publicLog p n m hn hlow hdegree) m
        (sourceDeltaV p.gamma p.degree n m) (sourceZeta p.gamma) := by
  exact Nat.find_spec (exists_passing p.gamma p.deletion p.degree n m
    p.gamma_pos p.degree_pos p.deletion_pos p.deletion_le hn hlow hdegree)

theorem publicLog_size (p : SourceConstants) (n m : ℕ)
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n) :
    n ≤ generatedN (publicLog p n m hn hlow hdegree) :=
  (Nat.le_pow_clog (by decide) n).trans
    (Nat.pow_le_pow_right (by decide) (publicLog_spec p n m hn hlow hdegree).1)

theorem publicLog_dyadic_bound (p : SourceConstants) (n m : ℕ)
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n) :
    generatedN (publicLog p n m hn hlow hdegree) ≤
      2*max n (generatedN (cutoffLog p.degree p.deletion)) :=
  first_passing_dyadic_bound p.gamma p.deletion p.degree n m p.gamma_pos
    p.degree_pos p.deletion_pos p.deletion_le hn hlow hdegree

def paddedSourceWidth (L m : ℕ) : ℕ := pow2Ceil (4*generatedS L*m)

def publicRepetition (L m : ℕ) : ℕ := generatedQ₂ L / paddedSourceWidth L m

/-- A passing first size need not be above the sufficient cutoff. Its literal
source-width test itself proves the divisibility needed by the constructor. -/
theorem passing_width_dvd (c : ℚ) (L m : ℕ) (δv ζ : ℚ)
    (h : GeneratedTests c L m δv ζ) :
    paddedSourceWidth L m ∣ generatedQ₂ L := by
  have hw : pow2Ceil (4*generatedS L*m) ≤ generatedQ₂ L := h.1.2.2.1
  have hq : generatedQ₂ L = 2^(4*L) := by
    unfold generatedQ₂ generatedN
    rw [← pow_mul]
    congr 1
    omega
  have hcount : 4*generatedS L*m ≤ generatedQ₂ L :=
    (Nat.le_pow_clog (by decide) _).trans hw
  have he : Nat.clog 2 (4*generatedS L*m) ≤ 4*L :=
    (Nat.clog_le_iff_le_pow (by decide)).2 (by simpa only [hq] using hcount)
  unfold paddedSourceWidth pow2Ceil
  rw [hq]
  exact Nat.pow_dvd_pow 2 he

theorem paddedSourceWidth_eq (L m : ℕ) :
    CurrentAdditive.EdgeSource.sourceQ0 (Fin (4*generatedS L)) (Fin m) =
      paddedSourceWidth L m := by
  rw [CurrentAdditive.EdgeSource.sourceQ0_literal]
  simp only [Fintype.card_fin, paddedSourceWidth, pow2Ceil,
    SourcePadding.powTwoCeil]

theorem passing_repetition_eq (c : ℚ) (L m : ℕ) (δv ζ : ℚ)
    (h : GeneratedTests c L m δv ζ) :
    generatedQ₂ L = LiteralEdgeEncoder.Width (generatedS L) m (publicRepetition L m) := by
  change generatedQ₂ L =
    CurrentAdditive.EdgeSource.sourceQ0 (Fin (4*generatedS L)) (Fin m)*publicRepetition L m
  rw [paddedSourceWidth_eq]
  exact (Nat.mul_div_cancel' (passing_width_dvd c L m δv ζ h)).symm

theorem passing_repetition_pos (c : ℚ) (L m : ℕ) (δv ζ : ℚ)
    (h : GeneratedTests c L m δv ζ) : 0 < publicRepetition L m := by
  have hq := passing_repetition_eq c L m δv ζ h
  have hpos : 0 < generatedQ₂ L := by unfold generatedQ₂ generatedN; positivity
  change 0 < publicRepetition L m
  by_contra hn
  have hz : publicRepetition L m = 0 := by omega
  simp only [LiteralEdgeEncoder.Width, hz, Nat.mul_zero] at hq
  omega

theorem passing_s_ge_four (c : ℚ) (L m : ℕ) (δv ζ : ℚ)
    (h : GeneratedTests c L m δv ζ) : 4 ≤ generatedS L := by
  have hs : 256 ≤ generatedS L := h.1.1
  omega

theorem generated_graph_increment (L : ℕ) :
    graphIncrement (generatedS L) (generatedQ₂ L) (generatedW L) (generatedQ L) =
      12*L+2*quarterCeil L := by
  have hs : Nat.clog 2 (generatedS L) = quarterCeil L := by
    simp only [generatedS, Nat.clog_pow, one_lt_two]
  have hq : Nat.clog 2 (generatedQ₂ L) = 4*L := by
    unfold generatedQ₂ generatedN
    rw [← pow_mul]
    simp only [Nat.clog_pow, one_lt_two]
    omega
  have hw : Nat.clog 2 (generatedW L) = 2*L := by
    unfold generatedW generatedN
    rw [← pow_mul]
    simp only [Nat.clog_pow, one_lt_two]
    omega
  have hQ : Nat.clog 2 (generatedQ L) = 6*L := by
    unfold generatedQ generatedN
    rw [← pow_mul]
    simp only [Nat.clog_pow, one_lt_two]
    omega
  unfold graphIncrement
  rw [hs, hq, hw, hQ]
  omega

def publicGraphRun (p : SourceConstants) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (edge : Fin m → Bool → Fin n) (k : ℕ) : StoredMatrix := by
  let L := publicLog p n m hn hlow hdegree
  have ht := (publicLog_spec p n m hn hlow hdegree).2
  haveI : NeZero (generatedS L) := ⟨by unfold generatedS; positivity⟩
  haveI : NeZero (generatedQ₂ L) := ⟨by unfold generatedQ₂ generatedN; positivity⟩
  haveI : NeZero (generatedW L) := ⟨by unfold generatedW generatedN; positivity⟩
  haveI : NeZero (generatedQ L) := ⟨by unfold generatedQ generatedN; positivity⟩
  exact graphRun (w := generatedW L) (Q := generatedQ L)
    (passing_s_ge_four _ _ _ _ _ ht) hn (passing_repetition_eq _ _ _ _ _ ht) edge L k

def publicGraphThreshold (p : SourceConstants) (n m : ℕ)
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n) (k : ℕ) : ℕ :=
  let L := publicLog p n m hn hlow hdegree
  Paper2.LookupSeed.exponent L+1+k*(12*L+2*quarterCeil L)

theorem publicGraphRun_yes (p : SourceConstants) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (edge : Fin m → Bool → Fin n) (k : ℕ) (colour : Fin n → Fin 3)
    (proper : ∀ j, colour (edge j false) ≠ colour (edge j true)) :
    D (publicGraphRun p hn hlow hdegree edge k).entry ≤
      publicGraphThreshold p n m hn hlow hdegree k := by
  let L := publicLog p n m hn hlow hdegree
  have ht := (publicLog_spec p n m hn hlow hdegree).2
  haveI : NeZero (generatedS L) := ⟨by unfold generatedS; positivity⟩
  haveI : NeZero (generatedQ₂ L) := ⟨by unfold generatedQ₂ generatedN; positivity⟩
  haveI : NeZero (generatedW L) := ⟨by unfold generatedW generatedN; positivity⟩
  haveI : NeZero (generatedQ L) := ⟨by unfold generatedQ generatedN; positivity⟩
  have hy := graphRun_yes (w := generatedW L) (Q := generatedQ L)
    (passing_s_ge_four _ _ _ _ _ ht) hn (passing_repetition_eq _ _ _ _ _ ht)
    edge L k colour proper
  change D (publicGraphRun p hn hlow hdegree edge k).entry ≤
    Paper2.LookupSeed.exponent L+1+
      k*graphIncrement (generatedS L) (generatedQ₂ L) (generatedW L) (generatedQ L) at hy
  rw [generated_graph_increment] at hy
  exact hy

def publicGraphRectangle (p : SourceConstants) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (edge : Fin m → Bool → Fin n) (k : ℕ) :=
  (publicGraphRun p hn hlow hdegree edge k).rectangle
    (publicGraphThreshold p n m hn hlow hdegree k)

theorem publicGraphRectangle_valid (p : SourceConstants) {n m : ℕ}
    (hn : 0 < n) (hlow : n ≤ 2*m) (hdegree : 2*m ≤ p.degree*n)
    (edge : Fin m → Bool → Fin n) (k : ℕ) :
    (publicGraphRectangle p hn hlow hdegree edge k).Valid :=
  StoredMatrix.rectangle_valid _ _

end CurrentAdditive.V39GeneratedConstruction
