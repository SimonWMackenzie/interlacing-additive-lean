import Paper2.A4Shells
import Paper2.SourceDensitySchedule
import EthInapproximability.CurrentPaper.SourceOriginalVariableCapture

/-!
# Unit 4 (Paper A), segments A4-S3 residue (size) and A4-S4 (T45 size relations)

Owner lane `owner:a-unit4-shell-2` (private, 25 September 2026). Continues
`a-unit4-shell-owner` (frozen objects `A4T10Finite`, `A4Shells` imported unchanged).

Everything here is derived from the FIELDS of the cited records, which remain parameters
`D : DinurReduction` (X03) and `B : BOTReduction (booleanOccurrence D)` (X04); adopting them as
Paper A's contract is the author's decision D-A7 and is NOT taken here. Banked facts reused by
exact name: `D.size`, `B.edges`, `BOTReduction.output_total_size`, `boolean_size`,
`boolean_occurrence`, `Sparsification.formula_length_log`, `nat_size_mul_le`,
`nat_size_add_one_le`, `nat_size_le_self`, `SourceOriginalVariableCapture.original_n_le_input`,
`SourceDensityScheduleScratch.twice_edges_le_degree_vertices`, and the predecessor's
`T10Finite.t10_source`.

* `H_T10Size_holds` discharges the predecessor's HYP interface `Shells.H_T10Size D B`.
* `t45_relations` gives, for the actual T10 graph of a valid `Φ` with `N = Φ.variables`
  variables, `N ≤ m`, `2 m ≤ Δ n` (`Δ = B.degreeBound`) and, when `Φ` is sparse with density
  `cs` (`Φ.clauses ≤ cs·N`, the density is a PARAMETER: D-A2/D-A6 are the author's),
  `n ≤ C·N·(⌈log₂(N+2)⌉+1)^q` with explicit `C, q` depending only on `D, B, cs`.
* `t45_shell_form` converts that into the form consumed by the T24 pieces,
  `n ≤ N·⌈log₂(N+2)⌉^(q+1)` for all `N ≥ 2^(2^q·C)`.

**None of these statements closes a ledger row** (T10, T45, X03, X04 stay open).
-/

namespace Paper2.Unit4Shell.T10Size

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The raw BOT edge count of the Boolean formula of `Φ`, in terms of Dinur's size field. -/
theorem raw_edges_le (Φ : ValidFormula) :
    (B.reduce (booleanFormula D Φ).val).edges.length ≤
      B.sizeConstant * booleanSizeFactor D * (D.sizeConstant *
        ((EncodedCNF.encode Φ.val).length + 1) *
          (((EncodedCNF.encode Φ.val).length + 1).size + 1) ^ D.sizeExponent) := by
  have he := B.edges (booleanFormula D Φ).val (booleanFormula D Φ).property
    (boolean_occurrence D Φ)
  have hb := boolean_size D Φ
  have hd := D.size Φ
  have hv : (booleanFormula D Φ).val.variables ≤ booleanSizeFactor D * (D.reduce Φ).constraints :=
    le_trans (Nat.le_add_right _ _) hb
  have hc : (D.reduce Φ).constraints ≤ D.sizeConstant *
      ((EncodedCNF.encode Φ.val).length + 1) *
        (((EncodedCNF.encode Φ.val).length + 1).size + 1) ^ D.sizeExponent :=
    le_trans (Nat.le_add_left _ _) hd
  calc (B.reduce (booleanFormula D Φ).val).edges.length
      ≤ B.sizeConstant * (booleanFormula D Φ).val.variables := he
    _ ≤ B.sizeConstant * (booleanSizeFactor D * (D.reduce Φ).constraints) :=
      Nat.mul_le_mul_left _ hv
    _ ≤ B.sizeConstant * (booleanSizeFactor D * (D.sizeConstant *
        ((EncodedCNF.encode Φ.val).length + 1) *
          (((EncodedCNF.encode Φ.val).length + 1).size + 1) ^ D.sizeExponent)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hc)
    _ = _ := by ring

/-- Total size of the T10 graph in terms of the input length `L = |encode Φ|`. -/
theorem t10_total_size (Φ : ValidFormula) :
    (t10Graph D B Φ).vertices + (t10Graph D B Φ).edges.length ≤
      3 * (Φ.val.variables + B.sizeConstant * booleanSizeFactor D * (D.sizeConstant *
        ((EncodedCNF.encode Φ.val).length + 1) *
          (((EncodedCNF.encode Φ.val).length + 1).size + 1) ^ D.sizeExponent) + 1) := by
  have h := B.output_total_size (booleanFormula D Φ).val (booleanFormula D Φ).property
    Φ.val.variables
  have hr := raw_edges_le D B Φ
  change (t10Graph D B Φ).vertices + (t10Graph D B Φ).edges.length ≤ _ at h
  omega

/-- The constant of `H_T10Size`. -/
def sizeC : ℕ := 8 + 3 * (B.sizeConstant * booleanSizeFactor D * D.sizeConstant *
  2 ^ D.sizeExponent)

/-- **`H_T10Size` discharged from the record fields.** For every valid `Φ`,
`vertices(t10Graph) + 2 ≤ sizeC·(|encode Φ|+1)^(e+1)`, `e = D.sizeExponent`.
Does not close a ledger row. -/
theorem t10_size_poly (Φ : ValidFormula) :
    (t10Graph D B Φ).vertices + 2 ≤
      sizeC D B * ((EncodedCNF.encode Φ.val).length + 1) ^ (D.sizeExponent + 1) := by
  set L := (EncodedCNF.encode Φ.val).length
  set e := D.sizeExponent
  set K := B.sizeConstant * booleanSizeFactor D * D.sizeConstant
  have htot := t10_total_size D B Φ
  have hn : Φ.val.variables ≤ L := SourceOriginalVariableCapture.original_n_le_input Φ.val
  have hs : (L + 1).size ≤ L + 1 := EncodedETHSourceComposition.nat_size_le_self _
  have hx : 1 ≤ L + 1 := by omega
  have hpow : ((L + 1).size + 1) ^ e ≤ (2 * (L + 1)) ^ e :=
    Nat.pow_le_pow_left (by omega) e
  have hkey : K * ((L + 1) * ((L + 1).size + 1) ^ e) ≤ K * 2 ^ e * (L + 1) ^ (e + 1) := by
    have : (L + 1) * ((L + 1).size + 1) ^ e ≤ 2 ^ e * (L + 1) ^ (e + 1) := by
      calc (L + 1) * ((L + 1).size + 1) ^ e ≤ (L + 1) * (2 * (L + 1)) ^ e :=
            Nat.mul_le_mul_left _ hpow
        _ = 2 ^ e * (L + 1) ^ (e + 1) := by rw [mul_pow, pow_succ]; ring
    calc K * ((L + 1) * ((L + 1).size + 1) ^ e) ≤ K * (2 ^ e * (L + 1) ^ (e + 1)) :=
          Nat.mul_le_mul_left _ this
      _ = K * 2 ^ e * (L + 1) ^ (e + 1) := by ring
  have hP : L + 1 ≤ (L + 1) ^ (e + 1) := by
    calc L + 1 = (L + 1) ^ 1 := (pow_one _).symm
      _ ≤ (L + 1) ^ (e + 1) := Nat.pow_le_pow_right hx (by omega)
  have h1 : 1 ≤ (L + 1) ^ (e + 1) := Nat.one_le_pow _ _ hx
  have hexp : B.sizeConstant * booleanSizeFactor D * (D.sizeConstant * (L + 1) *
      ((L + 1).size + 1) ^ e) = K * ((L + 1) * ((L + 1).size + 1) ^ e) := by
    simp only [K]; ring
  rw [hexp] at htot
  have hC : sizeC D B * (L + 1) ^ (e + 1) =
      8 * (L + 1) ^ (e + 1) + 3 * (K * 2 ^ e * (L + 1) ^ (e + 1)) := by
    simp only [sizeC, K, e]; ring
  rw [hC]
  have hv0 : (t10Graph D B Φ).vertices ≤
      3 * (Φ.val.variables + K * ((L + 1) * ((L + 1).size + 1) ^ e) + 1) := by omega
  nlinarith

theorem H_T10Size_holds : Shells.H_T10Size D B :=
  ⟨sizeC D B, D.sizeExponent + 1, t10_size_poly D B⟩

/-! ## T45 (`lem:source-size`) for the actual T10 graph -/

/-- `N.size ≤ ⌈log₂(N+2)⌉`. -/
theorem size_le_clog (N : ℕ) : N.size ≤ Nat.clog 2 (N + 2) := by
  apply Nat.size_le.mpr
  have h := Nat.le_pow_clog (by norm_num : 1 < 2) (N + 2)
  omega

/-- Input length of a sparse valid formula: `|encode Φ| + 1 ≤ (4 + 8cs)·N·(N.size+1)`. -/
theorem encode_length_sparse (Φ : ValidFormula) (cs : ℕ)
    (hsparse : Φ.val.clauses.length ≤ cs * Φ.val.variables) (hN : 1 ≤ Φ.val.variables) :
    (EncodedCNF.encode Φ.val).length + 1 ≤
      (4 + 8 * cs) * Φ.val.variables * (Φ.val.variables.size + 1) := by
  have hl := Sparsification.formula_length_log Φ.val Φ.property
  set N := Φ.val.variables
  set s := N.size
  set mc := Φ.val.clauses.length
  have hs : 1 ≤ s := Nat.size_pos.mpr (by omega)
  have hmc : mc * (6 * s + 8) ≤ cs * N * (6 * s + 8) := Nat.mul_le_mul_right _ hsparse
  have h1 : N + 3 ≤ 4 * N * (s + 1) := by nlinarith
  have h2 : cs * N * (6 * s + 8) ≤ 8 * cs * N * (s + 1) := by nlinarith
  have hexp : (4 + 8 * cs) * N * (s + 1) = 4 * N * (s + 1) + 8 * cs * N * (s + 1) := by ring
  rw [hexp]
  omega

/-- The quasilinear constant of T45 (depends only on `D`, `B`, `cs`). -/
def t45C (cs : ℕ) : ℕ :=
  3 * (2 + B.sizeConstant * booleanSizeFactor D * D.sizeConstant * (4 + 8 * cs) *
    ((4 + 8 * cs).size + 3) ^ D.sizeExponent)

/-- **T45 (`lem:source-size`) for the actual T10 graph, from the record fields.** With
`N = Φ.variables`, `n` vertices, `m` edges and `Δ = B.degreeBound`: `N ≤ m`, `2m ≤ Δ n`, and
for a sparse `Φ` (`clauses ≤ cs·N`, `N ≥ 1`), `n + m ≤ t45C·N·(N.size+1)^(e+1)`.
Does not close a ledger row. -/
theorem t45_relations (Φ : ValidFormula) :
    Φ.val.variables ≤ (t10Graph D B Φ).edges.length ∧
    2 * (t10Graph D B Φ).edges.length ≤ B.degreeBound * (t10Graph D B Φ).vertices ∧
    ∀ cs : ℕ, Φ.val.clauses.length ≤ cs * Φ.val.variables → 1 ≤ Φ.val.variables →
      (t10Graph D B Φ).vertices + (t10Graph D B Φ).edges.length ≤
        t45C D B cs * Φ.val.variables *
          (Φ.val.variables.size + 1) ^ (D.sizeExponent + 1) := by
  obtain ⟨_, hNm, hinc, hdeg, _, _, _⟩ := t10_source D B Φ
  refine ⟨hNm, ?_, ?_⟩
  · haveI : NeZero (t10Graph D B Φ).vertices := ⟨(t10_vertices_pos D B Φ).ne'⟩
    have h := Paper2.SourceDensityScheduleScratch.twice_edges_le_degree_vertices
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound hdeg
    simpa only [Fintype.card_fin] using h
  · intro cs hsparse hN
    set N := Φ.val.variables
    set s := N.size
    set e := D.sizeExponent
    set L := (EncodedCNF.encode Φ.val).length
    set K := 4 + 8 * cs
    have hs1 : 1 ≤ s := Nat.size_pos.mpr (by omega)
    have hL := encode_length_sparse Φ cs hsparse hN
    -- size of L+1
    have hsz : (L + 1).size + 1 ≤ (K.size + 3) * (s + 1) := by
      have h1 := Nat.size_le_size hL
      have h2 := EncodedETHSourceComposition.nat_size_mul_le (K * N) (s + 1)
      have h3 := EncodedETHSourceComposition.nat_size_mul_le K N
      have h4 := EncodedETHSourceComposition.nat_size_le_self (s + 1)
      nlinarith
    have hA : (L + 1) * ((L + 1).size + 1) ^ e ≤
        K * (K.size + 3) ^ e * (N * (s + 1) ^ (e + 1)) := by
      calc (L + 1) * ((L + 1).size + 1) ^ e
          ≤ (K * N * (s + 1)) * ((K.size + 3) * (s + 1)) ^ e :=
            Nat.mul_le_mul hL (Nat.pow_le_pow_left hsz e)
        _ = K * (K.size + 3) ^ e * (N * (s + 1) ^ (e + 1)) := by
            rw [mul_pow, pow_succ]; ring
    have htot := t10_total_size D B Φ
    set M := B.sizeConstant * booleanSizeFactor D * D.sizeConstant
    have hexp : B.sizeConstant * booleanSizeFactor D * (D.sizeConstant * (L + 1) *
        ((L + 1).size + 1) ^ e) = M * ((L + 1) * ((L + 1).size + 1) ^ e) := by
      simp only [M]; ring
    rw [hexp] at htot
    have hMA := Nat.mul_le_mul_left M hA
    have hNs : N ≤ N * (s + 1) ^ (e + 1) :=
      Nat.le_mul_of_pos_right N (Nat.one_le_pow _ _ (by omega))
    have hNs1 : 1 ≤ N * (s + 1) ^ (e + 1) := le_trans hN hNs
    have hC : t45C D B cs * N * (s + 1) ^ (e + 1) =
        3 * (2 * (N * (s + 1) ^ (e + 1)) +
          M * (K * (K.size + 3) ^ e * (N * (s + 1) ^ (e + 1)))) := by
      simp only [t45C, M, K, e]; ring
    rw [hC]
    omega

/-- The T24 shell form of T45: `n ≤ N·⌈log₂(N+2)⌉^(q+1)` beyond an explicit cutoff, where
`q = D.sizeExponent + 1`. -/
theorem t45_shell_form (cs : ℕ) :
    ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      2 ^ (2 ^ (D.sizeExponent + 1) * t45C D B cs) ≤ Φ.val.variables →
      (t10Graph D B Φ).vertices ≤
        Φ.val.variables * (Nat.clog 2 (Φ.val.variables + 2)) ^ (D.sizeExponent + 2) := by
  intro Φ hsparse hbig
  have hN : 1 ≤ Φ.val.variables := le_trans (Nat.one_le_two_pow) hbig
  obtain ⟨_, _, hsz⟩ := t45_relations D B Φ
  have h := hsz cs hsparse hN
  set N := Φ.val.variables
  set q := D.sizeExponent + 1
  set C := t45C D B cs
  set ℓ := Nat.clog 2 (N + 2)
  have hsℓ : N.size ≤ ℓ := size_le_clog N
  have hℓ1 : 1 ≤ ℓ := by
    have := Nat.size_pos.mpr (show 0 < N by omega)
    omega
  -- C·2^q ≤ ℓ from the cutoff
  have hCℓ : 2 ^ q * C ≤ ℓ := by
    have h1 : 2 ^ (2 ^ q * C) < N + 2 := by omega
    by_contra hcon
    rw [not_le] at hcon
    have h3 : 2 ^ ℓ ≤ 2 ^ (2 ^ q * C) := Nat.pow_le_pow_right (by norm_num) hcon.le
    have h4 : N + 2 ≤ 2 ^ ℓ := Nat.le_pow_clog (by norm_num) _
    omega
  have hpow : (N.size + 1) ^ q ≤ 2 ^ q * ℓ ^ q := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) q
  have hv : (t10Graph D B Φ).vertices ≤ C * N * (N.size + 1) ^ q := by omega
  calc (t10Graph D B Φ).vertices ≤ C * N * (N.size + 1) ^ q := hv
    _ ≤ C * N * (2 ^ q * ℓ ^ q) := Nat.mul_le_mul_left _ hpow
    _ = N * ((2 ^ q * C) * ℓ ^ q) := by ring
    _ ≤ N * (ℓ * ℓ ^ q) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hCℓ)
    _ = N * ℓ ^ (D.sizeExponent + 2) := by
        simp only [q]; rw [show D.sizeExponent + 2 = (D.sizeExponent + 1) + 1 from rfl, pow_succ]
        ring

end Paper2.Unit4Shell.T10Size
