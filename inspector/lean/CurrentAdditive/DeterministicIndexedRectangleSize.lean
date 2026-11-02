import CurrentAdditive.IndexedActualConstruction
import CurrentAdditive.DeterministicEndpointNumeric
import CurrentAdditive.DeterministicETHPhysicalSquare
import CurrentAdditive.DeterministicETHIndexedSeedEndpoint
/-! The public indexed resource recurrence bounds the exact encoded rectangle,
including row count, column count, and the threshold header. No rectangle
producer or machine clock is assumed. -/

namespace CurrentAdditive.DeterministicIndexedRectangleSize

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicAdmissibility
open CurrentAdditive.DeterministicIteration
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.IndexedSemanticIteration
open CurrentAdditive.IndexedExecutableStepRecovery
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite
open Paper2

set_option maxHeartbeats 1000000

universe u

theorem numbered_rectangle_length_le_stage_size {N : ℕ}
    (R : Stage.{u} N) (e : ExplicitNumberings R) (b : ℕ) :
    (encodeInstance (numberedRectangle R e b)).length ≤
      5*R.encodingSize + 2*b + 3 := by
  let r := rows R
  let c := cols R
  let S := R.encodingSize
  have hr : 0 < r := rows_pos R
  have hc : 0 < c := cols_pos R
  have hentries : r*c ≤ S := R.entries_le_encoding
  have hrS : r ≤ S := by
    have hh : r ≤ r*c := Nat.le_mul_of_pos_right _ hc
    omega
  have hcS : c ≤ S := by
    have hh : c ≤ r*c := Nat.le_mul_of_pos_left _ hr
    omega
  have hrbits : r.bits.length ≤ r := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hcbits : c.bits.length ≤ c := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hbbits : b.bits.length ≤ b := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  rw [numberedRectangle_encoded_length]
  dsimp [r, c, S] at *
  omega

theorem indexed_rectangle_length_le_public_power
    (v e L : ℕ) [NeZero v] [NeZero (s L)] [NeZero (s L-3)]
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L),
      StepInputs (V := Fin v) (E := Fin e) L R T)
    (numberings : ∀ R : Stage (N L), ExplicitNumberings R)
    (G : IndexedSemanticIteration.Graph (Fin v) (Fin e))
    (A C₁ C₀ k b : ℕ) (hA : 2 ≤ A)
    (hC₀ : C₁+1 ≤ C₀)
    (hresource : ResourceContract
      (indexedActualConstruction v e L T inputs) G (N L) A C₁) :
    let C := indexedActualConstruction v e L T inputs
    let R := state C G k
    (encodeInstance (numberedRectangle R (numberings R) b)).length ≤
      5 * (N L)^(C₀*A^k) + 2*b + 3 := by
  let C := indexedActualConstruction v e L T inputs
  let R := state C G k
  have hN : 2 ≤ N L := by
    have h4 := N_ge_four L (by have hh := T.large; omega : 2 ≤ L)
    omega
  have hsize := (size_and_steps_at_public_exponent C G
    (N L) A C₁ C₀ k hN hA hC₀
    (indexedActual_valid v e L T inputs G) hresource).1
  have hstage : R.encodingSize ≤ (N L)^(C₀*A^k) := hsize
  have hword := numbered_rectangle_length_le_stage_size R (numberings R) b
  dsimp only [C, R] at hstage hword ⊢
  omega

private theorem succ_le_pow_of_two_le (n k : ℕ) (hn : 2 ≤ n) :
    k+1 ≤ n^k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have hh := Nat.mul_le_mul_left n ih
      nlinarith

theorem dynamic_threshold_le_public_power (L a C₀ k : ℕ)
    (hL : 2004 ≤ L) (ha : 1 ≤ a) (hC₀ : 2 ≤ C₀) :
    2*budget (Paper2.LookupSeed.exponent L+1) (h L) k+k ≤
      (N L)^(C₀*(2^a)^k) := by
  let n := N L
  have hn : 4 ≤ n := N_ge_four L (by omega)
  have hLplus : L+1 ≤ s L := L_plus_one_le_s L (by omega)
  have h65 : 65*s L ≤ n := coefficient_mul_s_le_N 65 L (by omega)
  have h13 : 13*s L ≤ n :=
    (Nat.mul_le_mul_right (s L) (by omega : 13 ≤ 65)).trans h65
  have hseedlog : Paper2.LookupSeed.exponent L ≤ 64*(L+1) := by
    unfold Paper2.LookupSeed.exponent
    apply (Nat.clog_le_iff_le_pow (by decide : 1 < (2:ℕ))).2
    exact Nat.le_of_lt Nat.lt_two_pow_self
  have hd₀ : Paper2.LookupSeed.exponent L+1 ≤ n := by
    have hh : 64*(L+1)+1 ≤ 65*s L := by nlinarith
    omega
  have hquarter : 4*((L+3)/4) ≤ L+3 := Nat.mul_div_le (L+3) 4
  have hh : h L ≤ n := by
    have h13L : h L ≤ 13*(L+1) := by unfold h; omega
    have h13s : 13*(L+1) ≤ 13*s L := Nat.mul_le_mul_left 13 hLplus
    exact (h13L.trans h13s).trans h13
  have hkh : k*h L ≤ k*n := Nat.mul_le_mul_left k hh
  have hbudget : 2*budget (Paper2.LookupSeed.exponent L+1) (h L) k+k ≤
      3*n*(k+1) := by
    dsimp [budget]
    nlinarith
  have hnsq : 3*n ≤ n^2 := by nlinarith
  have hpowk : k+1 ≤ n^k := succ_le_pow_of_two_le n k (by omega)
  have hlarge : 3*n*(k+1) ≤ n^(k+2) := by
    calc
      3*n*(k+1) ≤ n^2*n^k := Nat.mul_le_mul hnsq hpowk
      _ = n^(k+2) := by rw [pow_add]; ring
  have hA : 2 ≤ 2^a := by
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) ha
    simpa using hp
  have hAk : k+1 ≤ (2^a)^k := succ_le_pow_of_two_le (2^a) k hA
  have hexp : k+2 ≤ C₀*(2^a)^k := by nlinarith
  exact hbudget.trans (hlarge.trans
    (Nat.pow_le_pow_right (by omega : 1 ≤ n) hexp))

theorem t10_dynamic_rectangle_length_le_public_power
    (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
    (Φ : ValidFormula) (L : ℕ)
    [NeZero (t10Graph D B Φ).vertices]
    [NeZero (s L)] [NeZero (s L-3)] [NeZero (q₁ L)]
    [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]
    (hL : L = publicLog (max (t10Graph D B Φ).vertices Φ.val.variables)
      B.degreeBound (sourceGap D B))
    (T : Schedule (Fin (t10Graph D B Φ).vertices)
      (Fin (t10Graph D B Φ).edges.length) L)
    (inputs : ∀ R : Stage (N L),
      StepInputs (V := Fin (t10Graph D B Φ).vertices)
        (E := Fin (t10Graph D B Φ).edges.length) L R T)
    (numberings : ∀ R : Stage (N L), ExplicitNumberings R)
    (a C₁ C₀ : ℕ) (ha : 1 ≤ a) (hC₀ : 2*C₁+2 ≤ C₀)
    (hresource : ResourceContract
      (indexedActualConstruction (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length L T inputs)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ)) (N L) (2^a) C₁) :
    let G := CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
      (t10Graph_valid D B Φ)
    let C := indexedActualConstruction (t10Graph D B Φ).vertices
      (t10Graph D B Φ).edges.length L T inputs
    let P := indexedActualNumberedTables (t10Graph D B Φ).vertices
      (t10Graph D B Φ).edges.length L T inputs numberings
    let k := CurrentAdditive.DeterministicEndpointNumeric.ethIterations a Φ.val.variables
    let R := state C G k
    let b := 2*budget (Paper2.LookupSeed.exponent L+1) (h L) k+k
    (encodeInstance
      (CurrentAdditive.DeterministicETHPhysicalSquare.rectangleInstance
        (P.table R) b)).length ≤
      5 * (N (publicLog
        (max (t10Graph D B Φ).vertices Φ.val.variables)
        B.degreeBound (sourceGap D B)))^(C₀*(2^a)^k) + 2*b + 3 := by
  let G := CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
    (t10Graph_valid D B Φ)
  let C := indexedActualConstruction (t10Graph D B Φ).vertices
    (t10Graph D B Φ).edges.length L T inputs
  let P := indexedActualNumberedTables (t10Graph D B Φ).vertices
    (t10Graph D B Φ).edges.length L T inputs numberings
  let k := CurrentAdditive.DeterministicEndpointNumeric.ethIterations a Φ.val.variables
  let R := state C G k
  let b := 2*budget (Paper2.LookupSeed.exponent L+1) (h L) k+k
  have hA : 2 ≤ 2^a := by
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) ha
    simpa using hh
  have hC : C₁+1 ≤ C₀ := by omega
  have hh := indexed_rectangle_length_le_public_power
    (t10Graph D B Φ).vertices (t10Graph D B Φ).edges.length
    L T inputs numberings G (2^a) C₁ C₀ k b hA hC hresource
  simpa only [C, P, R, G, k, b, hL] using hh

theorem t10_dynamic_rectangle_length_le_ten_power
    (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
    (Φ : ValidFormula) (L : ℕ)
    [NeZero (t10Graph D B Φ).vertices]
    [NeZero (s L)] [NeZero (s L-3)] [NeZero (q₁ L)]
    [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]
    (hL : L = publicLog (max (t10Graph D B Φ).vertices Φ.val.variables)
      B.degreeBound (sourceGap D B))
    (T : Schedule (Fin (t10Graph D B Φ).vertices)
      (Fin (t10Graph D B Φ).edges.length) L)
    (inputs : ∀ R : Stage (N L),
      StepInputs (V := Fin (t10Graph D B Φ).vertices)
        (E := Fin (t10Graph D B Φ).edges.length) L R T)
    (numberings : ∀ R : Stage (N L), ExplicitNumberings R)
    (a C₁ C₀ : ℕ) (ha : 1 ≤ a) (hC₀ : 2*C₁+2 ≤ C₀)
    (hresource : ResourceContract
      (indexedActualConstruction (t10Graph D B Φ).vertices
        (t10Graph D B Φ).edges.length L T inputs)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
        (t10Graph_valid D B Φ)) (N L) (2^a) C₁) :
    let G := CanonicalEdgeTape.graphEdge (t10Graph D B Φ)
      (t10Graph_valid D B Φ)
    let C := indexedActualConstruction (t10Graph D B Φ).vertices
      (t10Graph D B Φ).edges.length L T inputs
    let P := indexedActualNumberedTables (t10Graph D B Φ).vertices
      (t10Graph D B Φ).edges.length L T inputs numberings
    let k := CurrentAdditive.DeterministicEndpointNumeric.ethIterations a Φ.val.variables
    let R := state C G k
    let b := 2*budget (Paper2.LookupSeed.exponent L+1) (h L) k+k
    (encodeInstance
      (CurrentAdditive.DeterministicETHPhysicalSquare.rectangleInstance
        (P.table R) b)).length ≤
      10 * (N (publicLog
        (max (t10Graph D B Φ).vertices Φ.val.variables)
        B.degreeBound (sourceGap D B)))^(C₀*(2^a)^k) := by
  let k := CurrentAdditive.DeterministicEndpointNumeric.ethIterations a Φ.val.variables
  let b := 2*budget (Paper2.LookupSeed.exponent L+1) (h L) k+k
  let B₀ := (N L)^(C₀*(2^a)^k)
  have hsource := t10_dynamic_rectangle_length_le_public_power
    D B Φ L hL T inputs numberings a C₁ C₀ ha hC₀ hresource
  have hthreshold : b ≤ B₀ :=
    dynamic_threshold_le_public_power L a C₀ k T.large ha (by omega)
  have hB₀ : 1 ≤ B₀ := Nat.one_le_pow _ _ (N_pos L)
  have hB_eq : B₀ =
      (N (publicLog (max (t10Graph D B Φ).vertices Φ.val.variables)
        B.degreeBound (sourceGap D B)))^(C₀*(2^a)^k) := by
    rw [← hL]
  dsimp only at hsource ⊢
  rw [← hB_eq] at hsource ⊢
  dsimp only [b, k] at hthreshold hsource ⊢
  omega

#print axioms numbered_rectangle_length_le_stage_size
#print axioms indexed_rectangle_length_le_public_power
#print axioms dynamic_threshold_le_public_power
#print axioms t10_dynamic_rectangle_length_le_public_power
#print axioms t10_dynamic_rectangle_length_le_ten_power

end CurrentAdditive.DeterministicIndexedRectangleSize
