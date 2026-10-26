import Paper2.A3Wrap
import Paper2.TotalFiniteResources
import Paper2.SourceDensitySchedule

/-!
# Unit 3 endpoint (H_A3 closure), segment 1: the H_A3 input-size bound

Lane `owner:a-h-a3-assembly-3` (private, 26 September 2026). Pure arithmetic.

Discharges the named premise `Paper2.A3Assembly.Wrap.InputSize Δ γ C E` of the frozen
`a-h-a3-assembly-owner-1` wrapper `Wrap.H_A3_of_local`, with `C = 4Δ + 9`, `E = 160`,
for EVERY `Δ, γ` (no positivity needed here):

* `|encode ![a, b, c]| = 2(|a| + |b| + |c|) + 3` (admitted `BitMachineBankCodec.encode_length`);
* `|EncodedGraph.encode g| ≤ n + 2 + m(4n + 4)` (admitted `EncodedGraph.encode_length_upper`);
* `2m ≤ Δ n` from the degree bound (admitted
  `SourceDensityScheduleScratch.twice_edges_le_degree_vertices`, parallel labels counted);
* `|tapeBits t| = inputBits` on both branches of `select` (the scheduled tape is the exact-length
  subtype `TapeList`, the fallback tape word is `[]`; the same case split as the admitted
  `selected_exact_lengths`, which needs extra hypotheses we do not require here);
* `inputBits ≤ (n+2)^(160(k+1))` (admitted `TotalFiniteResourcesScratch.selected_announced_counts_le`,
  exact reuse, needs `1 ≤ k`).
-/

namespace Paper2.A3Assembly.Size

open EthInapproximability.CurrentPaper
open Paper2

/-- Every tape of the selected law has exactly `inputBits` bits, on both branches, with no
graph hypothesis. -/
theorem tapeBits_length {n m : ℕ} (hn : 0 < n) (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) :
    ∀ t : (TotalFiniteConstructorScratch.select hn edge Δ γ k).Tape,
      ((TotalFiniteConstructorScratch.select hn edge Δ γ k).tapeBits t).length =
        (TotalFiniteConstructorScratch.select hn edge Δ γ k).inputBits := by
  by_cases hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ
  · letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    rw [TotalFiniteConstructorScratch.select_good hn edge Δ γ k hc]
    intro t
    exact t.property
  · rw [TotalFiniteConstructorScratch.select_bad hn edge Δ γ k hc]
    intro t
    rfl

/-- The selected tape word is within the admitted resource bound. -/
theorem tapeBits_length_le {n m : ℕ} (hn : 0 < n) (edge : Fin m → Bool → Fin n) (Δ : ℕ)
    (γ : ℚ) (k : ℕ) (hk : 1 ≤ k)
    (t : (TotalFiniteConstructorScratch.select hn edge Δ γ k).Tape) :
    ((TotalFiniteConstructorScratch.select hn edge Δ γ k).tapeBits t).length ≤
      (n + 2) ^ (160 * (k + 1)) := by
  rw [tapeBits_length hn edge Δ γ k t]
  exact (TotalFiniteResourcesScratch.selected_announced_counts_le hn edge Δ γ k hk).2

/-- Edge count from the degree bound: `2 m ≤ Δ n`. -/
theorem twice_edges_le (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (Δ : ℕ)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ) :
    2 * g.edges.length ≤ Δ * g.vertices := by
  haveI : NeZero g.vertices := ⟨Nat.ne_of_gt hn⟩
  have h := SourceDensityScheduleScratch.twice_edges_le_degree_vertices
    (CanonicalEdgeTape.graphEdge g hg) Δ hdeg
  simpa only [Fintype.card_fin] using h

private theorem k_le_pow (n k : ℕ) : k ≤ (n + 2) ^ (160 * (k + 1)) := by
  have h1 : k < 2 ^ k := Nat.lt_two_pow_self
  have h2 : 2 ^ k ≤ (n + 2) ^ k := Nat.pow_le_pow_left (by omega) k
  have h3 : (n + 2) ^ k ≤ (n + 2) ^ (160 * (k + 1)) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

private theorem sq_le_pow (n k : ℕ) : (n + 2) ^ 2 ≤ (n + 2) ^ (160 * (k + 1)) :=
  Nat.pow_le_pow_right (by omega) (by omega)

/-- Pure arithmetic of the input size. -/
private theorem size_arith (n m Δ k G W X : ℕ)
    (hG : G ≤ n + 2 + m * (4 * n + 4)) (hm : 2 * m ≤ Δ * n)
    (hW : W ≤ X) (hk : k ≤ X) (hY : (n + 2) ^ 2 ≤ X) :
    2 * (G + k + W) + 3 ≤ (4 * Δ + 9) * X := by
  have hY' : (n + 2) * (n + 2) ≤ X := by simpa only [pow_two] using hY
  have hmn : m * (4 * n + 4) ≤ 2 * Δ * ((n + 2) * (n + 2)) := by
    have : m * (4 * n + 4) = (2 * m) * (2 * n + 2) := by ring
    rw [this]
    calc (2 * m) * (2 * n + 2) ≤ (Δ * n) * (2 * n + 2) := Nat.mul_le_mul_right _ hm
      _ ≤ 2 * Δ * ((n + 2) * (n + 2)) := by nlinarith
  have hmX : m * (4 * n + 4) ≤ 2 * Δ * X :=
    hmn.trans (Nat.mul_le_mul_left _ hY')
  have hn2 : n + 2 ≤ X := by nlinarith
  have hX1 : 1 ≤ X := by omega
  nlinarith

/-- **Segment 1.** The named premise `InputSize` of `Wrap.H_A3_of_local`, with `C = 4Δ + 9`,
`E = 160`, for every `Δ` and `γ`. -/
theorem inputSize (Δ : ℕ) (γ : ℚ) : Wrap.InputSize Δ γ (4 * Δ + 9) 160 := by
  intro g hg hn k hk _hsurj hdeg t
  rw [BitMachineBankCodec.encode_length]
  simp only [Wrap.inputBank, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, List.length_replicate]
  have hG := EncodedGraph.encode_length_upper g hg
  have hm := twice_edges_le g hg hn Δ hdeg
  have hW := tapeBits_length_le hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k hk t
  have hkX := k_le_pow g.vertices k
  have hY := sq_le_pow g.vertices k
  exact size_arith g.vertices g.edges.length Δ k _ _ _ hG hm hW hkX hY

end Paper2.A3Assembly.Size

#print axioms Paper2.A3Assembly.Size.tapeBits_length
#print axioms Paper2.A3Assembly.Size.tapeBits_length_le
#print axioms Paper2.A3Assembly.Size.twice_edges_le
#print axioms Paper2.A3Assembly.Size.inputSize
