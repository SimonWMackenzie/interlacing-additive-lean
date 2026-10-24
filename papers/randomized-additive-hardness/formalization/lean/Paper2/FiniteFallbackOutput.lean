import Paper2.FiniteFallbackIdentity
import Paper2.YaoMaterializationTable

/-!
# Finite fallback output selected by an actual finite graph decision

This is the graph-case selector and literal row-major table from frozen v12
Appendix D. It assumes no colourability answer or gap certificate. It does
not prove that a failed public schedule implies a fixed bound on graph size,
or charge exhaustive search and matrix printing in a machine model.
-/

namespace Paper2.FiniteFallbackOutput

open Workspace.Types.Protocol Workspace.Types.CommComplexity
open FiniteFallbackIdentity YaoMaterialization

/-- Exact finite three-colourability proposition for a Fin-indexed graph. -/
def ThreeColourable {v e : ℕ} (edge : Fin e → Bool → Fin v) : Prop :=
  ∃ colour : Fin v → Fin 3,
    ∀ z : Fin e, colour (edge z false) ≠ colour (edge z true)

instance threeColourableDecidable {v e : ℕ} (edge : Fin e → Bool → Fin v) :
    Decidable (ThreeColourable edge) := by
  unfold ThreeColourable
  exact Fintype.decidableExistsFintype

/-- The frozen special case `k=1` has one row and two columns; for `k≥2`
the output is `2^(k-1)` square. The unused `k=0` branch is a zero singleton. -/
def rows : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | k + 2 => 2 ^ (k + 1)

def cols : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | k + 2 => 2 ^ (k + 1)

def hardMatrix : (k : ℕ) → Fin (rows k) → Fin (cols k) → Bool
  | 0 => fun _ _ => false
  | 1 => oneRow
  | k + 2 => identityMatrix (2 ^ (k + 1))

/-- Finite-graph choice, made by the exhaustive decidable proposition itself. -/
def fallbackMatrix {v e : ℕ} (edge : Fin e → Bool → Fin v) (k : ℕ) :
    Fin (rows k) → Fin (cols k) → Bool :=
  if ThreeColourable edge then fun _ _ => false else hardMatrix k

/-- A literal row-major Boolean output, with dimensions announced by `k`. -/
def fallbackTable {v e : ℕ} (edge : Fin e → Bool → Fin v) (k : ℕ) :
    SerializedTable (rows k) (cols k) :=
  tabulate (fallbackMatrix edge k)

/-- The fallback announces zero additive allowance, as in Appendix D. -/
def budget : ℕ := 0

theorem fallbackTable_matrix {v e : ℕ} (edge : Fin e → Bool → Fin v) (k : ℕ) :
    (fallbackTable edge k).matrix = fallbackMatrix edge k := by
  funext i j
  exact tabulate_matrix _ i j

theorem fallbackTable_bits_length {v e : ℕ} (edge : Fin e → Bool → Fin v)
    (k : ℕ) : (fallbackTable edge k).bits.length = rows k * cols k :=
  tabulate_length _

theorem zero_D (mX mY : ℕ) :
    D (fun (_ : Fin mX) (_ : Fin mY) => false) = 0 := by
  apply Nat.le_zero.mp
  apply Nat.sInf_le
  exact ⟨Protocol.leaf false, rfl, by intro _ _; rfl⟩

/-- The YES output has exact communication cost zero, without a certificate
passed into the constructor. -/
theorem fallback_yes_D {v e : ℕ} (edge : Fin e → Bool → Fin v) (k : ℕ)
    (h : ThreeColourable edge) : D (fallbackTable edge k).matrix = 0 := by
  rw [fallbackTable_matrix]
  simp only [fallbackMatrix, if_pos h]
  exact zero_D _ _

/-- For a graph that is not three-colourable, the exact identity branch has
cost `k` whenever `k≥2`. -/
theorem fallback_no_D {v e : ℕ} (edge : Fin e → Bool → Fin v)
    (k : ℕ) (hk : 2 ≤ k) (h : ¬ ThreeColourable edge) :
    D (fallbackTable edge k).matrix = k := by
  rw [fallbackTable_matrix]
  simp only [fallbackMatrix, if_neg h]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  simpa only [hardMatrix, Nat.add_sub_cancel_right] using
    identity_D (j + 2) (by omega)

/-- Frozen `k=1` exception, with the one-row `[0,1]` matrix. -/
theorem fallback_no_one_D {v e : ℕ} (edge : Fin e → Bool → Fin v)
    (h : ¬ ThreeColourable edge) :
    D (fallbackTable edge 1).matrix = 1 := by
  rw [fallbackTable_matrix]
  simpa only [fallbackMatrix, if_neg h, hardMatrix] using oneRow_D

/-- Exact dimensions and hence exact output bit count for every `k≥2`. -/
theorem fallback_bits_length_ge_two {v e : ℕ} (edge : Fin e → Bool → Fin v)
    (k : ℕ) (hk : 2 ≤ k) :
    (fallbackTable edge k).bits.length = 2 ^ (k - 1) * 2 ^ (k - 1) := by
  rw [fallbackTable_bits_length]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  simp [rows, cols]

theorem fallback_bits_length_one {v e : ℕ} (edge : Fin e → Bool → Fin v) :
    (fallbackTable edge 1).bits.length = 2 := by
  simp [fallbackTable_bits_length, rows, cols]

/-- An explicit exponential output-size ceiling, valid in both specified
positive-level branches. This is a bit-count statement, not runtime. -/
theorem fallback_bits_length_le {v e : ℕ} (edge : Fin e → Bool → Fin v)
    (k : ℕ) (hk : 1 ≤ k) :
    (fallbackTable edge k).bits.length ≤ 2 ^ (2 * k) := by
  by_cases h1 : k = 1
  · subst k
    rw [fallback_bits_length_one]
    norm_num
  · have hk2 : 2 ≤ k := by omega
    rw [fallback_bits_length_ge_two edge k hk2, ← pow_add]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)

#print axioms threeColourableDecidable
#print axioms fallbackTable_matrix
#print axioms fallback_yes_D
#print axioms fallback_no_D
#print axioms fallback_no_one_D
#print axioms fallback_bits_length_ge_two
#print axioms fallback_bits_length_le

-- Small kernel/VM smoke checks that the finite branch actually evaluates.
#eval decide (ThreeColourable (v := 1) (e := 0)
  (fun z _ => Fin.elim0 z))
#eval decide (ThreeColourable (v := 1) (e := 1)
  (fun _ _ => (0 : Fin 1)))
#eval (fallbackTable (v := 1) (e := 1)
  (fun _ _ => (0 : Fin 1)) 2).bits
#eval (fallbackTable (v := 1) (e := 1)
  (fun _ _ => (0 : Fin 1)) 1).bits

end Paper2.FiniteFallbackOutput
