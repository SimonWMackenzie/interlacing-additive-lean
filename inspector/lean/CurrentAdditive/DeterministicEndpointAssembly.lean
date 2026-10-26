import CurrentAdditive.DeterministicEndpointPadding

/-! One same-state consumer of the checked iteration recurrence and semantic
square padding. The presentation fields are the narrow physical-interface
facts still to be supplied by the actual CodeD constructor. -/

namespace CurrentAdditive.DeterministicEndpointAssembly

open CurrentAdditive.DeterministicIteration
open CurrentAdditive.DeterministicEndpointPadding
open Paper2.SquarePadding
open Workspace.Types.CommComplexity

universe u v

variable {Graph : Type u} {State : Type v}

/-- The only table bridge used here: each actual stage has one ordinary
Boolean rectangle, its communication cost is the state's cost, its entries
are charged by the complete encoding, and padding can reach public `N`. -/
structure TablePresentation (C : Construction Graph State) (N : ℕ) where
  rows : State → ℕ
  cols : State → ℕ
  table : (R : State) → Fin (rows R) → Fin (cols R) → Bool
  rows_pos : ∀ R, 0 < rows R
  cols_pos : ∀ R, 0 < cols R
  exact_cost : ∀ R, D (table R) = C.cost R
  entries_le_encoding : ∀ R, rows R * cols R ≤ C.size R
  public_side : ∀ R, N ≤ max (rows R) (cols R)

def paddedTable (C : Construction Graph State) (N : ℕ)
    (P : TablePresentation C N) (R : State) :
    Fin (side (P.rows R) (P.cols R)) →
      Fin (side (P.rows R) (P.cols R)) → Bool :=
  matrix (P.rows_pos R) (P.cols_pos R) (P.table R)

/-- A single iterated state has the manuscript's universal, separate YES,
and separate NO conclusions after semantic power-of-two padding. There is
no global NO premise and no manufactured protocol-cost certificate. -/
theorem padded_conditional_reduction
    (C : Construction Graph State) (G : Graph)
    (Yes No : Graph → Prop) (N A C₁ C₀ d₀ h k : ℕ)
    (hN : 2 ≤ N) (hA : 2 ≤ A) (hC₀ : C₁ + 1 ≤ C₀)
    (V : ValidContract C G)
    (U : UniversalContract C G d₀ h)
    (Y : Yes G → YesContract C G d₀ h)
    (H : No G → NoContract C G d₀ h)
    (R : ResourceContract C G N A C₁)
    (P : TablePresentation C N) :
    let F := state C G k
    let S := side (P.rows F) (P.cols F)
    let M := paddedTable C N P F
    D M ≤ budget d₀ h k + k ∧
    (Yes G → D M ≤ budget d₀ h k) ∧
    (No G → D M = budget d₀ h k + k ∧ C.profile G F) ∧
    N ≤ S ∧ (∃ e, S = 2^e) ∧
    S^2 ≤ N^((2*C₁+2)*A^k) ∧
    totalStepTime C G k ≤ N^(C₀*A^k) := by
  let F := state C G k
  have hbase := conditional_reduction C G Yes No N A C₁ C₀ d₀ h k
    hN hA hC₀ V U Y H R
  have hD : D (paddedTable C N P F) = C.cost F := by
    rw [paddedTable, D_matrix, P.exact_cost]
  have hpad := padded_literal_table (P.rows_pos F) (P.cols_pos F)
    (P.public_side F) (P.table F)
  have hsize : C.size F ≤ N^(C₁*A^k) := by
    calc
      C.size F ≤ envelope C N F := by dsimp [envelope]; omega
      _ ≤ N^(C₁*A^k) := growth_iteration C G N A C₁ k V R
  have hSq : (side (P.rows F) (P.cols F))^2 ≤
      N^((2*C₁+2)*A^k) :=
    padded_entries_le_public_power (P.rows F) (P.cols F)
      (C.size F) N A C₁ k (P.rows_pos F) (P.cols_pos F)
      hN hA (P.entries_le_encoding F) hsize
  dsimp only
  refine ⟨?_, ?_, ?_, hpad.2.1, hpad.2.2, hSq, hbase.2.2.2.2⟩
  · rw [hD]
    exact hbase.1
  · intro hy
    rw [hD]
    exact hbase.2.1 hy
  · intro hn
    rw [hD]
    exact hbase.2.2.1 hn

/-- Absorb the square writer's quadratic output length into one larger
public exponent. Physical running time of that writer remains to be bound
against this same exponent by CodeD. -/
theorem padded_conditional_one_exponent
    (C : Construction Graph State) (G : Graph)
    (Yes No : Graph → Prop) (N A C₁ C₀ d₀ h k : ℕ)
    (hN : 2 ≤ N) (hA : 2 ≤ A) (hC₀ : 2*C₁+2 ≤ C₀)
    (V : ValidContract C G)
    (U : UniversalContract C G d₀ h)
    (Y : Yes G → YesContract C G d₀ h)
    (H : No G → NoContract C G d₀ h)
    (R : ResourceContract C G N A C₁)
    (P : TablePresentation C N) :
    let F := state C G k
    let S := side (P.rows F) (P.cols F)
    let M := paddedTable C N P F
    D M ≤ budget d₀ h k + k ∧
    (Yes G → D M ≤ budget d₀ h k) ∧
    (No G → D M = budget d₀ h k + k ∧ C.profile G F) ∧
    N ≤ S ∧ (∃ e, S = 2^e) ∧
    S^2 ≤ N^(C₀*A^k) ∧
    totalStepTime C G k ≤ N^(C₀*A^k) := by
  have hb := padded_conditional_reduction C G Yes No N A C₁ C₀ d₀ h k
    hN hA (by omega : C₁+1 ≤ C₀) V U Y H R P
  dsimp only at hb ⊢
  rcases hb with ⟨hu, hy, hno, hside, hpow, hsize, hclock⟩
  have hexp : (2*C₁+2)*A^k ≤ C₀*A^k :=
    Nat.mul_le_mul_right _ hC₀
  exact ⟨hu, hy, hno, hside, hpow,
    hsize.trans (Nat.pow_le_pow_right (by omega : 0 < N) hexp), hclock⟩

#print axioms padded_conditional_reduction
#print axioms padded_conditional_one_exponent

end CurrentAdditive.DeterministicEndpointAssembly
