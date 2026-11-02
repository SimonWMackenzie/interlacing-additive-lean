import Paper2.RecursiveSamplingSource

/-!
# Uniform graph-label choices on the exact source item carrier

Frozen v12 Appendix D and Section 4. A public enumeration of graph vertices
is an input encoding, not an enumeration of any recursive product carrier.
Group and vertex/auxiliary labels are drawn separately and then reassociated
by the same equivalence as `SourceLawBinding.matrixColumnLaw`.
-/

namespace Paper2.RecursiveSampling

open SourceMatrix RecursiveSamplingProgram RecursiveSamplingLaws

variable {X V : Type*} [Fintype V] [Nonempty V] {q₁ q₂ s : ℕ}

def vertex (order : Fin (Fintype.card V) ≃ V) : Program V :=
  Program.map order (Program.uniform (Fintype.card V) Fintype.card_pos)

def vertexLabels (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s) :
    Program (Fin (4 * s) × V) :=
  prod (Program.uniform (4 * s) (by omega)) (vertex order)

def auxiliaryLabels (s : ℕ) (hs : 4 ≤ s) : Program (Fin (4 * s) × Fin (s - 3)) :=
  prod (Program.uniform (4 * s) (by omega)) (Program.uniform (s - 3) (by omega))

def graphRows [NeZero q₁] (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    (p : Program X) : Program (RawRow q₁ q₂ s X (SourceConstruction.Items s V)) := by
  letI : NeZero s := ⟨by omega⟩
  exact Program.map (SourceLawBinding.rawRowEquiv q₁ q₂ s X V)
    (rows (vertexLabels order hs) (auxiliaryLabels s hs) p)

theorem maxDraws_vertex (order : Fin (Fintype.card V) ≃ V) :
    Program.maxDraws (vertex order) = 1 := by simp [vertex]

theorem maxDraws_vertexLabels_le (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s) :
    Program.maxDraws (vertexLabels order hs) ≤ 2 := by
  apply (maxDraws_prod_le _ _).trans
  change (Program.uniform (4 * s) _).maxDraws + (vertex order).maxDraws ≤ 2
  rw [Program.maxDraws_uniform, maxDraws_vertex]

theorem maxDraws_auxiliaryLabels_le (s : ℕ) (hs : 4 ≤ s) :
    Program.maxDraws (auxiliaryLabels s hs) ≤ 2 := by
  apply (maxDraws_prod_le _ _).trans
  change (Program.uniform (4 * s) _).maxDraws + (Program.uniform (s - 3) _).maxDraws ≤ 2
  rw [Program.maxDraws_uniform, Program.maxDraws_uniform]

theorem generates_vertex (order : Fin (Fintype.card V) ≃ V) :
    Generates (vertex order) (PositiveRationalLaw.uniform V).toFiniteLaw := by
  letI : NeZero (Fintype.card V) := ⟨Fintype.card_ne_zero⟩
  exact generates_uniform_equiv (Fintype.card V) order

theorem generates_vertexLabels (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s) :
    Generates (vertexLabels order hs) (by
      letI : NeZero (4 * s) := ⟨by omega⟩
      exact (PositiveRationalLaw.uniform (Fin (4 * s) × V)).toFiniteLaw) := by
  letI : NeZero (4 * s) := ⟨by omega⟩
  have h := generates_rational_prod (generates_uniform (4 * s)) (generates_vertex order)
  rw [uniform_prod] at h
  exact h

theorem generates_auxiliaryLabels (s : ℕ) (hs : 4 ≤ s) :
    Generates (auxiliaryLabels s hs) (by
      letI : NeZero (4 * s) := ⟨by omega⟩
      letI : NeZero (s - 3) := ⟨by omega⟩
      exact (PositiveRationalLaw.uniform (Fin (4 * s) × Fin (s - 3))).toFiniteLaw) := by
  letI : NeZero (4 * s) := ⟨by omega⟩
  letI : NeZero (s - 3) := ⟨by omega⟩
  have h := generates_rational_prod (generates_uniform (4 * s)) (generates_uniform (s - 3))
  rw [uniform_prod] at h
  exact h

theorem generates_graphRows [Fintype X] [NeZero q₁]
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    {p : Program X} {μ : PositiveRationalLaw X} (hp : Generates p μ.toFiniteLaw) :
    Generates (graphRows (q₁ := q₁) (q₂ := q₂) order hs p)
      (SourceLawBinding.matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw := by
  letI : NeZero s := ⟨by omega⟩
  letI : NeZero (4 * s) := ⟨by omega⟩
  letI : NeZero (s - 3) := ⟨by omega⟩
  exact generates_relabel
    (generates_rows (generates_vertexLabels order hs) (generates_auxiliaryLabels s hs) hp)
    (SourceLawBinding.rawRowEquiv q₁ q₂ s X V)

theorem maxDraws_graphRows_le [NeZero q₁] [NeZero q₂]
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s) (p : Program X) :
    Program.maxDraws (graphRows (q₁ := q₁) (q₂ := q₂) order hs p) ≤
      3 + q₂ * (1 + Program.maxDraws p) := by
  letI : NeZero s := ⟨by omega⟩
  simp only [graphRows, Program.maxDraws_map]
  exact maxDraws_rows_le _ _ _
    (maxDraws_vertexLabels_le order hs) (maxDraws_auxiliaryLabels_le s hs)

end Paper2.RecursiveSampling
