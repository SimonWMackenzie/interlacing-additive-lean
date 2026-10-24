import EthInapproximability.CurrentPaper.Construction
import EthInapproximability.CurrentPaper.MatrixStage4Codes
import EthInapproximability.CurrentPaper.MatrixMaterialization

/-!
# Physical ordered enumeration of the current protected duplicate

Frozen v8 anchors: `A-stage4-details.tex`, `lem:paper-weighted-blowup` and
`tab:paper-protected-blowup`; `B-effectivity-details.tex`,
`thm:paper-materialization`.  These lists order labels by support group,
underlying label, copy index, and (for columns) the final uniform copy index.
The list index is an explicit ordinal address; this module does not claim a
bit-machine runtime bound for constructing the addresses or entries.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedEnumeration

open Construction WeightedDuplication MatrixMaterialization MatrixStage4Codes

universe u

variable {X T V B Ω Δ : Type u}
variable [Fintype X] [Fintype T] [Fintype V] [Fintype B]
variable [Fintype Ω] [Fintype Δ]

/-- An ordered support group, with every actual copy index physically present. -/
def rowGroup (i : Fin 4) {n : ℕ}
    (e : rowSupport X T V B i ≃ Fin n) :
    List (Rows X T V B) :=
  (List.ofFn fun j => e.symm j).flatMap fun x =>
    List.ofFn fun copy : Fin (copies (rowSupport X T V B) rowWeight i) =>
      ⟨i, (x, copy)⟩

/-- The two column groups, before the uniform factor. -/
def columnGroup (i : Fin 2) {n : ℕ}
    (e : columnSupport Ω Δ i ≃ Fin n) :
    List (Carrier (columnSupport Ω Δ) columnWeight) :=
  (List.ofFn fun j => e.symm j).flatMap fun x =>
    List.ofFn fun copy : Fin (copies (columnSupport Ω Δ) columnWeight i) =>
      ⟨i, (x, copy)⟩

/-- All four row supports of the manuscript, in its public order. -/
def rowLabels
    (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B)) : List (Rows X T V B) :=
  rowGroup 0 eX ++ rowGroup 1 eT ++ rowGroup 2 eV ++ rowGroup 3 eB

/-- The 182:2 support groups, followed by `Sdup` uniform copies per label. -/
def columnLabels
    (eΩ : Ω ≃ Fin (Fintype.card Ω))
    (eΔ : Δ ≃ Fin (Fintype.card Δ)) (Sdup : ℕ) :
    List (Columns Ω Δ Sdup) :=
  (columnGroup 0 eΩ ++ columnGroup 1 eΔ).flatMap fun c =>
    List.ofFn fun uniform : Fin Sdup => (c, uniform)

@[simp] theorem rowGroup_length (i : Fin 4) {n : ℕ}
    (e : rowSupport X T V B i ≃ Fin n) :
    (rowGroup i e).length = n * copies (rowSupport X T V B) rowWeight i := by
  simp [rowGroup, List.sum_ofFn]

@[simp] theorem columnGroup_length (i : Fin 2) {n : ℕ}
    (e : columnSupport Ω Δ i ≃ Fin n) :
    (columnGroup i e).length =
      n * copies (columnSupport Ω Δ) columnWeight i := by
  simp [columnGroup, List.sum_ofFn]

@[simp] theorem rowLabels_length
    (eX : X ≃ Fin (Fintype.card X)) (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V)) (eB : B ≃ Fin (Fintype.card B)) :
    (rowLabels eX eT eV eB).length = Fintype.card (Rows X T V B) := by
  simp [rowLabels, Fin.sum_univ_succ, Fintype.card_prod,
    Fintype.card_fin, card_rowSupport]

@[simp] theorem columnLabels_length
    (eΩ : Ω ≃ Fin (Fintype.card Ω)) (eΔ : Δ ≃ Fin (Fintype.card Δ))
    (Sdup : ℕ) :
    (columnLabels eΩ eΔ Sdup).length = Fintype.card (Columns Ω Δ Sdup) := by
  simp [columnLabels, Fin.sum_univ_succ,
    Fintype.card_prod, Fintype.card_fin, card_columnSupport]
  ring

/-- Literal ordinal decoders for the two transpose-oriented carriers of `N`. -/
def decodeRow (eΩ : Ω ≃ Fin (Fintype.card Ω))
    (eΔ : Δ ≃ Fin (Fintype.card Δ)) (Sdup : ℕ)
    (i : Fin (Fintype.card (Columns Ω Δ Sdup))) : Columns Ω Δ Sdup :=
  (columnLabels eΩ eΔ Sdup).get
    (i.cast (columnLabels_length eΩ eΔ Sdup).symm)

def decodeColumn (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B))
    (j : Fin (Fintype.card (Rows X T V B))) : Rows X T V B :=
  (rowLabels eX eT eV eB).get
    (j.cast (rowLabels_length eX eT eV eB).symm)

/-- The physical ordinal entry is exactly the protected matrix's entry. -/
def entry (H : X → Ω → Bool) (iT : T → X) (iV : V → X)
    (iB : B → X) (iD : Δ → Ω) (Sdup : ℕ)
    (eX : X ≃ Fin (Fintype.card X)) (eT : T ≃ Fin (Fintype.card T))
    (eV : V ≃ Fin (Fintype.card V)) (eB : B ≃ Fin (Fintype.card B))
    (eΩ : Ω ≃ Fin (Fintype.card Ω)) (eΔ : Δ ≃ Fin (Fintype.card Δ))
    (i : Fin (Fintype.card (Columns Ω Δ Sdup)))
    (j : Fin (Fintype.card (Rows X T V B))) : Bool :=
  H (rowForget iT iV iB (decodeColumn eX eT eV eB j))
    (columnForget iD (decodeRow eΩ eΔ Sdup i))

theorem entry_eq_transposedMatrix (H : X → Ω → Bool)
    (iT : T → X) (iV : V → X) (iB : B → X) (iD : Δ → Ω)
    (Sdup : ℕ) (eX : X ≃ Fin (Fintype.card X))
    (eT : T ≃ Fin (Fintype.card T)) (eV : V ≃ Fin (Fintype.card V))
    (eB : B ≃ Fin (Fintype.card B)) (eΩ : Ω ≃ Fin (Fintype.card Ω))
    (eΔ : Δ ≃ Fin (Fintype.card Δ))
    (i : Fin (Fintype.card (Columns Ω Δ Sdup)))
    (j : Fin (Fintype.card (Rows X T V B))) :
    entry H iT iV iB iD Sdup eX eT eV eB eΩ eΔ i j =
      transposedMatrix H iT iV iB iD Sdup
        (decodeRow eΩ eΔ Sdup i) (decodeColumn eX eT eV eB j) := rfl

end EthInapproximability.CurrentPaper.MatrixWeightedEnumeration
