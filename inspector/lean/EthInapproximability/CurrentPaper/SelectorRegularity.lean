import EthInapproximability.ParameterizedNP.TerminalStateRealization

/-!
# Exact fibres of a distinct-coordinate selector

Source: frozen v8 `A-stage4-details.tex`, the last paragraph of the proof of
`lem:paper-protected-preparation`, invoking `eq:paper-local-capacity` from
`03-parameterized-construction.tex`. Selecting the `q₁ + 3` distinct column
coordinates does not decrease the common tuple density.

Only the generic finite `RegularOn` geometry is reused. There is no matrix
lower-bound, graph-witness, balancedness or communication-cost assumption.
The degree is proved to be exactly `|Y| ^ (n - k)` for an embedding
`Fin k ↪ Fin n`, including `k = 0` and `k = n`.
-/

namespace EthInapproximability.CurrentPaper.SelectorRegularity

open EthInapproximability.ParameterizedNP.TerminalStateRealization

variable {Y : Type*} [Fintype Y] {n k : ℕ}

/-- Retain the coordinates selected by an embedding, in their given order. -/
def select (e : Fin k ↪ Fin n) (γ : Fin n → Y) : Fin k → Y :=
  fun i => γ (e i)

open Classical in
/-- Every selected tuple has exactly one free value for each unused coordinate. -/
theorem select_regular (e : Fin k ↪ Fin n) :
    RegularOn (Finset.univ : Finset (Fin n → Y)) (select e)
      (Fintype.card Y ^ (n - k)) := by
  classical
  intro c
  let K := {i : Fin n // i ∉ Set.range e}
  have hcard : Fintype.card K = n - k := by
    simp only [K, Fintype.card_subtype_compl, Fintype.card_range,
      Fintype.card_fin]
  calc
    (Finset.univ.filter (fun γ => select e γ = c)).card =
        (Finset.univ : Finset (K → Y)).card := by
      apply Finset.card_bij (fun γ _ => fun i : K => γ i.val)
      · intro γ hγ
        exact Finset.mem_univ _
      · intro γ hγ δ hδ heq
        have hγc := (Finset.mem_filter.mp hγ).2
        have hδc := (Finset.mem_filter.mp hδ).2
        funext i
        by_cases hi : i ∈ Set.range e
        · obtain ⟨j, rfl⟩ := hi
          exact (congrFun hγc j).trans (congrFun hδc j).symm
        · exact congrFun heq ⟨i, hi⟩
      · intro z hz
        let γ : Fin n → Y := fun i =>
          if hi : i ∈ Set.range e then c hi.choose else z ⟨i, hi⟩
        have hγ : select e γ = c := by
          funext i
          have hi : e i ∈ Set.range e := ⟨i, rfl⟩
          have hchoice : hi.choose = i := e.injective hi.choose_spec
          simp only [select, γ, dif_pos hi, hchoice]
        refine ⟨γ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hγ⟩, ?_⟩
        funext i
        exact dif_neg i.property
    _ = Fintype.card Y ^ (n - k) := by
      rw [Finset.card_univ, Fintype.card_fun, hcard]

/-- Nonempty alphabets give a positive selector degree, with no guard on `k`. -/
theorem select_degree_pos [Nonempty Y] :
    0 < Fintype.card Y ^ (n - k) :=
  Nat.pow_pos Fintype.card_pos

open Classical in
/-- Selecting distinct coordinates preserves the fraction of retained tuples. -/
theorem select_density [Nonempty Y] (e : Fin k ↪ Fin n)
    (C : Finset (Fin n → Y)) :
    (C.card : ℝ) / (Fintype.card Y : ℝ) ^ n ≤
      ((C.image (select e)).card : ℝ) / (Fintype.card Y : ℝ) ^ k := by
  have h := regularOn_density_transfer (select_regular (Y := Y) e)
    (select_degree_pos (Y := Y) (n := n) (k := k)) (Finset.subset_univ C)
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow] using h

open Classical in
/-- Fractional lower bounds transfer to the very same projected tuple set. -/
theorem select_density_ge [Nonempty Y] (e : Fin k ↪ Fin n)
    (C : Finset (Fin n → Y)) {ρ : ℝ}
    (hC : ρ ≤ (C.card : ℝ) / (Fintype.card Y : ℝ) ^ n) :
    ρ ≤ ((C.image (select e)).card : ℝ) / (Fintype.card Y : ℝ) ^ k :=
  hC.trans (select_density e C)

end EthInapproximability.CurrentPaper.SelectorRegularity
