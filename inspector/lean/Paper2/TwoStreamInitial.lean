import Paper2.TwoStreamLiveStops
import Paper2.SourceSupportInitialCore

/-!
# Initial protocol on the original two-stream restriction

Frozen v12, Section 5, `res:two-stream`, lines 134--201. The original
retained rows and the two separately tagged column families determine
the state. Extending its protocol to ambient carriers only retracts to
genuine retained inputs; it preserves cost and all retained entries.
-/

namespace Paper2.TwoStreamInitial

open Workspace.Types.Protocol ProjectedSupportFrontier

variable {Rw Raw S J Ω F : Type*} {s : ℕ}

def retainedColumns (O : Set Ω) (G : Set F) : Set (Ω ⊕ F) :=
  (Sum.inl '' O) ∪ (Sum.inr '' G)

@[simp] theorem inl_mem (O : Set Ω) (G : Set F) (c : Ω) :
    Sum.inl c ∈ retainedColumns O G ↔ c ∈ O := by
  simp [retainedColumns]

@[simp] theorem inr_mem (O : Set Ω) (G : Set F) (f : F) :
    Sum.inr f ∈ retainedColumns O G ↔ f ∈ G := by
  simp [retainedColumns]

/-- Retractions use actual retained labels, so no default value changes
the matrix on which the protocol was given. The transpose makes original
row messages the Bob messages followed by the checked scheduled walk. -/
noncomputable def ambientProtocol (R : Set Rw) (O : Set Ω) (G : Set F)
    (row0 : R) (col0 : retainedColumns O G)
    (P : Protocol R (retainedColumns O G) Bool) : Protocol (Ω ⊕ F) Rw Bool :=
  Workspace.UpperBound.Protocol.comap
    (SourceSupportInitial.columnRetraction (retainedColumns O G) col0)
    (SourceSupportInitial.columnRetraction R row0)
    (Workspace.UpperBound.Protocol.transpose P)

@[simp] theorem ambientProtocol_cost (R : Set Rw) (O : Set Ω) (G : Set F)
    (row0 : R) (col0 : retainedColumns O G)
    (P : Protocol R (retainedColumns O G) Bool) :
    (ambientProtocol R O G row0 col0 P).cost = P.cost := by
  simp only [ambientProtocol, Workspace.UpperBound.Protocol.comap_cost,
    Workspace.UpperBound.Protocol.transpose_cost]

theorem ambientProtocol_eval (R : Set Rw) (O : Set Ω) (G : Set F)
    (row0 : R) (col0 : retainedColumns O G)
    (P : Protocol R (retainedColumns O G) Bool)
    (r : R) (c : retainedColumns O G) :
    (ambientProtocol R O G row0 col0 P).eval c.val r.val = P.eval r c := by
  simp only [ambientProtocol, Workspace.UpperBound.Protocol.comap_eval,
    Workspace.UpperBound.Protocol.transpose_eval,
    SourceSupportInitial.columnRetraction_retained]

theorem ambientProtocol_computesOn
    (M : Rw → (Ω ⊕ F) → Bool) (R : Set Rw) (O : Set Ω) (G : Set F)
    (row0 : R) (col0 : retainedColumns O G)
    (P : Protocol R (retainedColumns O G) Bool)
    (hP : P.Computes (fun r c => M r.val c.val)) :
    ∀ r ∈ R, ∀ c ∈ retainedColumns O G,
      (ambientProtocol R O G row0 col0 P).eval c r = M r c := by
  intro r hr c hc
  exact (ambientProtocol_eval R O G row0 col0 P ⟨r, hr⟩ ⟨c, hc⟩).trans
    (hP ⟨r, hr⟩ ⟨c, hc⟩)

noncomputable def initial (R : Set Rw) (O : Set Ω) (G : Set F)
    (row0 : R) (col0 : retainedColumns O G)
    (P : Protocol R (retainedColumns O G) Bool)
    (star : Fin s) (supports : Fin s → Finset Raw) :
    State (Ω ⊕ F) Rw (Fin s) Raw where
  protocol := ambientProtocol R O G row0 col0 P
  columns := R
  coordinates := Finset.univ
  attachments := {star}
  support := supports

theorem initial_counts (R : Set Rw) (O : Set Ω) (G : Set F)
    (row0 : R) (col0 : retainedColumns O G)
    (P : Protocol R (retainedColumns O G) Bool)
    (star : Fin s) (supports : Fin s → Finset Raw) :
    (initial R O G row0 col0 P star supports).coordinates.card = s ∧
    (initial R O G row0 col0 P star supports).attachments.card = 1 ∧
    (initial R O G row0 col0 P star supports).attachments ⊆
      (initial R O G row0 col0 P star supports).coordinates := by
  simp [initial]

theorem initial_reaches (R : Set Rw) (O : Set Ω) (G : Set F)
    (row0 : R) (col0 : retainedColumns O G)
    (P : Protocol R (retainedColumns O G) Bool)
    (star : Fin s) (supports : Fin s → Finset Raw) (input : Raw → Rw)
    (hR : ∀ i, ∀ w ∈ supports i, input w ∈ R) :
    ∀ i ∈ (initial R O G row0 col0 P star supports).coordinates,
      ∀ w ∈ (initial R O G row0 col0 P star supports).support i,
        input w ∈ (initial R O G row0 col0 P star supports).columns := by
  intro i _ w hw
  exact hR i w hw

theorem initial_ordinary_entries
    (M : Rw → (Ω ⊕ F) → Bool) (T : S → J → Bool)
    (bin : Rw → Fin s) (selector : Rw → S) (Φ : Ω → Fin s → J)
    (hordinary : ∀ r c, M r (.inl c) = T (selector r) (Φ c (bin r)))
    (R : Set Rw) (O : Set Ω) (G : Set F)
    (row0 : R) (col0 : retainedColumns O G)
    (P : Protocol R (retainedColumns O G) Bool)
    (hP : P.Computes (fun r c => M r.val c.val))
    (star : Fin s) (supports : Fin s → Finset Raw) (input : Raw → Rw)
    (hR : ∀ i, ∀ w ∈ supports i, input w ∈ R)
    (hbin : ∀ i, ∀ w ∈ supports i, bin (input w) = i) :
    ∀ i ∈ (initial R O G row0 col0 P star supports).coordinates,
      ∀ w ∈ (initial R O G row0 col0 P star supports).support i, ∀ c ∈ O,
      (initial R O G row0 col0 P star supports).protocol.eval (.inl c) (input w) =
        T (selector (input w)) (Φ c i) := by
  intro i _ w hw c hc
  change (ambientProtocol R O G row0 col0 P).eval (.inl c) (input w) = _
  rw [ambientProtocol_computesOn M R O G row0 col0 P hP
    (input w) (hR i w hw) (.inl c) ((inl_mem O G c).mpr hc),
    hordinary, hbin i w hw]

theorem rows_nonempty_of_floor [Fintype S]
    (μ : FiniteLaw S) (selector : Rw → S) (input : Raw → Rw)
    (R : Set Rw) (support : Finset Raw) (t : ℝ) (ht : 0 < t)
    (hm : t ≤ ProjectedSupportStep.mass μ (fun w => selector (input w)) support)
    (hR : ∀ w ∈ support, input w ∈ R) : R.Nonempty := by
  have hne : support.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he, ProjectedSupportStep.mass_empty] at hm
    linarith
  obtain ⟨w, hw⟩ := hne
  exact ⟨input w, hR w hw⟩

theorem columns_nonempty_of_mass [Fintype Ω]
    (κ : FiniteLaw Ω) (O : Set Ω) (G : Set F)
    (hO : 0 < κ.prob (· ∈ O)) : (retainedColumns O G).Nonempty := by
  have hne : O.Nonempty := by
    by_contra hn
    have he := Set.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Set.mem_empty_iff_false, FiniteLaw.prob_false] at hO
    exact (lt_irrefl _ hO)
  obtain ⟨c, hc⟩ := hne
  exact ⟨.inl c, (inl_mem O G c).mpr hc⟩

/-- The original displayed slack, including zero ordinary deletion,
forces the strict density used when selecting an ordinary column child. -/
theorem ordinary_density [Fintype Ω] (κ : FiniteLaw Ω) (O : Set Ω)
    (q : ℕ) (hq : 0 < q) (x ε δ : ℝ) (hx : 0 ≤ x)
    (hO : 1 - ε ≤ κ.prob (· ∈ O)) (hδ : δ ≤ 1)
    (hslack : 2 * q * x + 5 * ε + 2 / q ≤ δ) :
    0 ≤ ε ∧ ε < 1 / 5 ∧ (4 / 5 : ℝ) < κ.prob (· ∈ O) := by
  have hp := κ.prob_le_one (· ∈ O)
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have ht : 0 ≤ 2 * (q : ℝ) * x := by positivity
  have hd : (0 : ℝ) < 2 / q := by positivity
  constructor
  · linarith
  constructor <;> linarith

end Paper2.TwoStreamInitial

#print axioms Paper2.TwoStreamInitial.ambientProtocol_computesOn
#print axioms Paper2.TwoStreamInitial.initial_ordinary_entries
#print axioms Paper2.TwoStreamInitial.rows_nonempty_of_floor
#print axioms Paper2.TwoStreamInitial.ordinary_density
