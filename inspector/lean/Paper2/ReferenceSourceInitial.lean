import Paper2.ReferenceInitial
import Paper2.ReferencePrefix
import Paper2.ReferenceSchedule
import Paper2.ReferenceCertificateTree
import Paper2.SourceSupportInitialCore

/-!
# Original-source initialization for the reference-certificate frontier

Frozen Paper 2 v12, restoration lines 193--201 and 250--271. The rows,
columns, and protocol here are those of one actual first interlace. The
ambient extension preserves the retained rectangle exactly; the family uses
literal unrestricted-tag row slices and the original normalized raw law.
-/

namespace Paper2.ReferenceSourceInitial

open Workspace.Types.Protocol SourceMatrix SourceLaws

variable {X Y V A : Type*} [Fintype X] [Fintype Y] [Fintype V] [Fintype A]
  [Nonempty V] [Nonempty A]
  {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]

abbrev Rows := Fin w × TaggedColumn q₁ q₂ s Y
abbrev Columns := Fin w → RawRow q₁ q₂ s X (V ⊕ A)

def sourceMatrix (base : X → Y → Bool)
    (activity : (V ⊕ A) → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y) :
    Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w) →
      Columns (X := X) (V := V) (A := A) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w) → Bool :=
  fullInterlace (N base activity ξ₀) w

def input (i : Fin w) (Z : RawColumn q₁ q₂ s Y) :
    Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w) :=
  (i, .unrestricted Z)

@[simp] theorem source_reference_entry (base : X → Y → Bool)
    (activity : (V ⊕ A) → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (i : Fin w) (Z : RawColumn q₁ q₂ s Y)
    (ys : Columns (X := X) (V := V) (A := A)
      (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)) :
    sourceMatrix base activity ξ₀ (input i Z) ys =
      raw base activity (ys i) Z := rfl

private theorem event_nonempty_of_prob_pos {T : Type*} [Fintype T]
    (κ : FiniteLaw T) (E : Set T) (h : 0 < κ.prob (· ∈ E)) : E.Nonempty := by
  by_contra hn
  have hnone : ∀ z, z ∉ E := by
    intro z hz
    exact hn ⟨z, hz⟩
  have he : (fun z : T => z ∈ E) = fun _ => False := by
    funext z
    exact propext ⟨fun hz => hnone z hz, False.elim⟩
  rw [he, FiniteLaw.prob_false] at h
  exact (not_lt_of_ge le_rfl) h

theorem retained_rows_nonempty (ν : PositiveRationalLaw Y) (hw : 0 < w)
    (R0 : Set (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (η x : ℝ) (hx : 0 ≤ x)
    (hR0 : 1 - η / (16 * w) ≤ (ReferenceInitial.firstRowLaw ν hw).prob (· ∈ R0))
    (hmargin : 2 * w * x + η / (16 * (127 / 128 : ℝ)) < 1) :
    R0.Nonempty := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hsmall : η < 16 * (w : ℝ) := by
    have hpos : 0 ≤ 2 * (w : ℝ) * x := by positivity
    have hg : η < 16 * (127 / 128 : ℝ) := by
      have hh : η / (16 * (127 / 128 : ℝ)) < 1 := by linarith
      apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 16 * (127 / 128 : ℝ))).mp at hh
      simpa using hh
    have hwr : (1 : ℝ) ≤ w := by exact_mod_cast hw
    nlinarith
  have hp : 0 < (ReferenceInitial.firstRowLaw ν hw).prob (· ∈ R0) := by
    have hd : η / (16 * (w : ℝ)) < 1 :=
      (div_lt_iff₀ (by positivity : (0 : ℝ) < 16 * (w : ℝ))).2 (by simpa using hsmall)
    linarith
  exact event_nonempty_of_prob_pos _ R0 hp

theorem retained_columns_nonempty (μ : PositiveRationalLaw X)
    (Y' : Set (Columns (X := X) (V := V) (A := A)
      (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (θ : ℝ) (hθ : 0 < θ)
    (hY : θ ≤ ((rowLaw (V := V) (A := A) μ q₁ q₂ s).iid w).toFiniteLaw.prob
      (· ∈ Y')) : Y'.Nonempty :=
  event_nonempty_of_prob_pos _ Y' (lt_of_lt_of_le hθ hY)

noncomputable def ambientProtocol
    (R0 : Set (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (Y' : Set (Columns (X := X) (V := V) (A := A)
      (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (row0 : R0) (col0 : Y') (P : Protocol R0 Y' Bool) :
    Protocol (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w))
      (Columns (X := X) (V := V) (A := A)
        (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)) Bool :=
  Workspace.UpperBound.Protocol.comap
    (SourceSupportInitial.columnRetraction R0 row0)
    (SourceSupportInitial.columnRetraction Y' col0) P

theorem ambientProtocol_cost (R0 : Set (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (Y' : Set (Columns (X := X) (V := V) (A := A)
      (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (row0 : R0) (col0 : Y') (P : Protocol R0 Y' Bool) :
    (ambientProtocol R0 Y' row0 col0 P).cost = P.cost := by
  simp [ambientProtocol, Workspace.UpperBound.Protocol.comap_cost]

theorem ambientProtocol_eval (R0 : Set (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (Y' : Set (Columns (X := X) (V := V) (A := A)
      (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (row0 : R0) (col0 : Y') (P : Protocol R0 Y' Bool)
    (row : R0) (col : Y') :
    (ambientProtocol R0 Y' row0 col0 P).eval row.val col.val = P.eval row col := by
  simp [ambientProtocol, Workspace.UpperBound.Protocol.comap_eval,
    SourceSupportInitial.columnRetraction_retained]

noncomputable def initialFamily
    (R0 : Set (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (E0 : Finset (Fin w)) :
    ReferenceCertificates.Family (Fin w) (RawColumn q₁ q₂ s Y) where
  active := Finset.univ \ E0
  unsplit := Finset.univ \ E0
  support i := by
    classical
    exact Finset.univ.filter (fun Z => Z ∈ ReferenceInitial.referenceSupport R0 i)

theorem initialFamily_valid
    (R0 : Set (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (E0 : Finset (Fin w)) :
    (initialFamily R0 E0).unsplit ⊆ (initialFamily R0 E0).active := by
  rfl

theorem initialFamily_reaches
    (R0 : Set (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (E0 : Finset (Fin w)) :
    ∀ i ∈ (initialFamily R0 E0).active,
      ∀ Z ∈ (initialFamily R0 E0).support i,
        input i Z ∈ R0 := by
  intro i _ Z hZ
  simpa [initialFamily, ReferenceInitial.referenceSupport, input] using hZ

theorem initialFamily_units
    (R0 : Set (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (E0 : Finset (Fin w)) :
    ReferenceCertificates.units (initialFamily R0 E0) = 2 * (w - E0.card) := by
  simp [ReferenceCertificates.units, initialFamily, Finset.card_sdiff]
  omega

theorem initialFamily_floor (ν : PositiveRationalLaw Y) (hw : 0 < w)
    (R0 : Set (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (E0 : Finset (Fin w)) (η x : ℝ)
    (hR0 : 1 - η / (16 * w) ≤ (ReferenceInitial.firstRowLaw ν hw).prob (· ∈ R0))
    (hmargin : 2 * w * x + η / (16 * (127 / 128 : ℝ)) < 1) :
    ∀ i ∈ (initialFamily R0 E0).active,
      ReferenceSchedule.floor w x 0 ≤
        SourceSupportStep.mass (rawLaw ν q₁ q₂ s).toFiniteLaw
          ((initialFamily R0 E0).support i) := by
  intro i _
  rw [ReferenceSchedule.floor_zero]
  simpa [initialFamily, SourceSupportStep.mass] using
    ReferenceInitial.reference_initial_floor ν hw R0 η x hR0 hmargin i

/-- The padded total protocol and the actual initial certificate family. -/
noncomputable def initialState
    (R0 : Set (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (Y' : Set (Columns (X := X) (V := V) (A := A)
      (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (row0 : R0) (col0 : Y') (P : Protocol R0 Y' Bool)
    (E0 : Finset (Fin w)) (r : ℕ) :
    ReferenceCertificateTree.State
      (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w))
      (Columns (X := X) (V := V) (A := A)
        (q₁ := q₁) (q₂ := q₂) (s := s) (w := w))
      (Fin w) (RawColumn q₁ q₂ s Y) where
  protocol := ReferencePrefix.padAlicePrefix r (ambientProtocol R0 Y' row0 col0 P)
  rows := R0
  family := initialFamily R0 E0

theorem initialState_correct
    (base : X → Y → Bool)
    (activity : (V ⊕ A) → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (R0 : Set (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (Y' : Set (Columns (X := X) (V := V) (A := A)
      (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (row0 : R0) (col0 : Y') (P : Protocol R0 Y' Bool)
    (hP : P.Computes (fun row col => sourceMatrix base activity ξ₀ row.val col.val))
    (E0 : Finset (Fin w)) (r : ℕ)
    (row : R0) (col : Y') :
    (initialState R0 Y' row0 col0 P E0 r).protocol.eval row.val col.val =
      sourceMatrix base activity ξ₀ row.val col.val := by
  change (ReferencePrefix.padAlicePrefix r (ambientProtocol R0 Y' row0 col0 P)).eval
    row.val col.val = _
  rw [ReferencePrefix.padAlicePrefix_eval, ambientProtocol_eval]
  exact hP row col

theorem initialState_cost
    (R0 : Set (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (Y' : Set (Columns (X := X) (V := V) (A := A)
      (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (row0 : R0) (col0 : Y') (P : Protocol R0 Y' Bool)
    (E0 : Finset (Fin w)) (C r : ℕ) (hC : 1 ≤ C)
    (hPcost : P.cost ≤ C + r - 1) :
    (initialState R0 Y' row0 col0 P E0 r).protocol.cost ≤ C + r - 1 := by
  change (ReferencePrefix.padAlicePrefix r (ambientProtocol R0 Y' row0 col0 P)).cost ≤ _
  have hp := ReferencePrefix.padAlicePrefix_cost_le r (ambientProtocol R0 Y' row0 col0 P)
  rw [ambientProtocol_cost] at hp
  omega

theorem initialState_reaches
    (R0 : Set (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (Y' : Set (Columns (X := X) (V := V) (A := A)
      (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (row0 : R0) (col0 : Y') (P : Protocol R0 Y' Bool)
    (E0 : Finset (Fin w)) (r : ℕ) :
    ∀ i ∈ (initialState R0 Y' row0 col0 P E0 r).family.active,
      ∀ Z ∈ (initialState R0 Y' row0 col0 P E0 r).family.support i,
        input i Z ∈ (initialState R0 Y' row0 col0 P E0 r).rows := by
  exact initialFamily_reaches R0 E0

theorem initialState_floor (ν : PositiveRationalLaw Y) (hw : 0 < w)
    (R0 : Set (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (Y' : Set (Columns (X := X) (V := V) (A := A)
      (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (row0 : R0) (col0 : Y') (P : Protocol R0 Y' Bool)
    (E0 : Finset (Fin w)) (r : ℕ) (η x : ℝ)
    (hR0 : 1 - η / (16 * w) ≤ (ReferenceInitial.firstRowLaw ν hw).prob (· ∈ R0))
    (hmargin : 2 * w * x + η / (16 * (127 / 128 : ℝ)) < 1) :
    ∀ i ∈ (initialState R0 Y' row0 col0 P E0 r).family.active,
      ReferenceSchedule.floor w x 0 ≤
        SourceSupportStep.mass (rawLaw ν q₁ q₂ s).toFiniteLaw
          ((initialState R0 Y' row0 col0 P E0 r).family.support i) := by
  exact initialFamily_floor ν hw R0 E0 η x hR0 hmargin

theorem initialState_units
    (R0 : Set (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (Y' : Set (Columns (X := X) (V := V) (A := A)
      (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (row0 : R0) (col0 : Y') (P : Protocol R0 Y' Bool)
    (E0 : Finset (Fin w)) (r : ℕ) :
    ReferenceCertificates.units (initialState R0 Y' row0 col0 P E0 r).family =
      2 * (w - E0.card) := initialFamily_units R0 E0

/-- Source-facing initialization: defaults are derived from the retained
positive-mass events, never supplied as extra source data. -/
theorem exists_initial_state
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool)
    (activity : (V ⊕ A) → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (R0 : Set (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (Y' : Set (Columns (X := X) (V := V) (A := A)
      (q₁ := q₁) (q₂ := q₂) (s := s) (w := w)))
    (P : Protocol R0 Y' Bool)
    (hP : P.Computes (fun row col => sourceMatrix base activity ξ₀ row.val col.val))
    (hw : 0 < w) (C r : ℕ) (hC : 1 ≤ C)
    (hPcost : P.cost ≤ C + r - 1)
    (η x θ : ℝ) (hx : 0 ≤ x) (hθ : 0 < θ)
    (hR0 : 1 - η / (16 * w) ≤ (ReferenceInitial.firstRowLaw ν hw).prob (· ∈ R0))
    (hY : θ ≤ ((rowLaw (V := V) (A := A) μ q₁ q₂ s).iid w).toFiniteLaw.prob
      (· ∈ Y'))
    (hmargin : 2 * w * x + η / (16 * (127 / 128 : ℝ)) < 1)
    (E0 : Finset (Fin w)) :
    ∃ row0 : R0, ∃ col0 : Y', ∃ st : ReferenceCertificateTree.State
        (Rows (Y := Y) (q₁ := q₁) (q₂ := q₂) (s := s) (w := w))
        (Columns (X := X) (V := V) (A := A)
          (q₁ := q₁) (q₂ := q₂) (s := s) (w := w))
        (Fin w) (RawColumn q₁ q₂ s Y),
      st = initialState R0 Y' row0 col0 P E0 r ∧
      st.rows = R0 ∧
      st.family = initialFamily R0 E0 ∧
      st.family.unsplit ⊆ st.family.active ∧
      ReferenceCertificates.units st.family = 2 * (w - E0.card) ∧
      (∀ i ∈ st.family.active, ∀ Z ∈ st.family.support i, input i Z ∈ st.rows) ∧
      (∀ i ∈ st.family.active,
        ReferenceSchedule.floor w x 0 ≤
          SourceSupportStep.mass (rawLaw ν q₁ q₂ s).toFiniteLaw
            (st.family.support i)) ∧
      (∀ row ∈ R0, ∀ col ∈ Y', st.protocol.eval row col =
        sourceMatrix base activity ξ₀ row col) ∧
      st.protocol.cost ≤ C + r - 1 := by
  classical
  obtain ⟨row0, hrow0⟩ := retained_rows_nonempty ν hw R0 η x hx hR0 hmargin
  obtain ⟨col0, hcol0⟩ := retained_columns_nonempty μ Y' θ hθ hY
  let st := initialState R0 Y' ⟨row0, hrow0⟩ ⟨col0, hcol0⟩ P E0 r
  refine ⟨⟨row0, hrow0⟩, ⟨col0, hcol0⟩, st, rfl, rfl, rfl,
    initialFamily_valid R0 E0,
    initialState_units R0 Y' ⟨row0, hrow0⟩ ⟨col0, hcol0⟩ P E0 r,
    initialState_reaches R0 Y' ⟨row0, hrow0⟩ ⟨col0, hcol0⟩ P E0 r,
    initialState_floor ν hw R0 Y' ⟨row0, hrow0⟩ ⟨col0, hcol0⟩ P E0 r η x
      hR0 hmargin, ?_,
    initialState_cost R0 Y' ⟨row0, hrow0⟩ ⟨col0, hcol0⟩ P E0 C r hC hPcost⟩
  intro row hrow col hcol
  exact initialState_correct base activity ξ₀ R0 Y'
    ⟨row0, hrow0⟩ ⟨col0, hcol0⟩ P hP E0 r ⟨row, hrow⟩ ⟨col, hcol⟩

end Paper2.ReferenceSourceInitial

#print axioms Paper2.ReferenceSourceInitial.retained_rows_nonempty
#print axioms Paper2.ReferenceSourceInitial.retained_columns_nonempty
#print axioms Paper2.ReferenceSourceInitial.initialState_correct
#print axioms Paper2.ReferenceSourceInitial.initialState_cost
#print axioms Paper2.ReferenceSourceInitial.exists_initial_state
