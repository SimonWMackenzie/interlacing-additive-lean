import Paper2.ReferenceSourceDestinations
import Paper2.ReferenceOriginalLeaves
import Paper2.SourceProfiles
import Paper2.SourceLawBinding
import Paper2.RestorationSourceMargins

/-!
# Public source profile and literal reference destinations

The source profile is discharged from the base matrix by the checked source
profile theorem. The source's column labels are related by an exact bijection,
so no independent profile is introduced for the reassociated raw-row type.
-/

namespace Paper2.ReferencePublicDestinations

open SourceMatrix SourceLawBinding SourceProfileParameters SourceProfilesSchedule
open Workspace.Types.Protocol
open ReferenceCertificateTree ReferenceCertificates Paper2.SourceSupportFrontier

abbrev ActualRows {Y : Type*} (q₁ q₂ s w : ℕ) :=
  Fin w × TaggedColumn q₁ q₂ s Y
abbrev ActualColumns {X V : Type*} (q₁ q₂ s w : ℕ) :=
  Fin w → RawRow q₁ q₂ s X (SourceConstruction.Items s V)

noncomputable def actualOriginalState
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V]
    {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    (R0 : Set (ActualRows (Y := Y) q₁ q₂ s w))
    (Y' : Set (ActualColumns (X := X) (V := V) q₁ q₂ s w))
    (row0 : R0) (col0 : Y') (P : Protocol R0 Y' Bool)
    (E0 : Finset (Fin w)) :
    State (ActualRows (Y := Y) q₁ q₂ s w)
      (ActualColumns (X := X) (V := V) q₁ q₂ s w)
      (Fin w) (RawColumn q₁ q₂ s Y) where
  protocol := Workspace.UpperBound.Protocol.comap
    (SourceSupportInitial.columnRetraction R0 row0)
    (SourceSupportInitial.columnRetraction Y' col0) P
  rows := R0
  family := ReferenceSourceInitial.initialFamily R0 E0

noncomputable def actualPaddedState
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V]
    {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    (R0 : Set (ActualRows (Y := Y) q₁ q₂ s w))
    (Y' : Set (ActualColumns (X := X) (V := V) q₁ q₂ s w))
    (row0 : R0) (col0 : Y') (P : Protocol R0 Y' Bool)
    (E0 : Finset (Fin w)) (r : ℕ) :
    State (ActualRows (Y := Y) q₁ q₂ s w)
      (ActualColumns (X := X) (V := V) q₁ q₂ s w)
      (Fin w) (RawColumn q₁ q₂ s Y) :=
  { (actualOriginalState R0 Y' row0 col0 P E0) with
    protocol := ReferencePrefix.padAlicePrefix r
      (actualOriginalState R0 Y' row0 col0 P E0).protocol }

theorem actualOriginalState_eval
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V]
    {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    (R0 : Set (ActualRows (Y := Y) q₁ q₂ s w))
    (Y' : Set (ActualColumns (X := X) (V := V) q₁ q₂ s w))
    (row0 : R0) (col0 : Y') (P : Protocol R0 Y' Bool)
    (E0 : Finset (Fin w)) (row : R0) (col : Y') :
    (actualOriginalState R0 Y' row0 col0 P E0).protocol.eval row.val col.val =
      P.eval row col := by
  simp [actualOriginalState, Workspace.UpperBound.Protocol.comap_eval,
    SourceSupportInitial.columnRetraction_retained]

theorem actualPaddedState_eval
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V]
    {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    (R0 : Set (ActualRows (Y := Y) q₁ q₂ s w))
    (Y' : Set (ActualColumns (X := X) (V := V) q₁ q₂ s w))
    (row0 : R0) (col0 : Y') (P : Protocol R0 Y' Bool)
    (E0 : Finset (Fin w)) (r : ℕ) (row : R0) (col : Y') :
    (actualPaddedState R0 Y' row0 col0 P E0 r).protocol.eval row.val col.val =
      P.eval row col := by
  rw [actualPaddedState, ReferencePrefix.padAlicePrefix_eval]
  exact actualOriginalState_eval R0 Y' row0 col0 P E0 row col

theorem actualPaddedState_cost
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V]
    {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
    (R0 : Set (ActualRows (Y := Y) q₁ q₂ s w))
    (Y' : Set (ActualColumns (X := X) (V := V) q₁ q₂ s w))
    (row0 : R0) (col0 : Y') (P : Protocol R0 Y' Bool)
    (E0 : Finset (Fin w)) (r : ℕ) :
    (actualPaddedState R0 Y' row0 col0 P E0 r).protocol.cost ≤
      max P.cost r := by
  have hh := ReferencePrefix.padAlicePrefix_cost_le r
    (actualOriginalState R0 Y' row0 col0 P E0).protocol
  have hco : (actualOriginalState R0 Y' row0 col0 P E0).protocol.cost =
      P.cost := by simp [actualOriginalState, Workspace.UpperBound.Protocol.comap_cost]
  rw [hco] at hh
  change (actualPaddedState R0 Y' row0 col0 P E0 r).protocol.cost ≤
    max P.cost r at hh
  exact hh

private theorem positive_event_nonempty {T : Type*} [Fintype T]
    (κ : FiniteLaw T) (E : Set T) (h : 0 < κ.prob (· ∈ E)) : E.Nonempty := by
  by_contra hn
  have he : (fun t : T => t ∈ E) = fun _ => False := by
    funext t
    apply propext
    exact ⟨fun ht => (hn ⟨t, ht⟩).elim, False.elim⟩
  rw [he, FiniteLaw.prob_false] at h
  exact (not_lt_of_ge le_rfl) h

/-- The final-node part of the actual-run argument, exposed separately so a
downstream owner can identify its unique surviving original coordinate. -/
theorem run_final_active_le_one
    {A K Rw : Type*} [Fintype A] [Fintype K] [Fintype Rw] {w : ℕ}
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw K)
    (F : A → K → Bool) (M : Rw → (Fin w → K) → Bool)
    (input : Fin w → A → Rw) (O : Set (Fin w → K))
    (s : State Rw (Fin w → K) (Fin w) A)
    (E0 : Finset (Fin w)) (r H : ℕ) (x : ℝ)
    (hw : w = 2 ^ r) (hH : 2 ≤ H) (hx : 0 < x)
    (hscale : 2 * (2 : ℝ) ^ r * x ≤ 1)
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hpair99 : ∀ S : Finset (Fin w), S.card = 2 → Disjoint S E0 →
      (99 / 100 : ℝ) ≤ ProductProjections.projectionMass
        (fun _ => ν.toFiniteLaw) (· ∈ O) S)
    (hactive : s.family.active = Finset.univ \ E0)
    (hreach : ∀ i ∈ s.family.active, ∀ a ∈ s.family.support i,
      input i a ∈ s.rows)
    (hfloor : ∀ i ∈ s.family.active,
      ReferenceSchedule.floor w x 0 ≤
        SourceSupportStep.mass μ.toFiniteLaw (s.family.support i))
    (hcompute : ∀ row ∈ s.rows, ∀ y ∈ O, s.protocol.eval row y = M row y)
    (hentry : ∀ i a, input i a ∈ s.rows → ∀ y ∈ O,
      M (input i a) y = F a (y i))
    (hcost : s.protocol.cost ≤ H + r) :
    ∀ v : (run μ.toFiniteLaw input (ReferenceSchedule.floor w x) 0 r s).Leaves,
      ((run μ.toFiniteLaw input (ReferenceSchedule.floor w x) 0 r s).route v).length = r →
      ((run μ.toFiniteLaw input (ReferenceSchedule.floor w x) 0 r s).state v).family.active.card ≤ 1 := by
  classical
  let floor := ReferenceSchedule.floor w x
  let T := run μ.toFiniteLaw input floor 0 r s
  have hrunFloor := run_floor μ.toFiniteLaw input floor
    (ReferenceSchedule.floor_half w x) 0 r s hfloor
  have hrunReach := run_reaches μ.toFiniteLaw input floor 0 r s hreach
  have hrunSets := run_sets_subset μ.toFiniteLaw input floor 0 r s
  intro v hv
  let node := T.state v
  have hnodesub := ReferenceRunCorrectness.rows_subset
    μ.toFiniteLaw input floor 0 r s v
  have hnodecomp := ReferenceRunCorrectness.computes_on_original_rectangle
    μ.toFiniteLaw input floor 0 r s M O hcompute v
  have hnodeavoid : Disjoint node.family.active E0 := by
    apply Finset.disjoint_left.mpr
    intro i hi hiE
    have hi0 := (hrunSets v).1 hi
    rw [hactive] at hi0
    exact (Finset.mem_sdiff.mp hi0).2 hiE
  have hnodefloor : ∀ i ∈ node.family.active,
      2 * x ≤ μ.toFiniteLaw.prob (· ∈ (node.family.support i : Set A)) := by
    intro i hi
    have hf := hrunFloor v i hi
    have heq : floor ((T.route v).length) = 2 * x := by
      change ReferenceSchedule.floor w x (T.route v).length = 2 * x
      rw [hv, ReferenceSchedule.floor_dyadic x hw (le_refl r)]
      simp
    have hf' : 2 * x ≤ SourceSupportStep.mass μ.toFiniteLaw (node.family.support i) := by
      simpa only [Nat.zero_add, ← heq] using hf
    simpa only [SourceSupportStep.mass] using hf'
  have hnodeentry : ∀ i a, input i a ∈ node.rows → ∀ y ∈ O,
      M (input i a) y = F a (y i) := by
    intro i a ha y hy
    exact hentry i a (hnodesub ha) y hy
  have hnodecost : node.protocol.cost ≤ H := by
    have hc := ReferenceRunCorrectness.remaining_cost
      μ.toFiniteLaw input floor r H s hcost v
    rw [hv] at hc
    simpa only [Nat.sub_self, Nat.add_zero] using hc
  have htwo : 2 * x ≤ 1 := by
    have hp : (1 : ℝ) ≤ 2 ^ r := by
      simpa only [one_pow] using
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    have hm := mul_le_mul_of_nonneg_right hp (le_of_lt hx)
    nlinarith [hscale]
  exact ReferenceTerminalCapacity.final_active_le_one μ ν F M input node.rows O
    node.protocol hnodecomp hnodeentry node.family E0 H x hnodeavoid
    hnodefloor (hrunReach v) hpair99 hH hx htwo hprofile hnodecost

private theorem profile_relabel_column
    {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (F : A → B → Bool) (μA : PositiveRationalLaw A)
    (μC : PositiveRationalLaw C) (e : C ≃ B) (x : ℝ) (H : ℤ)
    (hp : RestrictionProfile F μA.toFiniteLaw (μC.relabel e).toFiniteLaw x H) :
    RestrictionProfile (fun a c => F a (e c)) μA.toFiniteLaw μC.toFiniteLaw x H := by
  classical
  intro j U V hU hV
  have hmass : ((μC.relabel e).toFiniteLaw).prob (· ∈ e '' V) =
      μC.toFiniteLaw.prob (· ∈ V) := by
    rw [PositiveRationalLaw.relabel_prob]
    congr 1
    funext c
    apply propext
    constructor
    · rintro ⟨d, hd, hed⟩
      exact e.injective hed ▸ hd
    · intro hc
      exact ⟨c, hc, rfl⟩
  have hbound := hp j U (e '' V) hU (by rw [hmass]; exact hV)
  have heq : Compression.restrictionD (fun a c => F a (e c)) U V =
      Compression.restrictionD F U (e '' V) := by
    simpa using (restrictionD_pullback_image F (fun a : A => a) e U V)
  exact heq ▸ hbound

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
local instance (L : ℕ) : NeZero (width L - 2) := ⟨by
  have h := width_admissible L
  omega⟩
local instance (L : ℕ) : Nonempty (Fin (4 * width L)) :=
  ⟨⟨0, by have h := SourceProfiles.width_ge_four L; omega⟩⟩
local instance (L : ℕ) : Nonempty (Fin (width L - 3)) := ⟨⟨0, by
  have h := SourceProfiles.width_ge_four L
  omega⟩⟩

set_option maxRecDepth 4096 in

/-- The fifth source profile, expressed on the literal sum-labelled columns
of `fullInterlace (N ...)`. This is a bijective relabelling of the profile
proved by `SourceProfiles.source_profiles`, not a new profile hypothesis. -/
theorem source_raw_profile
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V] [Nonempty V]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d : ℕ) (hd : 3 ≤ d)
    (hD : Workspace.Types.CommComplexity.D base = d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw
      (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (activity : SourceConstruction.Items (width L) V →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y) :
    RestrictionProfile
      (fun Z row => raw base
        (fun item α => activity (itemEquiv (width L) V item) α)
        row Z)
      (SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
      (SourceLaws.rowLaw
        (V := Fin (4 * width L) × V)
        (A := Fin (4 * width L) × Fin (width L - 3))
        μ (width L - 2) (outerWidth L) (width L)).toFiniteLaw
      (x L)
      ((d + exponent L + outerExponent L + exponent L : ℕ) : ℤ) := by
  obtain ⟨_, _, _, _, hraw⟩ := SourceProfiles.source_profiles μ ν base L d hd
    hD hp hinner houter hwide href activity ξ₀
  let e := rawRowEquiv (width L - 2) (outerWidth L) (width L) X V
  let μC := SourceLaws.rowLaw
    (V := Fin (4 * width L) × V)
    (A := Fin (4 * width L) × Fin (width L - 3))
    μ (width L - 2) (outerWidth L) (width L)
  have hraw' : RestrictionProfile
      (fun Z row => N base activity ξ₀ (.unrestricted Z) row)
      (SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
      (μC.relabel e).toFiniteLaw
      (x L)
      ((d + exponent L + outerExponent L + exponent L : ℕ) : ℤ) := by
    simpa only [μC, e, matrixColumnLaw] using hraw
  have htransport := profile_relabel_column
    (fun Z row => N base activity ξ₀ (.unrestricted Z) row)
    (SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L))
    μC e (x L)
    ((d + exponent L + outerExponent L + exponent L : ℕ) : ℤ) hraw'
  convert htransport using 1
  funext Z row
  rcases row with row | ⟨item, x⟩
  · rfl
  · rcases item with ⟨g, v⟩ | ⟨g, a⟩ <;> rfl

/-- The destination count for the literal first interlace, with the
raw-reference profile derived from the public base hypotheses. -/
theorem public_source_destinations
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V] [Nonempty V]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d : ℕ) (hd : 3 ≤ d)
    (hD : Workspace.Types.CommComplexity.D base = d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw
      (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (activity : SourceConstruction.Items (width L) V →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y)
    (w r Q C : ℕ) (hw : w = 2 ^ r) (hQ : 0 < Q) (hC : 4 ≤ C)
    (hCeq : C - 1 = d + exponent L + outerExponent L + exponent L)
    (eta : ℝ) (heta : 0 < eta) (heta1 : eta < 1)
    (R0 : Set (ReferenceSourceInitial.Rows (Y := Y)
      (q₁ := width L - 2) (q₂ := outerWidth L) (s := width L) (w := w)))
    (Y' : Set (ReferenceSourceInitial.Columns (X := X)
      (V := Fin (4 * width L) × V)
      (A := Fin (4 * width L) × Fin (width L - 3))
      (q₁ := width L - 2) (q₂ := outerWidth L) (s := width L) (w := w)))
    (P : Protocol R0 Y' Bool)
    (hP : P.Computes (fun row col =>
      ReferenceSourceInitial.sourceMatrix base
        (fun item α => activity (itemEquiv (width L) V item) α)
        ξ₀ row.val col.val))
    (hPcost : P.cost ≤ C + r - 1)
    (hR0 : 1 - eta / (16 * w) ≤
      (ReferenceInitial.firstRowLaw ν (by rw [hw]; positivity)).prob (· ∈ R0))
    (hY : RestorationCoverParameters.theta Q ≤
      ((SourceLaws.rowLaw
        (V := Fin (4 * width L) × V)
        (A := Fin (4 * width L) × Fin (width L - 3))
        μ (width L - 2) (outerWidth L) (width L)).iid w).toFiniteLaw.prob (· ∈ Y'))
    (hmargin : 2 * w * x L + eta / (16 * (127 / 128 : ℝ)) < 1) :
    ∃ E0 : Finset (Fin w), E0.card ≤ RestorationPublicCovers.e0 Q eta ∧
      ∃ row0 : R0, ∃ col0 : Y', ∃ st : ReferenceCertificateTree.State
        (ReferenceSourceInitial.Rows (Y := Y)
          (q₁ := width L - 2) (q₂ := outerWidth L) (s := width L) (w := w))
        (ReferenceSourceInitial.Columns (X := X)
          (V := Fin (4 * width L) × V)
          (A := Fin (4 * width L) × Fin (width L - 3))
          (q₁ := width L - 2) (q₂ := outerWidth L) (s := width L) (w := w))
        (Fin w) (RawColumn (width L - 2) (outerWidth L) (width L) Y),
      st = ReferenceSourceInitial.initialState R0 Y' row0 col0 P E0 r ∧
      let T := ReferenceCertificateTree.run
        (SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
        ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) 0 r st
      let fam := fun v : T.Leaves => (T.state v).family
      let final := fun v : T.Leaves => (T.route v).length = r
      w - ReferenceOwners.exceptionBudget (RestorationPublicCovers.e0 Q eta) ≤
        (ReferenceOwners.ownerNodes fam final).card ∧
      ReferenceOwners.exceptionalCapacity fam final
        (fun v => 2 ^ (r - (T.route v).length)) ≤
          ReferenceOwners.exceptionBudget (RestorationPublicCovers.e0 Q eta) := by
  letI : Nonempty (Fin (4 * width L) × V) := inferInstance
  letI : Nonempty (Fin (4 * width L) × Fin (width L - 3)) := inferInstance
  have hraw := source_raw_profile μ ν base L d hd hD hp hinner houter hwide
    href activity ξ₀
  rw [← hCeq] at hraw
  exact ReferenceSourceDestinations.source_destinations μ ν base
    (fun item α => activity (itemEquiv (width L) V item) α)
    ξ₀ R0 Y' P hP r Q C hw hQ hC hPcost eta (x L) heta heta1
    (by unfold x; positivity) hR0 hY hmargin hraw

/-- Original-leaf exclusion for the *un-padded* ambient extension of the
restricted source protocol. The cover set is explicit, so this applies to
the same `E0` chosen for the destination count. -/
theorem public_unpadded_leaves_empty
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V] [Nonempty V]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d : ℕ) (hd : 3 ≤ d)
    (hD : Workspace.Types.CommComplexity.D base = d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (activity : SourceConstruction.Items (width L) V →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y)
    (w r C : ℕ) (hw : w = 2 ^ r) (hC : 4 ≤ C)
    (hCeq : C - 1 = d + exponent L + outerExponent L + exponent L)
    (eta : ℝ) (heta : eta < 2 / 5)
    (R0 : Set (ReferenceSourceInitial.Rows (Y := Y)
      (q₁ := width L - 2) (q₂ := outerWidth L) (s := width L) (w := w)))
    (Y' : Set (ReferenceSourceInitial.Columns (X := X)
      (V := Fin (4 * width L) × V)
      (A := Fin (4 * width L) × Fin (width L - 3))
      (q₁ := width L - 2) (q₂ := outerWidth L) (s := width L) (w := w)))
    (row0 : R0) (col0 : Y') (P : Protocol R0 Y' Bool)
    (hP : P.Computes (fun row col =>
      ReferenceSourceInitial.sourceMatrix base
        (fun item α => activity (itemEquiv (width L) V item) α)
        ξ₀ row.val col.val))
    (hR0 : 1 - eta / (16 * w) ≤
      (ReferenceInitial.firstRowLaw ν (by rw [hw]; positivity)).prob (· ∈ R0))
    (hmargin : 2 * w * x L + eta / (16 * (127 / 128 : ℝ)) < 1)
    (E0 : Finset (Fin w))
    (hsingle : ∀ S : Finset (Fin w), S.card = 1 → Disjoint S E0 →
      1 - eta ≤ ProductProjections.projectionMass
        (fun _ => (SourceLaws.rowLaw
          (V := Fin (4 * width L) × V)
          (A := Fin (4 * width L) × Fin (width L - 3))
          μ (width L - 2) (outerWidth L) (width L)).toFiniteLaw)
        (· ∈ Y') S) :
    let original : State
      (ReferenceSourceInitial.Rows (Y := Y)
        (q₁ := width L - 2) (q₂ := outerWidth L) (s := width L) (w := w))
      (ReferenceSourceInitial.Columns (X := X)
        (V := Fin (4 * width L) × V)
        (A := Fin (4 * width L) × Fin (width L - 3))
        (q₁ := width L - 2) (q₂ := outerWidth L) (s := width L) (w := w))
      (Fin w) (RawColumn (width L - 2) (outerWidth L) (width L) Y) :=
      { protocol := ReferenceSourceInitial.ambientProtocol R0 Y' row0 col0 P
        rows := R0, family := ReferenceSourceInitial.initialFamily R0 E0 }
    ∀ v : (run (SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
      ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) 0 r original).Leaves,
      ((run (SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
        ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) 0 r original).state v).protocol.cost = 0 →
      ((run (SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
        ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) 0 r original).state v).family.active = ∅ := by
  letI : Nonempty (Fin (4 * width L) × V) := inferInstance
  letI : Nonempty (Fin (4 * width L) × Fin (width L - 3)) := inferInstance
  let original : State _ _ (Fin w) (RawColumn (width L - 2) (outerWidth L) (width L) Y) :=
    { protocol := ReferenceSourceInitial.ambientProtocol R0 Y' row0 col0 P
      rows := R0, family := ReferenceSourceInitial.initialFamily R0 E0 }
  have hraw := source_raw_profile μ ν base L d hd hD hp hinner houter hwide
    href activity ξ₀
  rw [← hCeq] at hraw
  have hreach := ReferenceSourceInitial.initialFamily_reaches R0 E0
  have hfloor := ReferenceSourceInitial.initialFamily_floor ν
    (by rw [hw]; positivity) R0 E0 eta (x L) hR0 hmargin
  have hcompute : ∀ row ∈ original.rows, ∀ y ∈ Y',
      original.protocol.eval row y =
        ReferenceSourceInitial.sourceMatrix base
          (fun item α => activity (itemEquiv (width L) V item) α) ξ₀ row y := by
    intro row hr y hy
    exact (ReferenceSourceInitial.ambientProtocol_eval R0 Y' row0 col0 P
      ⟨row, hr⟩ ⟨y, hy⟩).trans (hP ⟨row, hr⟩ ⟨y, hy⟩)
  exact ReferenceOriginalLeaves.unpadded_run_leaf_active_empty
    (SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L))
    (SourceLaws.rowLaw
      (V := Fin (4 * width L) × V)
      (A := Fin (4 * width L) × Fin (width L - 3))
      μ (width L - 2) (outerWidth L) (width L))
    (fun Z row => raw base
      (fun item α => activity (itemEquiv (width L) V item) α) row Z)
    (ReferenceSourceInitial.sourceMatrix base
      (fun item α => activity (itemEquiv (width L) V item) α) ξ₀)
    ReferenceSourceInitial.input Y' original E0 r (C - 1) (x L) eta hw
    (by omega) (by unfold x; positivity) heta hraw hsingle
    rfl hreach hfloor hcompute (by intro i Z _ y _; rfl)

set_option maxRecDepth 4096 in
/-- Actual-Items destination package. In contrast to the reassociated
intermediate above, every leaf here is a physical leaf of the original
`Items`-column protocol. The same public exceptional set is used for the
padded count and the unpadded original-leaf exclusion. -/
theorem actual_items_destinations
    {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V] [Nonempty V]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool) (L d : ℕ) (hd : 3 ≤ d)
    (hD : Workspace.Types.CommComplexity.D base = d)
    (hp : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw (rho L) (d : ℤ))
    (hinner : (width L : ℝ) * rho L ≤ 1 / 1000)
    (houter : (outerWidth L : ℝ) * x L ≤ 1 / 10000)
    (hwide : (10 * L : ℝ) ≤ (outerWidth L : ℝ) / 4096)
    (href : (width L : ℝ) * x L ≤ 1 / 10000)
    (activity : SourceConstruction.Items (width L) V →
      Fin (outerWidth L) → Option (Fin (width L)))
    (ξ₀ : Tail (width L) Y)
    (w r Q C : ℕ) (hw : w = 2 ^ r) (hQ : 0 < Q) (hC : 4 ≤ C)
    (hCeq : C - 1 = d + exponent L + outerExponent L + exponent L)
    (delta zeta eta : ℝ) (hdelta : 0 < delta) (hzeta : 0 < zeta)
    (hetaDef : eta = SourceDeletionParameters.eta (width L) delta zeta)
    (R0 : Set (ActualRows (Y := Y) (width L - 2) (outerWidth L) (width L) w))
    (Y' : Set (ActualColumns (X := X) (V := V)
      (width L - 2) (outerWidth L) (width L) w))
    (P : Protocol R0 Y' Bool)
    (hP : P.Computes (fun row col =>
      fullInterlace (N base activity ξ₀) w row.val col.val))
    (hPcost : P.cost ≤ C + r - 1)
    (hR0 : 1 - eta / (16 * w) ≤
      (ReferenceInitial.firstRowLaw ν (by rw [hw]; positivity)).prob (· ∈ R0))
    (hY : RestorationCoverParameters.theta Q ≤
      ((matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L) (width L)
        (SourceProfiles.width_ge_four L)).toFiniteLaw.iid w).prob (· ∈ Y'))
    (hmargin : 2 * w * x L + eta / (16 * (127 / 128 : ℝ)) < 1) :
    ∃ E0 : Finset (Fin w), ∃ row0 : R0, ∃ col0 : Y',
      let κ := matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L)
        (width L) (SourceProfiles.width_ge_four L)
      let st := actualPaddedState R0 Y' row0 col0 P E0 r
      let original := actualOriginalState R0 Y' row0 col0 P E0
      let T := run (SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
        ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) 0 r st
      let O := run (SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)).toFiniteLaw
        ReferenceSourceInitial.input (ReferenceSchedule.floor w (x L)) 0 r original
      let fam := fun v : T.Leaves => (T.state v).family
      let final := fun v : T.Leaves => (T.route v).length = r
      E0.card ≤ RestorationPublicCovers.e0 Q eta ∧
      (∀ S : Finset (Fin w), S.card = 1 → Disjoint S E0 →
        1 - eta ≤ ProductProjections.projectionMass
          (fun _ => κ.toFiniteLaw) (· ∈ Y') S) ∧
      (∀ S : Finset (Fin w), S.card = 2 → Disjoint S E0 →
        (99 / 100 : ℝ) ≤ ProductProjections.projectionMass
          (fun _ => κ.toFiniteLaw) (· ∈ Y') S) ∧
      (∀ S : Finset (Fin w), S.card = 2 → Disjoint S E0 →
        (18 / 25 : ℝ) ≤ ProductProjections.projectionMass
          (fun _ => κ.toFiniteLaw) (· ∈ Y') S) ∧
      (∀ j : Fin (RestorationCoverParameters.tExponent Q - 2),
        ∀ S : Finset (Fin w),
          S.card = RestorationCovers.smallSize j.val → Disjoint S E0 →
          (18 / 25 : ℝ) ≤ ProductProjections.projectionMass
            (fun _ => κ.toFiniteLaw) (· ∈ Y') S) ∧
      w - ReferenceOwners.exceptionBudget (RestorationPublicCovers.e0 Q eta) ≤
        (ReferenceOwners.ownerNodes fam final).card ∧
      ReferenceOwners.exceptionalCapacity fam final
        (fun v => 2 ^ (r - (T.route v).length)) ≤
          ReferenceOwners.exceptionBudget (RestorationPublicCovers.e0 Q eta) ∧
      (∀ v : T.Leaves, final v → (fam v).active.card ≤ 1) ∧
      (∀ v : O.Leaves, (O.state v).protocol.cost = 0 →
        (O.state v).family.active = ∅) ∧
      Function.Injective (ReferenceOwners.origin fam final) ∧
      (∀ v : {v // v ∈ ReferenceOwners.ownerNodes fam final},
        ∀ i ∈ (fam v.val).unsplit,
          i = ReferenceOwners.origin fam final v) := by
  classical
  let κ := matrixColumnLaw (V := V) μ (width L - 2) (outerWidth L) (width L)
    (SourceProfiles.width_ge_four L)
  let μRaw := SourceLaws.rawLaw ν (width L - 2) (outerWidth L) (width L)
  let floor := ReferenceSchedule.floor w (x L)
  let M : ActualRows (Y := Y) (width L - 2) (outerWidth L) (width L) w →
      ActualColumns (X := X) (V := V) (width L - 2) (outerWidth L) (width L) w →
      Bool := fullInterlace (N (q₁ := width L - 2) base activity ξ₀) w
  let F : RawColumn (width L - 2) (outerWidth L) (width L) Y →
      RawRow (width L - 2) (outerWidth L) (width L) X
        (SourceConstruction.Items (width L) V) → Bool :=
    fun Z row => N base activity ξ₀ (.unrestricted Z) row
  have hwpos : 0 < w := by rw [hw]; positivity
  have heta : 0 < eta := by
    rw [hetaDef]
    exact SourceDeletionParameters.eta_pos (width L)
      (by have h := SourceProfiles.width_ge_four L; omega) delta zeta hdelta hzeta
  have heta2 : eta < 2 / 5 := by
    rw [hetaDef]
    exact RestorationSourceMargins.eta_lt_two_fifths (width L)
      (by have h := SourceProfiles.width_ge_four L; omega) delta zeta hdelta hzeta
  have heta1 : eta < 1 := by linarith
  obtain ⟨E0, hE, hsingle, hpair99, hpair18, hdyadic⟩ :=
    RestorationPublicCovers.exists_cover κ.toFiniteLaw w Q hQ eta heta heta1 Y' hY
  obtain ⟨rowVal, hrowVal⟩ :=
    ReferenceSourceInitial.retained_rows_nonempty ν hwpos R0 eta (x L)
      (by unfold x; positivity) hR0 hmargin
  obtain ⟨colVal, hcolVal⟩ := positive_event_nonempty (κ.toFiniteLaw.iid w) Y'
    (lt_of_lt_of_le (RestorationCoverParameters.theta_pos hQ) hY)
  let row0 : R0 := ⟨rowVal, hrowVal⟩
  let col0 : Y' := ⟨colVal, hcolVal⟩
  let st := actualPaddedState R0 Y' row0 col0 P E0 r
  let original := actualOriginalState R0 Y' row0 col0 P E0
  have hraw := (SourceProfiles.source_profiles μ ν base L d hd hD hp
    hinner houter hwide href activity ξ₀).2.2.2.2
  rw [← hCeq] at hraw
  have hreach := ReferenceSourceInitial.initialFamily_reaches R0 E0
  have hfloor := ReferenceSourceInitial.initialFamily_floor ν hwpos R0 E0
    eta (x L) hR0 hmargin
  have hactive : st.family.active = Finset.univ \ E0 := rfl
  have hvalid : st.family.unsplit ⊆ st.family.active := by
    exact ReferenceSourceInitial.initialFamily_valid R0 E0
  have hunits : 2 * st.family.active.card ≤ units st.family := by
    have hc := ReferenceSourceInitial.initialFamily_units R0 E0
    change units st.family = 2 * (w - E0.card) at hc
    rw [hc]
    have hsub : E0.card ≤ w := by
      simpa using Finset.card_le_card (Finset.subset_univ E0)
    have hcard : (Finset.univ \ E0).card = w - E0.card := by
      rw [Finset.card_sdiff]
      simp
    change 2 * (Finset.univ \ E0).card ≤ 2 * (w - E0.card)
    omega
  have hcomputeOrig : ∀ row ∈ original.rows, ∀ y ∈ Y',
      original.protocol.eval row y = M row y := by
    intro row hr y hy
    exact (actualOriginalState_eval R0 Y' row0 col0 P E0
      ⟨row, hr⟩ ⟨y, hy⟩).trans (hP ⟨row, hr⟩ ⟨y, hy⟩)
  have hcompute : ∀ row ∈ st.rows, ∀ y ∈ Y',
      st.protocol.eval row y = M row y := by
    intro row hr y hy
    exact (actualPaddedState_eval R0 Y' row0 col0 P E0 r
      ⟨row, hr⟩ ⟨y, hy⟩).trans (hP ⟨row, hr⟩ ⟨y, hy⟩)
  have hentry : ∀ i Z, ReferenceSourceInitial.input i Z ∈ st.rows →
      ∀ y ∈ Y', M (ReferenceSourceInitial.input i Z) y = F Z (y i) := by
    intro i Z _ y _
    rfl
  have hprefix : ReferencePrefix.NoEarlyLeaf r st.protocol :=
    ReferencePrefix.padAlicePrefix_noEarlyLeaf r _
  have hcost : st.protocol.cost ≤ (C - 1) + r := by
    have hc := actualPaddedState_cost R0 Y' row0 col0 P E0 r
    change st.protocol.cost ≤ max P.cost r at hc
    omega
  have hscale : 2 * (2 : ℝ) ^ r * x L ≤ 1 := by
    have hwreal : (w : ℝ) = (2 : ℝ) ^ r := by exact_mod_cast hw
    have htail : 0 ≤ eta / (16 * (127 / 128 : ℝ)) := by positivity
    rw [← hwreal]
    linarith
  have hcount := ReferenceDestinations.run_destinations μRaw κ F M
    ReferenceSourceInitial.input Y' st E0 (RestorationPublicCovers.e0 Q eta)
    Q (C - 1) r (x L) hw hE hQ (by omega) (by unfold x; positivity)
    hscale hraw hY hpair99 hpair18 hdyadic hactive hvalid hunits
    hreach hfloor hcompute hentry hprefix hcost
  have hfinal := run_final_active_le_one μRaw κ F M
    ReferenceSourceInitial.input Y' st E0 r (C - 1) (x L) hw
    (by omega) (by unfold x; positivity) hscale hraw hpair99
    hactive hreach hfloor hcompute hentry hcost
  have hleaf := ReferenceOriginalLeaves.unpadded_run_leaf_active_empty
    μRaw κ F M ReferenceSourceInitial.input Y' original E0 r (C - 1)
    (x L) eta hw (by omega) (by unfold x; positivity) heta2 hraw
    hsingle rfl hreach hfloor hcomputeOrig
    (by intro i Z _ y _; rfl)
  let T := run μRaw.toFiniteLaw ReferenceSourceInitial.input floor 0 r st
  let O := run μRaw.toFiniteLaw ReferenceSourceInitial.input floor 0 r original
  let fam := fun v : T.Leaves => (T.state v).family
  let final := fun v : T.Leaves => (T.route v).length = r
  have hvalidRun := run_valid μRaw.toFiniteLaw ReferenceSourceInitial.input
    floor 0 r st hvalid
  have hinj := ReferenceOwners.run_origin_injective μRaw.toFiniteLaw
    ReferenceSourceInitial.input floor r st
  have horigin : ∀ v : {v // v ∈ ReferenceOwners.ownerNodes fam final},
      ∀ i ∈ (fam v.val).unsplit, i = ReferenceOwners.origin fam final v := by
    intro v i hi
    exact ReferenceOwners.origin_eq_of_mem fam final hvalidRun hfinal v i hi
  refine ⟨E0, row0, col0, hE, hsingle, hpair99, hpair18, hdyadic,
    ?_, ?_, hfinal, hleaf, hinj, horigin⟩
  · exact hcount.1
  · exact hcount.2

end Paper2.ReferencePublicDestinations

#print axioms Paper2.ReferencePublicDestinations.profile_relabel_column
#print axioms Paper2.ReferencePublicDestinations.source_raw_profile
#print axioms Paper2.ReferencePublicDestinations.run_final_active_le_one
#print axioms Paper2.ReferencePublicDestinations.public_source_destinations
#print axioms Paper2.ReferencePublicDestinations.public_unpadded_leaves_empty
#print axioms Paper2.ReferencePublicDestinations.actual_items_destinations
