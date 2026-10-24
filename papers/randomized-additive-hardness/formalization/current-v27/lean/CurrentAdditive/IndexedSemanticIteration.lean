import CurrentAdditive.IndexedSuccessorSemantic
import CurrentAdditive.IndexedGraphUpper
import CurrentAdditive.GeneratedWProfileAtSchedule

/-!
The one-step data below contains only finite indexed source labels, their
positive rational laws, and the physical size/clock fields.  In particular it
contains no assertion about the communication cost or future restriction
profile.  The fixed `step` is the literal two-stream `Sources.successor` on
those labels.  A separate Code_D implementation must supply these inputs and
their charged size/clock; this module closes the semantic table and upper
protocol interfaces for that same step.
-/

namespace CurrentAdditive.IndexedSemanticIteration

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.DeterministicIteration

universe u

variable {V E : Type u} [Fintype V] [Fintype E] [DecidableEq V]
  (L : ℕ) [Nonempty V] [Nonempty (Fin (4*s L))]
  [Nonempty (Fin (s L-3))]
  [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)]
  [NeZero (w L)] [NeZero (Q L)]

abbrev Graph (V E : Type u) := E → Bool → V

/-- Graph-independent public schedule.  Once selected, its repetition count
and source-item index law are reused on every stage and on both promises. -/
structure Schedule (V E : Type u) [Fintype V] [Fintype E] (L : ℕ)
    [NeZero (s L)] where
  large : 2004 ≤ L
  order : Paper2.SourceConstruction.Items (s L) V ≃
    Fin (Fintype.card (Paper2.SourceConstruction.Items (s L) V))
  rep : ℕ
  repetition : q₂ L = Paper2.SourceItems.sourceQ0 (Fin (4*s L)) E * rep

/-- The public source-item distribution is fixed by Appendix I.  It is
uniform on groups and splits vertex/auxiliary item mass evenly. -/
noncomputable def actualItemLaw :
    PositiveRationalLaw (Paper2.SourceConstruction.Items (s L) V) :=
  CurrentAdditive.DeterministicIndexedMatrix.itemLaw
    (G := Fin (4*s L)) (V := V) (A := Fin (s L-3))

/-- The public graph-size and degree guards select one repetition count,
independently of a colouring or a communication protocol. -/
theorem schedule_exists (Δ : ℕ)
    (hL : 24*Δ+2004 ≤ L)
    (hV : Fintype.card V ≤ N L) (hE : 0 < Fintype.card E)
    (hdegree : 2*Fintype.card E ≤ Δ*Fintype.card V) :
    Nonempty (Schedule V E L) := by
  obtain ⟨rep, hq⟩ :=
    CurrentAdditive.DeterministicIndexedMatrix.scheduled_graph_repetition
      L Δ hL hV hE hdegree
  exact ⟨{
    large := by omega
    order := Fintype.equivFin _
    rep := rep
    repetition := hq
  }⟩

/-- All finite data of a single source call.  Its field `entries_le_size`
charges the actual Boolean rectangle; a physical constructor must additionally
charge indices, laws, and arithmetic work in `encodingSize` and `stepClock`. -/
structure StepInputs (R : Stage.{u} (N L))
    (T : Schedule V E L) where
  src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
    (s := s L) R.rowLaw R.colLaw
  streams : Sources.InternalStreams src (actualItemLaw (V := V) L) (w L)
  final : CodeSource 8192 (Q L) (Fin (w L) × Sources.Column src)
    ((PositiveRationalLaw.uniform (Fin (w L))).prod
      (Sources.columnLaw src))
  tail : Tail (s L) R.Col
  encodingSize : ℕ
  stepClock : ℕ
  entries_le_size : Fintype.card final.Label *
    Fintype.card (Fin (Q L) ×
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label))) ≤
      encodingSize

/-- The literal successor, indexed by the *current* stage's row and column
alphabets.  The output remains a `Stage (N L)` even though those alphabets
change with each application. -/
noncomputable def next (T : Schedule V E L)
    (inputs : ∀ R : Stage.{u} (N L), StepInputs L R T)
    (G : Graph V E) (R : Stage.{u} (N L)) : Stage.{u} (N L) :=
  let i := inputs R
  successorStage i.src i.streams i.final R.matrix
    (Paper2.SourceConstruction.activity T.order G
      (by have h := s_ge_64 L (by have := T.large; omega : 24 ≤ L); omega)
      T.rep T.repetition) i.tail
    i.encodingSize i.stepClock i.entries_le_size (schedule_Q_ge_N L)

theorem next_matrix (T : Schedule V E L)
    (inputs : ∀ R : Stage.{u} (N L), StepInputs L R T)
    (G : Graph V E) (R : Stage.{u} (N L)) :
    (next L T inputs G R).matrix =
      Sources.successor (inputs R).src (inputs R).streams
        (inputs R).final R.matrix
        (Paper2.SourceConstruction.activity T.order G
          (by have h := s_ge_64 L (by have := T.large; omega : 24 ≤ L); omega)
          T.rep T.repetition) (inputs R).tail := rfl

/-- The weak pre-restoration profile is already proved for the very same
complete three-stream indexed matrix used in `next`.  The two numerical
guards are fields of the public admissibility test. -/
theorem next_W_weak_profile (T : Schedule V E L)
    (inputs : ∀ R : Stage.{u} (N L), StepInputs L R T)
    (G : Graph V E) (R : Stage.{u} (N L))
    (d : ℕ) (hd : 3 ≤ d) (hD : D R.matrix = d)
    (hp : RestrictionProfile R.matrix R.rowLaw.toFiniteLaw
      R.colLaw.toFiniteLaw (ρ L : ℝ) (d : ℤ))
    (he : 128 * CurrentAdditive.conditioningExceptionCount
      (θ L : ℝ) 1 ≤ w L)
    (hx : (w L : ℝ) * (x L : ℝ) ≤ 1/10000) :
    let i := inputs R
    RestrictionProfile
      (Sources.W i.src i.streams R.matrix
        (Paper2.SourceConstruction.activity T.order G
          (by have h := s_ge_64 L (by have := T.large; omega : 24 ≤ L); omega)
          T.rep T.repetition) i.tail)
      i.streams.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin (w L))).prod
        (Sources.columnLaw i.src)).toFiniteLaw)
      (θ L : ℝ)
      ((d+2*((L+3)/4)+6*L : ℕ) : ℤ) := by
  let i := inputs R
  have h := Sources.generated_W_profile_at_schedule
    (G := Fin (4*s L)) (V := V) (Aux := Fin (s L-3))
    L T.large i.src (actualItemLaw (V := V) L) i.streams
    R.matrix
    (Paper2.SourceConstruction.activity T.order G
      (by have hh := s_ge_64 L (by have := T.large; omega : 24 ≤ L); omega)
      T.rep T.repetition)
    i.tail d hd hD hp he hx
  convert h using 1
  congr 1
  omega

/-- The one actual construction consumed by the generic iteration theorem.
The source call is mathematical at this point; its executable Code_D producer
and physical clock are independent obligations. -/
noncomputable def construction (T : Schedule V E L)
    (seed : Graph V E → Stage.{u} (N L))
    (inputs : ∀ R : Stage.{u} (N L), StepInputs L R T) :
    Construction (Graph V E) (Stage.{u} (N L)) where
  seed := seed
  step := next L T inputs
  cost := fun R => D R.matrix
  valid := fun _ _ => True
  profile := fun _ R => RestrictionProfile R.matrix
    R.rowLaw.toFiniteLaw R.colLaw.toFiniteLaw (ρ L : ℝ) (D R.matrix : ℤ)
  size := Stage.encodingSize
  -- A stage's clock is the cost of constructing its *next* stage.  The
  -- output's stored field would shift the total-time sum by one step.
  stepTime := fun R => (inputs R).stepClock

theorem valid (T : Schedule V E L)
    (seed : Graph V E → Stage.{u} (N L))
    (inputs : ∀ R : Stage.{u} (N L), StepInputs L R T)
    (G : Graph V E) :
    ValidContract (construction L T seed inputs) G :=
  ⟨trivial, fun _ _ => trivial⟩

theorem one_step_upper (T : Schedule V E L)
    (inputs : ∀ R : Stage.{u} (N L), StepInputs L R T)
    (G : Graph V E) (R : Stage.{u} (N L)) :
    D (next L T inputs G R).matrix ≤ D R.matrix + h L + 1 ∧
    (∀ colour : V → Fin 3,
      (∀ e, colour (G e false) ≠ colour (G e true)) →
      D (next L T inputs G R).matrix ≤ D R.matrix + h L) := by
  let i := inputs R
  have hs := Sources.scheduled_graph_successor_upper L T.large i.src
    T.order G T.rep T.repetition (actualItemLaw (V := V) L)
    i.streams i.final i.tail R.matrix
  simpa only [next_matrix] using hs

/-- The universal contract is for every source graph, independent of its
colourability or NO promise. -/
theorem universal (T : Schedule V E L)
    (seed : Graph V E → Stage.{u} (N L))
    (inputs : ∀ R : Stage.{u} (N L), StepInputs L R T)
    (G : Graph V E) (d₀ : ℕ)
    (seed_upper : D (seed G).matrix ≤ d₀) :
    UniversalContract (construction L T seed inputs) G d₀ (h L) := by
  refine ⟨seed_upper, ?_⟩
  intro R _
  exact (one_step_upper L T inputs G R).1

/-- The YES proof uses a colouring only as a witness for the cheaper
protocol; the constructor itself never receives it. -/
theorem yes (T : Schedule V E L)
    (seed : Graph V E → Stage.{u} (N L))
    (inputs : ∀ R : Stage.{u} (N L), StepInputs L R T)
    (G : Graph V E) (d₀ : ℕ)
    (seed_upper : D (seed G).matrix ≤ d₀)
    (colour : V → Fin 3)
    (proper : ∀ e, colour (G e false) ≠ colour (G e true)) :
    YesContract (construction L T seed inputs) G d₀ (h L) := by
  refine ⟨seed_upper, ?_⟩
  intro R _
  exact (one_step_upper L T inputs G R).2 colour proper

/-- Every iterated stage has its own original indexed laws and a numbered
ordinary Boolean table with unchanged deterministic communication cost. -/
noncomputable def tables (T : Schedule V E L)
    (seed : Graph V E → Stage.{u} (N L))
    (inputs : ∀ R : Stage.{u} (N L), StepInputs L R T) :
    CurrentAdditive.DeterministicEndpointAssembly.TablePresentation
      (construction L T seed inputs) (N L) :=
  {
    rows := IndexedStagePresentation.rows
    cols := IndexedStagePresentation.cols
    table := IndexedStagePresentation.table
    rows_pos := IndexedStagePresentation.rows_pos
    cols_pos := IndexedStagePresentation.cols_pos
    exact_cost := IndexedStagePresentation.table_cost
    entries_le_encoding := Stage.entries_le_encoding
    public_side := Stage.public_side
  }

#print axioms next_matrix
#print axioms schedule_exists
#print axioms next_W_weak_profile
#print axioms one_step_upper
#print axioms universal
#print axioms yes
#print axioms tables

end CurrentAdditive.IndexedSemanticIteration
