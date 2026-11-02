import CurrentAdditive.IndexedProfileSchedule
import Paper2.SourceConstruction
import CurrentAdditive.DeterministicIndexedUpper

/-! Appendix I upper protocols for the actual indexed successor built with
the public SourceItems graph activity. The matrix constructor does not receive
the YES colouring; only the proof of its cheaper protocol does. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicParameters

theorem Sources.graph_indexed_successor_upper
    {V E X Y : Type*} [Fintype V] [Fintype E]
    [Fintype X] [Fintype Y] [DecidableEq V] [DecidableEq X] [DecidableEq Y]
    {wise q₁ q₂ s w Q : ℕ} [NeZero q₁] [NeZero q₂]
    [NeZero s] [NeZero w] [NeZero Q]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := wise) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (order : Paper2.SourceConstruction.Items s V ≃
      Fin (Fintype.card (Paper2.SourceConstruction.Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (rep : ℕ)
    (hq : q₂ = Paper2.SourceItems.sourceQ0 (Fin (4*s)) E * rep)
    (μI : PositiveRationalLaw (Paper2.SourceConstruction.Items s V))
    (streams : InternalStreams src μI w)
    (final : CodeSource wise Q (Fin w × Column src)
      ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
    (ξ₀ : Tail s Y) (R : X → Y → Bool)
    (a b c f : ℕ) (hq₁ : q₁ + 2 = s) (hsa : s = 2^a)
    (hqb : q₂ = 2^b) (hw : w = 2^c) (hQ : Q = 2^f) :
    D (successor src streams final R
      (Paper2.SourceConstruction.activity order edge hs rep hq) ξ₀) ≤
        D R + (a+a+b+c+f) + 1 ∧
    (∀ colour : V → Fin 3,
      (∀ e, colour (edge e false) ≠ colour (edge e true)) →
      D (successor src streams final R
        (Paper2.SourceConstruction.activity order edge hs rep hq) ξ₀) ≤
          D R + (a+a+b+c+f)) := by
  classical
  let activity := Paper2.SourceConstruction.activity order edge hs rep hq
  have hlogS : Nat.clog 2 s = a := by rw [hsa, Nat.clog_pow 2 a (by decide)]
  have hlogQ₂ : Nat.clog 2 q₂ = b := by rw [hqb, Nat.clog_pow 2 b (by decide)]
  have hlogW : Nat.clog 2 w = c := by rw [hw, Nat.clog_pow 2 c (by decide)]
  have hlogQ : Nat.clog 2 Q = f := by rw [hQ, Nat.clog_pow 2 f (by decide)]
  have hsel : Nat.clog 2 (q₁+s+1) ≤ a+1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ, ← hsa]
    omega
  have hu := Sources.indexed_successor_universal_D_le src streams final activity ξ₀ R
  rw [hlogS, hlogQ₂, hlogW, hlogQ] at hu
  dsimp only [activity] at hu
  refine ⟨by omega, ?_⟩
  intro colour proper
  have hc := Paper2.SourceConstruction.activity_collisionFree
    order edge hs rep hq colour proper
  have hy := Sources.indexed_successor_yes_D_le src streams final
    (Paper2.SourceItems.yesAssignment hs colour) activity hc ξ₀ R
  rw [hq₁, hlogS, hlogQ₂, hlogW, hlogQ] at hy
  dsimp only [activity] at hy
  omega

/-- Both manuscript-size upper bounds for the same public, indexed graph
successor. A proper three-colouring is supplied only to the YES proof. -/
theorem Sources.scheduled_graph_successor_upper
    {V E X Y : Type*} [Fintype V] [Fintype E]
    [Fintype X] [Fintype Y] [DecidableEq V] [DecidableEq X] [DecidableEq Y]
    (L : ℕ) (hL : 2004 ≤ L)
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)]
    [NeZero (w L)] [NeZero (Q L)]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) μX μY)
    (order : Paper2.SourceConstruction.Items (s L) V ≃
      Fin (Fintype.card (Paper2.SourceConstruction.Items (s L) V)))
    (edge : E → Bool → V) (rep : ℕ)
    (hq : q₂ L = Paper2.SourceItems.sourceQ0 (Fin (4*s L)) E * rep)
    (μI : PositiveRationalLaw (Paper2.SourceConstruction.Items (s L) V))
    (streams : InternalStreams src μI (w L))
    (final : CodeSource 8192 (Q L) (Fin (w L) × Column src)
      ((PositiveRationalLaw.uniform (Fin (w L))).prod (columnLaw src)))
    (ξ₀ : Tail (s L) Y) (R : X → Y → Bool) :
    D (successor src streams final R
      (Paper2.SourceConstruction.activity order edge
        (by have hs := s_ge_64 L (by omega); omega) rep hq) ξ₀) ≤
        D R + h L + 1 ∧
    (∀ colour : V → Fin 3,
      (∀ e, colour (edge e false) ≠ colour (edge e true)) →
      D (successor src streams final R
        (Paper2.SourceConstruction.activity order edge
          (by have hs := s_ge_64 L (by omega); omega) rep hq) ξ₀) ≤
            D R + h L) := by
  have hs : 3 ≤ s L := by
    have hh := s_ge_64 L (by omega)
    omega
  have hq₁ : q₁ L + 2 = s L := by
    dsimp [q₁]
    exact Nat.sub_add_cancel (by omega : 2 ≤ s L)
  have hw : w L = 2^(2*L) := by
    change (2^L)^2 = 2^(2*L)
    rw [← pow_mul]
    congr 1
    omega
  have hQ : Q L = 2^(6*L) := by
    change (2^L)^6 = 2^(6*L)
    rw [← pow_mul]
    congr 1
    omega
  have hb := Sources.graph_indexed_successor_upper src order edge hs rep hq
    μI streams final ξ₀ R ((L+3)/4) (4*L) (2*L) (6*L)
    hq₁ rfl (q₂_eq_pow L) hw hQ
  have hcost : ((L+3)/4)+((L+3)/4)+4*L+2*L+6*L = h L := by
    dsimp [h]
    omega
  constructor
  · convert hb.1 using 1; omega
  · intro colour proper
    have hy := hb.2 colour proper
    convert hy using 1; omega

/-- The source's explicit graph-size guards give the exact public repetition
count required by the indexed coordinate constructor. -/
theorem scheduled_graph_repetition
    {V E : Type*} [Fintype V] [Fintype E]
    (L Δ : ℕ) (hL : 24*Δ+2004 ≤ L)
    (hV : Fintype.card V ≤
      CurrentAdditive.DeterministicParameters.N L) (hE : 0 < Fintype.card E)
    (hdegree : 2*Fintype.card E ≤ Δ*Fintype.card V) :
    ∃ rep : ℕ, q₂ L =
      Paper2.SourceItems.sourceQ0 (Fin (4*s L)) E * rep := by
  let k := Nat.clog 2 (12*s L*Fintype.card E)
  have hcard : Fintype.card
      (Paper2.SourceItems.Coord (Fin (4*s L)) E) =
        12*s L*Fintype.card E := by
    rw [Paper2.SourceItems.card_coord]
    simp only [Fintype.card_fin]
    ring
  have hq₀ : Paper2.SourceItems.sourceQ0 (Fin (4*s L)) E = 2^k := by
    dsimp [Paper2.SourceItems.sourceQ0,
      Paper2.SourcePadding.powTwoCeil, k]
    rw [hcard]
  have hlarge := q₂_large_for_graph L Δ (Fintype.card V)
    (Fintype.card E) hL hV hE hdegree
  have hle : 2^k ≤ 2^(4*L) := by
    simpa only [k, hq₀, q₂_eq_pow] using hlarge
  have hk : k ≤ 4*L :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle
  have hdiv : Paper2.SourceItems.sourceQ0 (Fin (4*s L)) E ∣ q₂ L := by
    rw [hq₀, q₂_eq_pow]
    exact pow_dvd_pow 2 hk
  exact ⟨q₂ L / Paper2.SourceItems.sourceQ0 (Fin (4*s L)) E,
    (Nat.mul_div_cancel' hdiv).symm⟩

/-- The public graph and size guards produce one concrete indexed successor
with both upper bounds. The YES bound is for any proper three-colouring of the
same graph, and the constructor itself is independent of that colouring. -/
theorem Sources.scheduled_graph_successor_upper_exists
    {V E X Y : Type*} [Fintype V] [Fintype E]
    [Fintype X] [Fintype Y] [DecidableEq V] [DecidableEq X] [DecidableEq Y]
    (L Δ : ℕ) (hL : 24*Δ+2004 ≤ L)
    (hV : Fintype.card V ≤
      CurrentAdditive.DeterministicParameters.N L) (hE : 0 < Fintype.card E)
    (hdegree : 2*Fintype.card E ≤ Δ*Fintype.card V)
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)]
    [NeZero (w L)] [NeZero (Q L)]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) μX μY)
    (order : Paper2.SourceConstruction.Items (s L) V ≃
      Fin (Fintype.card (Paper2.SourceConstruction.Items (s L) V)))
    (edge : E → Bool → V)
    (μI : PositiveRationalLaw (Paper2.SourceConstruction.Items (s L) V))
    (streams : InternalStreams src μI (w L))
    (final : CodeSource 8192 (Q L) (Fin (w L) × Column src)
      ((PositiveRationalLaw.uniform (Fin (w L))).prod (columnLaw src)))
    (ξ₀ : Tail (s L) Y) (R : X → Y → Bool) :
    ∃ rep : ℕ, ∃ hq : q₂ L =
      Paper2.SourceItems.sourceQ0 (Fin (4*s L)) E * rep,
      D (successor src streams final R
        (Paper2.SourceConstruction.activity order edge
          (by have hs := s_ge_64 L (by omega); omega) rep hq) ξ₀) ≤
          D R + h L + 1 ∧
      (∀ colour : V → Fin 3,
        (∀ e, colour (edge e false) ≠ colour (edge e true)) →
        D (successor src streams final R
          (Paper2.SourceConstruction.activity order edge
            (by have hs := s_ge_64 L (by omega); omega) rep hq) ξ₀) ≤
              D R + h L) := by
  obtain ⟨rep, hq⟩ := scheduled_graph_repetition L Δ hL hV hE hdegree
  exact ⟨rep, hq, Sources.scheduled_graph_successor_upper
    L (by omega) src order edge rep hq μI streams final ξ₀ R⟩

end CurrentAdditive.DeterministicIndexedMatrix
