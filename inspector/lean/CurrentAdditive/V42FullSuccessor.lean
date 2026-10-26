import CurrentAdditive.V42PublicSchedule
import CurrentAdditive.V39FullAmplifier

/-! Literal replacement-v42 full-product successor. This file establishes
its unconditional YES/general upper and rank bounds on the same actual
source matrix, before the separate NO/profile composition. -/
namespace CurrentAdditive.V42FullSuccessor
open Paper2 Paper2.SourceMatrix Paper2.RankLeaves Workspace.Types.CommComplexity
open CurrentAdditive.EdgeSourceMatrix
open V42PublicSchedule
set_option maxHeartbeats 2000000

def fullS (L : ℕ) : ℕ := V42Schedule.s (fullExponent L)
def fullQ₁ (L : ℕ) : ℕ := fullS L-2
def fullQ₂ (L : ℕ) : ℕ := V42Schedule.q₂ (fullExponent L) L
def fullW (L : ℕ) : ℕ := V42Schedule.w (fullExponent L)
def fullQ (L : ℕ) : ℕ := V42Schedule.Q (fullExponent L)
def fullQlog (L : ℕ) : ℕ := 24*fullExponent L
def overhead (L : ℕ) : ℕ := fullOverhead L

theorem fullS_ge_256 (L : ℕ) : 256≤fullS L := by
  unfold fullS V42Schedule.s fullExponent
  change 2^8 ≤ 2^(16+ell L)
  exact Nat.pow_le_pow_right (by decide) (by omega)
theorem fullQ₂_mul (L : ℕ) : fullQ₂ L=2^L*(fullS L)^2 := by
  simp only [fullQ₂,fullS,V42Schedule.q₂,V42Schedule.s]
  rw [pow_add,show 2*fullExponent L=fullExponent L*2 by omega,pow_mul]
theorem fullQ_pow (L : ℕ) : fullQ L=2^(fullQlog L) := rfl
instance fullS_neZero (L : ℕ) : NeZero (fullS L) := ⟨by unfold fullS V42Schedule.s; positivity⟩
instance fullQ₁_neZero (L : ℕ) : NeZero (fullQ₁ L) := ⟨by have := fullS_ge_256 L; unfold fullQ₁; omega⟩
instance fullQ₂_neZero (L : ℕ) : NeZero (fullQ₂ L) := ⟨by unfold fullQ₂ V42Schedule.q₂; positivity⟩
instance fullW_neZero (L : ℕ) : NeZero (fullW L) := ⟨by unfold fullW V42Schedule.w; positivity⟩
instance fullQ_neZero (L : ℕ) : NeZero (fullQ L) := ⟨by unfold fullQ V42Schedule.Q; positivity⟩

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
  [DecidableEq V] [DecidableEq E] [DecidableEq X] [DecidableEq Y]

noncomputable def internal (L : ℕ)
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (rep : ℕ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep)
    (R : X → Y → Bool) (ξ₀ : Tail (fullS L) Y) :
    (Fin (fullW L) → RawRow (fullQ₁ L) (fullQ₂ L) (fullS L) X (Items (fullS L) V)) →
    (Fin (fullW L) × V38Matrix.TaggedColumn (fullQ₁ L) (fullQ₂ L) (fullS L) Y) → Bool :=
  fun z a => V38Matrix.matrix order edge (by have := fullS_ge_256 L; omega) rep hq R ξ₀ a.2 (z a.1)

noncomputable def successor (L : ℕ)
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (rep : ℕ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep)
    (R : X → Y → Bool) (ξ₀ : Tail (fullS L) Y) :
    (Fin (fullQ L) → Fin (fullW L) × V38Matrix.TaggedColumn (fullQ₁ L) (fullQ₂ L) (fullS L) Y) →
    (Fin (fullQ L) × (Fin (fullW L) → RawRow (fullQ₁ L) (fullQ₂ L) (fullS L) X (Items (fullS L) V))) → Bool :=
  fun z a => internal L order edge rep hq R ξ₀ a.2 (z a.1)

noncomputable def rowLaw (ν : PositiveRationalLaw Y) (L : ℕ) :=
  V38OneStep.successorRowLaw (q₁ := fullQ₁ L) (q₂ := fullQ₂ L)
    (s := fullS L) (w := fullW L) (Q := fullQ L) ν
noncomputable def columnLaw (μ : PositiveRationalLaw X) (L : ℕ) :=
  V38OneStep.successorColumnLaw (q₁ := fullQ₁ L) (q₂ := fullQ₂ L)
    (s := fullS L) (V := V) (w := fullW L) (Q := fullQ L) μ
    (by have := fullS_ge_256 L; omega)

theorem upper
    (L : ℕ)
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (rep : ℕ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep)
    (R : X → Y → Bool) (ξ₀ : Tail (fullS L) Y) :
    D (successor L order edge rep hq R ξ₀) ≤ D R+overhead L+1 ∧
    (∀ colour : V → Fin 3, (∀ e, colour (edge e false)≠colour (edge e true)) →
      D (successor L order edge rep hq R ξ₀) ≤ D R+overhead L) := by
  classical
  have hs : 3≤fullS L := by have := fullS_ge_256 L; omega
  have hq₁ : fullQ₁ L+2=fullS L := by unfold fullQ₁; omega
  have hq₂ : fullQ₂ L=2^(L+2*(fullExponent L)) := by
    rfl
  have hu := V38Matrix.matrix_upper_budgets (q₁ := fullQ₁ L) order edge hs rep hq R ξ₀
    (fullExponent L) (L+2*(fullExponent L)) hq₁ rfl hq₂
  have hw : fullW L=2^(8*fullExponent L) := rfl
  have hW : D (internal L order edge rep hq R ξ₀) ≤
      8*fullExponent L+D (V38Matrix.matrix (q₁ := fullQ₁ L) order edge hs rep hq R ξ₀) := by
    have hh := Paper2.fullInterlace_transpose_D_le
      (V38Matrix.matrix (q₁ := fullQ₁ L) order edge hs rep hq R ξ₀) (fullW L)
      (by unfold fullW V42Schedule.w; positivity)
    rw [hw,Nat.clog_pow 2 _ (by decide)] at hh
    exact hh
  have hS : D (successor L order edge rep hq R ξ₀) ≤
      fullQlog L+D (internal L order edge rep hq R ξ₀) := by
    have hh := Paper2.fullInterlace_transpose_D_le (internal L order edge rep hq R ξ₀)
      (fullQ L) (by unfold fullQ V42Schedule.Q; positivity)
    rw [show Nat.clog 2 (fullQ L)=fullQlog L by
      rw [fullQ_pow,Nat.clog_pow 2 _ (by decide)]] at hh
    exact hh
  constructor
  · have := hu.1
    unfold overhead V42PublicSchedule.fullOverhead fullQlog at *
    omega
  · intro colour proper
    have := hu.2 colour proper
    unfold overhead V42PublicSchedule.fullOverhead fullQlog at *
    omega

/-- The two literal interlaces multiply the actual current two-family
source rank by their widths. -/
theorem rank_le
    (L : ℕ) (hn : Fintype.card V≤2^L)
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (rep : ℕ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep)
    (R : X → Y → Bool) (ξ₀ : Tail (fullS L) Y) :
    (realMatrix (successor L order edge rep hq R ξ₀)).rank≤
      2^overhead L*(realMatrix R).rank := by
  classical
  have hs : 3≤fullS L := by have := fullS_ge_256 L; omega
  have hsq : 2*fullS L+2≤(fullS L)^2 := by nlinarith
  have ha : 1≤2^L := Nat.one_le_two_pow
  have hkey : 2*(Fintype.card V+fullS L)≤fullQ₂ L := by
    rw [fullQ₂_mul]
    have hm := Nat.mul_le_mul_left (2^L) hsq
    nlinarith
  have hI : Fintype.card (Items (fullS L) V)≤2*fullS L*fullQ₂ L := by
    simp only [Items,Fintype.card_prod,Fintype.card_fin,Fintype.card_sum]
    have hm := Nat.mul_le_mul_left (2*fullS L) hkey
    have hsub : fullS L-3≤fullS L := Nat.sub_le _ _
    nlinarith
  have hN := V38Matrix.matrix_rank_le (q₁ := fullQ₁ L) order edge hs rep hq R ξ₀
  have hW : (realMatrix (internal L order edge rep hq R ξ₀)).rank≤
      fullW L*(realMatrix (V38Matrix.matrix (q₁ := fullQ₁ L) order edge hs rep hq R ξ₀)).rank := by
    have hh := fullInterlace_rank_le (V38Matrix.matrix (q₁ := fullQ₁ L) order edge hs rep hq R ξ₀)
      (fullW L)
    change (realMatrix (fun z a => fullInterlace
      (V38Matrix.matrix (q₁ := fullQ₁ L) order edge hs rep hq R ξ₀) (fullW L) a z)).rank≤_
    rw [transpose_rank]
    exact hh
  have hS : (realMatrix (successor L order edge rep hq R ξ₀)).rank≤
      fullQ L*(realMatrix (internal L order edge rep hq R ξ₀)).rank := by
    change (realMatrix (fun z a => fullInterlace
      (internal L order edge rep hq R ξ₀) (fullQ L) a z)).rank≤_
    rw [transpose_rank]
    exact fullInterlace_rank_le _ _
  have hfactor : fullS L*fullQ₁ L*fullQ₂ L+Fintype.card (Items (fullS L) V)≤
      (fullS L)^2*fullQ₂ L := by
    have hq₁ : fullQ₁ L+2=fullS L := by unfold fullQ₁; omega
    calc _≤fullS L*fullQ₁ L*fullQ₂ L+2*fullS L*fullQ₂ L := Nat.add_le_add_left hI _
         _=fullS L*(fullQ₁ L+2)*fullQ₂ L := by ring
         _=_ := by rw [hq₁]; ring
  have hpow : fullQ L*fullW L*((fullS L)^2*fullQ₂ L)=2^overhead L := by
    rw [fullQ_pow]
    simp only [fullQ₂,fullS,fullW,V42Schedule.q₂,V42Schedule.s,V42Schedule.w,←pow_mul,←pow_add]
    congr 1
    unfold overhead V42PublicSchedule.fullOverhead fullQlog
    omega
  calc
    _≤fullQ L*(fullW L*((fullS L*fullQ₁ L*fullQ₂ L+
        Fintype.card (Items (fullS L) V))*(realMatrix R).rank)) :=
      hS.trans (Nat.mul_le_mul_left _ (hW.trans (Nat.mul_le_mul_left _ hN)))
    _≤fullQ L*(fullW L*(((fullS L)^2*fullQ₂ L)*(realMatrix R).rank)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hfactor))
    _=(fullQ L*fullW L*((fullS L)^2*fullQ₂ L))*(realMatrix R).rank := by ring
    _=_ := by rw [hpow]


#print axioms upper
#print axioms rank_le
end CurrentAdditive.V42FullSuccessor
