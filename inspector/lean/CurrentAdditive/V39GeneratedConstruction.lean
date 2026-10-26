import CurrentAdditive.V38Matrix
import CurrentAdditive.DeterministicIndexedUpper
import Mathlib.Logic.Equiv.Fin.Basic

/-!
Literal two-family construction for selected v39, det:construction.
Finite alphabets are numbered by supplied executable equivalences. Source
generation is a single reusable callable operation, with no profile, protocol,
colouring or graph-promise inputs. The constructor and source-machine clock
are separate obligations; this file does not assert a physical printer.
-/

namespace CurrentAdditive.V39GeneratedConstruction

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicIndexedMatrix
open scoped BigOperators

def uniform (n : ℕ) [NeZero n] : PositiveRationalLaw (Fin n) where
  weight _ := (n : ℚ)⁻¹
  positive _ := inv_pos.mpr (by exact_mod_cast NeZero.pos n)
  total := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (NeZero.pos n).ne')

def product {A B : Type} [Fintype A] [Fintype B]
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw B) :
    PositiveRationalLaw (A × B) where
  weight a := μ.weight a.1 * ν.weight a.2
  positive a := mul_pos (μ.positive _) (ν.positive _)
  total := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ν.total, mul_one, μ.total]

def mixture {A B : Type} [Fintype A] [Fintype B]
    (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw B) :
    PositiveRationalLaw (A ⊕ B) where
  weight
    | .inl a => (255 / 256) * μ.weight a
    | .inr b => (1 / 256) * ν.weight b
  positive a := by
    cases a with
    | inl a => exact mul_pos (by norm_num) (μ.positive a)
    | inr b => exact mul_pos (by norm_num) (ν.positive b)
  total := by
    rw [Fintype.sum_sum_type]
    simp only [← Finset.mul_sum, μ.total, ν.total, mul_one]
    norm_num

def reindex {A : Type} [Fintype A] {n : ℕ}
    (e : A ≃ Fin n) (μ : PositiveRationalLaw A) :
    PositiveRationalLaw (Fin n) where
  weight i := μ.weight (e.symm i)
  positive i := μ.positive (e.symm i)
  total := by
    rw [← Equiv.sum_comp e]
    simpa using μ.total

/-- All output indices remain present even when their decoded tuples agree. -/
structure ExactList (D q : ℕ) (A : Type) [Fintype A] [DecidableEq A]
    (μ : PositiveRationalLaw A) where
  size : ℕ
  law : PositiveRationalLaw (Fin size)
  decode : Fin size → Fin q → A
  exactLaw : IsDWise D law.toFiniteLaw decode μ.toFiniteLaw

def ExactList.source {D q : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    {μ : PositiveRationalLaw A} (src : ExactList D q A μ) :
    CodeSource D q A μ where
  Label := Fin src.size
  finite := inferInstance
  decEq := inferInstance
  law := src.law
  decode := src.decode
  exactLaw := src.exactLaw

/-- Input law and output index law are rational data. This interface is the
single remaining Code D operation; it carries no desired matrix conclusion. -/
structure CodeD (D : ℕ) where
  run : (q n : ℕ) → (μ : PositiveRationalLaw (Fin n)) →
    ExactList D q (Fin n) μ

theorem pi_reindex {A : Type} [Fintype A] {n : ℕ}
    (e : A ≃ Fin n) (μ : PositiveRationalLaw A)
    {J : Type} [Fintype J] [DecidableEq J] (E : (J → A) → Prop) :
    (FiniteLaw.pi (fun _ : J => (reindex e μ).toFiniteLaw)).prob
      (fun z => E (fun i => e.symm (z i))) =
      (FiniteLaw.pi (fun _ : J => μ.toFiniteLaw)).prob E := by
  apply FiniteLaw.prob_preimage_eq_of_fibres
  intro y
  have hev : (fun z : J → Fin n => (fun i => e.symm (z i)) = y) =
      (fun z => ∀ i, z i = e (y i)) := by
    funext z
    apply propext
    constructor
    · intro h i
      have := congrFun h i
      simpa using congrArg e this
    · intro h
      funext i
      simp [h i]
  rw [hev]
  rw [FiniteLaw.pi_prob_coordinatewise
    (fun _ : J => (reindex e μ).toFiniteLaw) (fun i z => z = e (y i))]
  simp only [FiniteLaw.prob_singleton, FiniteLaw.pi,
    PositiveRationalLaw.toFiniteLaw, reindex, Equiv.symm_apply_apply]

def ExactList.renumber {D q n : ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (e : A ≃ Fin n) (μ : PositiveRationalLaw A)
    (src : ExactList D q (Fin n) (reindex e μ)) : ExactList D q A μ where
  size := src.size
  law := src.law
  decode j p := e.symm (src.decode j p)
  exactLaw S hS E := (src.exactLaw S hS
    (fun z => E (fun i => e.symm (z i)))).trans (pi_reindex e μ E)

def CodeD.call {D : ℕ} (c : CodeD D) (q : ℕ)
    {A : Type} [Fintype A] [DecidableEq A] {n : ℕ}
    (e : A ≃ Fin n) (μ : PositiveRationalLaw A) : ExactList D q A μ :=
  (c.run q n (reindex e μ)).renumber e μ

section Construction

variable {D q₁ q₂ s w Q nx ny ni : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]
  (c : CodeD D) (μX : PositiveRationalLaw (Fin nx))
  (μY : PositiveRationalLaw (Fin ny)) (μI : PositiveRationalLaw (Fin ni))

/-- The first three literal Code D calls. -/
structure SourceData where
  gamma : ExactList D (q₁+s+1) (Fin ny) μY
  inner : ExactList D q₂ (Fin q₁ × Fin nx) (product (uniform q₁) μX)
  outer : ExactList D s (Fin q₂ × Fin gamma.size)
    (product (uniform q₂) gamma.law)

def sourceData : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY :=
  let gamma := c.run (q₁+s+1) ny μY
  let inner := c.call q₂ finProdFinEquiv (product (uniform q₁) μX)
  let outer := c.call s finProdFinEquiv (product (uniform q₂) gamma.law)
  ⟨gamma, inner, outer⟩

namespace SourceData

variable {μX μY μI}
variable (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

abbrev Column := (Fin src.outer.size × Fin src.gamma.size) ⊕
  (Fin q₂ × Fin src.gamma.size)

abbrev Row := (Fin s × Fin src.inner.size) ⊕ (Fin ni × Fin nx)

def columnOrder : src.Column ≃
    Fin (src.outer.size*src.gamma.size+q₂*src.gamma.size) :=
  (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv

def columnLaw : PositiveRationalLaw src.Column :=
  mixture (product src.outer.law src.gamma.law)
    (product (uniform q₂) src.gamma.law)

def rowLaw : PositiveRationalLaw (src.Row (ni := ni)) :=
  mixture (product (uniform s) src.inner.law) (product μI μX)

def decodeRow : src.Row (ni := ni) → RawRow q₁ q₂ s (Fin nx) (Fin ni)
  | .inl (p, z) => .inl (p, src.inner.decode z)
  | .inr ix => .inr ix

def decodeColumn : src.Column → RawColumn q₁ q₂ s (Fin ny)
  | .inl (j, γ) => (tail (src.gamma.decode γ),
      fun p => let a := src.outer.decode j p; (a.1, src.gamma.decode a.2))
  | .inr (a, γ) => (tail (src.gamma.decode γ), fun _ => (a, src.gamma.decode γ))

def B (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s)) :
    src.Row (ni := ni) → src.Column → Bool :=
  fun k Z => raw R activity (src.decodeRow k) (src.decodeColumn Z)

/-- The next three calls are independent complete metadata, base and selector
lists. Their product indices are retained, even when words decode equally. -/
structure Streams where
  metadata : ExactList D w (Fin s ⊕ Fin ni) (mixture (uniform s) μI)
  base : ExactList D w (Fin nx) μX
  selector : ExactList D w (Fin src.inner.size) src.inner.law

def streams : src.Streams (w := w) (μI := μI) :=
  ⟨c.call w finSumFinEquiv (mixture (uniform s) μI),
    c.run w nx μX, c.run w src.inner.size src.inner.law⟩

namespace Streams

variable (st : src.Streams (w := w) (μI := μI))

abbrev Label := Fin st.metadata.size × (Fin st.base.size × Fin st.selector.size)

def order : st.Label ≃ Fin (st.metadata.size*(st.base.size*st.selector.size)) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv

def law : PositiveRationalLaw st.Label :=
  product st.metadata.law (product st.base.law st.selector.law)

def decode (j : st.Label) (p : Fin w) : src.Row (ni := ni) :=
  match st.metadata.decode j.1 p with
  | .inl bin => .inl (bin, st.selector.decode j.2.2 p)
  | .inr i => .inr (i, st.base.decode j.2.1 p)

end Streams

/-- Seventh call. No expansion to a full-product input alphabet occurs. -/
def final : ExactList D Q (Fin w × src.Column)
    (product (uniform w) src.columnLaw) :=
  c.call Q ((Equiv.prodCongr (Equiv.refl _) src.columnOrder).trans finProdFinEquiv)
    (product (uniform w) src.columnLaw)

def successor (st : src.Streams (w := w) (μI := μI))
    (out : ExactList D Q (Fin w × src.Column)
      (product (uniform w) src.columnLaw))
    (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s)) :
    Fin out.size → (Fin Q × st.Label) → Bool :=
  fun j a => src.B R activity (Streams.decode src st a.2 (out.decode j a.1).1)
    (out.decode j a.1).2

theorem B_upper (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s)) :
    Workspace.Types.CommComplexity.D (src.B R activity) ≤ Nat.clog 2 s + Nat.clog 2 q₂ +
      Nat.clog 2 (q₁+s+1) + Workspace.Types.CommComplexity.D R := by
  have hp := Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (raw (q₁ := q₁) R activity) src.decodeRow src.decodeColumn
  exact hp.trans (Paper2.SourceMatrix.raw_D_le activity R)

theorem B_yes (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s))
    (assign : Fin ni → Fin s) (hc : CollisionFree assign activity) :
    Workspace.Types.CommComplexity.D (src.B R activity) ≤ Nat.clog 2 s + Nat.clog 2 q₂ +
      Nat.clog 2 (q₁+2) + Workspace.Types.CommComplexity.D R := by
  have hp := Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (raw (q₁ := q₁) R activity) src.decodeRow src.decodeColumn
  exact hp.trans (Paper2.SourceMatrix.raw_D_le_of_collisionFree assign activity hc R)

theorem successor_cost (st : src.Streams (w := w) (μI := μI))
    (out : ExactList D Q (Fin w × src.Column)
      (product (uniform w) src.columnLaw))
    (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s)) :
    Workspace.Types.CommComplexity.D (src.successor st out R activity) ≤ Nat.clog 2 Q + Nat.clog 2 w +
      Workspace.Types.CommComplexity.D (src.B R activity) := by
  let N := fun Z k => src.B R activity k Z
  let W := fun (j : st.Label) (pZ : Fin w × src.Column) => src.B R activity
    (Streams.decode src st j pZ.1) pZ.2
  have hi := Paper2.indexedInterlace_transpose_D_le N (NeZero.pos w)
    (Streams.decode src st)
  change Workspace.Types.CommComplexity.D W ≤ Nat.clog 2 w +
    Workspace.Types.CommComplexity.D N at hi
  have ht : Workspace.Types.CommComplexity.D N =
      Workspace.Types.CommComplexity.D (src.B R activity) := transpose_D _
  have hi' : Workspace.Types.CommComplexity.D W ≤ Nat.clog 2 w + Workspace.Types.CommComplexity.D (src.B R activity) := by
    rw [ht] at hi
    exact hi
  have ho := Paper2.indexedInterlace_transpose_D_le W (NeZero.pos Q) out.decode
  change Workspace.Types.CommComplexity.D (src.successor st out R activity) ≤ Nat.clog 2 Q + Workspace.Types.CommComplexity.D W at ho
  omega

theorem successor_upper (st : src.Streams (w := w) (μI := μI))
    (out : ExactList D Q (Fin w × src.Column)
      (product (uniform w) src.columnLaw))
    (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s)) :
    Workspace.Types.CommComplexity.D (src.successor st out R activity) ≤ Workspace.Types.CommComplexity.D R +
      (Nat.clog 2 s+Nat.clog 2 q₂+Nat.clog 2 (q₁+s+1)+
        Nat.clog 2 w+Nat.clog 2 Q) := by
  have := src.successor_cost st out R activity
  have := src.B_upper R activity
  omega

theorem successor_yes (st : src.Streams (w := w) (μI := μI))
    (out : ExactList D Q (Fin w × src.Column)
      (product (uniform w) src.columnLaw))
    (R : Fin nx → Fin ny → Bool)
    (activity : Fin ni → Fin q₂ → Option (Fin s))
    (assign : Fin ni → Fin s) (hc : CollisionFree assign activity) :
    Workspace.Types.CommComplexity.D (src.successor st out R activity) ≤ Workspace.Types.CommComplexity.D R +
      (Nat.clog 2 s+Nat.clog 2 q₂+Nat.clog 2 (q₁+2)+
        Nat.clog 2 w+Nat.clog 2 Q) := by
  have := src.successor_cost st out R activity
  have := src.B_yes R activity assign hc
  omega

end SourceData
end Construction

end CurrentAdditive.V39GeneratedConstruction
