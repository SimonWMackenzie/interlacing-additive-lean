import CurrentAdditive.V39StoredGenerated
import CurrentAdditive.EdgeIndexedLawProduction
import CurrentAdditive.DeterministicETHSeed

/-! A literal finite graph-to-table algorithm, with actual public item law,
edge-only activity, indexed lookup seed, seven order-8192 sources per round,
and explicit intermediate matrix/law storage. The current schedule must still
choose the positive widths and its public repetition equality. NO/profile and
physical bit-runtime are separate obligations, not constructor hypotheses. -/

namespace CurrentAdditive.V39GeneratedConstruction

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open CurrentAdditive.LiteralEdgeEncoder
open CurrentAdditive.DeterministicETHSeed
open Paper2.LookupSeed

def lookupSeed (L : ℕ) : NumberedMatrix := by
  haveI : NeZero (width L) := ⟨(Nat.two_pow_pos (exponent L)).ne'⟩
  exact ⟨2^(width L), width L, uniform _, uniform _, indexedSeed L⟩

def storedLookupSeed (L : ℕ) : StoredMatrix := StoredMatrix.ofNumbered (lookupSeed L)

theorem storedLookupSeed_cost (L : ℕ) :
    D (storedLookupSeed L).entry = exponent L+1 := by
  have he : (storedLookupSeed L).entry = indexedSeed L := by
    funext r c
    exact StoredMatrix.ofNumbered_entry (lookupSeed L) r c
  rw [he]
  exact indexedSeed_cost L

variable {s n m r q₂ w Q : ℕ} [NeZero s] [NeZero q₂] [NeZero w] [NeZero Q]

/-- Public coordinate relabelling only; repeated base coordinates are ordered
exactly as the literal edge encoder. -/
def graphActivity (hs : 3 ≤ s)
    (hq : q₂ = LiteralEdgeEncoder.Width s m r)
    (edge : Fin m → Bool → Fin n) :
    Fin (4*s*(n+(s-3))) → Fin q₂ → Option (Fin s) :=
  fun i a => indexedActivity hs edge i (Fin.cast hq a)

theorem graphActivity_yes (hs : 3 ≤ s)
    (hq : q₂ = LiteralEdgeEncoder.Width s m r)
    (edge : Fin m → Bool → Fin n) (colour : Fin n → Fin 3)
    (proper : ∀ j, colour (edge j false) ≠ colour (edge j true)) :
    CollisionFree (indexedAssignment hs colour) (graphActivity hs hq edge) := by
  intro a i j b b' hi hj heq
  exact indexedActivity_collisionFree hs edge colour proper
    (Fin.cast hq a) i j b b' hi hj heq

def graphRun (hs : 4 ≤ s) (hn : 0 < n)
    (hq : q₂ = LiteralEdgeEncoder.Width s m r)
    (edge : Fin m → Bool → Fin n) (L k : ℕ) : StoredMatrix := by
  haveI : NeZero (s-2) := ⟨by omega⟩
  exact StoredMatrix.iterate (q₁ := s-2) (s := s) (w := w) (Q := Q)
    (indexedItemLaw s n hs hn) (graphActivity (by omega) hq edge)
    k (storedLookupSeed L)

def graphIncrement (s q₂ w Q : ℕ) : ℕ :=
  2*Nat.clog 2 s+Nat.clog 2 q₂+Nat.clog 2 w+Nat.clog 2 Q

def graphThreshold (L k s q₂ w Q : ℕ) : ℕ :=
  exponent L+1+k*graphIncrement s q₂ w Q

theorem graphRun_yes (hs : 4 ≤ s) (hn : 0 < n)
    (hq : q₂ = LiteralEdgeEncoder.Width s m r)
    (edge : Fin m → Bool → Fin n) (L k : ℕ)
    (colour : Fin n → Fin 3)
    (proper : ∀ j, colour (edge j false) ≠ colour (edge j true)) :
    D (graphRun (w := w) (Q := Q) hs hn hq edge L k).entry ≤
      graphThreshold L k s q₂ w Q := by
  haveI : NeZero (s-2) := ⟨by omega⟩
  have hs3 : 3 ≤ s := by omega
  have hy := StoredMatrix.iterate_yes (q₁ := s-2) (s := s) (w := w) (Q := Q)
    (indexedItemLaw s n hs hn) (graphActivity hs3 hq edge) k (storedLookupSeed L)
    (indexedAssignment hs3 colour) (graphActivity_yes hs3 hq edge colour proper)
  have hs2 : s-2+2 = s := by omega
  rw [storedLookupSeed_cost, hs2] at hy
  have hh : Nat.clog 2 s+Nat.clog 2 q₂+Nat.clog 2 s+
      Nat.clog 2 w+Nat.clog 2 Q = graphIncrement s q₂ w Q := by
    simp only [graphIncrement]
    omega
  rw [hh] at hy
  exact hy

def graphRectangle (hs : 4 ≤ s) (hn : 0 < n)
    (hq : q₂ = LiteralEdgeEncoder.Width s m r)
    (edge : Fin m → Bool → Fin n) (L k : ℕ) :=
  (graphRun (w := w) (Q := Q) hs hn hq edge L k).rectangle
    (graphThreshold L k s q₂ w Q)

theorem graphRectangle_valid (hs : 4 ≤ s) (hn : 0 < n)
    (hq : q₂ = LiteralEdgeEncoder.Width s m r)
    (edge : Fin m → Bool → Fin n) (L k : ℕ) :
    (graphRectangle (w := w) (Q := Q) hs hn hq edge L k).Valid :=
  StoredMatrix.rectangle_valid _ _

end CurrentAdditive.V39GeneratedConstruction
