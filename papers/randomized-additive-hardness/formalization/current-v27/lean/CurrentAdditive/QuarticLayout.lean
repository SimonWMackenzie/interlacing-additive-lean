import CurrentAdditive.QuarticDispatchAssembly
import Paper2.A3LLayout

/-! The existing physical bank layout with its canonical start region replaced
by the literal v27 quartic schedule. -/

namespace Paper2.CurrentAdditive.QuarticLayout

open EthInapproximability.CurrentPaper
open Paper2 Paper2.A3Assembly
open Paper2.SourceProfileParameters Paper2.SourceRecursiveNoSampling
open Paper2.CurrentAdditive.QuarticDispatchSpec
open Paper2.CurrentAdditive.QuarticConstructor
open CurrentAdditive.RandomizedSchedule

variable (FS : Type) [Fintype FS] [DecidableEq FS]

/-- The numeric start bank consumed by the checked v27 success and probe machines. -/
noncomputable def startCanon27 (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0 < g.vertices) (k : ℕ)
    (t : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :
    SuccessOrient.Stack → List Bool :=
  SuccessOrient.startBank g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
    (width (Nat.clog 2 g.vertices)) (width (Nat.clog 2 g.vertices) - 2)
    (outerWidth (Nat.clog 2 g.vertices))
    (width27 (Nat.clog 2 g.vertices))
    (Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) γ Δ) k
    (sourceRows (Nat.clog 2 g.vertices)
      (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))
      (q27 (V := Fin g.vertices) (E := Fin g.edges.length)
        (Nat.clog 2 g.vertices) γ Δ) k)
    (sourceCols (Nat.clog 2 g.vertices)
      (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))
      (q27 (V := Fin g.vertices) (E := Fin g.edges.length)
        (Nat.clog 2 g.vertices) γ Δ) k)
    ((select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t)

/-- The physical front postcondition, with the source packet preserved and the
literal quartic parameter bank in the master region. -/
def Mid1_27 (Δ : ℕ) (γ : ℚ) (CM EM : ℕ) : Pred Δ γ (Lift.a FS) :=
  fun g hg hn k t S =>
    (∃ (b : Bool) (Z : FS → List Bool),
      S = Lift.layoutBank FS (inputBank27 Δ γ g hg hn k t)
        (Lift.region FS (startCanon27 Δ γ g hg hn k t) ![[b], [], []] Z)) ∧
    (BitMachineBankCodec.encode S).length ≤
      CM * (g.vertices + 2) ^ (EM * (k + 1))

/-- The physical probe postcondition; only the second flag has changed. -/
def Mid2_27 (Δ : ℕ) (γ : ℚ) (CM EM : ℕ) : Pred Δ γ (Lift.a FS) :=
  fun g hg hn k t S =>
    (∃ (b₁ b₂ : Bool) (Z : FS → List Bool),
      S = Lift.layoutBank FS (inputBank27 Δ γ g hg hn k t)
        (Lift.region FS (startCanon27 Δ γ g hg hn k t) ![[b₁], [b₂], []] Z)) ∧
    (BitMachineBankCodec.encode S).length ≤
      CM * (g.vertices + 2) ^ (EM * (k + 1))

theorem input_layout27 (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0 < g.vertices) (k : ℕ)
    (t : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :
    Wrap.widen (Lift.a FS) (inputBank27 Δ γ g hg hn k t) =
      Lift.layoutBank FS (inputBank27 Δ γ g hg hn k t) (fun _ => []) :=
  Lift.widen_eq FS _

#print axioms input_layout27

end Paper2.CurrentAdditive.QuarticLayout
