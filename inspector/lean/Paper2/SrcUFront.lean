import Paper2.SrcU

/-! Unit 3, segment (1), the unrestricted source arm, first three phases
(`SrcU.z2` = item operands ; outer-token equality ; physical scan) on the
bank `SrcU.JA`, both scan branches, with the exact phase-3 bank in the
normal form `Sum.elim (B-part) (Sum.elim (scan bank) (Fin 4 part))` and the
activity/rank read-out relating the scan cells to `scanAtCanonical`. -/

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.SrcU

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource RecursiveRequestCodeShape
open RecursiveLabelCodecScratch RecursiveEntries SourceMatrix
open BitMachineRawSequence (leftLabel)
open Paper2.OTOps (u)
open Paper2.OTBody (B BB aC eqC sC idxB lblB ob)
open Paper2.ScanDecodeMachine (K D0)
open Paper2.RankRun (R RB)

theorem liftA {Kk L V : Type*} [DecidableEq Kk] (ι : Kk ↪ JA)
    (P : L → TM2.Stmt (fun _ : Kk => Bool) L V)
    (W : JA → List Bool) (S T : Kk → List Bool) (hS : ∀ k, S k = W (ι k)) (l : L) (v v' : V)
    (t : ℕ)
    (hrun : ((advance P)^[t]) (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) =
      ⟨none, v', T⟩) :
    ((advance (fun l => stackStmt ι (P l)))^[t])
        (⟨some l, v, W⟩ : TM2.Cfg (fun _ : JA => Bool) L V) =
      ⟨none, v', bank ι W T⟩ := by
  have hs := BitMachineStackRun.run ι W P (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) t
  rw [hrun] at hs
  simp only [stackCfg] at hs
  rwa [bank_eq_self ι W S hS] at hs

variable {p s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q] [NeZero s]

/-- The JJ-part of the entry bank: decode cells `r`, `m` (the others blank),
the literal public graph bytes, the controller cells blank. -/
def JJ0 (g : EncodedGraph.Graph) (r : ℕ) : ScanJoin.JJ → List Bool :=
  Sum.elim (D0 0 r g.edges.length 0)
    (Sum.elim (EndpointOperands.entry g 0) (RB [] [] [] [] [] [] []))

def JJ1 (g : EncodedGraph.Graph) (r ig xv : ℕ) (kb : Bool) : ScanJoin.JJ → List Bool :=
  Sum.elim (D0 0 r g.edges.length ig)
    (Sum.elim (EndpointOperands.entry g 0)
      (RB [] [] (CanonicalEndpointRankMachine.unaryWord xv) [] [] [kb] []))

theorem items_bank (X : B → List Bool) (g : EncodedGraph.Graph) (r ig xv : ℕ) (kb : Bool)
    (w0 w1 : List Bool) :
    Function.update (Function.update (Function.update (Function.update
      (Sum.elim X (Sum.elim (JJ0 g r) ![w0, [], [], []]) : JA → List Bool) srcA w1)
      iA (List.replicate ig true)) iK [kb]) iX (CanonicalEndpointRankMachine.unaryWord xv) =
    Sum.elim X (Sum.elim (JJ1 g r ig xv kb) ![w1, [], [], []]) := by
  have hD : Function.update (D0 0 r g.edges.length 0) (12 : K) (List.replicate ig true) =
      D0 0 r g.edges.length ig := by
    funext j; fin_cases j <;> rfl
  have hR : Function.update (Function.update (RB [] [] [] [] [] [] [] : R → List Bool) (5 : R) [kb])
      (2 : R) (CanonicalEndpointRankMachine.unaryWord xv) =
      RB [] [] (CanonicalEndpointRankMachine.unaryWord xv) [] [] [kb] [] := by
    funext j; fin_cases j <;> rfl
  have hF : Function.update (![w0, [], [], []] : Fin 4 → List Bool) 0 w1 = ![w1, [], [], []] := by
    funext j; fin_cases j <;> rfl
  simp only [srcA, iA, iK, iX, JJ0, JJ1, Sum.update_elim_inr, Sum.update_elim_inl, hD, hR, hF]

theorem scan_entry (X : B → List Bool) (Z4 : Fin 4 → List Bool) (g : EncodedGraph.Graph)
    (a r ig xv : ℕ) (kb : Bool) (hX : X aC = u a) :
    ∀ x, ScanJoin.W0 g a r ig xv kb x =
      (Sum.elim X (Sum.elim (JJ1 g r ig xv kb) Z4) : JA → List Bool) (ιS x) := by
  intro x
  by_cases hx : x = K0
  · subst hx
    rw [ιS_K0]
    simp only [Sum.elim_inl, hX]
    rfl
  · rw [ιS_ne x hx]
    rcases x with x | x
    · fin_cases x
      · exact absurd rfl hx
      all_goals rfl
    · rfl

end

end Paper2.SrcU
