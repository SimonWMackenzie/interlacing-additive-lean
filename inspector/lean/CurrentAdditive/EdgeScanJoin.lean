import CurrentAdditive.EdgeScanTest
import Paper2.RankRun
import Paper2.EndpointOperands
import Paper2.TagDispatch

/-! Physical edge-only scan assembled from two divisions, the group test, actual encoded-graph endpoint retrieval, and the existing endpoint-rank controller at its edge kind. Every shared operand cell is identified below. The separate EdgeActivityRank bridge supplies finite source semantics. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace CurrentAdditive.LiteralEdgeScanJoin

noncomputable section

open Paper2
open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)
open CurrentAdditive.LiteralEdgeDecodeDependency (K u)
open Paper2.EndpointOperands (KE uC vC)
open Paper2.RankRun (R RB)

abbrev JJ := K ⊕ (KE ⊕ R)

def eCE : KE := .inl GraphPrefixBind.eC

def ιTf (i : K) : JJ := if i = 8 then .inr (.inl eCE) else if i = 5 then .inr (.inr 4) else .inl i

def ιEf (x : KE) : JJ := if x = uC then .inr (.inr 0) else if x = vC then .inr (.inr 1) else .inr (.inl x)

theorem ιTf_inj : Function.Injective ιTf := by
  intro a b h
  simp only [ιTf] at h
  split_ifs at h <;> simp_all

theorem ιEf_inj : Function.Injective ιEf := by
  intro a b h
  simp only [ιEf] at h
  split_ifs at h <;> simp_all

def ιT : K ↪ JJ := ⟨ιTf, ιTf_inj⟩
def ιE : KE ↪ JJ := ⟨ιEf, ιEf_inj⟩
def ιR : R ↪ JJ := ⟨fun i => .inr (.inr i), fun a b h => by simpa using h⟩

def ansC : JJ := .inl 13
def actC : JJ := .inr (.inr 6)

def opCtl := (GraphPrefixBind.startCtl,
  ((((none : Option Bool), (none : Option Bool)), (none : Option Bool)), (none : Option Bool)))

def armF : Unit → TM2.Stmt (fun _ : JJ => Bool) Unit Unit :=
  fun _ => push actC (fun _ => false) halt

def armT := BitMachineRawSequence.program (fun l => stackStmt ιE (EndpointOperands.program l))
  (fun l => stackStmt ιR (RankRun.prog l)) (.inl .s0) opCtl RankRun.startCtl

def disp := TagDispatch.ifProgram ansC armF armT () (leftLabel (leftLabel GraphPrefixBind.startLabel))
  () (opCtl, RankRun.startCtl)

def testCtl := ((false,false), ((none : Option Bool), (none : Option Bool)))

def full := BitMachineRawSequence.program (fun l => stackStmt ιT (LiteralEdgeScanTest.program l)) disp
  (.inl ()) testCtl ((none : Option Bool), ((), (opCtl, RankRun.startCtl)))

/-- Entry bank: the decode entry (`a`, `r`, `m`, `ig`), the literal public
graph bytes (edge-index cell blank), and the item operands (terminated item
value, kind bit); everything else blank. -/
def W0 (g : EncodedGraph.Graph) (a r ig xv : ℕ) (kb : Bool) : JJ → List Bool :=
  Sum.elim (LiteralEdgeDecodeMachine.initialBank a r g.edges.length ig)
    (Sum.elim (EndpointOperands.entry g 0)
      (RB [] [] (CanonicalEndpointRankMachine.unaryWord xv) [] [] [kb] []))

theorem lift {Kk L V : Type*} [DecidableEq Kk] (ι : Kk ↪ JJ)
    (P : L → TM2.Stmt (fun _ : Kk => Bool) L V)
    (W : JJ → List Bool) (S T : Kk → List Bool) (hS : ∀ k, S k = W (ι k)) (l : L) (v v' : V)
    (t : ℕ)
    (hrun : ((advance P)^[t]) (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) =
      ⟨none, v', T⟩) :
    ((advance (fun l => stackStmt ι (P l)))^[t])
        (⟨some l, v, W⟩ : TM2.Cfg (fun _ : JJ => Bool) L V) =
      ⟨none, v', bank ι W T⟩ := by
  have hs := BitMachineStackRun.run ι W P (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) t
  rw [hrun] at hs
  simp only [stackCfg] at hs
  rwa [bank_eq_self ι W S hS] at hs

theorem notT_E (x : KE) (hx : x ≠ eCE) : ¬ ∃ k, ιT k = .inr (.inl x) := by
  rintro ⟨k, hk⟩
  change ιTf k = _ at hk
  simp only [ιTf] at hk
  split_ifs at hk <;> simp_all

theorem notT_R (i : R) (hi : i ≠ 4) : ¬ ∃ k, ιT k = .inr (.inr i) := by
  rintro ⟨k, hk⟩
  change ιTf k = _ at hk
  simp only [ιTf] at hk
  split_ifs at hk <;> simp_all

theorem notE_R (i : R) (h0 : i ≠ 0) (h1 : i ≠ 1) : ¬ ∃ x, ιE x = .inr (.inr i) := by
  rintro ⟨x, hx⟩
  change ιEf x = _ at hx
  simp only [ιEf] at hx
  split_ifs at hx <;> simp_all

theorem notE_inl (i : K) : ¬ ∃ x, ιE x = .inl i := by
  rintro ⟨x, hx⟩
  change ιEf x = _ at hx
  simp only [ιEf] at hx
  split_ifs at hx <;> simp_all

/-- Phase 1: decode and test. -/
theorem phase1 (g : EncodedGraph.Graph) (a r ig xv : ℕ) (kb : Bool) :
    ∃ t ≤ LiteralEdgeDecodeMachine.clock a r g.edges.length +
        (a / r / g.edges.length + ig + 4) + 1, ∃ c,
      ((advance (fun l => stackStmt ιT (LiteralEdgeScanTest.program l)))^[t])
        (⟨some (leftLabel (leftLabel .start)), testCtl,
          W0 g a r ig xv kb⟩ : TM2.Cfg (fun _ : JJ => Bool) _ _) =
        ⟨none, c, bank ιT (W0 g a r ig xv kb) (LiteralEdgeScanTest.finalBank a r g.edges.length ig)⟩ := by
  obtain ⟨t, ht, c, h⟩ := LiteralEdgeScanTest.test_run a r g.edges.length ig
  refine ⟨t, ht, c, lift ιT LiteralEdgeScanTest.program _ _ _ ?_ _ _ _ t h⟩
  intro k
  fin_cases k <;> rfl

/-! ### The bank after phase 1 -/

def W1 (g : EncodedGraph.Graph) (a r ig xv : ℕ) (kb : Bool) : JJ → List Bool :=
  bank ιT (W0 g a r ig xv kb) (LiteralEdgeScanTest.finalBank a r g.edges.length ig)

theorem W1_ans (g : EncodedGraph.Graph) (a r ig xv : ℕ) (kb : Bool) :
    W1 g a r ig xv kb ansC = [decide (0 < g.edges.length ∧ a / r / g.edges.length = ig)] := by
  show bank ιT _ _ (ιT 13) = _
  rw [bank_at]; rfl

theorem W1_e (g : EncodedGraph.Graph) (a r ig xv : ℕ) (kb : Bool) :
    W1 g a r ig xv kb (.inr (.inl eCE)) = u (a / r % g.edges.length) := by
  show bank ιT _ _ (ιT 8) = _
  rw [bank_at]; rfl

theorem W1_t (g : EncodedGraph.Graph) (a r ig xv : ℕ) (kb : Bool) :
    W1 g a r ig xv kb (.inr (.inr 4)) = u (0) := by
  show bank ιT _ _ (ιT 5) = _
  rw [bank_at]; rfl

theorem W1_E (g : EncodedGraph.Graph) (a r ig xv : ℕ) (kb : Bool) (x : KE) (hx : x ≠ eCE) :
    W1 g a r ig xv kb (.inr (.inl x)) = EndpointOperands.entry g 0 x :=
  bank_outside ιT _ _ _ (notT_E x hx)

theorem W1_R (g : EncodedGraph.Graph) (a r ig xv : ℕ) (kb : Bool) (i : R) (hi : i ≠ 4) :
    W1 g a r ig xv kb (.inr (.inr i)) =
      RB [] [] (CanonicalEndpointRankMachine.unaryWord xv) [] [] [kb] [] i :=
  bank_outside ιT _ _ _ (notT_R i hi)

/-! ### False branch -/

theorem armF_run (S : JJ → List Bool) :
    ((advance armF)^[1]) (⟨some (), (), S⟩ : TM2.Cfg (fun _ : JJ => Bool) Unit Unit) =
      ⟨none, (), Function.update S actC (false :: S actC)⟩ := rfl

/-- Unselected coordinate (other group, padding, or no edges): the program
halts with the activity cell `[false]` and nothing else changed after the
test. -/
theorem join_false (g : EncodedGraph.Graph) (a r ig xv : ℕ) (kb : Bool)
    (h : ¬ (0 < g.edges.length ∧ a / r / g.edges.length = ig)) :
    ∃ t ≤ (LiteralEdgeDecodeMachine.clock a r g.edges.length +
        (a / r / g.edges.length + ig + 4) + 1) + (1 + 1) + 1, ∃ c,
      ((advance full)^[t])
        (⟨some (leftLabel (leftLabel (leftLabel .start))),
          (testCtl, ((none : Option Bool), ((), (opCtl, RankRun.startCtl)))),
          W0 g a r ig xv kb⟩ : TM2.Cfg (fun _ : JJ => Bool) _ _) =
        ⟨none, c, Function.update (Function.update (W1 g a r ig xv kb) ansC []) actC [false]⟩ := by
  obtain ⟨t1, ht1, c1, h1⟩ := phase1 g a r ig xv kb
  have hans : W1 g a r ig xv kb ansC = false :: [] := by
    rw [W1_ans]; simp [h]
  have hact : Function.update (W1 g a r ig xv kb) ansC [] actC = [] := by
    rw [Function.update_of_ne (by simp [actC, ansC])]
    exact W1_R g a r ig xv kb 6 (by decide)
  have hF := armF_run (Function.update (W1 g a r ig xv kb) ansC [])
  rw [hact] at hF
  obtain ⟨t2, ht2, h2⟩ := TagDispatch.if_false ansC armF armT ()
    (leftLabel (leftLabel GraphPrefixBind.startLabel)) () (opCtl, RankRun.startCtl)
    (W1 g a r ig xv kb) [] hans 1 () _ hF
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs (fun l => stackStmt ιT (LiteralEdgeScanTest.program l))
    disp (leftLabel (leftLabel .start)) (.inl ()) testCtl c1
    ((none : Option Bool), ((), (opCtl, RankRun.startCtl))) _ (W0 g a r ig xv kb)
    (W1 g a r ig xv kb) _ t1 t2 h1 h2
  exact ⟨t, by omega, _, hr⟩

/-! ### True branch -/

def W2 (g : EncodedGraph.Graph) (a r ig xv : ℕ) (kb : Bool) : JJ → List Bool :=
  Function.update (W1 g a r ig xv kb) ansC []

theorem ιE_u : ιE uC = .inr (.inr 0) := by simp [ιE, ιEf]
theorem ιE_v : ιE vC = .inr (.inr 1) := by simp [ιE, ιEf, uC, vC]
theorem ιE_e : ιE eCE = .inr (.inl eCE) := by simp [ιE, ιEf, eCE, uC, vC]
theorem ιE_other (x : KE) (h1 : x ≠ uC) (h2 : x ≠ vC) : ιE x = .inr (.inl x) := by
  simp [ιE, ιEf, h1, h2]

theorem entry_other (g : EncodedGraph.Graph) (e : ℕ) (x : KE) (h1 : x ≠ uC) (h2 : x ≠ vC)
    (h3 : x ≠ eCE) : EndpointOperands.entry g e x = EndpointOperands.entry g 0 x := by
  rcases x with y | j
  · rcases y with y | y | y
    · rfl
    · rfl
    · fin_cases y
      · exact absurd rfl h3
      · rfl
  · fin_cases j
    · exact absurd rfl h1
    · exact absurd rfl h2

theorem restrE (g : EncodedGraph.Graph) (a r ig xv : ℕ) (kb : Bool) :
    ∀ x : KE, EndpointOperands.entry g (a / r % g.edges.length) x =
      W2 g a r ig xv kb (ιE x) := by
  intro x
  have hne : ∀ y : KE ⊕ R, (.inr y : JJ) ≠ ansC := by intro y h; cases h
  by_cases h1 : x = uC
  · subst h1
    rw [ιE_u, W2, Function.update_of_ne (hne _), W1_R _ _ _ _ _ _ 0 (by decide)]
    rfl
  · by_cases h2 : x = vC
    · subst h2
      rw [ιE_v, W2, Function.update_of_ne (hne _), W1_R _ _ _ _ _ _ 1 (by decide)]
      rfl
    · by_cases h3 : x = eCE
      · subst h3
        rw [ιE_e, W2, Function.update_of_ne (hne _), W1_e]
        rfl
      · rw [ιE_other x h1 h2, W2, Function.update_of_ne (hne _), W1_E _ _ _ _ _ _ x h3,
          entry_other g _ x h1 h2 h3]

def W3 (g : EncodedGraph.Graph) (hg : g.Valid) (a r ig xv : ℕ) (kb : Bool)
    (e : Fin g.edges.length) : JJ → List Bool :=
  bank ιE (W2 g a r ig xv kb) (Sum.elim (GraphPrefixBind.Wv g hg e.val
    (UnaryFieldListParserScratch.contents
      (UnaryFieldListParserScratch.tokens (CanonicalEdgePrefix.suffix (CanonicalEdgeTape.graphEdge g hg) e))
      (List.replicate g.vertices true) [] []
      (UnaryFieldListParserScratch.tokens
        (CanonicalEdgePair.preceding (CanonicalEdgeTape.graphEdge g hg) e).reverse) [true]))
    ![CanonicalEndpointRankMachine.unaryWord (CanonicalEdgeTape.graphEdge g hg e false).val,
      CanonicalEndpointRankMachine.unaryWord (CanonicalEdgeTape.graphEdge g hg e true).val])

theorem restrR (g : EncodedGraph.Graph) (hg : g.Valid) (a r ig xv : ℕ) (kb : Bool)
    (e : Fin g.edges.length) :
    ∀ i : R, RB (CanonicalEndpointRankMachine.unaryWord (CanonicalEdgeTape.graphEdge g hg e false).val)
      (CanonicalEndpointRankMachine.unaryWord (CanonicalEdgeTape.graphEdge g hg e true).val)
      (CanonicalEndpointRankMachine.unaryWord xv) [] (List.replicate (0) true) [kb] [] i =
      W3 g hg a r ig xv kb e (ιR i) := by
  have hne : ∀ y : KE ⊕ R, (.inr y : JJ) ≠ ansC := by intro y h; cases h
  intro i
  fin_cases i
  · show _ = bank ιE _ _ (.inr (.inr 0))
    rw [← ιE_u, bank_at]; rfl
  · show _ = bank ιE _ _ (.inr (.inr 1))
    rw [← ιE_v, bank_at]; rfl
  · show _ = bank ιE _ _ (.inr (.inr 2))
    rw [bank_outside ιE _ _ _ (notE_R 2 (by decide) (by decide)), W2,
      Function.update_of_ne (hne _), W1_R _ _ _ _ _ _ 2 (by decide)]; rfl
  · show _ = bank ιE _ _ (.inr (.inr 3))
    rw [bank_outside ιE _ _ _ (notE_R 3 (by decide) (by decide)), W2,
      Function.update_of_ne (hne _), W1_R _ _ _ _ _ _ 3 (by decide)]; rfl
  · show _ = bank ιE _ _ (.inr (.inr 4))
    rw [bank_outside ιE _ _ _ (notE_R 4 (by decide) (by decide)), W2,
      Function.update_of_ne (hne _), W1_t]; rfl
  · show _ = bank ιE _ _ (.inr (.inr 5))
    rw [bank_outside ιE _ _ _ (notE_R 5 (by decide) (by decide)), W2,
      Function.update_of_ne (hne _), W1_R _ _ _ _ _ _ 5 (by decide)]; rfl
  · show _ = bank ιE _ _ (.inr (.inr 6))
    rw [bank_outside ιE _ _ _ (notE_R 6 (by decide) (by decide)), W2,
      Function.update_of_ne (hne _), W1_R _ _ _ _ _ _ 6 (by decide)]; rfl

/-- Exit bank of the selected case. -/
def Wtrue (g : EncodedGraph.Graph) (hg : g.Valid) (a r ig xv : ℕ) (kb : Bool)
    (e : Fin g.edges.length) : JJ → List Bool :=
  bank ιR (W3 g hg a r ig xv kb e)
    (RB [] [] [] (List.replicate (CanonicalEndpointRankMachine.semanticRank
        (RankRun.kindOfNat (0)) (RankRun.itemOfBool kb)
        (CanonicalEdgeTape.graphEdge g hg e false).val
        (CanonicalEdgeTape.graphEdge g hg e true).val xv) true) [] []
      [CanonicalEndpointRankMachine.semanticActive (RankRun.kindOfNat (0))
        (RankRun.itemOfBool kb) (CanonicalEdgeTape.graphEdge g hg e false).val
        (CanonicalEdgeTape.graphEdge g hg e true).val xv])

/-- Selected coordinate: the same program fetches the two endpoint words of
the decoded edge occurrence from the literal public bytes and runs the
production endpoint-rank controller. -/
theorem join_true (g : EncodedGraph.Graph) (hg : g.Valid) (a r ig xv : ℕ) (kb : Bool)
    (h : 0 < g.edges.length ∧ a / r / g.edges.length = ig) :
    let e : Fin g.edges.length := ⟨a / r % g.edges.length, Nat.mod_lt _ h.1⟩
    let edge := CanonicalEdgeTape.graphEdge g hg
    ∃ t ≤ (LiteralEdgeDecodeMachine.clock a r g.edges.length +
        (a / r / g.edges.length + ig + 4) + 1) +
        ((((103 * ((EncodedGraph.encode g).length + 1)^3 +
          (2 * (CanonicalEdgeTape.word edge).length + 2) + (2 * g.vertices + 2) +
          (2 * e.val + 2) + (2 * e.val + 2) + 1 + 1 +
          UnaryFieldListParserScratch.fuel g.vertices (2 * (e.val + 1))
            (CanonicalEdgeTape.word edge) + 7) +
          ((edge e true).val + (edge e false).val + 7) + 1) +
          (max (edge e false).val (max (edge e true).val xv) + 7) + 1) + 1) + 1,
      ∃ c,
      ((advance full)^[t])
        (⟨some (leftLabel (leftLabel (leftLabel .start))),
          (testCtl, ((none : Option Bool), ((), (opCtl, RankRun.startCtl)))),
          W0 g a r ig xv kb⟩ : TM2.Cfg (fun _ : JJ => Bool) _ _) =
        ⟨none, c, Wtrue g hg a r ig xv kb e⟩ := by
  intro e edge
  obtain ⟨t1, ht1, c1, h1⟩ := phase1 g a r ig xv kb
  have hans : W1 g a r ig xv kb ansC = true :: [] := by
    rw [W1_ans]; simp [h]
  obtain ⟨tE, htE, cE, hE⟩ := EndpointOperands.operands_run g hg e
  have hE' := lift ιE EndpointOperands.program (W2 g a r ig xv kb)
    (EndpointOperands.entry g e.val) _ (restrE g a r ig xv kb) _ _ _ tE hE
  obtain ⟨tR, htR, cR, hR⟩ := RankRun.rank_run 0 (by decide) kb
    (edge e false).val (edge e true).val xv
  have hR' := lift ιR RankRun.prog (W3 g hg a r ig xv kb e) _ _ (restrR g hg a r ig xv kb e)
    _ _ _ tR hR
  obtain ⟨tA, htA, hA⟩ := BitMachineRawSequence.runs
    (fun l => stackStmt ιE (EndpointOperands.program l)) (fun l => stackStmt ιR (RankRun.prog l))
    (leftLabel GraphPrefixBind.startLabel) (.inl .s0) opCtl cE RankRun.startCtl cR
    (W2 g a r ig xv kb) (W3 g hg a r ig xv kb e) (Wtrue g hg a r ig xv kb e) tE tR hE' hR'
  obtain ⟨t2, ht2, h2⟩ := TagDispatch.if_true ansC armF armT ()
    (leftLabel (leftLabel GraphPrefixBind.startLabel)) () (opCtl, RankRun.startCtl)
    (W1 g a r ig xv kb) [] hans tA (opCtl, cR) _ hA
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs (fun l => stackStmt ιT (LiteralEdgeScanTest.program l))
    disp (leftLabel (leftLabel .start)) (.inl ()) testCtl c1
    ((none : Option Bool), ((), (opCtl, RankRun.startCtl))) _ (W0 g a r ig xv kb)
    (W1 g a r ig xv kb) _ t1 t2 h1 h2
  have htE' : tE ≤ (103 * ((EncodedGraph.encode g).length + 1)^3 +
      (2 * (CanonicalEdgeTape.word edge).length + 2) + (2 * g.vertices + 2) +
      (2 * e.val + 2) + (2 * e.val + 2) + 1 + 1 +
      UnaryFieldListParserScratch.fuel g.vertices (2 * (e.val + 1))
        (CanonicalEdgeTape.word edge) + 7) +
      ((edge e true).val + (edge e false).val + 7) + 1 := htE
  have htR' : tR ≤ max (edge e false).val (max (edge e true).val xv) + 7 := htR
  exact ⟨t, by omega, _, hr⟩

theorem Wtrue_act (g : EncodedGraph.Graph) (hg : g.Valid) (a r ig xv : ℕ) (kb : Bool)
    (e : Fin g.edges.length) :
    Wtrue g hg a r ig xv kb e actC =
      [CanonicalEndpointRankMachine.semanticActive (RankRun.kindOfNat (0))
        (RankRun.itemOfBool kb) (CanonicalEdgeTape.graphEdge g hg e false).val
        (CanonicalEdgeTape.graphEdge g hg e true).val xv] := by
  show bank ιR _ _ (ιR 6) = _
  rw [bank_at]; rfl

theorem Wtrue_rank (g : EncodedGraph.Graph) (hg : g.Valid) (a r ig xv : ℕ) (kb : Bool)
    (e : Fin g.edges.length) :
    Wtrue g hg a r ig xv kb e (.inr (.inr 3)) =
      List.replicate (CanonicalEndpointRankMachine.semanticRank
        (RankRun.kindOfNat (0)) (RankRun.itemOfBool kb)
        (CanonicalEdgeTape.graphEdge g hg e false).val
        (CanonicalEdgeTape.graphEdge g hg e true).val xv) true := by
  show bank ιR _ _ (ιR 3) = _
  rw [bank_at]; rfl

#print axioms join_false
#print axioms join_true
#print axioms Wtrue_act
#print axioms Wtrue_rank

end

end CurrentAdditive.LiteralEdgeScanJoin
