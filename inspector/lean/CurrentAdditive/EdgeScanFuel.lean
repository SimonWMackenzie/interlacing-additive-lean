import CurrentAdditive.EdgeScanValue

/-! Uniform numeric bounds for the actual current edge scan. All work in the
physical join, including graph-byte conversion and unary endpoint parsing,
is included. Input size means the total bit count of its prepared W0 bank,
not the length of a compact selector address or an enclosing formula. -/

namespace CurrentAdditive.LiteralEdgeScanFuel

noncomputable section

open Paper2 EthInapproximability.CurrentPaper
open LiteralEdgeScanJoin
open scoped BigOperators

def bankBits (g : EncodedGraph.Graph) (a r ig xv : ℕ) (kb : Bool) : ℕ :=
  ∑ j : JJ, (W0 g a r ig xv kb j).length

theorem bankBits_eq (g : EncodedGraph.Graph) (a r ig xv : ℕ) (kb : Bool) :
    bankBits g a r ig xv kb =
      (EncodedGraph.encode g).length+a+r+g.edges.length+ig+xv+2 := by
  simp [bankBits, W0, Fintype.sum_sum_type,
    LiteralEdgeDecodeMachine.initialBank, LiteralEdgeDecodeDependency.u,
    EndpointOperands.entry, GraphPrefixBind.initBank,
    PublicGraphEndpointMachine.initialBank, SourceNormalizationMachineDecode.start,
    RankRun.RB, CanonicalEndpointRankMachine.unaryWord, Fin.sum_univ_succ]
  omega

def envelope (g : EncodedGraph.Graph) (a r ig xv : ℕ) : ℕ :=
  (EncodedGraph.encode g).length+a+r+g.edges.length+ig+xv+3

theorem envelope_eq_bank (g : EncodedGraph.Graph) (a r ig xv : ℕ) (kb : Bool) :
    envelope g a r ig xv = bankBits g a r ig xv kb+1 := by
  rw [bankBits_eq]
  unfold envelope
  omega

def trueFuel (g : EncodedGraph.Graph) (hg : g.Valid) (a r ig xv : ℕ)
    (e : Fin g.edges.length) : ℕ :=
  let edge := CanonicalEdgeTape.graphEdge g hg
  ((LiteralEdgeDecodeMachine.clock a r g.edges.length+
      (a/r/g.edges.length+ig+4)+1)+
    ((((103*((EncodedGraph.encode g).length+1)^3+
      (2*(CanonicalEdgeTape.word edge).length+2)+(2*g.vertices+2)+
      (2*e.val+2)+(2*e.val+2)+1+1+
      UnaryFieldListParserScratch.fuel g.vertices (2*(e.val+1))
        (CanonicalEdgeTape.word edge)+7)+
      ((edge e true).val+(edge e false).val+7)+1)+
      (max (edge e false).val (max (edge e true).val xv)+7)+1)+1)+1)

def falseFuel (g : EncodedGraph.Graph) (a r ig : ℕ) : ℕ :=
  ((LiteralEdgeDecodeMachine.clock a r g.edges.length+
    (a/r/g.edges.length+ig+4)+1)+(1+1)+1)

def scanPosFuel (g : EncodedGraph.Graph) (hg : g.Valid)
    (a r ig xv : ℕ) (kb : Bool) : ℕ :=
  if h : 0<g.edges.length ∧ a/r/g.edges.length=ig then
    let e : Fin g.edges.length := ⟨a/r%g.edges.length, Nat.mod_lt _ h.1⟩
    trueFuel g hg a r ig xv e+
      (CanonicalEndpointRankMachine.semanticRank (RankRun.kindOfNat 0)
        (RankRun.itemOfBool kb)
        (CanonicalEdgeTape.graphEdge g hg e false).val
        (CanonicalEdgeTape.graphEdge g hg e true).val xv+3)
  else falseFuel g a r ig+(0+3)

theorem semanticRank_le (kb : Bool) (u v x : ℕ) :
    CanonicalEndpointRankMachine.semanticRank (RankRun.kindOfNat 0)
      (RankRun.itemOfBool kb) u v x ≤ x+2 := by
  cases kb <;> dsimp [RankRun.kindOfNat, RankRun.itemOfBool,
    CanonicalEndpointRankMachine.semanticRank] <;> split_ifs <;> omega

theorem trueFuel_le (g : EncodedGraph.Graph) (hg : g.Valid) (a r ig xv : ℕ)
    (e : Fin g.edges.length) :
    trueFuel g hg a r ig xv e ≤ 300*(envelope g a r ig xv)^3 := by
  let B := envelope g a r ig xv
  have hgsize := EncodedGraph.encode_length_lower g
  have hb : 0 < B := by dsimp [B, envelope]; omega
  have henc : (EncodedGraph.encode g).length+1 ≤ B := by dsimp [B, envelope]; omega
  have hn : g.vertices ≤ B := by dsimp [B, envelope]; omega
  have hm : g.edges.length ≤ B := by dsimp [B, envelope]; omega
  have ha : a ≤ B := by dsimp [B, envelope]; omega
  have hr : r ≤ B := by dsimp [B, envelope]; omega
  have hi : ig ≤ B := by dsimp [B, envelope]; omega
  have hx : xv ≤ B := by dsimp [B, envelope]; omega
  have he : e.val ≤ B := by have := e.isLt; omega
  have hdiv : a/r/g.edges.length ≤ B :=
    ((Nat.div_le_self (a/r) g.edges.length).trans (Nat.div_le_self a r)).trans ha
  have hdec := LiteralEdgeDecodeMachine.clock_le a r g.edges.length
  have hdec' : LiteralEdgeDecodeMachine.clock a r g.edges.length ≤ 22*B+19 := by omega
  let edge := CanonicalEdgeTape.graphEdge g hg
  have hw₀ := CanonicalEdgeTape.word_length_le edge
  have hmul : g.edges.length*g.vertices ≤ B^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hm hn
  have hw : (CanonicalEdgeTape.word edge).length ≤ 2*B^2 := by nlinarith
  have hu : (edge e false).val ≤ B := (edge e false).isLt.le.trans hn
  have hv : (edge e true).val ≤ B := (edge e true).isLt.le.trans hn
  have hmax : max (edge e false).val (max (edge e true).val xv) ≤ B :=
    max_le hu (max_le hv hx)
  have hparse : UnaryFieldListParserScratch.fuel g.vertices (2*(e.val+1))
      (CanonicalEdgeTape.word edge) ≤ 6*B^2+9*B+8 := by
    unfold UnaryFieldListParserScratch.fuel
    omega
  have hcube : ((EncodedGraph.encode g).length+1)^3 ≤ B^3 := by gcongr
  have hcoarse : trueFuel g hg a r ig xv e ≤ 103*B^3+10*B^2+50*B+100 := by
    unfold trueFuel
    dsimp only
    dsimp only [edge] at hw hmax hparse hu hv
    omega
  have hb3 : B ≤ B^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hb (show 1 ≤ 3 by omega)
  have hs3 : B^2 ≤ B^3 := Nat.pow_le_pow_right hb (by omega)
  have hc3 : 1 ≤ B^3 := by have := pow_pos hb 3; omega
  change trueFuel g hg a r ig xv e ≤ 300*B^3
  omega

theorem falseFuel_le (g : EncodedGraph.Graph) (a r ig xv : ℕ) :
    falseFuel g a r ig ≤ 200*(envelope g a r ig xv)^3 := by
  let B := envelope g a r ig xv
  have hb : 0 < B := by dsimp [B, envelope]; omega
  have ha : a ≤ B := by dsimp [B, envelope]; omega
  have hr : r ≤ B := by dsimp [B, envelope]; omega
  have hi : ig ≤ B := by dsimp [B, envelope]; omega
  have hm : g.edges.length ≤ B := by dsimp [B, envelope]; omega
  have hdiv : a/r/g.edges.length ≤ B :=
    ((Nat.div_le_self (a/r) g.edges.length).trans (Nat.div_le_self a r)).trans ha
  have hdec := LiteralEdgeDecodeMachine.clock_le a r g.edges.length
  have hb3 : B ≤ B^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hb (show 1 ≤ 3 by omega)
  have hc3 : 1 ≤ B^3 := by have := pow_pos hb 3; omega
  unfold falseFuel
  change _ ≤ 200*B^3
  omega

theorem scanPosFuel_le (g : EncodedGraph.Graph) (hg : g.Valid)
    (a r ig xv : ℕ) (kb : Bool) :
    scanPosFuel g hg a r ig xv kb ≤ 1000*(envelope g a r ig xv)^3 := by
  let B := envelope g a r ig xv
  have hb : 0 < B := by dsimp [B, envelope]; omega
  have hx : xv ≤ B := by dsimp [B, envelope]; omega
  have hb3 : B ≤ B^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hb (show 1 ≤ 3 by omega)
  have hc3 : 1 ≤ B^3 := by have := pow_pos hb 3; omega
  unfold scanPosFuel
  split_ifs with h
  · dsimp only
    have ht := trueFuel_le g hg a r ig xv
      ⟨a/r%g.edges.length, Nat.mod_lt _ h.1⟩
    have hrank := semanticRank_le kb
      (CanonicalEdgeTape.graphEdge g hg ⟨a/r%g.edges.length, Nat.mod_lt _ h.1⟩ false).val
      (CanonicalEdgeTape.graphEdge g hg ⟨a/r%g.edges.length, Nat.mod_lt _ h.1⟩ true).val xv
    change _ ≤ 1000*B^3
    change _ ≤ 300*B^3 at ht
    omega
  · have ht := falseFuel_le g a r ig xv
    change _ ≤ 1000*B^3
    change _ ≤ 200*B^3 at ht
    omega

theorem scanPosFuel_bankBits (g : EncodedGraph.Graph) (hg : g.Valid)
    (a r ig xv : ℕ) (kb : Bool) :
    scanPosFuel g hg a r ig xv kb ≤ 1000*(bankBits g a r ig xv kb+1)^3 := by
  rw [← envelope_eq_bank]
  exact scanPosFuel_le g hg a r ig xv kb

/-- A numeric public envelope. Unary selector/item operands are charged by
their actual values. This is not a logarithmic-address time claim. -/
def publicEnvelope (g : EncodedGraph.Graph) (s q₂ : ℕ) : ℕ :=
  (EncodedGraph.encode g).length+g.vertices+g.edges.length+5*s+2*q₂+3

theorem envelope_le_public (g : EncodedGraph.Graph) (s q₂ : ℕ)
    (a : Fin q₂) (ig : Fin (4*s)) (z : Fin g.vertices ⊕ Fin (s-3)) :
    envelope g a.val
      (q₂/CurrentAdditive.EdgeSource.sourceQ0 (Fin (4*s)) (Fin g.edges.length))
      ig.val (CanonicalEndpointRankBridge.itemValue z) ≤ publicEnvelope g s q₂ := by
  have ha := a.isLt
  have hi := ig.isLt
  have hr := Nat.div_le_self q₂
    (CurrentAdditive.EdgeSource.sourceQ0 (Fin (4*s)) (Fin g.edges.length))
  have hx : CanonicalEndpointRankBridge.itemValue z ≤ g.vertices+s := by
    cases z with
    | inl v =>
      change v.val ≤ _
      have := v.isLt
      omega
    | inr v =>
      change v.val ≤ _
      have := v.isLt
      have := Nat.sub_le s 3
      omega
  unfold envelope publicEnvelope
  omega

theorem scanPosFuel_public (g : EncodedGraph.Graph) (hg : g.Valid) (s q₂ : ℕ)
    (a : Fin q₂) (ig : Fin (4*s)) (z : Fin g.vertices ⊕ Fin (s-3)) (kb : Bool) :
    scanPosFuel g hg a.val
      (q₂/CurrentAdditive.EdgeSource.sourceQ0 (Fin (4*s)) (Fin g.edges.length))
      ig.val (CanonicalEndpointRankBridge.itemValue z) kb ≤
        1000*(publicEnvelope g s q₂)^3 := by
  apply (scanPosFuel_le g hg _ _ _ _ kb).trans
  have h := envelope_le_public g s q₂ a ig z
  gcongr

end
end CurrentAdditive.LiteralEdgeScanFuel
