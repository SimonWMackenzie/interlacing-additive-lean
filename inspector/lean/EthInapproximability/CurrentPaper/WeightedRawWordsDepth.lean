import EthInapproximability.CurrentPaper.WeightedRawWordsOps

/-! # S2a: b = sourceDepth n from master N (edge_candidate)

The production `ETHScaleEdgePreparation.fullProgram` runs with its raw cell
on master `N` and every other stack in the private `edge` region. Its output
`clog 2 (n+2)` is copied into consumer word 1 and master `B`; then the whole
`edge` region is cleared physically. The residue is only existentially known,
so the clear is charged through `BitMachineStackGrowth.run_growth`. -/

namespace EthInapproximability.CurrentPaper.WeightedRawWords

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

def edgeSlots : ETHScaleEdgePreparation.Stack ↪ Global where
  toFun k := if k = ETHScaleEdgePreparation.raw then aux .N else aux (.edge k)
  inj' := by
    intro a b h
    by_cases ha : a = ETHScaleEdgePreparation.raw <;>
      by_cases hb : b = ETHScaleEdgePreparation.raw <;>
      simp only [ha, hb, if_true, if_false, aux] at h
    · exact ha.trans hb.symm
    · cases h
    · cases h
    · exact Aux.edge.inj (Sum.inr.inj h)

def edgeProgram := fun l => stackStmt edgeSlots (ETHScaleEdgePreparation.fullProgram l)

def cand : ETHScaleEdgePreparation.Stack := ETHScaleEdgePreparation.candidateEmbed (.inr 0)

theorem cand_ne_raw : cand ≠ ETHScaleEdgePreparation.raw := by
  simp [cand, ETHScaleEdgePreparation.candidateEmbed, ETHScaleEdgePreparation.raw]

def edgeCtrl : ETHScaleEdgePreparation.FullControl :=
  ((none, ()), (ETHParameterScaleMachineLogCopy.copyControl none, none))

def edgeStartLabel : ETHScaleEdgePreparation.FullLabel :=
  BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan)

def edgeBound (n : ℕ) : ℕ :=
  (2*n+5) + (ETHScaleColumnCandidate.logCost (n+2) + (2 * Nat.clog 2 (n+2) + 2) + 1) + 1

def edgePer : ℕ := BitMachineStackGrowth.perStep ETHScaleEdgePreparation.fullProgram

theorem edge_embedded (n : ℕ) (G : Global → List Bool)
    (hN : G (aux .N) = List.replicate n true)
    (hE : ∀ k, G (aux (.edge k)) = []) :
    ∃ t ≤ edgeBound n, ∃ F : ETHScaleEdgePreparation.Stack → List Bool,
      ((advance edgeProgram)^[t])
        (⟨some edgeStartLabel, edgeCtrl, G⟩ :
          TM2.Cfg (fun _ : Global => Bool) ETHScaleEdgePreparation.FullLabel
            ETHScaleEdgePreparation.FullControl) =
        ⟨none, edgeCtrl, bank edgeSlots G F⟩ ∧
      F ETHScaleEdgePreparation.raw = List.replicate n true ∧
      F cand = List.replicate (Nat.clog 2 (n+2)) true ∧
      ∀ k, (F k).length ≤ n + edgePer * edgeBound n := by
  obtain ⟨t, ht, F, hr, hraw, hcand⟩ := ETHScaleEdgePreparation.edge_candidate n
  refine ⟨t, ht, F, ?_, hraw, hcand, ?_⟩
  · have h := region_run edgeSlots ETHScaleEdgePreparation.fullProgram _ _ t hr G
      (by
        intro k
        by_cases hk : k = ETHScaleEdgePreparation.raw
        · subst hk
          simp [ETHScaleEdgePreparation.initial, edgeSlots, hN]
        · simp [ETHScaleEdgePreparation.initial, edgeSlots, hk, hE])
    exact h
  · intro k
    have hg := BitMachineStackGrowth.run_growth ETHScaleEdgePreparation.fullProgram
      (⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel .scan)),
        ((none, ()), (ETHParameterScaleMachineLogCopy.copyControl none, none)),
        ETHScaleEdgePreparation.initial n⟩ :
        TM2.Cfg (fun _ : ETHScaleEdgePreparation.Stack => Bool)
          ETHScaleEdgePreparation.FullLabel ETHScaleEdgePreparation.FullControl) t k
    rw [hr] at hg
    have hi : (ETHScaleEdgePreparation.initial n k).length ≤ n := by
      unfold ETHScaleEdgePreparation.initial
      split <;> simp
    have hm : edgePer * t ≤ edgePer * edgeBound n := Nat.mul_le_mul_left _ ht
    have hg' : (F k).length ≤ (ETHScaleEdgePreparation.initial n k).length + edgePer * t := hg
    omega

/-- The private edge-region cells, in a fixed finite enumeration. -/
def edgeCells : Fin (Fintype.card ETHScaleEdgePreparation.Stack) → Global :=
  fun i => aux (.edge ((Fintype.equivFin ETHScaleEdgePreparation.Stack).symm i))

theorem edgeCells_injective : Function.Injective edgeCells := by
  intro i j h
  simpa [edgeCells, aux] using h

def edgeCard : ℕ := Fintype.card ETHScaleEdgePreparation.Stack

/-- Bank after S2a: word 1 and master `B` hold `sourceDepth n`. -/
def afterDepth (G : Global → List Bool) (n : ℕ) : Global → List Bool :=
  Function.update (Function.update G (rawCell 1)
    (List.replicate (EffectiveIteration.sourceDepth n) true))
    (aux .B) (List.replicate (EffectiveIteration.sourceDepth n) true)

theorem rawCell_ne_aux (j : Fin 6) (a : Aux) : rawCell j ≠ aux a := by
  simp [rawCell, cons, aux]

theorem aux_ne_rawCell (j : Fin 6) (a : Aux) : aux a ≠ rawCell j := by
  simp [rawCell, cons, aux]

def depthCopy1 := copyProg (aux (.edge cand)) (rawCell 1)
  (aux_ne_rawCell 1 _) (by simp [aux]) (rawCell_ne_aux 1 _)
def depthCopy2 := copyProg (aux (.edge cand)) (aux .B)
  (by simp [aux]) (by simp [aux]) (by simp [aux])

def depthProgram :=
  BitMachineRawSequence.program edgeProgram
    (BitMachineRawSequence.program depthCopy1
      (BitMachineRawSequence.program depthCopy2 (clearProgram edgeCells)
        0 none ((), none))
      (BitMachineRawSequence.leftLabel .scan) none (none, ((), none)))
    (BitMachineRawSequence.leftLabel .scan) edgeCtrl (none, (none, ((), none)))

def depthBound (n : ℕ) : ℕ :=
  edgeBound n + ((2 * EffectiveIteration.sourceDepth n + 2) +
    ((2 * EffectiveIteration.sourceDepth n + 2) +
      (edgeCard * (n + edgePer * edgeBound n) + edgeCard + 2) + 1) + 1) + 1

theorem depth_run (n : ℕ) (G : Global → List Bool)
    (hN : G (aux .N) = List.replicate n true)
    (hE : ∀ k, G (aux (.edge k)) = [])
    (h1 : G (rawCell 1) = []) (hB : G (aux .B) = []) (hcs : G (aux .cs) = []) :
    ∃ t ≤ depthBound n,
      ((advance depthProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel edgeStartLabel),
          (edgeCtrl, (none, (none, ((), none)))), G⟩ :
          TM2.Cfg (fun _ : Global => Bool) _ _) =
        ⟨none, (edgeCtrl, (none, (none, ((), none)))), afterDepth G n⟩ := by
  obtain ⟨t1, ht1, F, hr1, hraw, hcand, hlen⟩ := edge_embedded n G hN hE
  set X := bank edgeSlots G F with hX
  have hXc : X (aux (.edge cand)) = List.replicate (EffectiveIteration.sourceDepth n) true := by
    have : aux (.edge cand) = edgeSlots cand := by
      simp [edgeSlots, cand_ne_raw]
    rw [this, hX, bank_at, hcand]
    rfl
  have hout : ∀ j, (¬ ∃ k, edgeSlots k = j) → X j = G j :=
    fun j hj => bank_outside edgeSlots G F j hj
  have hX1 : X (rawCell 1) = [] := by
    rw [hout _ (by rintro ⟨k, hk⟩; by_cases h : k = ETHScaleEdgePreparation.raw <;>
      simp [edgeSlots, h, rawCell, cons, aux] at hk)]
    exact h1
  have hXB : X (aux .B) = [] := by
    rw [hout _ (by rintro ⟨k, hk⟩; by_cases h : k = ETHScaleEdgePreparation.raw <;>
      simp [edgeSlots, h, aux] at hk)]
    exact hB
  have hXcs : X (aux .cs) = [] := by
    rw [hout _ (by rintro ⟨k, hk⟩; by_cases h : k = ETHScaleEdgePreparation.raw <;>
      simp [edgeSlots, h, aux] at hk)]
    exact hcs
  -- copy 1
  have hc1 := copy_word (aux (.edge cand)) (rawCell 1) (aux_ne_rawCell 1 _)
    (by simp [aux]) (rawCell_ne_aux 1 _) X hX1 hXcs
  rw [hXc] at hc1
  set X1 := Function.update X (rawCell 1)
    (List.replicate (EffectiveIteration.sourceDepth n) true) with hX1def
  have hc2 := copy_word (aux (.edge cand)) (aux .B) (by simp [aux]) (by simp [aux])
    (by simp [aux]) X1
    (by rw [hX1def, Function.update_of_ne (aux_ne_rawCell 1 _)]; exact hXB)
    (by rw [hX1def, Function.update_of_ne (aux_ne_rawCell 1 _)]; exact hXcs)
  have hX1c : X1 (aux (.edge cand)) =
      List.replicate (EffectiveIteration.sourceDepth n) true := by
    rw [hX1def, Function.update_of_ne (aux_ne_rawCell 1 _)]; exact hXc
  rw [hX1c] at hc2
  set X2 := Function.update X1 (aux .B)
    (List.replicate (EffectiveIteration.sourceDepth n) true) with hX2def
  -- clear
  have hcl := clear_run edgeCells edgeCells_injective X2
  have hsum : (∑ i, (X2 (edgeCells i)).length) ≤ edgeCard * (n + edgePer * edgeBound n) := by
    apply sum_le_mul
    intro i
    have hne1 : edgeCells i ≠ rawCell 1 := aux_ne_rawCell 1 _
    have hne2 : edgeCells i ≠ aux .B := by simp [edgeCells, aux]
    rw [hX2def, Function.update_of_ne hne2, hX1def, Function.update_of_ne hne1, hX]
    by_cases hr : ∃ k, edgeSlots k = edgeCells i
    · obtain ⟨k, hk⟩ := hr
      rw [← hk, bank_at]
      exact hlen k
    · rw [bank_outside edgeSlots G F _ hr]
      simp [edgeCells, hE]
  have hfinal : BitMachineClearBank.cleared edgeCells X2 = afterDepth G n := by
    have hn1 : ∀ i, edgeCells i ≠ rawCell 1 := fun i => aux_ne_rawCell 1 _
    have hn2 : ∀ i, edgeCells i ≠ aux .B := fun i => by simp [edgeCells, aux]
    rw [hX2def, cleared_update_comm _ _ _ _ hn2, hX1def, cleared_update_comm _ _ _ _ hn1,
      hX, cleared_bank_eq edgeCells edgeSlots G F (fun i => hE _)]
    · rfl
    · intro k
      by_cases hk : k = ETHScaleEdgePreparation.raw
      · right
        subst hk
        simp [edgeSlots, hraw, hN]
      · left
        refine ⟨(Fintype.equivFin ETHScaleEdgePreparation.Stack) k, ?_⟩
        simp [edgeCells, edgeSlots, hk]
  rw [hfinal] at hcl
  -- compose
  obtain ⟨t3, ht3, h3⟩ := BitMachineRawSequence.runs depthCopy2 (clearProgram edgeCells)
    BitMachineCopy.Label.scan 0 none none ((), none) ((), none) X1 X2 (afterDepth G n)
    _ _ hc2 hcl
  obtain ⟨t2, ht2, h2⟩ := BitMachineRawSequence.runs depthCopy1 _
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none
    (none, ((), none)) (none, ((), none)) X X1 (afterDepth G n) _ _ hc1 h3
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs edgeProgram _
    edgeStartLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) edgeCtrl edgeCtrl
    (none, (none, ((), none))) (none, (none, ((), none))) G X (afterDepth G n)
    t1 t2 hr1 h2
  refine ⟨t, ?_, h⟩
  unfold depthBound
  have hl1 : (X (aux (.edge cand))).length = EffectiveIteration.sourceDepth n := by
    rw [hXc]; simp
  simp only [List.length_replicate] at ht2 ht3
  unfold edgeCard at hsum ⊢
  omega

#print axioms edge_embedded
#print axioms depth_run

end
end EthInapproximability.CurrentPaper.WeightedRawWords
