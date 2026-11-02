import EthInapproximability.CurrentPaper.WeightedRawWordsConsumer

/-! # S4: the level-0 handoff theorem

One fixed program: the S1 guarded parse and constant writer, then S2, S3 and
a short tail (copy `C` into consumer word 0, copy `Gw` into the consumer's
parser input, push the guard bit), each joined by one charged handoff. From
the literal branch packet its exit bank is exactly

  `Sum.elim (WeightedRawRowsSource.initialBank (runParameters G c b (seedState b) 0)
     (serializeGraph G) noW) (masterBank ...)`

with `b = sourceDepth n`: the admitted consumer start bank with an empty
writer, and the master region `N, Gw, C, B, Y = y₀, E` (`Jc`, `K` empty).
No input word is installed: every cell is produced by a charged machine. -/

namespace EthInapproximability.CurrentPaper.WeightedRawWords

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

theorem rawCell_ne_pIn (j : Fin 6) : rawCell j ≠ pInCell := by
  simp [rawCell, pInCell, cons, pInCons, pInWB, WeightedActualSizeSuffix.scaleKey]

theorem aux_ne_pIn (a : Aux) : aux a ≠ pInCell := by
  simp [aux, pInCell, cons]

def tCopy0 := copyProg (aux .C) (rawCell 0) (aux_ne_rawCell 0 _) (by simp) (rawCell_ne_aux 0 _)
def tCopyP := copyProg (aux .Gw) pInCell (aux_ne_pIn _) (by simp) (by simp [pInCell, cons, aux])

def t2 := BitMachineRawSequence.program tCopyP (SourceClauseFixedUnary.program pInCell 1)
  0 none ()
/-- The S4 tail program. -/
def tailProgram := BitMachineRawSequence.program tCopy0 t2
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none (none, ())

def tailCtrl : BitMachineRawSequence.Control (Option Bool)
    (BitMachineRawSequence.Control (Option Bool) Unit) := (none, (none, ()))

def tailBank (X : Global → List Bool) (w : List Bool) (c : ℕ) : Global → List Bool :=
  Function.update (Function.update X (rawCell 0) (List.replicate c true))
    pInCell (true :: w)

theorem tail_run (X : Global → List Bool) (w : List Bool) (c : ℕ)
    (hC : X (aux .C) = List.replicate c true) (hGw : X (aux .Gw) = w)
    (h0 : X (rawCell 0) = []) (hp : X pInCell = []) (hcs : X (aux .cs) = []) :
    ∃ t ≤ (2 * c + 2) + ((2 * w.length + 2) + 2 + 1) + 1,
      ((advance tailProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan), tailCtrl, X⟩ :
          TM2.Cfg (fun _ : Global => Bool) _ _) =
        ⟨none, tailCtrl, tailBank X w c⟩ := by
  have s1 := copy_word (aux .C) (rawCell 0) (aux_ne_rawCell 0 _) (by simp)
    (rawCell_ne_aux 0 _) X h0 hcs
  rw [hC] at s1
  simp only [List.length_replicate] at s1
  set X1 := Function.update X (rawCell 0) (List.replicate c true) with hX1
  have s2 := copy_word (aux .Gw) pInCell (aux_ne_pIn _) (by simp)
    (by simp [pInCell, cons, aux]) X1
    (by rw [hX1, Function.update_of_ne (Ne.symm (rawCell_ne_pIn 0))]; exact hp)
    (by rw [hX1, Function.update_of_ne (aux_ne_rawCell 0 _)]; exact hcs)
  have hX1G : X1 (aux .Gw) = w := by
    rw [hX1, Function.update_of_ne (aux_ne_rawCell 0 _)]; exact hGw
  rw [hX1G] at s2
  have s3 := push_unary pInCell (Function.update X1 pInCell w) 1
  rw [Function.update_self, Function.update_idem] at s3
  have hw1 : List.replicate 1 true ++ w = true :: w := rfl
  rw [hw1] at s3
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs tCopyP
    (SourceClauseFixedUnary.program pInCell 1) BitMachineCopy.Label.scan 0 none none () ()
    X1 (Function.update X1 pInCell w) (tailBank X w c) _ _ s2 s3
  obtain ⟨u, hu, r⟩ := BitMachineRawSequence.runs tCopy0 t2 BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none none (none, ()) (none, ())
    X X1 (tailBank X w c) _ _ s1 r2
  exact ⟨u, by omega, r⟩

/-! ## The whole level-0 program -/

def afterS1Program :=
  BitMachineRawSequence.program level0Program
    (BitMachineRawSequence.program edgesProgram tailProgram
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) edgesCtrl tailCtrl)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    level0Ctrl (edgesCtrl, tailCtrl)

/-- The fixed level-0 raw-word program (`c` is a program constant). -/
def rawWordsProgram (c : ℕ) :=
  unpackProgram c afterS1Program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel edgeStartLabel)))
    (level0Ctrl, (edgesCtrl, tailCtrl))

/-- Exit bank of the level-0 program. -/
def exitBank {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (n c : ℕ) :
    Global → List Bool :=
  tailBank (afterEdges (level0Bank n (EncodedGraph.encode (EncodedETHSource.serializeGraph G)) c)
    (Fintype.card E)) (EncodedGraph.encode (EncodedETHSource.serializeGraph G)) c

def rawWordsBound (n c N : ℕ) (g : EncodedGraph.Graph) : ℕ :=
  (7 * ((SourceOriginalBranchPackets.packet n (EncodedGraph.encode g)).length + 1) + 1) +
    ((c + 1) + (level0Bound n + (edgesBound g + ((2 * c + 2) + ((2 * N + 2) + 2 + 1) + 1) + 1) + 1)
      + 1) + 1

theorem rawWords_run {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (n c : ℕ) :
    ∃ t ≤ rawWordsBound n c (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length
        (EncodedETHSource.serializeGraph G),
      ((advance (rawWordsProgram c))^[t])
        (unpackStart c (SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))
          (level0Ctrl, (edgesCtrl, tailCtrl))) =
        ⟨none, (none, ((), (level0Ctrl, (edgesCtrl, tailCtrl)))), exitBank G n c⟩ := by
  set w := EncodedGraph.encode (EncodedETHSource.serializeGraph G) with hw
  obtain ⟨t1, ht1, h1⟩ := level0_run n w c
  obtain ⟨t2, ht2, h2⟩ := edges_run G (level0Bank n w c)
    (by simp [level0Bank, costFinal, afterDepth, afterUnpack, afterParse, hw])
    (by intro k; simp [level0Bank, costFinal, afterDepth, afterUnpack, afterParse])
    (by simp [level0Bank, costFinal, afterDepth, afterUnpack, afterParse])
    (by simp [level0Bank, costFinal, afterDepth, afterUnpack, afterParse])
    (by simp [level0Bank, costFinal, afterDepth, afterUnpack, afterParse])
  obtain ⟨t3, ht3, h3⟩ := tail_run (afterEdges (level0Bank n w c) (Fintype.card E)) w c
    (by simp [afterEdges, level0Bank, costFinal, afterDepth, afterUnpack, afterParse])
    (by simp [afterEdges, level0Bank, costFinal, afterDepth, afterUnpack, afterParse])
    (by simp [afterEdges, level0Bank, costFinal, afterDepth, afterUnpack, afterParse])
    (by simp [afterEdges, level0Bank, costFinal, afterDepth, afterUnpack, afterParse,
      pInCell, rawCell, cons, aux, pInCons, pInWB, WeightedActualSizeSuffix.scaleKey])
    (by simp [afterEdges, level0Bank, costFinal, afterDepth, afterUnpack, afterParse])
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs edgesProgram tailProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    edgesCtrl edgesCtrl tailCtrl tailCtrl (level0Bank n w c)
    (afterEdges (level0Bank n w c) (Fintype.card E)) (exitBank G n c) t2 t3 h2 h3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs level0Program
    (BitMachineRawSequence.program edgesProgram tailProgram
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) edgesCtrl tailCtrl)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel edgeStartLabel))
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    level0Ctrl level0Ctrl (edgesCtrl, tailCtrl) (edgesCtrl, tailCtrl)
    (afterUnpack n w c) (level0Bank n w c) (exitBank G n c) t1 u2 h1 r2
  obtain ⟨t, ht, h⟩ := unpack_valid n w c afterS1Program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel edgeStartLabel)))
    (level0Ctrl, (edgesCtrl, tailCtrl)) (level0Ctrl, (edgesCtrl, tailCtrl))
    (exitBank G n c) u1 r1
  refine ⟨t, ?_, h⟩
  unfold rawWordsBound
  rw [← hw]
  omega

/-! ## The exit bank is the admitted consumer start bank plus the masters -/

/-- The master region at level 0. -/
def masterBank (n : ℕ) (w : List Bool) (c b y e : ℕ) : Aux → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (fun _ => []) Aux.N (List.replicate n true))
    Aux.Gw w) Aux.C (List.replicate c true)) Aux.B (List.replicate b true))
    Aux.Y (List.replicate y true)) Aux.E (List.replicate e true)

theorem restrictL_inl {A B : Type*} [DecidableEq A] [DecidableEq (A ⊕ B)]
    (F : A ⊕ B → List Bool) (y : A) (u : List Bool) :
    (fun x => Function.update F (Sum.inl y) u (Sum.inl x)) =
      Function.update (fun x => F (Sum.inl x)) y u := by
  funext x
  by_cases h : x = y
  · subst h; simp
  · simp [Function.update_apply, h]

theorem restrictL_inr {A B : Type*} [DecidableEq (A ⊕ B)]
    (F : A ⊕ B → List Bool) (a : B) (u : List Bool) :
    (fun x => Function.update F (Sum.inr a) u (Sum.inl x)) = fun x => F (Sum.inl x) := by
  funext x
  simp [Function.update_apply]

theorem restrictR_inl {A B : Type*} [DecidableEq (A ⊕ B)]
    (F : A ⊕ B → List Bool) (y : A) (u : List Bool) :
    (fun a => Function.update F (Sum.inl y) u (Sum.inr a)) = fun a => F (Sum.inr a) := by
  funext a
  simp [Function.update_apply]

theorem restrictR_inr {A B : Type*} [DecidableEq B] [DecidableEq (A ⊕ B)]
    (F : A ⊕ B → List Bool) (b : B) (u : List Bool) :
    (fun a => Function.update F (Sum.inr b) u (Sum.inr a)) =
      Function.update (fun a => F (Sum.inr a)) b u := by
  funext a
  by_cases h : a = b
  · subst h; simp
  · simp [Function.update_apply, h]

theorem split_bank (F : Global → List Bool) :
    F = Sum.elim (fun x => F (Sum.inl x)) (fun a => F (Sum.inr a)) := by
  funext j
  cases j <;> rfl

theorem exitBank_eq {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (n c : ℕ) :
    exitBank G n c =
      Sum.elim
        (WeightedRawRowsSource.initialBank
          (EffectiveIteration.runParameters G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)) 0)
          (EncodedETHSource.serializeGraph G) noW)
        (masterBank n (EncodedGraph.encode (EncodedETHSource.serializeGraph G)) c
          (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget (Fintype.card E)) := by
  set w := EncodedGraph.encode (EncodedETHSource.serializeGraph G) with hw
  set b := EffectiveIteration.sourceDepth n with hb
  rw [split_bank (exitBank G n c)]
  congr 1
  · -- consumer region
    rw [EffectiveIteration.runParameters_zero_indexing, consumer_chain]
    have v0 : W6 (EffectiveIteration.initialInput c (Fintype.card E) b) 0 =
        List.replicate c true := rfl
    have v1 : W6 (EffectiveIteration.initialInput c (Fintype.card E) b) 1 =
        List.replicate b true := rfl
    have v2 : W6 (EffectiveIteration.initialInput c (Fintype.card E) b) 2 =
        List.replicate (1 + costExp b) true := by
      simp [W6, ETHParameterScaleMachineInput.words, EffectiveIteration.initialInput,
        costExp_eq, Nat.add_comm]
    have v3 : W6 (EffectiveIteration.initialInput c (Fintype.card E) b) 3 =
        List.replicate (2 ^ 2 ^ costExp b) true := by
      simp [W6, ETHParameterScaleMachineInput.words, EffectiveIteration.initialInput,
        costExp_eq, IndexSeed.width]
    have v4 : W6 (EffectiveIteration.initialInput c (Fintype.card E) b) 4 =
        List.replicate (2 ^ costExp b) true := by
      simp [W6, ETHParameterScaleMachineInput.words, EffectiveIteration.initialInput,
        costExp_eq, IndexSeed.width]
    have v5 : W6 (EffectiveIteration.initialInput c (Fintype.card E) b) 5 =
        List.replicate (Fintype.card E) true := rfl
    rw [v0, v1, v2, v3, v4, v5]
    unfold exitBank tailBank afterEdges
    rw [level0Bank_eq]
    simp only [pInCell, rawCell, aux, cons, restrictL_inl, restrictL_inr]
    have hne : ∀ j, pInCons ≠ consRaw j := by
      intro j
      simp [pInCons, consRaw, pInWB, rawWB, WeightedBinsGraphQ.binSlots,
        WeightedBinsGeneric.paramSlots, BinsWriterAssembly.paramSlots]
    funext x
    by_cases hx : x = pInCons
    · subst hx
      rw [Function.update_self]
      simp only [Function.update_of_ne (hne _), Function.update_self]
    · rw [Function.update_of_ne hx]
      simp only [Function.update_apply, hx, if_false]
      rfl
  · -- master region
    unfold exitBank tailBank afterEdges
    rw [level0Bank_eq]
    simp only [pInCell, rawCell, aux, cons, restrictR_inl, restrictR_inr]
    unfold masterBank
    simp only [Iteration.seedState, costExp_eq, Nat.add_comm]
    rfl

/-- S4, combined: from the literal packet, the fixed program halts with the
admitted consumer start bank (empty writer) and the level-0 master region. -/
theorem level0_handoff {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E) (n c : ℕ) :
    ∃ t ≤ rawWordsBound n c (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length
        (EncodedETHSource.serializeGraph G),
      ((advance (rawWordsProgram c))^[t])
        (unpackStart c (SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))
          (level0Ctrl, (edgesCtrl, tailCtrl))) =
        ⟨none, (none, ((), (level0Ctrl, (edgesCtrl, tailCtrl)))),
          Sum.elim
            (WeightedRawRowsSource.initialBank
              (EffectiveIteration.runParameters G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)) 0)
              (EncodedETHSource.serializeGraph G) noW)
            (masterBank n (EncodedGraph.encode (EncodedETHSource.serializeGraph G)) c
              (EffectiveIteration.sourceDepth n)
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget
              (Fintype.card E))⟩ := by
  obtain ⟨t, ht, h⟩ := rawWords_run G n c
  rw [exitBank_eq] at h
  exact ⟨t, ht, h⟩

/-- The same fixed program halts on every undecodable input. -/
theorem rawWords_reject (c : ℕ) (input : List Bool)
    (hd : BitMachineBankCodec.decode 2 input = none) :
    ∃ t ≤ 5 * (input.length + 1) + 2, ∃ T : Global → List Bool,
      ((advance (rawWordsProgram c))^[t])
        (unpackStart c input (level0Ctrl, (edgesCtrl, tailCtrl))) =
        ⟨none, (some false, ((), (level0Ctrl, (edgesCtrl, tailCtrl)))), T⟩ :=
  unpack_reject c input hd afterS1Program _ _

#print axioms level0_handoff
#print axioms rawWords_reject
#print axioms tail_run
#print axioms rawWords_run
#print axioms exitBank_eq

end
end EthInapproximability.CurrentPaper.WeightedRawWords
