import EthInapproximability.CurrentPaper.WeightedRawRowsSource
import Mathlib.Data.Fin.VecNotation

/-! Source-preserving transfer of the raw-six `Parameters.Input.columns` word
to weighted-writer cell 27. The writer dimension is initially blank. -/

namespace EthInapproximability.CurrentPaper.WeightedRawColumnsSource

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section
set_option maxRecDepth 4096

abbrev Stack := WeightedRawRowsSource.Stack
def rawColumns : Stack :=
  WeightedActualSizeSuffix.scaleKey (.inl (ETHScaleGlobalLog.raw 4))
def writer := WeightedRawRowsSource.writer
def slots : Fin 3 ↪ Stack :=
  ⟨![rawColumns,writer 27,writer 63],by
    intro a b h
    fin_cases a <;> fin_cases b <;>
      simp [rawColumns,writer,WeightedRawRowsSource.writer,
        WeightedScalarComplete.writer,
        WeightedActualSizeSuffix.scaleKey,WeightedActualSizeSuffix.writer,
        WeightedMTPrefix.writer,WeightedPrefixAT.writer,
        WeightedScaleDerivedFromBins.writer,WeightedBinsGraphQ.writer,
        WeightedGraphQJoined.writer] at h ⊢⟩
def program := MatrixStage4ScalarPreparationOps.copyProgram slots
def initialBank := WeightedRawRowsSource.initialBank
def finalBank (i : Parameters.Input) (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) : Stack → List Bool :=
  Function.update (initialBank i g W) (writer 27)
    (List.replicate i.columns true)

theorem initial_rawColumns (i : Parameters.Input) (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) :
    initialBank i g W rawColumns = List.replicate i.columns true := by
  change (WeightedBinsGraphQ.initialBank i g W)
    (WeightedBinsGraphQ.binSlots
      (WeightedBinsGeneric.paramSlots
        (ETHBinsJoinedScratch.scaleEmbed
          (ETHScaleActualComplete.oldEmbed
            (ETHScaleGlobalLog.raw 4))))) = _
  simp only [WeightedBinsGraphQ.initialBank,bank_at,
    WeightedBinsGeneric.initialBank,ETHBinsJoinedScratch.initialBank,
    ETHScaleActualComplete.initialBank,ETHScaleGlobalLog.initial,
    ETHParameterScaleMachineInput.words]
  rfl

theorem initial_writer (i : Parameters.Input) (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool) (k : Fin 64) :
    initialBank i g W (writer k) = W k :=
  WeightedRawRowsSource.initial_writer i g W k

private theorem sum_right_update {A B : Type*} [DecidableEq A] [DecidableEq B]
    (F : A → List Bool) (W : B → List Bool) (k : B) (word : List Bool) :
    Sum.elim F (Function.update W k word) =
      Function.update (Sum.elim F W) (.inr k) word := by
  funext j
  cases j <;> simp

private theorem sum_left_update {A B : Type*} [DecidableEq A] [DecidableEq B]
    (F : A → List Bool) (W : B → List Bool) (k : A) (word : List Bool) :
    Sum.elim (Function.update F k word) W =
      Function.update (Sum.elim F W) (.inl k) word := by
  funext j
  cases j <;> simp

private theorem sum_left_update_any {A B : Type*}
    (dA : DecidableEq A) (d : DecidableEq (A ⊕ B))
    (F : A → List Bool) (W : B → List Bool) (k : A) (word : List Bool) :
    Sum.elim (@Function.update A (fun _ => List Bool) dA F k word) W =
      @Function.update (A ⊕ B) (fun _ => List Bool) d
        (Sum.elim F W) (.inl k) word := by
  funext j
  rcases j with j | j
  · by_cases hj : j = k
    · subst j; simp [Function.update]
    · simp [Function.update,hj]
  · simp [Function.update]

private theorem bank_foreign_update_outside {K J : Type*}
    [DecidableEq K] [DecidableEq J]
    (ι : K ↪ J) (F : J → List Bool) (S : K → List Bool)
    (j : J) (word : List Bool) (hout : ¬ ∃ k, ι k = j) :
    bank ι (Function.update F j word) S =
      Function.update (bank ι F S) j word := by
  funext z
  by_cases hz : z = j
  · subst z
    rw [bank_outside ι (Function.update F j word) S j hout]
    simp
  · by_cases hr : ∃ k, ι k = z
    · obtain ⟨k,rfl⟩ := hr
      rw [bank_at,Function.update_of_ne hz,bank_at]
    · rw [bank_outside ι (Function.update F j word) S z hr]
      simp only [Function.update_of_ne hz]
      rw [bank_outside ι F S z hr]

private theorem bank_foreign_update_inside {K J : Type*}
    [DecidableEq K] [DecidableEq J]
    (ι : K ↪ J) (F : J → List Bool) (S : K → List Bool)
    (k : K) (word : List Bool) :
    bank ι (Function.update F (ι k) word) S = bank ι F S := by
  funext z
  by_cases hr : ∃ p, ι p = z
  · obtain ⟨p,rfl⟩ := hr; rw [bank_at,bank_at]
  · rw [bank_outside ι _ S z hr,bank_outside ι F S z hr]
    have hne : z ≠ ι k := by
      intro h; exact hr ⟨k,h.symm⟩
    simp [hne]

theorem initial_update_writer (i : Parameters.Input)
    (g : EncodedGraph.Graph) (W : Fin 64 → List Bool)
    (word : List Bool) :
    initialBank i g (Function.update W 27 word) =
      Function.update (initialBank i g W) (writer 27) word := by
  have hbin : WeightedBinsGeneric.initialBank i
      (Function.update W 27 word) =
      Function.update (WeightedBinsGeneric.initialBank i W) (.inr 27) word := by
    simp only [WeightedBinsGeneric.initialBank,WeightedBinsGeneric.foreignBank,
      sum_right_update]
    exact bank_foreign_update_outside WeightedBinsGeneric.paramSlots
      (Sum.elim (fun _ => []) W) (ETHBinsJoinedScratch.initialBank i)
      (.inr 27) word (by rintro ⟨k,h⟩; cases h)
  have hparser : (GraphVertexPreludeJoin.parserStart g
      (Function.update W 27 word)).stk =
      Function.update (GraphVertexPreludeJoin.parserStart g W).stk
        (.inr 27) word := by
    change bank GraphVertexPreludeJoin.parserSlots
        (Sum.elim (fun _ => []) (Function.update W 27 word))
        (SourceNormalizationMachineDecode.guardedStart
          (true :: EncodedGraph.encode g)).stk = _
    rw [sum_right_update]
    exact bank_foreign_update_outside GraphVertexPreludeJoin.parserSlots
      (Sum.elim (fun _ => []) W) _ (.inr 27) word
      (by rintro ⟨k,h⟩; cases h)
  have hgraph : WeightedGraphQJoined.initialBank g
      (Function.update W 27 word) =
      Function.update (WeightedGraphQJoined.initialBank g W)
        (WeightedGraphQJoined.writer 27) word := by
    simp only [WeightedGraphQJoined.initialBank,WeightedGraphQJoined.lift]
    rw [hparser,bank_update]
    rfl
  have hbase : WeightedBinsGraphQ.base g
      (Function.update W 27 word) =
      Function.update (WeightedBinsGraphQ.base g W)
        (WeightedBinsGraphQ.graphSlots (WeightedGraphQJoined.writer 27)) word := by
    simp only [WeightedBinsGraphQ.base,hgraph]
    exact sum_right_update (fun _ => [])
      (WeightedGraphQJoined.initialBank g W)
      (WeightedGraphQJoined.writer 27) word
  have hjoined : WeightedBinsGraphQ.initialBank i g
      (Function.update W 27 word) =
      Function.update (WeightedBinsGraphQ.initialBank i g W)
        (WeightedBinsGraphQ.writer 27) word := by
    simp only [WeightedBinsGraphQ.initialBank,hbase,hbin]
    change bank WeightedBinsGraphQ.binSlots
      (Function.update (WeightedBinsGraphQ.base g W)
        (WeightedBinsGraphQ.binSlots (.inr 27)) word)
      (Function.update (WeightedBinsGeneric.initialBank i W) (.inr 27) word) = _
    rw [bank_foreign_update_inside,bank_update]
    rfl
  simp only [initialBank,WeightedRawRowsSource.initialBank,
    WeightedScalarComplete.initialBank,
    WeightedActualSizeSuffix.initialBank,WeightedMTPrefix.initialBank,
    WeightedPrefixAT.initialBank,WeightedScaleDerivedFromBins.initialBank,
    hjoined]
  rw [sum_left_update,sum_left_update]
  exact sum_left_update_any
    (fun a b => instDecidableEqSum a b : DecidableEq WeightedMTPrefix.Stack)
    (inferInstanceAs (DecidableEq Stack))
    (Sum.elim (Sum.elim (WeightedBinsGraphQ.initialBank i g W)
      (fun _ => [])) (fun _ => []) : WeightedMTPrefix.Stack → List Bool)
    (fun _ : ChosenPrimeRaw.Stack ⊕ Fin 8 => [])
    ((.inl (.inl (WeightedBinsGraphQ.writer 27))) :
      WeightedMTPrefix.Stack) word

theorem copy_run (i : Parameters.Input) (g : EncodedGraph.Graph)
    (W : Fin 64 → List Bool)
    (h27 : W 27 = []) (h63 : W 63 = []) :
    ((advance program)^[2*i.columns+2])
      (⟨some .scan,none,initialBank i g W⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none,none,finalBank i g W⟩ := by
  have hs := initial_rawColumns i g W
  have ht := (initial_writer i g W 27).trans h27
  have hb := (initial_writer i g W 63).trans h63
  have h := MatrixStage4ScalarPreparationOps.copy_run slots
    (initialBank i g W) hb
  change ((advance program)^[2*(initialBank i g W rawColumns).length+2])
    (⟨some .scan,none,initialBank i g W⟩ :
      TM2.Cfg (fun _ : Stack => Bool) _ _) =
    ⟨none,none,Function.update (initialBank i g W) (writer 27)
      (initialBank i g W rawColumns ++ initialBank i g W (writer 27))⟩ at h
  rw [hs,ht,List.append_nil] at h
  simpa only [program,finalBank,List.length_replicate] using h

#print axioms copy_run

end
end EthInapproximability.CurrentPaper.WeightedRawColumnsSource
