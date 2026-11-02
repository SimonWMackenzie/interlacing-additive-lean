import CurrentAdditive.QuarticPacketFront

/-! Copy the seven exact quartic numeric inputs from the graph/count carrier
to the generic physical threshold and sample-dimension machine. -/

namespace Paper2.CurrentAdditive.QuarticNumericFront.TM27

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.RandomizedSchedule

abbrev Stack := Packet27.Stack
abbrev JM := TMFront.JM

def src (i : Fin 7) : Stack :=
  ![Packet27.packet 1,
    Packet27.graph (Graph27.new (LQ27.wc (.inl LProducer.pC))),
    Packet27.graph (Graph27.new (LQ27.wc (.inl LProducer.sC))),
    Packet27.graph (Graph27.new (LQ27.wc (.inl LProducer.q2C))),
    Packet27.graph (Graph27.new (LQ27.wc (.inr (.inl 9)))),
    Packet27.graph (Graph27.new (LQ27.qc (.inl 24))),
    Packet27.graph (Graph27.new (LQ27.wc (.inl (LProducer.outR 0))))] i

def dest (i : Fin 7) : Stack := Packet27.tm (FullFront.dB i)
def copies (i : Fin 7) : Fin 3 ↪ Stack :=
  ⟨![src i, dest i, Packet27.scratch], by
    intro x y h
    fin_cases i <;> fin_cases x <;> fin_cases y <;>
      simp_all [src, dest, Packet27.graph, Packet27.tm, Packet27.packet,
        Packet27.scratch]⟩

theorem src_ne_dst (i j : Fin 7) : copies i 0 ≠ copies j 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [copies, src, dest, Packet27.graph, Packet27.tm, Packet27.packet]
theorem scratch_ne_dst (i j : Fin 7) : copies i 2 ≠ copies j 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [copies, dest, Packet27.scratch, Packet27.tm]
theorem dst_injective (i j : Fin 7) (h : copies i 1 = copies j 1) : i = j := by
  have h' : FullFront.dB i = FullFront.dB j := by
    simpa [copies, dest, Packet27.tm] using h
  exact FullFront.dB_inj i j h'

theorem width_in_graph_exit (g : EncodedGraph.Graph) (hg : g.Valid)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool) :
    Packet27.graphExit g hg FLold FQold FLnew FQnew
      (Graph27.new (LQ27.wc (.inr (.inl 9)))) =
      List.replicate (width27 (Nat.clog 2 g.vertices)) true := by
  unfold Packet27.graphExit
  change bank Graph27.newSlots
      (CopyAll.done Graph27.copies 2 (Graph27.oldBank g hg FLold FQold))
      (bank LQ27.qSlots
        (CopyAll.done LQ27.copySlots 4
          (LQ27.widthBank g.vertices g.edges.length FLnew)) FQnew)
      (Graph27.newSlots (LQ27.wc (.inr (.inl 9)))) = _
  rw [bank_at Graph27.newSlots]
  rw [bank_outside LQ27.qSlots _ _ (LQ27.wc (.inr (.inl 9)))
    (by rintro ⟨x, hx⟩; cases hx)]
  rw [CopyAll.done_off LQ27.copySlots _ (LQ27.wc (.inr (.inl 9)))
    (by intro i; fin_cases i <;> simp [LQ27.copySlots, LQ27.target,
      LQ27.qc, LQ27.wc]) 4]
  change (Function.update (Function.update (Function.update
    (WidthMachine.initial (RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))) 1
    (List.replicate 4 true)) 5
    (List.replicate (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices)) true))
    9 (List.replicate (width27 (Nat.clog 2 g.vertices)) true)) 9 = _
  exact Function.update_self _ _ _

theorem lcell_in_graph_exit (g : EncodedGraph.Graph) (hg : g.Valid)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool)
    (x : LProducer.LK) :
    Packet27.graphExit g hg FLold FQold FLnew FQnew
      (Graph27.new (LQ27.wc (.inl x))) = FLnew x := by
  unfold Packet27.graphExit
  change bank Graph27.newSlots
      (CopyAll.done Graph27.copies 2 (Graph27.oldBank g hg FLold FQold))
      (bank LQ27.qSlots
        (CopyAll.done LQ27.copySlots 4
          (LQ27.widthBank g.vertices g.edges.length FLnew)) FQnew)
      (Graph27.newSlots (LQ27.wc (.inl x))) = _
  rw [bank_at Graph27.newSlots]
  rw [bank_outside LQ27.qSlots _ _ (LQ27.wc (.inl x))
    (by rintro ⟨y, hy⟩; cases hy)]
  rw [CopyAll.done_off LQ27.copySlots _ (LQ27.wc (.inl x))
    (by intro i; fin_cases i <;> simp [LQ27.copySlots, LQ27.target,
      LQ27.qc, LQ27.wc]) 4]
  rfl

theorem qcell_in_graph_exit (g : EncodedGraph.Graph) (hg : g.Valid)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool)
    (x : QProducer.QK) :
    Packet27.graphExit g hg FLold FQold FLnew FQnew
      (Graph27.new (LQ27.qc x)) = FQnew x := by
  unfold Packet27.graphExit
  change bank Graph27.newSlots
      (CopyAll.done Graph27.copies 2 (Graph27.oldBank g hg FLold FQold))
      (bank LQ27.qSlots
        (CopyAll.done LQ27.copySlots 4
          (LQ27.widthBank g.vertices g.edges.length FLnew)) FQnew)
      (Graph27.newSlots (LQ27.qSlots x)) = _
  rw [bank_at Graph27.newSlots, bank_at LQ27.qSlots]

theorem packet_lcell (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool)
    (x : LProducer.LK) :
    Packet27.exitBank g hg k word FLold FQold FLnew FQnew
      (Packet27.graph (Graph27.new (LQ27.wc (.inl x)))) = FLnew x :=
  lcell_in_graph_exit g hg FLold FQold FLnew FQnew x

theorem packet_qcell (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool)
    (x : QProducer.QK) :
    Packet27.exitBank g hg k word FLold FQold FLnew FQnew
      (Packet27.graph (Graph27.new (LQ27.qc x))) = FQnew x :=
  qcell_in_graph_exit g hg FLold FQold FLnew FQnew x

theorem packet_width (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool) :
    Packet27.exitBank g hg k word FLold FQold FLnew FQnew
      (Packet27.graph (Graph27.new (LQ27.wc (.inr (.inl 9))))) =
      List.replicate (width27 (Nat.clog 2 g.vertices)) true :=
  width_in_graph_exit g hg FLold FQold FLnew FQnew

theorem source_values (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool) (Δ : ℕ) (γ : ℚ)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool)
    (hFacts : CountFront.LFacts g.vertices FLnew)
    (hQ : FQnew (.inl 24) = List.replicate
      (Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
        (Nat.clog 2 g.vertices) γ Δ) true)
    (i : Fin 7) :
    Packet27.exitBank g hg k word FLold FQold FLnew FQnew (copies i 0) =
      List.replicate (![k, LookupSeed.width (Nat.clog 2 g.vertices),
        SourceProfileParameters.width (Nat.clog 2 g.vertices),
        SourceProfileParameters.outerWidth (Nat.clog 2 g.vertices),
        width27 (Nat.clog 2 g.vertices),
        Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
          (Nat.clog 2 g.vertices) γ Δ,
        Nat.clog 2 g.vertices] i) true := by
  obtain ⟨-, -, -, -, -, -, -, hp, hs, hq2, -, -, -, -, -, -, g0, g1,
    hr0, -, hout0, -⟩ := hFacts
  have hp' : FLnew LProducer.pC =
      List.replicate (LookupSeed.width (Nat.clog 2 g.vertices)) true := by
    rw [LProducer.p_eq]
    exact hp
  have hs' : FLnew LProducer.sC =
      List.replicate (SourceProfileParameters.width (Nat.clog 2 g.vertices)) true := by
    rw [LProducer.s_eq]
    exact hs
  have hq2' : FLnew LProducer.q2C =
      List.replicate (SourceProfileParameters.outerWidth (Nat.clog 2 g.vertices)) true := by
    rw [LProducer.q₂_eq]
    exact hq2
  have hL : FLnew (LProducer.outR 0) =
      List.replicate (Nat.clog 2 g.vertices) true := (hr0 _).trans hout0
  fin_cases i
  · rfl
  · exact (packet_lcell g hg k word FLold FQold FLnew FQnew LProducer.pC).trans hp'
  · exact (packet_lcell g hg k word FLold FQold FLnew FQnew LProducer.sC).trans hs'
  · exact (packet_lcell g hg k word FLold FQold FLnew FQnew LProducer.q2C).trans hq2'
  · exact packet_width g hg k word FLold FQold FLnew FQnew
  · exact (packet_qcell g hg k word FLold FQold FLnew FQnew (.inl 24)).trans hQ
  · exact (packet_lcell g hg k word FLold FQold FLnew FQnew
      (LProducer.outR 0)).trans hL

def afterCopies (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool) (v : Fin 5 → ℕ) (L : ℕ)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool) :
    Stack → List Bool :=
  Sum.elim (Packet27.graphExit g hg FLold FQold FLnew FQnew)
    (Sum.elim (TMFront.TM0 k v L)
      (Sum.elim (fun _ => [])
        (Sum.elim (FullFront.X0 g k word) (fun _ => []))))

theorem doneB (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool) (p s q₂ w Q L : ℕ)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool)
    (hv : ∀ i, Packet27.exitBank g hg k word FLold FQold FLnew FQnew
      (copies i 0) = List.replicate (![k,p,s,q₂,w,Q,L] i) true) :
    CopyAll.done copies 7
      (Packet27.exitBank g hg k word FLold FQold FLnew FQnew) =
      afterCopies g hg k word ![p,s,q₂,w,Q] L FLold FQold FLnew FQnew := by
  let B := Packet27.exitBank g hg k word FLold FQold FLnew FQnew
  funext z
  by_cases hz : ∃ j, copies j 1 = z
  · obtain ⟨j, rfl⟩ := hz
    rw [CopyAll.done_dst copies dst_injective B j]
    dsimp only [B]
    rw [hv j]
    have he : B (copies j 1) = [] := rfl
    change Packet27.exitBank g hg k word FLold FQold FLnew FQnew
      (copies j 1) = [] at he
    rw [he, List.append_nil]
    change _ = TMFront.TM0 k ![p,s,q₂,w,Q] L (FullFront.dB j)
    fin_cases j <;> rfl
  · rw [CopyAll.done_off copies B z (fun j h => hz ⟨j, h⟩)]
    rcases z with z | (y | (y | (y | y)))
    · rfl
    · change [] = TMFront.TM0 k ![p,s,q₂,w,Q] L y
      rcases y with (a' | ⟨i, x⟩) | (m | f)
      · fin_cases a'
        · rfl
        · rfl
        · exact absurd ⟨0, rfl⟩ hz
        · rfl
      · by_cases hx : x = .inl 0
        · subst hx
          fin_cases i
          · exact absurd ⟨1, rfl⟩ hz
          · exact absurd ⟨2, rfl⟩ hz
          · exact absurd ⟨3, rfl⟩ hz
          · exact absurd ⟨4, rfl⟩ hz
          · exact absurd ⟨5, rfl⟩ hz
        · show [] = (if x = .inl 0 then _ else [])
          rw [if_neg hx]
      · by_cases hm : m = 2
        · subst hm
          exact absurd ⟨6, rfl⟩ hz
        · show [] = Function.update (fun _ => []) (2 : TMFront.MK)
            (MProducer.u L) m
          rw [Function.update_of_ne hm]
      · rfl
    · rfl
    · rfl
    · rfl

theorem source_doneB (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool) (Δ : ℕ) (γ : ℚ)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool)
    (hFacts : CountFront.LFacts g.vertices FLnew)
    (hQ : FQnew (.inl 24) = List.replicate
      (Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
        (Nat.clog 2 g.vertices) γ Δ) true) :
    CopyAll.done copies 7
      (Packet27.exitBank g hg k word FLold FQold FLnew FQnew) =
      afterCopies g hg k word
        (vector27 g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ)
        (Nat.clog 2 g.vertices) FLold FQold FLnew FQnew := by
  exact doneB g hg k word
    (LookupSeed.width (Nat.clog 2 g.vertices))
    (SourceProfileParameters.width (Nat.clog 2 g.vertices))
    (SourceProfileParameters.outerWidth (Nat.clog 2 g.vertices))
    (width27 (Nat.clog 2 g.vertices))
    (Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) γ Δ)
    (Nat.clog 2 g.vertices)
    FLold FQold FLnew FQnew
    (source_values g hg k word Δ γ FLold FQold FLnew FQnew hFacts hQ)

theorem runCopies (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool) (p s q₂ w Q L : ℕ)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool)
    (hv : ∀ i, Packet27.exitBank g hg k word FLold FQold FLnew FQnew
      (copies i 0) = List.replicate (![k,p,s,q₂,w,Q,L] i) true) :
    ∃ t ≤ 7 * (2 * (k+p+s+q₂+w+Q+L) + 3) + 1, ∃ vc,
      ((advance (CopyAll.prog copies))^[t])
        (⟨some (.inl ⟨0, by omega⟩), none,
          Packet27.exitBank g hg k word FLold FQold FLnew FQnew⟩ :
          TM2.Cfg (fun _ : Stack => Bool) (CopyAll.Lab 7) (Option Bool)) =
        ⟨none, vc, afterCopies g hg k word ![p,s,q₂,w,Q] L
          FLold FQold FLnew FQnew⟩ := by
  obtain ⟨t, ht, vc, hr⟩ := CopyAll.all_run copies src_ne_dst scratch_ne_dst
    dst_injective (Packet27.exitBank g hg k word FLold FQold FLnew FQnew)
    (fun _ => rfl) (k+p+s+q₂+w+Q+L)
    (fun i => by
      rw [hv i, List.length_replicate]
      fin_cases i <;> simp <;> omega) none
  refine ⟨t, ht, vc, ?_⟩
  rw [doneB g hg k word p s q₂ w Q L FLold FQold FLnew FQnew hv] at hr
  exact hr

def tmProgram := fun l => stackStmt Packet27.tmSlots (TMFront.tmProg l)

def afterTM (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool)
    (FT : TMFront.TK → List Bool) (FM : TMFront.MK → List Bool) :
    Stack → List Bool :=
  Sum.elim (Packet27.graphExit g hg FLold FQold FLnew FQnew)
    (Sum.elim (Sum.elim FT (Sum.elim FM (fun _ => [])))
      (Sum.elim (fun _ => [])
        (Sum.elim (FullFront.X0 g k word) (fun _ => []))))

theorem runTM (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool) (v : Fin 5 → ℕ) (L : ℕ)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool) :
    ∃ t ≤ TMFront.tmBd k v L, ∃ vc,
      ∃ FT : TMFront.TK → List Bool, ∃ FM : TMFront.MK → List Bool,
      ((advance tmProgram)^[t])
        (⟨some TMFront.tmStart, TMFront.tmCtl,
          afterCopies g hg k word v L FLold FQold FLnew FQnew⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, vc, afterTM g hg k word FLold FQold FLnew FQnew FT FM⟩ ∧
      TMFront.TFacts k v FT ∧
      TMFront.MFacts (TMFront.thrVal k v) k L FM := by
  obtain ⟨t, ht, vc, FT, FM, hr, hTF, hMF⟩ := TMFront.tm_run k v L
  have hrun := BitMachineStackRun.run Packet27.tmSlots
    (afterCopies g hg k word v L FLold FQold FLnew FQnew)
    TMFront.tmProg
    (⟨some TMFront.tmStart, TMFront.tmCtl, TMFront.TM0 k v L⟩ :
      TM2.Cfg (fun _ : JM => Bool) _ _) t
  rw [hr] at hrun
  have hstart : stackCfg Packet27.tmSlots
      (afterCopies g hg k word v L FLold FQold FLnew FQnew)
      (⟨some TMFront.tmStart, TMFront.tmCtl, TMFront.TM0 k v L⟩ :
        TM2.Cfg (fun _ : JM => Bool) _ _) =
      ⟨some TMFront.tmStart, TMFront.tmCtl,
        afterCopies g hg k word v L FLold FQold FLnew FQnew⟩ := by
    simp only [stackCfg]
    rw [bank_eq_self Packet27.tmSlots
      (afterCopies g hg k word v L FLold FQold FLnew FQnew)
      (TMFront.TM0 k v L) (fun x => rfl)]
  rw [hstart] at hrun
  have hend : bank Packet27.tmSlots
      (afterCopies g hg k word v L FLold FQold FLnew FQnew)
      (Sum.elim FT (Sum.elim FM (fun _ => []))) =
      afterTM g hg k word FLold FQold FLnew FQnew FT FM := by
    funext z
    rcases z with z | (y | y)
    · exact bank_outside Packet27.tmSlots _ _ _ (by rintro ⟨x, hx⟩; cases hx)
    · exact bank_at Packet27.tmSlots _ _ y
    · exact bank_outside Packet27.tmSlots _ _ _ (by rintro ⟨x, hx⟩; cases hx)
  simp only [stackCfg] at hrun
  rw [hend] at hrun
  exact ⟨t, ht, vc, FT, FM, hrun, hTF, hMF⟩

end
end Paper2.CurrentAdditive.QuarticNumericFront.TM27

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.TM27.width_in_graph_exit
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.TM27.source_doneB
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.TM27.runCopies
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.TM27.runTM
