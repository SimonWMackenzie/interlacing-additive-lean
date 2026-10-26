import EthInapproximability.CurrentPaper.SourceNormalizationMachineSupport
import EthInapproximability.CurrentPaper.SourceNormalizationMachineMark
import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-!
# Relabelling a physical endpoint stream with a retained copy offset

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`.
Each endpoint is replaced by its support-prefix rank plus an offset held on
a unary stack. The support vector, original variable count, graph payload,
and offset are physically retained. A final reversal restores stream order.
This is still an embedded stage, not the full canonical graph serializer.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineRanks

open Turing TM2.Stmt BitMachineEncoding BitMachineComposition

inductive Phase where
  | read | clearIndex | copyOffset | restoreOffset | writeRank | finish
  deriving DecidableEq, Fintype

abbrev Stack := Fin 5 ⊕ Fin 5
abbrev Label := SourceNormalizationMachineSupport.Label ⊕ Phase
abbrev Control := SourceNormalizationMachineSupport.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some Phase.clearIndex) (SourceNormalizationMachineSupport.program false l)
  | .inr .read => pop (.inr 0) (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (branch (fun v => v.2.getD false)
          (push (.inl 1) (fun _ => true) (goto (fun _ => .inr .read)))
          (load (fun _ => ((none,false),none)) (goto (fun _ => .inl .scan))))
        (load (fun _ => ((none,false),none)) (goto (fun _ => .inr .finish))))
  | .inr .clearIndex => pop (.inl 1) (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome) (goto (fun _ => .inr .clearIndex))
        (goto (fun _ => .inr .copyOffset)))
  | .inr .copyOffset => pop (.inr 2) (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push (.inl 3) (fun _ => true) (push (.inl 2) (fun _ => true)
          (goto (fun _ => .inr .copyOffset))))
        (goto (fun _ => .inr .restoreOffset)))
  | .inr .restoreOffset => pop (.inl 2) (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push (.inr 2) (fun _ => true) (goto (fun _ => .inr .restoreOffset)))
        (goto (fun _ => .inr .writeRank)))
  | .inr .writeRank => pop (.inl 3) (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push (.inr 3) (fun _ => true) (goto (fun _ => .inr .writeRank)))
        (push (.inr 3) (fun _ => false)
          (load (fun _ => ((none,false),none)) (goto (fun _ => .inr .read)))))
  | .inr .finish => pop (.inr 3) (fun v b => (v.1,b))
      (branch (fun v => v.2.isSome)
        (push (.inr 4) (fun v => v.2.getD false) (goto (fun _ => .inr .finish)))
        (load (fun _ => ((none,false),none)) halt))

def cfg (l : Option Label) (s : Control)
    (vector index saved rank payload stream originalN offset revout output : List Bool) : Config :=
  ⟨l,s,Sum.elim ![vector,index,saved,rank,payload] ![stream,originalN,offset,revout,output]⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

def rankAt (bits : List Bool) (u : ℕ) : ℕ := (bits.take u).count true

def rankedStream (bits : List Bool) (offset : ℕ) (indices : List ℕ) : List Bool :=
  SourceNormalizationMachineMark.endpointStream (indices.map fun u => rankAt bits u + offset)

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run,Function.iterate_succ_apply,advance,h,Option.getD_some]

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run,Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem read_run (u a : ℕ) (s : Control)
    (bits payload stream originalN offset revout output : List Bool) :
    run (u + 1) (cfg (some (.inr .read)) s bits (List.replicate a true) [] []
      payload (EncodedGraph.unary u ++ stream) originalN offset revout output) =
    cfg (some (.inl .scan)) ((none,false),none) bits (List.replicate (a + u) true)
      [] [] payload stream originalN offset revout output := by
  induction u generalizing a s with
  | zero =>
      apply congrArg (fun S => (⟨some (.inl .scan),((none,false),none),S⟩ : Config))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | succ u ih =>
      have hs : TM2.step program (cfg (some (.inr .read)) s bits
          (List.replicate a true) [] [] payload (EncodedGraph.unary (u + 1) ++ stream)
          originalN offset revout output) =
          some (cfg (some (.inr .read)) (s.1,some true) bits (List.replicate (a + 1) true)
            [] [] payload (EncodedGraph.unary u ++ stream) originalN offset revout output) := by
        apply congrArg (fun S => some (⟨some (.inr .read),(s.1,some true),S⟩ : Config))
        funext k
        cases k with
        | inl k => fin_cases k <;> rfl
        | inr k => fin_cases k <;> rfl
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (run_succ hs (u + 1)).trans (ih (a + 1) (s.1,some true))

private theorem clearIndex_run (u : ℕ) (s : Control)
    (bits rank payload stream originalN offset revout output : List Bool) :
    run (u + 1) (cfg (some (.inr .clearIndex)) s bits (List.replicate u true) [] rank
      payload stream originalN offset revout output) =
    cfg (some (.inr .copyOffset)) (s.1,none) bits [] [] rank
      payload stream originalN offset revout output := by
  induction u generalizing s with
  | zero =>
      apply congrArg (fun S => (⟨some (.inr .copyOffset),(s.1,none),S⟩ : Config))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | succ u ih =>
      have hs : TM2.step program (cfg (some (.inr .clearIndex)) s bits
          (List.replicate (u + 1) true) [] rank payload stream originalN offset revout output) =
          some (cfg (some (.inr .clearIndex)) (s.1,some true) bits
            (List.replicate u true) [] rank payload stream originalN offset revout output) := by
        apply congrArg (fun S => some (⟨some (.inr .clearIndex),(s.1,some true),S⟩ : Config))
        funext k
        cases k with
        | inl k => fin_cases k <;> rfl
        | inr k => fin_cases k <;> rfl
      exact (run_succ hs (u + 1)).trans (ih _)

private theorem copyOffset_run (o r a : ℕ) (s : Control)
    (bits payload stream originalN revout output : List Bool) :
    run (o + 1) (cfg (some (.inr .copyOffset)) s bits [] (List.replicate a true)
      (List.replicate r true) payload stream originalN (List.replicate o true) revout output) =
    cfg (some (.inr .restoreOffset)) (s.1,none) bits [] (List.replicate (a + o) true)
      (List.replicate (r + o) true) payload stream originalN [] revout output := by
  induction o generalizing a r s with
  | zero =>
      apply congrArg (fun S => (⟨some (.inr .restoreOffset),(s.1,none),S⟩ : Config))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | succ o ih =>
      have hs : TM2.step program (cfg (some (.inr .copyOffset)) s bits []
          (List.replicate a true) (List.replicate r true) payload stream originalN
          (List.replicate (o + 1) true) revout output) =
          some (cfg (some (.inr .copyOffset)) (s.1,some true) bits []
            (List.replicate (a + 1) true) (List.replicate (r + 1) true) payload stream
            originalN (List.replicate o true) revout output) := by
        apply congrArg (fun S => some (⟨some (.inr .copyOffset),(s.1,some true),S⟩ : Config))
        funext k
        cases k with
        | inl k => fin_cases k <;> rfl
        | inr k => fin_cases k <;> rfl
      rw [show o + 1 + 1 = (o + 1) + 1 by omega, run_succ hs]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (r + 1) (a + 1) (s.1,some true)

private theorem restoreOffset_run (o a : ℕ) (s : Control)
    (bits rank payload stream originalN revout output : List Bool) :
    run (o + 1) (cfg (some (.inr .restoreOffset)) s bits [] (List.replicate o true)
      rank payload stream originalN (List.replicate a true) revout output) =
    cfg (some (.inr .writeRank)) (s.1,none) bits [] [] rank payload stream originalN
      (List.replicate (a + o) true) revout output := by
  induction o generalizing a s with
  | zero =>
      apply congrArg (fun S => (⟨some (.inr .writeRank),(s.1,none),S⟩ : Config))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | succ o ih =>
      have hs : TM2.step program (cfg (some (.inr .restoreOffset)) s bits []
          (List.replicate (o + 1) true) rank payload stream originalN
          (List.replicate a true) revout output) =
          some (cfg (some (.inr .restoreOffset)) (s.1,some true) bits []
            (List.replicate o true) rank payload stream originalN
            (List.replicate (a + 1) true) revout output) := by
        apply congrArg (fun S => some (⟨some (.inr .restoreOffset),(s.1,some true),S⟩ : Config))
        funext k
        cases k with
        | inl k => fin_cases k <;> rfl
        | inr k => fin_cases k <;> rfl
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (run_succ hs (o + 1)).trans (ih (a + 1) (s.1,some true))

private theorem writeRank_run (r : ℕ) (s : Control)
    (bits payload stream originalN offset revout output : List Bool) :
    run (r + 1) (cfg (some (.inr .writeRank)) s bits [] [] (List.replicate r true)
      payload stream originalN offset revout output) =
    cfg (some (.inr .read)) ((none,false),none) bits [] [] [] payload stream originalN
      offset ((EncodedGraph.unary r).reverse ++ revout) output := by
  induction r generalizing s revout with
  | zero =>
      apply congrArg (fun S => (⟨some (.inr .read),((none,false),none),S⟩ : Config))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | succ r ih =>
      have hs : TM2.step program (cfg (some (.inr .writeRank)) s bits [] []
          (List.replicate (r + 1) true) payload stream originalN offset revout output) =
          some (cfg (some (.inr .writeRank)) (s.1,some true) bits [] []
            (List.replicate r true) payload stream originalN offset (true :: revout) output) := by
        apply congrArg (fun S => some (⟨some (.inr .writeRank),(s.1,some true),S⟩ : Config))
        funext k
        cases k with
        | inl k => fin_cases k <;> rfl
        | inr k => fin_cases k <;> rfl
      rw [run_succ hs, ih]
      congr 1
      simp [EncodedGraph.unary,List.replicate_succ,List.reverse_cons,List.append_assoc]

theorem one_rank (bits : List Bool) (u : ℕ) (hu : u < bits.length) (o : ℕ)
    (payload stream originalN revout output : List Bool) :
    ∃ t ≤ 5 * u + 3 * o + 7,
      run t (cfg (some (.inr .read)) ((none,false),none) bits [] [] [] payload
        (EncodedGraph.unary u ++ stream) originalN (List.replicate o true) revout output) =
      cfg (some (.inr .read)) ((none,false),none) bits [] [] [] payload stream originalN
        (List.replicate o true) ((EncodedGraph.unary (rankAt bits u + o)).reverse ++ revout)
        output := by
  let before := bits.take u
  let after := bits.drop (u + 1)
  have hlen : before.length = u := by simp [before,Nat.min_eq_left (Nat.le_of_lt hu)]
  have hsplit : bits = before ++ bits[u] :: after := by
    simp only [before,after,List.getElem_cons_drop,List.take_append_drop]
  have hs := SourceNormalizationMachineSupport.rank_run before bits[u] after payload
  rw [hlen,← hsplit] at hs
  let c := SourceNormalizationMachineSupport.cfg (some .scan) (none,false)
    bits (List.replicate u true) [] [] payload
  let T : Fin 5 → List Bool := ![stream,originalN,List.replicate o true,revout,output]
  obtain ⟨v,hv,he⟩ := BitMachineSubroutine.lift_outputs
    (SourceNormalizationMachineSupport.program false) program (some Phase.clearIndex)
    (fun _ => rfl) none T c (2 * u + 2)
    (by simpa only [SourceNormalizationMachineSupport.run,c] using congrArg TM2.Cfg.l hs)
  rw [show ((advance (SourceNormalizationMachineSupport.program false))^[2 * u + 2]) c = _
    from hs] at he
  have he' : run v (cfg (some (.inl .scan)) ((none,false),none) bits
      (List.replicate u true) [] [] payload stream originalN (List.replicate o true) revout output) =
      cfg (some (.inr .clearIndex)) ((none,bits[u]),none) bits (List.replicate u true) []
        (List.replicate (rankAt bits u) true) payload stream originalN
        (List.replicate o true) revout output := he
  have hread := read_run u 0 ((none,false),none) bits payload stream originalN
    (List.replicate o true) revout output
  simp only [Nat.zero_add,List.replicate_zero] at hread
  have hclear := clearIndex_run u ((none,bits[u]),none) bits
    (List.replicate (rankAt bits u) true) payload stream originalN (List.replicate o true) revout output
  have hcopy := copyOffset_run o (rankAt bits u) 0 ((none,bits[u]),none)
    bits payload stream originalN revout output
  have hrestore := restoreOffset_run o 0 ((none,bits[u]),none) bits
    (List.replicate (rankAt bits u + o) true) payload stream originalN revout output
  simp only [Nat.zero_add,List.replicate_zero] at hcopy hrestore
  have hwrite := writeRank_run (rankAt bits u + o) ((none,bits[u]),none)
    bits payload stream originalN (List.replicate o true) revout output
  refine ⟨u + 1 + v + (u + 1) + (o + 1) + (o + 1) + (rankAt bits u + o + 1), ?_, ?_⟩
  · have hc : rankAt bits u ≤ u :=
      (List.count_le_length (a := true) (l := before)).trans (Nat.le_of_eq hlen)
    omega
  · exact (run_add ((run_add ((run_add ((run_add ((run_add hread v).trans he') (u + 1)).trans
      hclear) (o + 1)).trans hcopy) (o + 1)).trans hrestore) (rankAt bits u + o + 1)).trans hwrite

theorem rank_stream_into (bits : List Bool) (indices : List ℕ)
    (hindices : ∀ u ∈ indices, u < bits.length) (o : ℕ)
    (payload suffix originalN revout output : List Bool) :
    ∃ t ≤ 5 * indices.sum + (3 * o + 7) * indices.length,
      run t (cfg (some (.inr .read)) ((none,false),none) bits [] [] [] payload
        (SourceNormalizationMachineMark.endpointStream indices ++ suffix) originalN
        (List.replicate o true) revout output) =
      cfg (some (.inr .read)) ((none,false),none) bits [] [] [] payload suffix originalN
        (List.replicate o true) ((rankedStream bits o indices).reverse ++ revout) output := by
  induction indices generalizing revout with
  | nil => exact ⟨0,by simp,rfl⟩
  | cons u us ih =>
      obtain ⟨v,hv,he⟩ := one_rank bits u (hindices u (by simp)) o payload
        (SourceNormalizationMachineMark.endpointStream us ++ suffix) originalN revout output
      obtain ⟨w,hw,hf⟩ := ih (fun z hz => hindices z (List.mem_cons_of_mem u hz))
        ((EncodedGraph.unary (rankAt bits u + o)).reverse ++ revout)
      refine ⟨v + w, ?_, ?_⟩
      · simp only [List.sum_cons,List.length_cons]
        nlinarith
      · simpa only [SourceNormalizationMachineMark.endpointStream,List.append_assoc,
          rankedStream,List.map_cons,List.reverse_append] using (run_add he w).trans hf

private theorem finish_run (revout : List Bool) (s : Control)
    (bits payload originalN offset output : List Bool) :
    run (revout.length + 1) (cfg (some (.inr .finish)) s bits [] [] [] payload [] originalN
      offset revout output) =
    cfg none ((none,false),none) bits [] [] [] payload [] originalN offset []
      (revout.reverse ++ output) := by
  induction revout generalizing s output with
  | nil =>
      apply congrArg (fun S => (⟨none,((none,false),none),S⟩ : Config))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | cons b bs ih =>
      have hs : TM2.step program (cfg (some (.inr .finish)) s bits [] [] [] payload [] originalN
          offset (b :: bs) output) =
          some (cfg (some (.inr .finish)) (s.1,some b) bits [] [] [] payload [] originalN
            offset bs (b :: output)) := by
        apply congrArg (fun S => some (⟨some (.inr .finish),(s.1,some b),S⟩ : Config))
        funext k
        cases k with
        | inl k => fin_cases k <;> rfl
        | inr k => fin_cases k <;> rfl
      rw [List.length_cons,run_succ hs,ih]
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

/-- A complete retained-offset relabelling pass, including the charged final
reversal. It returns unary endpoint fields in the original input order. -/
theorem rank_stream (bits : List Bool) (indices : List ℕ)
    (hindices : ∀ u ∈ indices, u < bits.length) (o : ℕ)
    (payload originalN : List Bool) :
    ∃ t ≤ 5 * indices.sum + (3 * o + 7) * indices.length +
        (rankedStream bits o indices).length + 2,
      run t (cfg (some (.inr .read)) ((none,false),none) bits [] [] [] payload
        (SourceNormalizationMachineMark.endpointStream indices) originalN
        (List.replicate o true) [] []) =
      cfg none ((none,false),none) bits [] [] [] payload [] originalN
        (List.replicate o true) [] (rankedStream bits o indices) := by
  obtain ⟨v,hv,he⟩ := rank_stream_into bits indices hindices o payload [] originalN [] []
  simp only [List.append_nil] at he
  have hs : TM2.step program
      (cfg (some (.inr .read)) ((none,false),none) bits [] [] [] payload [] originalN
        (List.replicate o true) (rankedStream bits o indices).reverse []) =
      some (cfg (some (.inr .finish)) ((none,false),none) bits [] [] [] payload [] originalN
        (List.replicate o true) (rankedStream bits o indices).reverse []) := by
    apply congrArg (fun S => some (⟨some (.inr .finish),((none,false),none),S⟩ : Config))
    funext k
    cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl
  have hf := finish_run (rankedStream bits o indices).reverse ((none,false),none)
    bits payload originalN (List.replicate o true) []
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hf
  refine ⟨v + ((rankedStream bits o indices).length + 1 + 1), by omega, ?_⟩
  exact (run_add he _).trans ((run_succ hs _).trans hf)

end EthInapproximability.CurrentPaper.SourceNormalizationMachineRanks
