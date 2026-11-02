import EthInapproximability.CurrentPaper.SourceNormalizationMachineSupport
import EthInapproximability.CurrentPaper.BitMachineSubroutine
import EthInapproximability.CurrentPaper.EncodedGraph

/-!
# Constructing the graph support from a physical endpoint stream

Source: frozen v8 `06-eth.tex`, `thm:paper-sparse-gap-source`.
The endpoint stream uses one unary-delimited word per endpoint. The graph
decoder is a separate stage. This controller repeatedly executes the literal
support-marking subroutine and explicitly clears each temporary index/rank.
The original variable count and graph payload remain on unchanged stacks.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineMark

open Turing TM2.Stmt BitMachineEncoding BitMachineComposition

inductive Phase where
  | read | clearIndex | clearRank
  deriving DecidableEq, Fintype

abbrev Stack := Fin 5 ⊕ Fin 2
abbrev Label := SourceNormalizationMachineSupport.Label ⊕ Phase
abbrev Control := SourceNormalizationMachineSupport.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some Phase.clearIndex) (SourceNormalizationMachineSupport.program true l)
  | .inr .read => pop (.inr 0) (fun v b => (v.1, b))
      (branch (fun v => v.2.isSome)
        (branch (fun v => v.2.getD false)
          (push (.inl 1) (fun _ => true) (goto (fun _ => .inr .read)))
          (load (fun _ => ((none, false), none)) (goto (fun _ => .inl .scan))))
        (load (fun _ => ((none, false), none)) halt))
  | .inr .clearIndex => pop (.inl 1) (fun v b => (v.1, b))
      (branch (fun v => v.2.isSome) (goto (fun _ => .inr .clearIndex))
        (goto (fun _ => .inr .clearRank)))
  | .inr .clearRank => pop (.inl 3) (fun v b => (v.1, b))
      (branch (fun v => v.2.isSome) (goto (fun _ => .inr .clearRank))
        (load (fun _ => ((none, false), none)) (goto (fun _ => .inr .read))))

def cfg (l : Option Label) (s : Control)
    (vector index saved rank payload stream originalN : List Bool) : Config :=
  ⟨l, s, Sum.elim ![vector,index,saved,rank,payload] ![stream,originalN]⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

def endpointStream : List ℕ → List Bool
  | [] => []
  | u :: us => EncodedGraph.unary u ++ endpointStream us

def markIndices (bits : List Bool) : List ℕ → List Bool
  | [] => bits
  | u :: us => markIndices (bits.set u true) us

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem read_run (u a : ℕ) (s : Control) (vector payload stream originalN : List Bool) :
    run (u + 1) (cfg (some (.inr .read)) s vector (List.replicate a true) [] []
      payload (EncodedGraph.unary u ++ stream) originalN) =
    cfg (some (.inl .scan)) ((none,false),none) vector (List.replicate (a + u) true)
      [] [] payload stream originalN := by
  induction u generalizing a s with
  | zero =>
      apply congrArg (fun S => (⟨some (.inl .scan), ((none,false),none), S⟩ : Config))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | succ u ih =>
      have hs : TM2.step program
          (cfg (some (.inr .read)) s vector (List.replicate a true) [] []
            payload (EncodedGraph.unary (u + 1) ++ stream) originalN) =
          some (cfg (some (.inr .read)) (s.1,some true) vector
            (List.replicate (a + 1) true) [] [] payload
            (EncodedGraph.unary u ++ stream) originalN) := by
        apply congrArg (fun S => some (⟨some (.inr .read), (s.1,some true), S⟩ : Config))
        funext k
        cases k with
        | inl k => fin_cases k <;> rfl
        | inr k => fin_cases k <;> rfl
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (run_succ hs (u + 1)).trans (ih (a + 1) (s.1,some true))

private theorem clearIndex_run (u : ℕ) (s : Control)
    (vector rank payload stream originalN : List Bool) :
    run (u + 1) (cfg (some (.inr .clearIndex)) s vector (List.replicate u true) []
      rank payload stream originalN) =
    cfg (some (.inr .clearRank)) (s.1,none) vector [] [] rank payload stream originalN := by
  induction u generalizing s with
  | zero =>
      apply congrArg (fun S => (⟨some (.inr .clearRank), (s.1,none), S⟩ : Config))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | succ u ih =>
      have hs : TM2.step program
          (cfg (some (.inr .clearIndex)) s vector (List.replicate (u + 1) true) []
            rank payload stream originalN) =
          some (cfg (some (.inr .clearIndex)) (s.1,some true) vector
            (List.replicate u true) [] rank payload stream originalN) := by
        apply congrArg (fun S => some (⟨some (.inr .clearIndex), (s.1,some true), S⟩ : Config))
        funext k
        cases k with
        | inl k => fin_cases k <;> rfl
        | inr k => fin_cases k <;> rfl
      exact (run_succ hs (u + 1)).trans (ih _)

private theorem clearRank_run (r : ℕ) (s : Control)
    (vector payload stream originalN : List Bool) :
    run (r + 1) (cfg (some (.inr .clearRank)) s vector [] [] (List.replicate r true)
      payload stream originalN) =
    cfg (some (.inr .read)) ((none,false),none) vector [] [] [] payload stream originalN := by
  induction r generalizing s with
  | zero =>
      apply congrArg (fun S => (⟨some (.inr .read), ((none,false),none), S⟩ : Config))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | succ r ih =>
      have hs : TM2.step program
          (cfg (some (.inr .clearRank)) s vector [] [] (List.replicate (r + 1) true)
            payload stream originalN) =
          some (cfg (some (.inr .clearRank)) (s.1,some true) vector [] []
            (List.replicate r true) payload stream originalN) := by
        apply congrArg (fun S => some (⟨some (.inr .clearRank), (s.1,some true), S⟩ : Config))
        funext k
        cases k with
        | inl k => fin_cases k <;> rfl
        | inr k => fin_cases k <;> rfl
      exact (run_succ hs (r + 1)).trans (ih _)

theorem one_mark (bits : List Bool) (u : ℕ) (hu : u < bits.length)
    (payload stream originalN : List Bool) :
    ∃ t ≤ 5 * u + 5,
      run t (cfg (some (.inr .read)) ((none,false),none) bits [] [] [] payload
        (EncodedGraph.unary u ++ stream) originalN) =
      cfg (some (.inr .read)) ((none,false),none) (bits.set u true) [] [] []
        payload stream originalN := by
  let before := bits.take u
  let after := bits.drop (u + 1)
  have hlen : before.length = u := by simp [before, Nat.min_eq_left (Nat.le_of_lt hu)]
  have hsplit : bits = before ++ bits[u] :: after := by
    simp only [before, after, List.getElem_cons_drop, List.take_append_drop]
  have hset : bits.set u true = before ++ true :: after := by
    rw [List.set_eq_take_append_cons_drop, if_pos hu]
  have hs := SourceNormalizationMachineSupport.mark_run before bits[u] after payload
  rw [hlen, ← hsplit, ← hset] at hs
  let c := SourceNormalizationMachineSupport.cfg (some .scan) (none,false)
    bits (List.replicate u true) [] [] payload
  let T : Fin 2 → List Bool := ![stream,originalN]
  obtain ⟨v,hv,he⟩ := BitMachineSubroutine.lift_outputs
    (SourceNormalizationMachineSupport.program true) program (some Phase.clearIndex)
    (fun _ => rfl) none T c (2 * u + 2)
    (by simpa only [SourceNormalizationMachineSupport.run,c] using congrArg TM2.Cfg.l hs)
  rw [show ((advance (SourceNormalizationMachineSupport.program true))^[2 * u + 2]) c = _
    from hs] at he
  have he' : run v
      (cfg (some (.inl .scan)) ((none,false),none) bits (List.replicate u true)
        [] [] payload stream originalN) =
      cfg (some (.inr .clearIndex)) ((none,bits[u]),none) (bits.set u true)
        (List.replicate u true) [] (List.replicate (before.count true) true)
        payload stream originalN := he
  have hread := read_run u 0 ((none,false),none) bits payload stream originalN
  simp only [Nat.zero_add,List.replicate_zero] at hread
  have hclear := clearIndex_run u ((none,bits[u]),none) (bits.set u true)
    (List.replicate (before.count true) true) payload stream originalN
  have hdone := clearRank_run (before.count true) ((none,bits[u]),none)
    (bits.set u true) payload stream originalN
  refine ⟨u + 1 + v + (u + 1) + (before.count true + 1), ?_, ?_⟩
  · have hc := List.count_le_length (a := true) (l := before)
    omega
  · exact (run_add ((run_add ((run_add hread v).trans he') (u + 1)).trans hclear)
      (before.count true + 1)).trans hdone

/-- Every endpoint is physically read and marked. The cost is a sum over
the endpoint indices, not a polynomial in an outer source-branch list. -/
theorem mark_stream (bits : List Bool) (indices : List ℕ)
    (hindices : ∀ u ∈ indices, u < bits.length) (payload originalN : List Bool) :
    ∃ t ≤ 5 * indices.sum + 5 * indices.length + 1,
      run t (cfg (some (.inr .read)) ((none,false),none) bits [] [] []
        payload (endpointStream indices) originalN) =
      cfg none ((none,false),none) (markIndices bits indices) [] [] []
        payload [] originalN := by
  induction indices generalizing bits with
  | nil =>
      refine ⟨1, by simp, ?_⟩
      apply congrArg (fun S => (⟨none, ((none,false),none), S⟩ : Config))
      funext k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k => fin_cases k <;> rfl
  | cons u us ih =>
      obtain ⟨v,hv,he⟩ := one_mark bits u (hindices u (by simp)) payload
        (endpointStream us) originalN
      obtain ⟨w,hw,hf⟩ := ih (bits.set u true) (by
        intro z hz
        simpa only [List.length_set] using hindices z (List.mem_cons_of_mem u hz))
      refine ⟨v + w, ?_, (run_add he w).trans hf⟩
      simp only [List.sum_cons, List.length_cons]
      omega

end EthInapproximability.CurrentPaper.SourceNormalizationMachineMark
