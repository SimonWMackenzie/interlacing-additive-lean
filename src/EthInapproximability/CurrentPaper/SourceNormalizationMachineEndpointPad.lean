import EthInapproximability.CurrentPaper.SourceNormalizationMachineK2Stream
import EthInapproximability.CurrentPaper.SourceNormalizationNumeric
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# Physical padded endpoint stream

Write the K2 unary suffix from the retained original vertex count, then
prepend a source-preserving physical copy of the decoder's ordered endpoint
stream. The output is the exact stream consumed by the rank relabeller.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineEndpointPad

open Turing BitMachineEncoding

abbrev Stack := Fin 7
abbrev Label := SourceNormalizationMachineK2Stream.Phase ⊕ BitMachineCopy.Label
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)

def k2Stack : SourceNormalizationMachineK2Stream.Stack ↪ Stack where
  toFun k := ⟨k.val, by omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun k : Stack => k.val) h

def copyStack : Fin 3 ↪ Stack where
  toFun k := match k.val with
    | 0 => 5
    | 1 => 2
    | _ => 6
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .inl l => BitMachineStackEmbedding.stmt k2Stack Sum.inl id id
      (some (.inr BitMachineCopy.Label.scan))
      (SourceNormalizationMachineK2Stream.program l)
  | .inr l => BitMachineStackEmbedding.stmt copyStack Sum.inr id id none
      (BitMachineCopy.program l)

def cfg (l : Option Label) (s : Option Bool)
    (vertices saved output payload originalN stream copySaved : List Bool) : Config :=
  ⟨l, s, ![vertices, saved, output, payload, originalN, stream, copySaved]⟩

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem k2_program_eq (l : SourceNormalizationMachineK2Stream.Phase) :
    program (.inl l) = BitMachineStackEmbedding.stmt k2Stack Sum.inl id id
      (some (.inr BitMachineCopy.Label.scan))
      (SourceNormalizationMachineK2Stream.program l) := rfl

private theorem copy_program_eq (l : BitMachineCopy.Label) :
    program (.inr l) = BitMachineStackEmbedding.stmt copyStack Sum.inr id id none
      (BitMachineCopy.program l) := rfl

def startBank (v : ℕ) (payload originalN stream : List Bool) : Stack → List Bool :=
  ![List.replicate v true, [], [], payload, originalN, stream, []]

def suffix (v : ℕ) : List Bool :=
  SourceNormalizationMachineMark.endpointStream [v, v + 1]

def copyForeign (v : ℕ) (payload originalN stream : List Bool) : Stack → List Bool :=
  ![List.replicate v true, [], suffix v, payload, originalN, stream, []]

private theorem k2_initial (v : ℕ) (payload originalN stream : List Bool) :
    BitMachineStackEmbedding.cfg k2Stack (startBank v payload originalN stream)
      Sum.inl id (some (.inr BitMachineCopy.Label.scan))
      (SourceNormalizationMachineK2Stream.cfg (some .start) none
        (List.replicate v true) [] [] payload originalN) =
    cfg (some (.inl .start)) none (List.replicate v true) [] [] payload originalN stream [] := by
  have hlocal : ∀ k : SourceNormalizationMachineK2Stream.Stack,
      (SourceNormalizationMachineK2Stream.cfg (some .start) none
        (List.replicate v true) [] [] payload originalN).stk k =
        startBank v payload originalN stream (k2Stack k) := by
    intro k
    fin_cases k <;> rfl
  have hbank := BitMachineStackEmbedding.bank_eq_self k2Stack
    (startBank v payload originalN stream) _ hlocal
  change (⟨some (.inl .start),none,
      BitMachineStackEmbedding.bank k2Stack (startBank v payload originalN stream)
        (SourceNormalizationMachineK2Stream.cfg (some .start) none
          (List.replicate v true) [] [] payload originalN).stk⟩ : Config) = _
  rw [hbank]
  rfl

theorem k2_stage (v : ℕ) (payload originalN stream : List Bool) :
    ∃ t ≤ 2 * v + 5,
      run t (BitMachineStackEmbedding.cfg k2Stack
        (startBank v payload originalN stream) Sum.inl id
        (some (.inr BitMachineCopy.Label.scan))
        (SourceNormalizationMachineK2Stream.cfg (some .start) none
          (List.replicate v true) [] [] payload originalN)) =
      BitMachineStackEmbedding.cfg k2Stack
        (startBank v payload originalN stream) Sum.inl id
        (some (.inr BitMachineCopy.Label.scan))
        (SourceNormalizationMachineK2Stream.cfg none none
          (List.replicate v true) []
          (SourceNormalizationMachineMark.endpointStream [v,v+1])
          payload originalN) := by
  have hs := SourceNormalizationMachineK2Stream.k2_run v payload originalN
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs k2Stack
    (startBank v payload originalN stream) Sum.inl id id (by intro s; rfl)
    (some (.inr BitMachineCopy.Label.scan))
    SourceNormalizationMachineK2Stream.program program k2_program_eq
    (SourceNormalizationMachineK2Stream.cfg (some .start) none
      (List.replicate v true) [] [] payload originalN) (2 * v + 5)
    (by change (SourceNormalizationMachineK2Stream.run (2 * v + 5) _).l = none
        rw [hs]; rfl)
  rw [show ((advance SourceNormalizationMachineK2Stream.program)^[2 * v + 5])
    (SourceNormalizationMachineK2Stream.cfg (some .start) none
      (List.replicate v true) [] [] payload originalN) = _ from hs] at he
  exact ⟨t, ht, he⟩

private theorem k2_final_update (v : ℕ) (payload originalN : List Bool) :
    (SourceNormalizationMachineK2Stream.cfg none none
      (List.replicate v true) [] (suffix v) payload originalN).stk =
    Function.update (SourceNormalizationMachineK2Stream.cfg (some .start) none
      (List.replicate v true) [] [] payload originalN).stk
      (2 : SourceNormalizationMachineK2Stream.Stack) (suffix v) := by
  funext k
  fin_cases k <;> simp [SourceNormalizationMachineK2Stream.cfg]

/-- K2 writing hands its actual output stack directly to the source-copy
program; neither a host-language concatenation nor an uncharged move occurs. -/
theorem k2_to_copy (v : ℕ) (payload originalN stream : List Bool) :
    BitMachineStackEmbedding.cfg k2Stack (startBank v payload originalN stream)
      Sum.inl id (some (.inr BitMachineCopy.Label.scan))
      (SourceNormalizationMachineK2Stream.cfg none none
        (List.replicate v true) [] (suffix v) payload originalN) =
    BitMachineStackEmbedding.cfg copyStack (copyForeign v payload originalN stream)
      Sum.inr id none (BitMachineCopy.cfg (some .scan) none stream (suffix v) []) := by
  let S := startBank v payload originalN stream
  have hinit : ∀ k : SourceNormalizationMachineK2Stream.Stack,
      (SourceNormalizationMachineK2Stream.cfg (some .start) none
        (List.replicate v true) [] [] payload originalN).stk k = S (k2Stack k) := by
    intro k
    fin_cases k <;> rfl
  have hbank : BitMachineStackEmbedding.bank k2Stack S
      (SourceNormalizationMachineK2Stream.cfg none none
        (List.replicate v true) [] (suffix v) payload originalN).stk =
      copyForeign v payload originalN stream := by
    rw [k2_final_update, BitMachineStackEmbedding.bank_update]
    rw [BitMachineStackEmbedding.bank_eq_self k2Stack S _ hinit]
    funext k
    fin_cases k <;> simp [S, startBank, copyForeign, k2Stack]
  have hcopy : ∀ k : Fin 3,
      (BitMachineCopy.cfg (some .scan) none stream (suffix v) []).stk k =
        copyForeign v payload originalN stream (copyStack k) := by
    intro k
    fin_cases k <;> rfl
  have hbank' := BitMachineStackEmbedding.bank_eq_self copyStack
    (copyForeign v payload originalN stream) _ hcopy
  change (⟨some (.inr BitMachineCopy.Label.scan), none,
      BitMachineStackEmbedding.bank k2Stack S
        (SourceNormalizationMachineK2Stream.cfg none none
          (List.replicate v true) [] (suffix v) payload originalN).stk⟩ : Config) =
    (⟨some (.inr BitMachineCopy.Label.scan), none,
      BitMachineStackEmbedding.bank copyStack
        (copyForeign v payload originalN stream)
        (BitMachineCopy.cfg (some .scan) none stream (suffix v) []).stk⟩ : Config)
  rw [hbank, hbank']

theorem copy_stage (v : ℕ) (payload originalN stream : List Bool) :
    ∃ t ≤ 2 * stream.length + 2,
      run t (BitMachineStackEmbedding.cfg copyStack
        (copyForeign v payload originalN stream) Sum.inr id none
        (BitMachineCopy.cfg (some .scan) none stream (suffix v) [])) =
      BitMachineStackEmbedding.cfg copyStack
        (copyForeign v payload originalN stream) Sum.inr id none
        (BitMachineCopy.cfg none none stream (stream ++ suffix v) []) := by
  have hs := BitMachineCopy.run_correct none stream (suffix v)
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs copyStack
    (copyForeign v payload originalN stream) Sum.inr id id (by intro s; rfl)
    none BitMachineCopy.program program copy_program_eq
    (BitMachineCopy.cfg (some .scan) none stream (suffix v) [])
    (2 * stream.length + 2)
    (by change (BitMachineCopy.run (2 * stream.length + 2) _).l = none
        rw [hs]; rfl)
  rw [show ((advance BitMachineCopy.program)^[2 * stream.length + 2])
    (BitMachineCopy.cfg (some .scan) none stream (suffix v) []) = _ from hs] at he
  exact ⟨t, ht, he⟩

private theorem copy_final_eq (v : ℕ) (payload originalN stream : List Bool) :
    BitMachineStackEmbedding.cfg copyStack (copyForeign v payload originalN stream)
      Sum.inr id none
      (BitMachineCopy.cfg none none stream (stream ++ suffix v) []) =
    cfg none none (List.replicate v true) [] (stream ++ suffix v)
      payload originalN stream [] := by
  let S := copyForeign v payload originalN stream
  have hlocal : ∀ k : Fin 3,
      (BitMachineCopy.cfg (some .scan) none stream (suffix v) []).stk k =
        S (copyStack k) := by
    intro k
    fin_cases k <;> rfl
  have hfin : (BitMachineCopy.cfg none none stream (stream ++ suffix v) []).stk =
      Function.update (BitMachineCopy.cfg (some .scan) none stream (suffix v) []).stk
        (1 : Fin 3) (stream ++ suffix v) := by
    funext k
    fin_cases k <;> simp [BitMachineCopy.cfg, BitMachineCopy.stackContents]
  have hbank : BitMachineStackEmbedding.bank copyStack S
      (BitMachineCopy.cfg none none stream (stream ++ suffix v) []).stk =
      Function.update S (copyStack 1) (stream ++ suffix v) := by
    rw [hfin, BitMachineStackEmbedding.bank_update]
    rw [BitMachineStackEmbedding.bank_eq_self copyStack S _ hlocal]
  change (⟨none,none,BitMachineStackEmbedding.bank copyStack S
    (BitMachineCopy.cfg none none stream (stream ++ suffix v) []).stk⟩ : Config) = _
  rw [hbank]
  apply congrArg (fun T => (⟨none,none,T⟩ : Config))
  funext k
  fin_cases k <;> simp [S, copyForeign, copyStack]

/-- A complete physical two-stage run retains the decoder stream and builds
its exact K2-padded copy in another stack. The original `n` is unchanged. -/
theorem endpointPad_run (v : ℕ) (payload originalN stream : List Bool) :
    ∃ t ≤ (2 * v + 5) + (2 * stream.length + 2),
      run t (cfg (some (.inl .start)) none
        (List.replicate v true) [] [] payload originalN stream []) =
      cfg none none (List.replicate v true) [] (stream ++ suffix v)
        payload originalN stream [] := by
  obtain ⟨a, ha, h₁⟩ := k2_stage v payload originalN stream
  obtain ⟨b, hb, h₂⟩ := copy_stage v payload originalN stream
  have hfirst : run a (cfg (some (.inl .start)) none
      (List.replicate v true) [] [] payload originalN stream []) =
      BitMachineStackEmbedding.cfg copyStack (copyForeign v payload originalN stream)
        Sum.inr id none
        (BitMachineCopy.cfg (some .scan) none stream (suffix v) []) := by
    exact (congrArg (run a) (k2_initial v payload originalN stream).symm).trans
      (h₁.trans (k2_to_copy v payload originalN stream))
  refine ⟨a + b, by omega, ?_⟩
  exact (run_add hfirst b).trans (h₂.trans (copy_final_eq v payload originalN stream))

theorem endpointStream_append (xs ys : List ℕ) :
    SourceNormalizationMachineMark.endpointStream (xs ++ ys) =
      SourceNormalizationMachineMark.endpointStream xs ++
        SourceNormalizationMachineMark.endpointStream ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, SourceNormalizationMachineMark.endpointStream,
        ih, List.append_assoc]

theorem endpointPad_graph_run (g : EncodedGraph.Graph)
    (payload originalN : List Bool) :
    ∃ t ≤ (2 * g.vertices + 5) +
        (2 * (SourceNormalizationMachineMark.endpointStream
          (SourceNormalizationNumeric.endpoints g)).length + 2),
      run t (cfg (some (.inl .start)) none
        (List.replicate g.vertices true) [] [] payload originalN
        (SourceNormalizationMachineMark.endpointStream
          (SourceNormalizationNumeric.endpoints g)) []) =
      cfg none none (List.replicate g.vertices true) []
        (SourceNormalizationMachineMark.endpointStream
          (SourceNormalizationNumeric.paddedEndpoints g))
        payload originalN
        (SourceNormalizationMachineMark.endpointStream
          (SourceNormalizationNumeric.endpoints g)) [] := by
  obtain ⟨t, ht, he⟩ := endpointPad_run g.vertices payload originalN
    (SourceNormalizationMachineMark.endpointStream
      (SourceNormalizationNumeric.endpoints g))
  refine ⟨t, ht, ?_⟩
  simpa only [suffix, SourceNormalizationNumeric.paddedEndpoints,
    endpointStream_append] using he

end EthInapproximability.CurrentPaper.SourceNormalizationMachineEndpointPad
