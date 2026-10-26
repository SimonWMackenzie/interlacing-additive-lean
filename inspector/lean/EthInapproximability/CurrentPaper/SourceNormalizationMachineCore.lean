import EthInapproximability.CurrentPaper.SourceNormalizationMachineSeed
import EthInapproximability.CurrentPaper.SourceNormalizationMachineMark
import EthInapproximability.CurrentPaper.SourceNormalizationMachinePad
import EthInapproximability.CurrentPaper.SourceNormalizationNumeric
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# Shared-bank support normalization controller

This is a literal finite program joining the three operational stages: an
all-false support seed from the decoded unary vertex count, marking the
decoded ordered endpoint stream, and appending the two K2 support bits.
Separate count, rank/copy, and canonical output-writing stages remain.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineCore

open Turing BitMachineEncoding BitMachineComposition

abbrev Stack := SourceNormalizationMachineMark.Stack ⊕ Fin 3
abbrev Label := SourceNormalizationMachineMark.Label ⊕
  (SourceNormalizationMachineSeed.Phase ⊕ SourceNormalizationMachinePad.Phase)
abbrev Control := SourceNormalizationMachineMark.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def seedStack : SourceNormalizationMachineSeed.Stack ↪ Stack where
  toFun k := match k.val with
    | 0 => .inr 0
    | 1 => .inr 1
    | 2 => .inl (.inl 0)
    | 3 => .inl (.inl 4)
    | _ => .inl (.inr 1)
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def padStack : SourceNormalizationMachinePad.Stack ↪ Stack where
  toFun k := match k.val with
    | 0 => .inl (.inl 0)
    | 1 => .inr 2
    | 2 => .inl (.inl 4)
    | _ => .inl (.inr 1)
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def seedLabel (l : SourceNormalizationMachineSeed.Phase) : Label := .inr (.inl l)
def padLabel (l : SourceNormalizationMachinePad.Phase) : Label := .inr (.inr l)
def seedControl (s : Option Bool) : Control := (((none,false),none),s)
def padControl (s : Option Bool) : Control := (((none,false),none),s)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some (.inr SourceNormalizationMachinePad.Phase.scan))
      (SourceNormalizationMachineMark.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt seedStack seedLabel
      seedControl Prod.snd (some (.inl (.inr SourceNormalizationMachineMark.Phase.read)))
      (SourceNormalizationMachineSeed.program l)
  | .inr (.inr l) => BitMachineStackEmbedding.stmt padStack padLabel
      padControl Prod.snd none (SourceNormalizationMachinePad.program l)

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def seedForeign (v : ℕ) (payload stream originalN : List Bool) : Stack → List Bool :=
  Sum.elim (Sum.elim ![[], [], [], [], payload] ![stream, originalN])
    ![List.replicate v true, [], []]

private theorem seed_program_eq (l : SourceNormalizationMachineSeed.Phase) :
    program (seedLabel l) = BitMachineStackEmbedding.stmt seedStack seedLabel
      seedControl Prod.snd (some (.inl (.inr SourceNormalizationMachineMark.Phase.read)))
      (SourceNormalizationMachineSeed.program l) := by cases l <;> rfl

private theorem pad_program_eq (l : SourceNormalizationMachinePad.Phase) :
    program (padLabel l) = BitMachineStackEmbedding.stmt padStack padLabel
      padControl Prod.snd none (SourceNormalizationMachinePad.program l) := by
  cases l <;> rfl

private theorem mark_program_eq (l : SourceNormalizationMachineMark.Label) :
    program (.inl l) = liftStmt (some (.inr SourceNormalizationMachinePad.Phase.scan))
      (SourceNormalizationMachineMark.program l) := rfl

/-- The shared controller really executes the unary support-seed program on
the selected banks, with all other banks retained. -/
theorem seed_stage (v : ℕ) (payload originalN : List Bool)
    (foreign : Stack → List Bool) :
    ∃ t ≤ 2 * v + 2,
      run t (BitMachineStackEmbedding.cfg seedStack foreign seedLabel seedControl
        (some (.inl (.inr SourceNormalizationMachineMark.Phase.read)))
        (SourceNormalizationMachineSeed.cfg (some .copy) none
          (List.replicate v true) [] [] payload originalN)) =
      BitMachineStackEmbedding.cfg seedStack foreign seedLabel seedControl
        (some (.inl (.inr SourceNormalizationMachineMark.Phase.read)))
        (SourceNormalizationMachineSeed.cfg none none
          (List.replicate v true) [] (List.replicate v false) payload originalN) := by
  have hs := SourceNormalizationMachineSeed.seed_run v payload originalN
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs seedStack foreign seedLabel
    seedControl Prod.snd (by intro s; rfl)
    (some (.inl (.inr SourceNormalizationMachineMark.Phase.read)))
    SourceNormalizationMachineSeed.program program seed_program_eq
    (SourceNormalizationMachineSeed.cfg (some .copy) none
      (List.replicate v true) [] [] payload originalN) (2 * v + 2)
    (by change (SourceNormalizationMachineSeed.run (2 * v + 2)
      (SourceNormalizationMachineSeed.cfg (some .copy) none
        (List.replicate v true) [] [] payload originalN)).l = none
        rw [hs]; rfl)
  rw [show ((advance SourceNormalizationMachineSeed.program)^[2 * v + 2])
    (SourceNormalizationMachineSeed.cfg (some .copy) none
      (List.replicate v true) [] [] payload originalN) = _ from hs] at he
  exact ⟨t, ht, he⟩

private theorem seed_local_initial (v : ℕ) (payload stream originalN : List Bool) :
    ∀ k : SourceNormalizationMachineSeed.Stack,
      (SourceNormalizationMachineSeed.cfg (some .copy) none
        (List.replicate v true) [] [] payload originalN).stk k =
      seedForeign v payload stream originalN (seedStack k) := by
  intro k
  fin_cases k <;> rfl

private theorem seed_local_final_update (v : ℕ) (payload originalN : List Bool) :
    (SourceNormalizationMachineSeed.cfg none none
      (List.replicate v true) [] (List.replicate v false) payload originalN).stk =
    Function.update (SourceNormalizationMachineSeed.cfg (some .copy) none
      (List.replicate v true) [] [] payload originalN).stk
      (2 : SourceNormalizationMachineSeed.Stack) (List.replicate v false) := by
  funext k
  fin_cases k <;> simp [SourceNormalizationMachineSeed.cfg]

/-- The seed machine's physical final state is exactly the mark machine's
initial state on the same shared bank, with no uncharged transfer. -/
theorem seed_to_mark (v : ℕ) (payload stream originalN : List Bool) :
    BitMachineStackEmbedding.cfg seedStack (seedForeign v payload stream originalN)
      seedLabel seedControl
      (some (.inl (.inr SourceNormalizationMachineMark.Phase.read)))
      (SourceNormalizationMachineSeed.cfg none none
        (List.replicate v true) [] (List.replicate v false) payload originalN) =
    liftCfg (some (.inr SourceNormalizationMachinePad.Phase.scan)) none
      ![List.replicate v true, [], []]
      (SourceNormalizationMachineMark.cfg (some (.inr .read)) ((none,false),none)
        (List.replicate v false) [] [] [] payload stream originalN) := by
  let S := seedForeign v payload stream originalN
  have hbank : BitMachineStackEmbedding.bank seedStack S
      (SourceNormalizationMachineSeed.cfg none none
        (List.replicate v true) [] (List.replicate v false) payload originalN).stk =
      Function.update S (seedStack 2) (List.replicate v false) := by
    rw [seed_local_final_update, BitMachineStackEmbedding.bank_update]
    exact congrArg (fun T => Function.update T (seedStack 2) (List.replicate v false))
      (BitMachineStackEmbedding.bank_eq_self seedStack S _
        (seed_local_initial v payload stream originalN))
  change (⟨some (.inl (.inr SourceNormalizationMachineMark.Phase.read)),
      seedControl none,
      BitMachineStackEmbedding.bank seedStack S
        (SourceNormalizationMachineSeed.cfg none none
          (List.replicate v true) [] (List.replicate v false) payload originalN).stk⟩ : Config) =
    (⟨some (.inl (.inr SourceNormalizationMachineMark.Phase.read)),
      (((none,false),none),none),
      Sum.elim (SourceNormalizationMachineMark.cfg (some (.inr .read))
        ((none,false),none) (List.replicate v false) [] [] [] payload stream originalN).stk
        ![List.replicate v true, [], []]⟩ : Config)
  apply congrArg (fun T => (⟨some (.inl (.inr SourceNormalizationMachineMark.Phase.read)),
    (((none,false),none),none),T⟩ : Config))
  rw [hbank]
  funext j
  rcases j with j | j
  · rcases j with j | j
    · fin_cases j <;> simp [S, seedForeign, seedStack,
        SourceNormalizationMachineMark.cfg]
    · fin_cases j <;> simp [S, seedForeign, seedStack,
        SourceNormalizationMachineMark.cfg]
  · fin_cases j <;> simp [S, seedForeign, seedStack,
      SourceNormalizationMachineMark.cfg]

/-- Marking uses the physical endpoint-stream consumer, not a host-language
set operation. The bound is per decoded graph, not per source-branch list. -/
theorem mark_stage (bits : List Bool) (indices : List ℕ)
    (hindices : ∀ u ∈ indices, u < bits.length)
    (payload originalN : List Bool) (foreign : Fin 3 → List Bool) :
    ∃ t ≤ 5 * indices.sum + 5 * indices.length + 1,
      run t (liftCfg (some (.inr SourceNormalizationMachinePad.Phase.scan)) none foreign
        (SourceNormalizationMachineMark.cfg (some (.inr .read)) ((none,false),none)
          bits [] [] [] payload
          (SourceNormalizationMachineMark.endpointStream indices) originalN)) =
      liftCfg (some (.inr SourceNormalizationMachinePad.Phase.scan)) none foreign
        (SourceNormalizationMachineMark.cfg none ((none,false),none)
          (SourceNormalizationMachineMark.markIndices bits indices)
          [] [] [] payload [] originalN) := by
  obtain ⟨u, hu, he⟩ := SourceNormalizationMachineMark.mark_stream
    bits indices hindices payload originalN
  obtain ⟨t, ht, hf⟩ := BitMachineSubroutine.lift_outputs
    SourceNormalizationMachineMark.program program
    (some (.inr SourceNormalizationMachinePad.Phase.scan)) mark_program_eq
    none foreign
    (SourceNormalizationMachineMark.cfg (some (.inr .read)) ((none,false),none)
      bits [] [] [] payload
      (SourceNormalizationMachineMark.endpointStream indices) originalN)
    u (by change (SourceNormalizationMachineMark.run u _).l = none
          rw [he]; rfl)
  rw [show ((advance SourceNormalizationMachineMark.program)^[u])
    (SourceNormalizationMachineMark.cfg (some (.inr .read)) ((none,false),none)
      bits [] [] [] payload
      (SourceNormalizationMachineMark.endpointStream indices) originalN) = _ from he] at hf
  exact ⟨t, ht.trans hu, hf⟩

def padForeign (vertices : ℕ) (bits payload originalN : List Bool) : Stack → List Bool :=
  Sum.elim (SourceNormalizationMachineMark.cfg none ((none,false),none)
    bits [] [] [] payload [] originalN).stk
    ![List.replicate vertices true, [], []]

/-- The marker's physical halt state is the padding machine's physical
initial state; the support vector, payload and original `n` occupy the same
stacks in both programs. -/
theorem mark_to_pad (vertices : ℕ) (bits payload originalN : List Bool) :
    liftCfg (some (.inr SourceNormalizationMachinePad.Phase.scan)) none
      ![List.replicate vertices true, [], []]
      (SourceNormalizationMachineMark.cfg none ((none,false),none)
        bits [] [] [] payload [] originalN) =
    BitMachineStackEmbedding.cfg padStack
      (padForeign vertices bits payload originalN)
      padLabel padControl none
      (SourceNormalizationMachinePad.cfg (some .scan) none bits [] payload originalN) := by
  let S := padForeign vertices bits payload originalN
  have hlocal : ∀ k : SourceNormalizationMachinePad.Stack,
      (SourceNormalizationMachinePad.cfg (some .scan) none bits [] payload originalN).stk k =
        S (padStack k) := by
    intro k
    fin_cases k <;> rfl
  have hbank := BitMachineStackEmbedding.bank_eq_self padStack S _ hlocal
  change (⟨some (padLabel .scan), padControl none, S⟩ : Config) =
    (⟨some (padLabel .scan), padControl none,
      BitMachineStackEmbedding.bank padStack S
        (SourceNormalizationMachinePad.cfg (some .scan) none bits [] payload originalN).stk⟩
      : Config)
  exact congrArg (fun T => (⟨some (padLabel .scan), padControl none,T⟩ : Config))
    hbank.symm

/-- The same controller physically appends the two K2 support cells after
marking and leaves original `n` on its stack. -/
theorem pad_stage (bits payload originalN : List Bool)
    (foreign : Stack → List Bool) :
    ∃ t ≤ 2 * bits.length + 4,
      run t (BitMachineStackEmbedding.cfg padStack foreign padLabel padControl none
        (SourceNormalizationMachinePad.cfg (some .scan) none bits [] payload originalN)) =
      BitMachineStackEmbedding.cfg padStack foreign padLabel padControl none
        (SourceNormalizationMachinePad.cfg none none
          (bits ++ [true, true]) [] payload originalN) := by
  have hs := SourceNormalizationMachinePad.append_run bits payload originalN
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs padStack foreign padLabel
    padControl Prod.snd (by intro s; rfl) none
    SourceNormalizationMachinePad.program program pad_program_eq
    (SourceNormalizationMachinePad.cfg (some .scan) none bits [] payload originalN)
    (2 * bits.length + 4)
    (by change (SourceNormalizationMachinePad.run (2 * bits.length + 4)
      (SourceNormalizationMachinePad.cfg (some .scan) none bits [] payload originalN)).l = none
        rw [hs]; rfl)
  rw [show ((advance SourceNormalizationMachinePad.program)^[2 * bits.length + 4])
    (SourceNormalizationMachinePad.cfg (some .scan) none bits [] payload originalN) = _
      from hs] at he
  exact ⟨t, ht, he⟩

/-- On a decoded valid graph, one physical finite-stack run creates exactly
the support vector in inherited vertex order, marks all edge endpoints in
their occurrence order, and appends the two K2 support cells. The original
SAT variable count is a retained stack, not a clock parameter. -/
theorem support_core_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (payload originalN : List Bool) :
    ∃ t ≤ (2 * g.vertices + 2) +
        (5 * (SourceNormalizationNumeric.endpoints g).sum +
          5 * (SourceNormalizationNumeric.endpoints g).length + 1) +
        (2 * g.vertices + 4),
      run t (BitMachineStackEmbedding.cfg seedStack
        (seedForeign g.vertices payload
          (SourceNormalizationMachineMark.endpointStream
            (SourceNormalizationNumeric.endpoints g)) originalN)
        seedLabel seedControl
        (some (.inl (.inr SourceNormalizationMachineMark.Phase.read)))
        (SourceNormalizationMachineSeed.cfg (some .copy) none
          (List.replicate g.vertices true) [] [] payload originalN)) =
      BitMachineStackEmbedding.cfg padStack
        (padForeign g.vertices (SourceNormalizationNumeric.support g) payload originalN)
        padLabel padControl none
        (SourceNormalizationMachinePad.cfg none none
          (SourceNormalizationNumeric.paddedSupport g) [] payload originalN) := by
  let indices := SourceNormalizationNumeric.endpoints g
  let stream := SourceNormalizationMachineMark.endpointStream indices
  let B := SourceNormalizationMachineMark.markIndices
    (List.replicate g.vertices false) indices
  have hindices : ∀ u ∈ indices, u < (List.replicate g.vertices false).length := by
    intro u hu
    simpa using SourceNormalizationNumeric.endpoints_bounded g hg u hu
  obtain ⟨s, hs, hseed⟩ := seed_stage g.vertices payload originalN
    (seedForeign g.vertices payload stream originalN)
  obtain ⟨m, hm, hmark⟩ := mark_stage
    (List.replicate g.vertices false) indices hindices payload originalN
    ![List.replicate g.vertices true, [], []]
  obtain ⟨p, hp, hpad⟩ := pad_stage B payload originalN
    (padForeign g.vertices B payload originalN)
  have hB : B = SourceNormalizationNumeric.support g :=
    SourceNormalizationNumeric.markIndices_false_eq_support g
  have hBlen : B.length = g.vertices := by
    simp [B, SourceNormalizationNumeric.markIndices_length]
  have hfirst : run s
      (BitMachineStackEmbedding.cfg seedStack
        (seedForeign g.vertices payload stream originalN)
        seedLabel seedControl
        (some (.inl (.inr SourceNormalizationMachineMark.Phase.read)))
        (SourceNormalizationMachineSeed.cfg (some .copy) none
          (List.replicate g.vertices true) [] [] payload originalN)) =
      liftCfg (some (.inr SourceNormalizationMachinePad.Phase.scan)) none
        ![List.replicate g.vertices true, [], []]
        (SourceNormalizationMachineMark.cfg (some (.inr .read)) ((none,false),none)
          (List.replicate g.vertices false) [] [] [] payload stream originalN) := by
    exact hseed.trans (seed_to_mark g.vertices payload stream originalN)
  have hsecond : run m
      (liftCfg (some (.inr SourceNormalizationMachinePad.Phase.scan)) none
        ![List.replicate g.vertices true, [], []]
        (SourceNormalizationMachineMark.cfg (some (.inr .read)) ((none,false),none)
          (List.replicate g.vertices false) [] [] [] payload stream originalN)) =
      BitMachineStackEmbedding.cfg padStack
        (padForeign g.vertices B payload originalN)
        padLabel padControl none
        (SourceNormalizationMachinePad.cfg (some .scan) none B [] payload originalN) := by
    exact hmark.trans (mark_to_pad g.vertices B payload originalN)
  refine ⟨s + m + p, ?_, ?_⟩
  · have hm' : m ≤ 5 * (SourceNormalizationNumeric.endpoints g).sum +
        5 * (SourceNormalizationNumeric.endpoints g).length + 1 := by
      simpa only [indices] using hm
    have hp' : p ≤ 2 * g.vertices + 4 := by simpa only [hBlen] using hp
    omega
  have hrun := (run_add ((run_add hfirst m).trans hsecond) p).trans hpad
  simpa only [indices, stream, B, hB, SourceNormalizationNumeric.paddedSupport] using hrun

end EthInapproximability.CurrentPaper.SourceNormalizationMachineCore
