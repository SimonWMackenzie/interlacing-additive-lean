import EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeCore
import EthInapproximability.CurrentPaper.SourceNormalizationMachineCounts

/-!
# Original-n repetition count after physical graph support normalization

The counter reuses the retained unary original SAT variable count and unary
original edge count. Its scratch stacks are cleared decoder work stacks;
the K2-padded support and endpoint stream remain foreign stacks.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeCount

open Turing BitMachineEncoding

abbrev Stack := SourceNormalizationMachineDecodeCore.Stack
abbrev Label := SourceNormalizationMachineDecodeCore.Label ⊕
  SourceNormalizationMachineCounts.Label
abbrev Control := SourceNormalizationMachineDecodeCore.Control ×
  SourceNormalizationMachineCounts.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def countStack : SourceNormalizationMachineCounts.Stack ↪ Stack where
  toFun
    | .inl k => .inl (.inl ⟨k.val, by omega⟩)
    | .inr k => match k.val with
      | 0 => .inr 2
      | 1 => .inl (.inr 1)
      | _ => .inl (.inl 6)
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def initialCount : SourceNormalizationMachineCounts.Control := (false,())
def afterCoreControl : SourceNormalizationMachineDecodeCore.Control :=
  SourceNormalizationMachineDecodeCore.coreControl
    (SourceNormalizationMachineCore.padControl none)
def decodeControl (v : SourceNormalizationMachineDecodeCore.Control) : Control :=
  (v,initialCount)
def countControl (v : SourceNormalizationMachineCounts.Control) : Control :=
  (afterCoreControl,v)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt
      (Function.Embedding.refl Stack) Sum.inl decodeControl Prod.fst
      (some (.inr (.inr SourceNormalizationMachineCounts.Phase.copyN)))
      (SourceNormalizationMachineDecodeCore.program l)
  | .inr l => BitMachineStackEmbedding.stmt countStack Sum.inr
      countControl Prod.snd none (SourceNormalizationMachineCounts.program l)

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def start (graphBits : List Bool) (originalN : ℕ) : Config :=
  ⟨(SourceNormalizationMachineDecodeCore.start graphBits originalN).l.map Sum.inl,
    decodeControl (SourceNormalizationMachineDecodeCore.start graphBits originalN).var,
    (SourceNormalizationMachineDecodeCore.start graphBits originalN).stk⟩

private theorem decode_program_eq (l : SourceNormalizationMachineDecodeCore.Label) :
    program (.inl l) = BitMachineStackEmbedding.stmt
      (Function.Embedding.refl Stack) Sum.inl decodeControl Prod.fst
      (some (.inr (.inr SourceNormalizationMachineCounts.Phase.copyN)))
      (SourceNormalizationMachineDecodeCore.program l) := rfl

private theorem count_program_eq (l : SourceNormalizationMachineCounts.Label) :
    program (.inr l) = BitMachineStackEmbedding.stmt countStack Sum.inr
      countControl Prod.snd none (SourceNormalizationMachineCounts.program l) := rfl

noncomputable def afterCore (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineDecodeCore.Config :=
  BitMachineStackEmbedding.cfg SourceNormalizationMachineDecodeCore.coreStack
    (SourceNormalizationMachineDecodeCore.decodedPadded g originalN).stk
    Sum.inr SourceNormalizationMachineDecodeCore.coreControl none
    (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN)

private theorem decode_initial (graphBits : List Bool) (originalN : ℕ) :
    BitMachineStackEmbedding.cfg (Function.Embedding.refl Stack)
      (SourceNormalizationMachineDecodeCore.start graphBits originalN).stk
      Sum.inl decodeControl
      (some (.inr (.inr SourceNormalizationMachineCounts.Phase.copyN)))
      (SourceNormalizationMachineDecodeCore.start graphBits originalN) =
        start graphBits originalN := by
  have hb := BitMachineStackEmbedding.bank_eq_self
    (Function.Embedding.refl Stack)
    (SourceNormalizationMachineDecodeCore.start graphBits originalN).stk
    (SourceNormalizationMachineDecodeCore.start graphBits originalN).stk (by
      intro k
      rfl)
  change (⟨_,_, BitMachineStackEmbedding.bank (Function.Embedding.refl Stack)
    (SourceNormalizationMachineDecodeCore.start graphBits originalN).stk
    (SourceNormalizationMachineDecodeCore.start graphBits originalN).stk⟩ : Config) = _
  rw [hb]
  rfl

private theorem decode_core_stage (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ SourceNormalizationMachineDecode.graphCost g +
      SourceNormalizationMachineDecodePad.padCost g +
      SourceNormalizationMachineDecodeCore.coreCost g,
      run t (start (EncodedGraph.encode g) originalN) =
        BitMachineStackEmbedding.cfg (Function.Embedding.refl Stack)
          (SourceNormalizationMachineDecodeCore.start
            (EncodedGraph.encode g) originalN).stk
          Sum.inl decodeControl
          (some (.inr (.inr SourceNormalizationMachineCounts.Phase.copyN)))
          (afterCore g originalN) := by
  obtain ⟨t,ht,he⟩ := SourceNormalizationMachineDecodeCore.decode_core_run
    g hg originalN
  obtain ⟨s,hs,hr⟩ := BitMachineStackEmbedding.outputs
    (Function.Embedding.refl Stack)
    (SourceNormalizationMachineDecodeCore.start
      (EncodedGraph.encode g) originalN).stk
    Sum.inl decodeControl Prod.fst (by intro v; rfl)
    (some (.inr (.inr SourceNormalizationMachineCounts.Phase.copyN)))
    SourceNormalizationMachineDecodeCore.program program decode_program_eq
    (SourceNormalizationMachineDecodeCore.start (EncodedGraph.encode g) originalN)
    t (by
      change (SourceNormalizationMachineDecodeCore.run t
        (SourceNormalizationMachineDecodeCore.start
          (EncodedGraph.encode g) originalN)).l = none
      rw [he]
      rfl)
  change ((advance SourceNormalizationMachineDecodeCore.program)^[t]) _ = _ at he
  rw [he] at hr
  refine ⟨s, hs.trans ht, ?_⟩
  exact (congrArg (run s) (decode_initial (EncodedGraph.encode g) originalN).symm).trans
    (by simpa only [run, afterCore] using hr)

private theorem afterCore_at (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : SourceNormalizationMachineCore.Stack) :
    (afterCore g originalN).stk
      (SourceNormalizationMachineDecodeCore.coreStack k) =
    (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN).stk k := by
  exact BitMachineStackEmbedding.bank_at
    SourceNormalizationMachineDecodeCore.coreStack
    (SourceNormalizationMachineDecodeCore.decodedPadded g originalN).stk
    (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN).stk k

private theorem afterCore_outside (g : EncodedGraph.Graph) (originalN : ℕ)
    (j : Stack)
    (hj : ¬ ∃ k : SourceNormalizationMachineCore.Stack,
      SourceNormalizationMachineDecodeCore.coreStack k = j) :
    (afterCore g originalN).stk j =
      (SourceNormalizationMachineDecodeCore.decodedPadded g originalN).stk j := by
  exact BitMachineStackEmbedding.bank_outside
    SourceNormalizationMachineDecodeCore.coreStack
    (SourceNormalizationMachineDecodeCore.decodedPadded g originalN).stk
    (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN).stk j hj

private theorem coreFinal_at (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : SourceNormalizationMachinePad.Stack) :
    (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN).stk
      (SourceNormalizationMachineCore.padStack k) =
    (SourceNormalizationMachinePad.cfg none none
      (SourceNormalizationNumeric.paddedSupport g) [] []
      (List.replicate originalN true)).stk k := by
  exact BitMachineStackEmbedding.bank_at
    SourceNormalizationMachineCore.padStack
    (SourceNormalizationMachineCore.padForeign g.vertices
      (SourceNormalizationNumeric.support g) []
      (List.replicate originalN true))
    (SourceNormalizationMachinePad.cfg none none
      (SourceNormalizationNumeric.paddedSupport g) [] []
      (List.replicate originalN true)).stk k

private theorem coreFinal_outside (g : EncodedGraph.Graph) (originalN : ℕ)
    (j : SourceNormalizationMachineCore.Stack)
    (hj : ¬ ∃ k : SourceNormalizationMachinePad.Stack,
      SourceNormalizationMachineCore.padStack k = j) :
    (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN).stk j =
      SourceNormalizationMachineCore.padForeign g.vertices
        (SourceNormalizationNumeric.support g) []
        (List.replicate originalN true) j := by
  exact BitMachineStackEmbedding.bank_outside
    SourceNormalizationMachineCore.padStack
    (SourceNormalizationMachineCore.padForeign g.vertices
      (SourceNormalizationNumeric.support g) []
      (List.replicate originalN true))
    (SourceNormalizationMachinePad.cfg none none
      (SourceNormalizationNumeric.paddedSupport g) [] []
      (List.replicate originalN true)).stk j hj

private theorem padded_outside (g : EncodedGraph.Graph) (originalN : ℕ)
    (j : Stack)
    (hj : ¬ ∃ k : SourceNormalizationMachineEndpointPad.Stack,
      SourceNormalizationMachineDecodePad.padStack k = j) :
    (SourceNormalizationMachineDecodeCore.decodedPadded g originalN).stk j =
      SourceNormalizationMachineDecodePad.afterDecodeBank g originalN j := by
  exact BitMachineStackEmbedding.bank_outside
    SourceNormalizationMachineDecodePad.padStack
    (SourceNormalizationMachineDecodePad.afterDecodeBank g originalN)
    (SourceNormalizationMachineDecodePad.padded g originalN).stk j hj

private theorem decoded_at (g : EncodedGraph.Graph) (originalN : ℕ)
    (k : SourceNormalizationMachineDecode.Stack) :
    SourceNormalizationMachineDecodePad.afterDecodeBank g originalN (.inl k) =
      (SourceNormalizationMachineDecodePad.decoded g).stk k := by
  exact BitMachineStackEmbedding.bank_at
    SourceNormalizationMachineDecodePad.decodeStack
    (SourceNormalizationMachineDecodePad.foreign (EncodedGraph.encode g) originalN)
    (SourceNormalizationMachineDecodePad.decoded g).stk k

private theorem count_initial_stacks (g : EncodedGraph.Graph) (originalN : ℕ) :
    ∀ k : SourceNormalizationMachineCounts.Stack,
      (SourceNormalizationMachineCounts.cfg
        (some (.inr SourceNormalizationMachineCounts.Phase.copyN)) false
        [] [] [] [] [] []
        (List.replicate originalN true)
        (List.replicate g.edges.length true) []).stk k =
      (afterCore g originalN).stk (countStack k) := by
  intro k
  fin_cases k <;>
    simp [countStack, SourceNormalizationMachineCounts.cfg]
  case «0» =>
    have hc : ¬ ∃ j : SourceNormalizationMachineCore.Stack,
        SourceNormalizationMachineDecodeCore.coreStack j =
          (.inl (.inl 0) : Stack) := by
      rintro ⟨j,hj⟩
      fin_cases j <;> simp [SourceNormalizationMachineDecodeCore.coreStack] at hj
    rw [afterCore_outside g originalN _ hc]
    have hp : ¬ ∃ j : SourceNormalizationMachineEndpointPad.Stack,
        SourceNormalizationMachineDecodePad.padStack j =
          (.inl (.inl 0) : Stack) := by
      rintro ⟨j,hj⟩
      fin_cases j <;> simp [SourceNormalizationMachineDecodePad.padStack] at hj
    rw [padded_outside g originalN _ hp,
      decoded_at g originalN (.inl 0)]
    rfl
  case «1» =>
    have h := afterCore_at g originalN
      (.inl (.inl (1 : Fin 5)))
    have h' : (afterCore g originalN).stk (.inl (.inl 1)) =
        (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN).stk
          (.inl (.inl (1 : Fin 5))) := by
      simpa [SourceNormalizationMachineDecodeCore.coreStack] using h
    rw [h']
    have hout : ¬ ∃ j : SourceNormalizationMachinePad.Stack,
        SourceNormalizationMachineCore.padStack j =
          (.inl (.inl (1 : Fin 5)) : SourceNormalizationMachineCore.Stack) := by
      rintro ⟨j,hj⟩
      fin_cases j <;> simp [SourceNormalizationMachineCore.padStack] at hj
    rw [coreFinal_outside g originalN _ hout]
    rfl
  case «2» =>
    have h := afterCore_at g originalN
      (.inl (.inl (2 : Fin 5)))
    have h' : (afterCore g originalN).stk (.inl (.inl 2)) =
        (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN).stk
          (.inl (.inl (2 : Fin 5))) := by
      simpa [SourceNormalizationMachineDecodeCore.coreStack] using h
    rw [h']
    have hout : ¬ ∃ j : SourceNormalizationMachinePad.Stack,
        SourceNormalizationMachineCore.padStack j =
          (.inl (.inl (2 : Fin 5)) : SourceNormalizationMachineCore.Stack) := by
      rintro ⟨j,hj⟩
      fin_cases j <;> simp [SourceNormalizationMachineCore.padStack] at hj
    rw [coreFinal_outside g originalN _ hout]
    rfl
  case «3» =>
    have h := afterCore_at g originalN
      (.inl (.inl (3 : Fin 5)))
    have h' : (afterCore g originalN).stk (.inl (.inl 3)) =
        (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN).stk
          (.inl (.inl (3 : Fin 5))) := by
      simpa [SourceNormalizationMachineDecodeCore.coreStack] using h
    rw [h']
    have hout : ¬ ∃ j : SourceNormalizationMachinePad.Stack,
        SourceNormalizationMachineCore.padStack j =
          (.inl (.inl (3 : Fin 5)) : SourceNormalizationMachineCore.Stack) := by
      rintro ⟨j,hj⟩
      fin_cases j <;> simp [SourceNormalizationMachineCore.padStack] at hj
    rw [coreFinal_outside g originalN _ hout]
    rfl
  case «4» =>
    have h := afterCore_at g originalN (.inr (1 : Fin 3))
    have h' : (afterCore g originalN).stk (.inl (.inl 4)) =
        (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN).stk
          (.inr (1 : Fin 3)) := by
      simpa [SourceNormalizationMachineDecodeCore.coreStack] using h
    rw [h']
    have hout : ¬ ∃ j : SourceNormalizationMachinePad.Stack,
        SourceNormalizationMachineCore.padStack j =
          (.inr (1 : Fin 3) : SourceNormalizationMachineCore.Stack) := by
      rintro ⟨j,hj⟩
      fin_cases j <;> simp [SourceNormalizationMachineCore.padStack] at hj
    rw [coreFinal_outside g originalN _ hout]
    rfl
  case «5» =>
    have h := afterCore_at g originalN (.inr (2 : Fin 3))
    have h' : (afterCore g originalN).stk (.inl (.inl 5)) =
        (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN).stk
          (.inr (2 : Fin 3)) := by
      simpa [SourceNormalizationMachineDecodeCore.coreStack] using h
    rw [h']
    have hp := coreFinal_at g originalN (1 : SourceNormalizationMachinePad.Stack)
    have hp' : (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN).stk
        (.inr (2 : Fin 3)) = [] := by
      simpa [SourceNormalizationMachineCore.padStack,
        SourceNormalizationMachinePad.cfg] using hp
    exact hp'
  case «6» =>
    have h := afterCore_at g originalN
      (.inl (.inr (1 : Fin 2)))
    have h' : (afterCore g originalN).stk (.inr 2) =
        (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN).stk
          (.inl (.inr (1 : Fin 2))) := by
      simpa [SourceNormalizationMachineDecodeCore.coreStack] using h
    rw [h']
    have hp := coreFinal_at g originalN (3 : SourceNormalizationMachinePad.Stack)
    have hp' : (SourceNormalizationMachineDecodeCore.coreFinalCfg g originalN).stk
        (.inl (.inr (1 : Fin 2))) = List.replicate originalN true := by
      simpa [SourceNormalizationMachineCore.padStack,
        SourceNormalizationMachinePad.cfg] using hp
    exact hp'.symm
  case «7» =>
    have hc : ¬ ∃ j : SourceNormalizationMachineCore.Stack,
        SourceNormalizationMachineDecodeCore.coreStack j =
          (.inl (.inr 1) : Stack) := by
      rintro ⟨j,hj⟩
      fin_cases j <;> simp [SourceNormalizationMachineDecodeCore.coreStack] at hj
    rw [afterCore_outside g originalN _ hc]
    have hp : ¬ ∃ j : SourceNormalizationMachineEndpointPad.Stack,
        SourceNormalizationMachineDecodePad.padStack j =
          (.inl (.inr 1) : Stack) := by
      rintro ⟨j,hj⟩
      fin_cases j <;> simp [SourceNormalizationMachineDecodePad.padStack] at hj
    rw [padded_outside g originalN _ hp,
      decoded_at g originalN (.inr 1)]
    rfl
  case «8» =>
    have hc : ¬ ∃ j : SourceNormalizationMachineCore.Stack,
        SourceNormalizationMachineDecodeCore.coreStack j =
          (.inl (.inl 6) : Stack) := by
      rintro ⟨j,hj⟩
      fin_cases j <;> simp [SourceNormalizationMachineDecodeCore.coreStack] at hj
    rw [afterCore_outside g originalN _ hc]
    have hp : ¬ ∃ j : SourceNormalizationMachineEndpointPad.Stack,
        SourceNormalizationMachineDecodePad.padStack j =
          (.inl (.inl 6) : Stack) := by
      rintro ⟨j,hj⟩
      fin_cases j <;> simp [SourceNormalizationMachineDecodePad.padStack] at hj
    rw [padded_outside g originalN _ hp,
      decoded_at g originalN (.inl 6)]
    rfl

def countInitialCfg (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineCounts.Config :=
  SourceNormalizationMachineCounts.cfg
    (some (.inr SourceNormalizationMachineCounts.Phase.copyN)) false
    [] [] [] [] [] []
    (List.replicate originalN true)
    (List.replicate g.edges.length true) []

def countFinalCfg (g : EncodedGraph.Graph) (originalN : ℕ) :
    SourceNormalizationMachineCounts.Config :=
  SourceNormalizationMachineCounts.cfg none false []
    (List.replicate (g.edges.length + 1) true) []
    (List.replicate ((originalN + g.edges.length) % (g.edges.length + 1)) true)
    (List.replicate (ParameterizedNP.GuardedSourceGraph.copyCount
      originalN g.edges.length) true) []
    (List.replicate originalN true)
    (List.replicate g.edges.length true) []

private theorem count_initial (g : EncodedGraph.Graph) (originalN : ℕ) :
    BitMachineStackEmbedding.cfg (Function.Embedding.refl Stack)
      (SourceNormalizationMachineDecodeCore.start
        (EncodedGraph.encode g) originalN).stk
      Sum.inl decodeControl
      (some (.inr (.inr SourceNormalizationMachineCounts.Phase.copyN)))
      (afterCore g originalN) =
    BitMachineStackEmbedding.cfg countStack (afterCore g originalN).stk
      Sum.inr countControl none (countInitialCfg g originalN) := by
  have hleft : BitMachineStackEmbedding.bank (Function.Embedding.refl Stack)
      (SourceNormalizationMachineDecodeCore.start
        (EncodedGraph.encode g) originalN).stk
      (afterCore g originalN).stk = (afterCore g originalN).stk := by
    funext k
    exact BitMachineStackEmbedding.bank_at (Function.Embedding.refl Stack)
      (SourceNormalizationMachineDecodeCore.start
        (EncodedGraph.encode g) originalN).stk
      (afterCore g originalN).stk k
  have hright := BitMachineStackEmbedding.bank_eq_self countStack
    (afterCore g originalN).stk (countInitialCfg g originalN).stk
    (count_initial_stacks g originalN)
  change (⟨some (.inr (.inr SourceNormalizationMachineCounts.Phase.copyN)),
    decodeControl (afterCore g originalN).var,
    BitMachineStackEmbedding.bank (Function.Embedding.refl Stack)
      (SourceNormalizationMachineDecodeCore.start
        (EncodedGraph.encode g) originalN).stk
      (afterCore g originalN).stk⟩ : Config) =
    (⟨some (.inr (.inr SourceNormalizationMachineCounts.Phase.copyN)),
      countControl (countInitialCfg g originalN).var,
      BitMachineStackEmbedding.bank countStack
        (afterCore g originalN).stk (countInitialCfg g originalN).stk⟩ : Config)
  rw [hleft, hright]
  rfl

theorem decode_count_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (originalN : ℕ) :
    ∃ t ≤ SourceNormalizationMachineDecode.graphCost g +
      SourceNormalizationMachineDecodePad.padCost g +
      SourceNormalizationMachineDecodeCore.coreCost g +
      (10 * originalN + 13 * g.edges.length + 13),
      run t (start (EncodedGraph.encode g) originalN) =
      BitMachineStackEmbedding.cfg countStack (afterCore g originalN).stk
        Sum.inr countControl none (countFinalCfg g originalN) := by
  obtain ⟨a,ha,hcore⟩ := decode_core_stage g hg originalN
  obtain ⟨b,hb,hcount⟩ := SourceNormalizationMachineCounts.count_run
    originalN g.edges.length []
  have hcount' : SourceNormalizationMachineCounts.run b
      (countInitialCfg g originalN) = countFinalCfg g originalN := by
    simpa only [countInitialCfg, countFinalCfg] using hcount
  obtain ⟨s,hs,hr⟩ := BitMachineStackEmbedding.outputs countStack
    (afterCore g originalN).stk Sum.inr countControl Prod.snd
    (by intro v; rfl) none
    SourceNormalizationMachineCounts.program program count_program_eq
    (countInitialCfg g originalN) b (by
      change (SourceNormalizationMachineCounts.run b
        (countInitialCfg g originalN)).l = none
      rw [hcount']
      rfl)
  change ((advance SourceNormalizationMachineCounts.program)^[b]) _ = _ at hcount'
  rw [show ((advance SourceNormalizationMachineCounts.program)^[b])
    (countInitialCfg g originalN) = countFinalCfg g originalN from hcount'] at hr
  refine ⟨a + s, by omega, ?_⟩
  exact (run_add hcore s).trans
    ((congrArg (run s) (count_initial g originalN)).trans
      (by simpa only [run] using hr))

end EthInapproximability.CurrentPaper.SourceNormalizationMachineDecodeCount
