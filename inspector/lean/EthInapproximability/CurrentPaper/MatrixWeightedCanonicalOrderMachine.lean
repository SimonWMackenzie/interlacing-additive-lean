import EthInapproximability.CurrentPaper.MatrixWeightedRowOrderMachineRun
import EthInapproximability.CurrentPaper.GraphVectors

/-!
# Physical canonical graph-item order table

Frozen v8 anchors: `A-stage4-details.tex`, `eq:paper-guarded-carriers`
and `eq:paper-guarded-edge-evaluator`; `B-effectivity-details.tex`,
`thm:paper-materialization` and its lexicographic/type-first order convention.

The three input words are unary `v`, `a=s-3`, and `K=4s`. The fixed program
enumerates vertex-group labels first and auxiliary-group labels second. It
copies each current copy-major rank into a reversed accumulator, adding a
false delimiter, then reverses that accumulator into the literal table.
There is no abstract `ItemOrder` query in the program. Empty groups do not
invoke division or require a positive divisor.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedCanonicalOrderMachine

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := Fin 9

def groupSource (aux : Bool) : Stack := if aux then 1 else 0
def skipSource (aux : Bool) : Stack := if aux then 0 else 1

def outerCopySlots : Fin 3 ↪ Stack where
  toFun := ![2,3,6]
  inj' := by decide

def innerCopySlots (aux : Bool) : Fin 3 ↪ Stack where
  toFun := ![groupSource aux,4,6]
  inj' := by cases aux <;> decide

def rankCopySlots : Fin 3 ↪ Stack where
  toFun := ![5,7,6]
  inj' := by decide

def skipCopySlots (aux : Bool) : Fin 3 ↪ Stack where
  toFun := ![skipSource aux,5,6]
  inj' := by cases aux <;> decide

def resetCopySlots : Fin 3 ↪ Stack where
  toFun := ![0,5,6]
  inj' := by decide

inductive Label where
  | outerCopy (aux : Bool) (l : BitMachineCopy.Label)
  | outer (aux : Bool)
  | innerCopy (aux : Bool) (l : BitMachineCopy.Label)
  | inner (aux : Bool)
  | rankCopy (aux : Bool) (l : BitMachineCopy.Label)
  | afterRank (aux : Bool)
  | skipCopy (aux : Bool) (l : BitMachineCopy.Label)
  | afterSkip (aux : Bool)
  | resetRank
  | resetCopy (l : BitMachineCopy.Label)
  | reverse
  deriving DecidableEq, Fintype

abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def start : Label := .outerCopy false .scan

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .outerCopy aux l => stmt outerCopySlots (Label.outerCopy aux)
      id id (some (.outer aux)) (BitMachineCopy.program l)
  | .outer aux => pop 3 (fun _ b => b)
      (branch Option.isSome
        (goto (fun _ => .innerCopy aux .scan))
        (goto (fun _ => if aux then .reverse else .resetRank)))
  | .innerCopy aux l => stmt (innerCopySlots aux) (Label.innerCopy aux)
      id id (some (.inner aux)) (BitMachineCopy.program l)
  | .inner aux => pop 4 (fun _ b => b)
      (branch Option.isSome
        (goto (fun _ => .rankCopy aux .scan))
        (goto (fun _ => .skipCopy aux .scan)))
  | .rankCopy aux l => stmt rankCopySlots (Label.rankCopy aux)
      id id (some (.afterRank aux)) (BitMachineCopy.program l)
  | .afterRank aux => push 7 (fun _ => false)
      (push 5 (fun _ => true) (goto (fun _ => .inner aux)))
  | .skipCopy aux l => stmt (skipCopySlots aux) (Label.skipCopy aux)
      id id (some (.afterSkip aux)) (BitMachineCopy.program l)
  | .afterSkip aux => goto (fun _ => .outer aux)
  | .resetRank => pop 5 (fun _ b => b)
      (branch Option.isSome
        (goto (fun _ => .resetRank))
        (goto (fun _ => .resetCopy .scan)))
  | .resetCopy l => stmt resetCopySlots Label.resetCopy
      id id (some (.outerCopy true .scan)) (BitMachineCopy.program l)
  | .reverse => pop 7 (fun _ b => b)
      (branch Option.isSome
        (push 8 (fun b => b.getD false) (goto (fun _ => .reverse)))
        halt)

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def initialBank (v a K : ℕ) : Stack → List Bool :=
  ![List.replicate v true, List.replicate a true,
    List.replicate K true, [], [], [], [], [], []]

def vertexRanks (v a K : ℕ) : List ℕ :=
  (List.range K).flatMap fun copy =>
    (List.range v).map fun i => copy * (v + a) + i

def auxiliaryRanks (v a K : ℕ) : List ℕ :=
  (List.range K).flatMap fun copy =>
    (List.range a).map fun i => copy * (v + a) + v + i

def canonicalWord (v a K : ℕ) : List Bool :=
  MatrixWeightedRowOrderLookup.fields
    (vertexRanks v a K ++ auxiliaryRanks v a K)

universe u w

variable {V : Type u} {E : Type w}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem vertex_rank (G :
    EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (s : ℕ) (i : Fin (GraphVectors.vertexCount V s)) :
    ((GraphVectors.itemOrder G s)
      (Fin.castAdd (GraphVectors.auxiliaryCount s) i)).val =
    i.val / Fintype.card V * (Fintype.card V + (s - 3)) +
      i.val % Fintype.card V := by
  rw [← Construction.vertexIndex, GraphVectors.itemOrder_vertex,
    GraphVectors.itemIndex_vertex_val]
  have hcopy : (GraphVectors.vertexLabels G s i).1.val =
      i.val / Fintype.card V := by rfl
  have hvertex : ((GraphVectors.vertexEnum G).symm
      (GraphVectors.vertexLabels G s i).2).val =
      i.val % Fintype.card V := by
    change ((GraphVectors.vertexEnum G).symm
      ((GraphVectors.vertexEnum G) i.modNat)).val = _
    simp
  rw [hcopy, hvertex]

theorem auxiliary_rank (G :
    EthInapproximability.ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (s : ℕ) (i : Fin (GraphVectors.auxiliaryCount s)) :
    ((GraphVectors.itemOrder G s)
      (Fin.natAdd (GraphVectors.vertexCount V s) i)).val =
    i.val / (s - 3) * (Fintype.card V + (s - 3)) +
      Fintype.card V + i.val % (s - 3) := by
  rw [← Construction.auxiliaryIndex, GraphVectors.itemOrder_auxiliary,
    GraphVectors.itemIndex_auxiliary_val]
  have hcopy : (GraphVectors.auxiliaryLabels s i).1.val =
      i.val / (s - 3) := by rfl
  have haux : (GraphVectors.auxiliaryLabels s i).2.val =
      i.val % (s - 3) := by rfl
  rw [hcopy, haux]

end EthInapproximability.CurrentPaper.MatrixWeightedCanonicalOrderMachine
