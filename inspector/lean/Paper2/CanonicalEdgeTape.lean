import Paper2.UnaryFieldListParser
import EthInapproximability.CurrentPaper.EncodedGraph

/-! A literal public graph tape: endpoint fields in indexed-edge-occurrence
order, false endpoint then true endpoint. Parsing is a fixed TM2 run on all
2m fields, not a graph-function lookup hidden in machine control. -/

namespace Paper2.CanonicalEdgeTape

open Paper2.RecursiveLabelCodecScratch
open Paper2.UnaryFieldListParserScratch
open EthInapproximability.CurrentPaper

def endpointField {n m : Nat} (edge : Fin m → Bool → Fin n)
    (t : Fin (2 * m)) : Fin n :=
  edge ⟨t.val / 2, by omega⟩ (t.val % 2 = 1)

def fields {n m : Nat} (edge : Fin m → Bool → Fin n) : List (Fin n) :=
  List.ofFn (endpointField edge)

def word {n m : Nat} (edge : Fin m → Bool → Fin n) : List Bool :=
  tokens (fields edge)

theorem fields_length {n m : Nat} (edge : Fin m → Bool → Fin n) :
    (fields edge).length = 2 * m := by simp [fields]

theorem endpoint_even {n m : Nat} (edge : Fin m → Bool → Fin n)
    (e : Fin m) :
    endpointField edge ⟨2 * e.val, by omega⟩ = edge e false := by
  simp [endpointField]

theorem endpoint_odd {n m : Nat} (edge : Fin m → Bool → Fin n)
    (e : Fin m) :
    endpointField edge ⟨2 * e.val + 1, by omega⟩ = edge e true := by
  have hdiv : (2 * e.val + 1) / 2 = e.val := by omega
  have hmod : (2 * e.val + 1) % 2 = 1 := by omega
  simp [endpointField, hdiv, hmod]

theorem physical_full_parse {n m : Nat} (edge : Fin m → Bool → Fin n) :
    run (fuel n (2 * m) (word edge))
      (initial n (2 * m) (word edge)) =
    cfg none none [] (List.replicate n true) [] []
      (tokens (fields edge).reverse) [true] := by
  simpa only [word, fields_length, List.append_nil] using
    (run_valid_fuel (fields edge) [])

theorem clock_eq {n m : Nat} (edge : Fin m → Bool → Fin n) :
    fuel n (2 * m) (word edge) =
      3 * ((word edge).length + n + 2 * m) + 2 := rfl

/-- Adapt the public ordered-edge occurrence, preserving its Boolean endpoint
orientation. This is only a mathematical identity until a charged converter
from public binary fields to the internal unary tape is built. -/
def graphEdge (g : EncodedGraph.Graph) (hg : g.Valid) :
    Fin g.edges.length → Bool → Fin g.vertices :=
  fun e b => EncodedGraph.endpoints g hg e (if b then 1 else 0)

theorem graphEdge_false (g : EncodedGraph.Graph) (hg : g.Valid)
    (e : Fin g.edges.length) :
    (graphEdge g hg e false).val = (g.edges.get e).1 := by
  simp [graphEdge]

theorem graphEdge_true (g : EncodedGraph.Graph) (hg : g.Valid)
    (e : Fin g.edges.length) :
    (graphEdge g hg e true).val = (g.edges.get e).2 := by
  simp [graphEdge]

private theorem tokens_length_le {n : Nat} (xs : List (Fin n)) :
    (tokens xs).length ≤ n * xs.length := by
  induction xs with
  | nil => simp [tokens]
  | cons x xs ih =>
      simp only [tokens, List.flatMap_cons, List.length_append, List.length_cons]
      have hx : ((finCodec n).encode x).length ≤ n := (finCodec n).length_le x
      have hxs : (List.flatMap (finCodec n).encode xs).length ≤ n * xs.length := by
        simpa only [tokens] using ih
      simp only [Nat.mul_add, mul_one]
      omega

theorem word_length_le {n m : Nat} (edge : Fin m → Bool → Fin n) :
    (word edge).length ≤ 2 * m * n := by
  have h := tokens_length_le (fields edge)
  simpa only [word, fields_length, Nat.mul_comm] using h

theorem decoded_word_length_le_square {input : List Bool}
    {g : EncodedGraph.Graph} (h : EncodedGraph.decode input = some g) :
    (word (graphEdge g (EncodedGraph.decode_valid h))).length ≤
      input.length ^ 2 := by
  have hsize := EncodedGraph.decoded_size_bound h
  have hword := word_length_le (graphEdge g (EncodedGraph.decode_valid h))
  nlinarith

end Paper2.CanonicalEdgeTape
