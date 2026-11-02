import CurrentAdditive.V40GraphParameterPrefix
import CurrentAdditive.V39UniformResource

namespace CurrentAdditive.V40GraphConstructorInputBounds
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction V38Schedule
set_option maxHeartbeats 8000000

/-- The original public byte base excludes the unary round count. -/
def base (g : EncodedGraph.Graph) (floor : Nat) := (EncodedGraph.encode g).length+floor+2
theorem base_ge_two (g : EncodedGraph.Graph) (floor : Nat) : 2≤base g floor := by unfold base;omega
theorem input_length (g : EncodedGraph.Graph) (floor K : Nat) :
    (V40GraphConstructorFront.input (EncodedGraph.encode g) floor K).length+1=2*(base g floor+K) := by
  rw[V40GraphParameterPrefix.input_length]
  unfold base
  omega
theorem base_le_input (g : EncodedGraph.Graph) (floor K : Nat) :
    base g floor≤(V40GraphConstructorFront.input (EncodedGraph.encode g) floor K).length+1 := by
  rw[input_length]
  omega

def dyadicBaseCoefficient (p : SourceConstants) := 8*p.degree+6

theorem generated_base_ge_two (p : SourceConstants) (floor n m : Nat)
    (hn : 0<n) (hlow : n≤2*m) (hdegree : 2*m≤p.degree*n) :
    2≤generatedN (publicLogFrom p floor n m hn hlow hdegree) := by
  have h := V40ActualPreparedSearch.selected_ge_two p floor n m hn hlow hdegree
  have hp := Nat.pow_le_pow_right (show 0<(2:Nat) by decide) h
  change 2≤2^(publicLogFrom p floor n m hn hlow hdegree)
  norm_num at hp
  omega

/-- The actual explicit graph bytes and the retained original floor are
polynomial in the selected dyadic N. No sparse-input promise is used. -/
theorem base_le_dyadic (p : SourceConstants) (g : EncodedGraph.Graph) (hg : g.Valid)
    (floor : Nat) (hn : 0<g.vertices) (hlow : g.vertices≤2*g.edges.length)
    (hdegree : 2*g.edges.length≤p.degree*g.vertices) :
    let N := generatedN (publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree)
    base g floor≤dyadicBaseCoefficient p*N^2 := by
  let N := generatedN (publicLogFrom p floor g.vertices g.edges.length hn hlow hdegree)
  have hN : 2≤N := generated_base_ge_two p floor g.vertices g.edges.length hn hlow hdegree
  have hs := publicLogFrom_size p floor g.vertices g.edges.length hn hlow hdegree
  have hfloor : floor≤N := (le_max_left _ _).trans hs
  have hnN : g.vertices≤N := (le_max_right _ _).trans hs
  have hmN : g.edges.length≤p.degree*N := by
    have hmul := Nat.mul_le_mul_left p.degree hnN
    omega
  have hterm : g.edges.length*(4*g.vertices+4)≤(p.degree*N)*(8*N) :=
    Nat.mul_le_mul hmN (by omega)
  have hgbytes := EncodedGraph.encode_length_upper g hg
  have hNpow : N≤N^2 := by nlinarith
  have hOne : 1≤N^2 := by nlinarith
  change (EncodedGraph.encode g).length+floor+2≤(8*p.degree+6)*N^2
  nlinarith

/-- Conversion of the complete paid clock preserves its amplification A;
only the leading fixed exponent grows, and it is explicitly at least1040. -/
theorem dyadic_clock_bound (B N time c C A K : Nat) (hN : 2≤N)
    (hB : B≤c*N^2) (ht : time≤B^(C*A^K)) :
    time≤N^(((c+2)*C+1040)*A^K) := by
  have hc : c≤N^c := (V39UniformResource.self_le_two_pow c).trans (Nat.pow_le_pow_left hN c)
  have hbase : B≤N^(c+2) := hB.trans (by
    calc
      c*N^2≤N^c*N^2 := Nat.mul_le_mul_right _ hc
      _ = _ := by rw[←pow_add])
  calc
    time≤B^(C*A^K) := ht
    _ ≤ (N^(c+2))^(C*A^K) := Nat.pow_le_pow_left hbase _
    _ = N^(((c+2)*C)*A^K) := by rw[←pow_mul];congr 1;ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by omega))

#print axioms base_le_dyadic
#print axioms dyadic_clock_bound
end CurrentAdditive.V40GraphConstructorInputBounds
