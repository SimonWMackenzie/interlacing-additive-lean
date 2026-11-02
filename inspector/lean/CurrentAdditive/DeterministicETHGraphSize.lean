import CurrentAdditive.DeterministicETHSourceBridge

/-! A fixed natural-number polynomial bound for the exact inherited T10
graph on sparse encoded CNFs. This supplies the graph exponent consumed by
the deterministic ETH dyadic schedule. -/

namespace CurrentAdditive.DeterministicETHSourceBridge

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite
open Paper2.Unit4Shell.T10Size

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- All constants depend only on the source records and the fixed sparse
clause density. -/
def graphPolynomialCutoff (cs : ℕ) : ℕ :=
  max 2 (t45C D B cs * 2^(D.sizeExponent+1))

/-- An integer polynomial source-graph size bound on every sufficiently
large sparse canonical formula. The graph is exactly `t10Graph D B Φ`. -/
theorem sparse_graph_vertices_polynomial (cs : ℕ) (Φ : ValidFormula)
    (hsparse : Φ.val.clauses.length ≤ cs * Φ.val.variables)
    (hlarge : graphPolynomialCutoff D B cs ≤ Φ.val.variables) :
    (t10Graph D B Φ).vertices ≤
      Φ.val.variables^(D.sizeExponent+3) := by
  let m := Φ.val.variables
  let e := D.sizeExponent+1
  let C := t45C D B cs
  have hm : 2 ≤ m := (le_max_left _ _).trans hlarge
  have hC : C * 2^e ≤ m := (le_max_right _ _).trans hlarge
  have hsize : m.size + 1 ≤ 2*m := by
    have hh := nat_size_le_self m
    omega
  have hpow : (m.size+1)^e ≤ 2^e*m^e := by
    calc
      (m.size+1)^e ≤ (2*m)^e := Nat.pow_le_pow_left hsize _
      _ = 2^e*m^e := by rw [mul_pow]
  have htot := (t45_relations D B Φ).2.2 cs hsparse (by omega : 1 ≤ m)
  change (t10Graph D B Φ).vertices + (t10Graph D B Φ).edges.length ≤
    C*m*(m.size+1)^e at htot
  have hn : (t10Graph D B Φ).vertices ≤ C*m*(m.size+1)^e := by omega
  have hpoly : (t10Graph D B Φ).vertices ≤ (C*2^e)*m^(e+1) := by
    calc
      (t10Graph D B Φ).vertices ≤ C*m*(m.size+1)^e := hn
      _ ≤ C*m*(2^e*m^e) := Nat.mul_le_mul_left _ hpow
      _ = (C*2^e)*m^(e+1) := by rw [pow_succ]; ring
  calc
    (t10Graph D B Φ).vertices ≤ (C*2^e)*m^(e+1) := hpoly
    _ ≤ m*m^(e+1) := Nat.mul_le_mul_right _ hC
    _ = m^(D.sizeExponent+3) := by
      dsimp [e]
      rw [pow_succ]
      ring

#print axioms sparse_graph_vertices_polynomial

end CurrentAdditive.DeterministicETHSourceBridge
