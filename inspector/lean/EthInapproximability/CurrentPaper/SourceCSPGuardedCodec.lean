import EthInapproximability.CurrentPaper.SourceCSPConstraintGuard
import EthInapproximability.CurrentPaper.SourceBooleanThreeCNF

/-!
# Codec alignment for the guarded CSP header

The literal codec places enough bits for its declared number of constraints.
Thus the physical bounded-unary header checker returns the exact unary
constraint count on encoded inputs, rather than merely a truncated count.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPGuardedCodec

open EncodedETHSource EncodedCommunication

theorem input_eq_header_rows {a q : Nat} (P : ConstraintInstance a q) :
    constraintBits P =
      SourceCSPHeaderParse.header P.vertices P.constraints a q ++
        SourceCSPCodec.fnFields SourceCSPCodec.rowFields (SourceCSPCodec.rowsOf P) := by
  simpa only [SourceCSPHeaderParse.header, List.append_assoc] using
    SourceCSPCodec.constraintBits_eq P

theorem constraint_count_fits {a q : Nat} (P : ConstraintInstance a q) :
    P.constraints ≤
      (SourceCSPHeaderParse.header P.vertices P.constraints a q ++
        SourceCSPCodec.fnFields SourceCSPCodec.rowFields (SourceCSPCodec.rowsOf P)).length := by
  rw [← input_eq_header_rows]
  exact SourceCSPCodec.constraints_le_bits P

theorem guard_result_exact {a q : Nat} (P : ConstraintInstance a q) :
    ProtocolBoundedUnary.result P.constraints.bits
      (List.replicate (constraintBits P).length true) [] =
        true :: List.replicate P.constraints true := by
  exact SourceCSPConstraintGuard.guard_result_at_constraint_count
    P.constraints (constraintBits P) (SourceCSPCodec.constraints_le_bits P)

/-- A positive-arity typed instance cannot contain even one constraint when
there are no vertices: its first query would have type `Fin 0`. -/
theorem zero_vertices_no_constraints {a q : Nat} (hq : 0 < q)
    (P : ConstraintInstance a q) (hn : P.vertices = 0) :
    P.constraints = 0 := by
  by_contra hm
  have hmp : 0 < P.constraints := by omega
  have index : Fin P.vertices := P.system.query ⟨0, hmp⟩ ⟨0, hq⟩
  have impossible : Fin 0 := by simpa only [hn] using index
  exact impossible.elim0

theorem zero_instance_cnf {a q : Nat} (hq : 0 < q)
    (P : ConstraintInstance a q) (hn : P.vertices = 0) :
    SourceBooleanEncoding.threeCNF P.system hq =
      (⟨0, []⟩ : EncodedCNF.Formula) := by
  have hm := zero_vertices_no_constraints hq P hn
  have hv : (SourceBooleanEncoding.threeCNF P.system hq).variables = 0 := by
    simp [SourceBooleanEncoding.threeCNF, SourceClauseEncoding.translate,
      SourceBooleanEncoding.formula, SourceBooleanEncoding.clauseCount, hn, hm]
  have hc : (SourceBooleanEncoding.threeCNF P.system hq).clauses = [] := by
    simp [SourceBooleanEncoding.threeCNF, SourceClauseEncoding.translate,
      SourceBooleanEncoding.formula, SourceClauseEncoding.fromIndexed,
      SourceBooleanEncoding.clauseCount, hn, hm]
  cases h : SourceBooleanEncoding.threeCNF P.system hq with
  | mk v cs =>
      simp only [h] at hv hc
      subst v
      subst cs
      rfl

theorem zero_instance_encoding {a q : Nat} (hq : 0 < q)
    (P : ConstraintInstance a q) (hn : P.vertices = 0) :
    EncodedCNF.encode (SourceBooleanEncoding.threeCNF P.system hq) =
      false :: natField 0 := by
  rw [zero_instance_cnf hq P hn]
  simp [EncodedCNF.encode, EncodedGraph.unary, EncodedCNF.clauseFields]

end EthInapproximability.CurrentPaper.SourceCSPGuardedCodec
