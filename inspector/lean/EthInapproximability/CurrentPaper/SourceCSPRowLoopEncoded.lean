import EthInapproximability.CurrentPaper.SourceCSPRowLoopAll
import EthInapproximability.CurrentPaper.SourceCSPHeaderRowBridge

/-!
# Canonical encoded-instance entry for the physical row loop

The semantic row list is exactly the finite enumeration encoded by
`SourceCSPPositiveHeader.rows`. The loop starts on the actual prepared
right-bank produced by `SourceCSPHeaderRowBridge`.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopEncoded

open Turing BitMachineEncoding
open SourceCSPRowLoopController
open SourceCSPRowLoopAll

def rowList {a q : Nat} (P : EncodedETHSource.ConstraintInstance a q) :
    List (SourceCSPCodec.Row P.vertices a q) :=
  List.ofFn (SourceCSPCodec.rowsOf P)

theorem rowList_length {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q) :
    (rowList P).length = P.constraints := by
  simp [rowList]

theorem rowList_bytes {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q) :
    rowBytes (rowList P) = SourceCSPPositiveHeader.rows P := by
  simp only [rowBytes, rowList, SourceCSPPositiveHeader.rows,
    SourceCSPCodec.fnFields, List.map_ofFn]
  rfl

theorem encoded_rows_accept {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q)
    (hn : 0 < P.vertices) :
    ∃ (t : Nat) (costs : List Nat),
      Charges (rowList P) costs ∧ costs.length = P.constraints ∧
      t ≤ costs.sum + 3 ∧
      ((advance (program q (a ^ q)))^[t])
        (⟨some (adminLabel .check), initialControl,
          SourceCSPHeaderRowBridge.ready
            (SourceCSPPositiveHeader.rows P)
            (List.replicate (P.vertices - 1) true)
            (List.replicate P.constraints true)⟩ : Config q (a ^ q)) =
        ⟨none, ((queryStart, resetStart), some true),
          Sum.elim (SourceCSPRowQueryFrame.initial []
            (List.replicate (P.vertices - 1) true))
            (fun k : Fin 4 => if k = 1 then
              List.replicate (P.vertices - 1) true else [])⟩ := by
  let E : Fin 4 → List Bool := fun k =>
    if k = 0 then List.replicate P.constraints true else
      if k = 1 then List.replicate (P.vertices - 1) true else []
  have hc : E 0 = List.replicate (rowList P).length true := by
    simp [E, rowList_length]
  have hcap : E 1 = List.replicate (P.vertices - 1) true := by simp [E]
  have hs : E 3 = [] := by simp [E]
  obtain ⟨t, costs, hcosts, hlen, ht, hrun⟩ :=
    rows_accept hn (rowList P) E hc hcap hs
  refine ⟨t, costs, hcosts, hlen.trans (rowList_length P), ht, ?_⟩
  have hstart : SourceCSPHeaderRowBridge.ready (q := q)
      (SourceCSPPositiveHeader.rows P)
      (List.replicate (P.vertices - 1) true)
      (List.replicate P.constraints true) =
      Sum.elim (SourceCSPRowQueryFrame.initial (q := q)
        (rowBytes (rowList P))
        (List.replicate (P.vertices - 1) true)) E := by
    rw [rowList_bytes]
    funext k
    cases k with
    | inl r => rfl
    | inr r => fin_cases r <;> simp [SourceCSPHeaderRowBridge.ready, E]
  have hend : Function.update E 0 [] =
      (fun k : Fin 4 => if k = 1 then
        List.replicate (P.vertices - 1) true else []) := by
    funext k
    fin_cases k <;> simp [E]
  rw [hstart]
  simpa only [hend] using hrun

end EthInapproximability.CurrentPaper.SourceCSPRowLoopEncoded
