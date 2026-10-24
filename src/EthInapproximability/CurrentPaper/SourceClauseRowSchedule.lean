import EthInapproximability.CurrentPaper.SourceClauseRowGate
import EthInapproximability.CurrentPaper.SourceBooleanThreeCNF

/-!
# Ordered assignment slots and row-literal instructions

These are the fixed finite-control indices for the physical row writer. Every
one of the `a^q` truth-table positions is a clause slot, including accepting
positions. A true bit prepends one positive literal; a false bit emits only
the `q` negative query literals. This file connects those instructions to the
source's actual labelled-clause order; it is not by itself a machine run.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseRowSchedule

open SourceBooleanEncoding EncodedCNF

def tuple (a q : ℕ) (k : Fin (a ^ q)) : Fin q → Fin a :=
  finFunctionFinEquiv.symm k

def slot (n a q row : ℕ) (k : Fin (a ^ q)) : ℕ :=
  n + n * (a * a) + row * a ^ q + k.val

theorem label_slot {n m a q : ℕ} (row : Fin m)
    (k : Fin (a ^ q)) :
    ((labelEquiv n m a q)
      (.inr (.inr (row, tuple a q k)))).val = slot n a q row.val k := by
  simp [labelEquiv, slot, tuple, finProdFinEquiv,
    finSumFinEquiv_apply_right, Fin.val_natAdd]
  change n + (n * (a * a) + (k.val + a ^ q * row.val)) =
    n + n * (a * a) + row.val * a ^ q + k.val
  rw [Nat.mul_comm (a ^ q) row.val]
  omega

theorem bit_address {n a : ℕ} (v : Fin n) (s : Fin a) :
    (bitIndex v s).val = v.val * a + s.val := by
  change s.val + a * v.val = v.val * a + s.val
  rw [Nat.mul_comm a v.val]
  omega

def tupleLiteral {a q : ℕ} (k : Fin (a ^ q))
    (query : Fin q → ℕ) (t : Fin q) : Literal :=
  negative (query t * a + (tuple a q k t).val)

def tupleClause {a q : ℕ} (hq : 0 < q) (k : Fin (a ^ q))
    (query : Fin q → ℕ) (accept : Bool) : List Literal :=
  let negatives := List.ofFn fun t : Fin q => tupleLiteral k query t
  if accept then
    positive (query ⟨0, hq⟩ * a + (tuple a q k ⟨0, hq⟩).val) :: negatives
  else negatives

theorem exact_row_clause {n m a q : ℕ} (P : CSP n m a q)
    (hq : 0 < q) (row : Fin m) (k : Fin (a ^ q)) :
    tupleClause hq k (fun t => (P.query row t).val)
      (P.accept row (tuple a q k)) =
    clause P hq (.inr (.inr (row, tuple a q k))) := by
  simp [tupleClause, tupleLiteral, clause, bit_address]

theorem tuple_gate_address {a q : ℕ} (k : Fin (a ^ q))
    (query : Fin q → ℕ) (t : Fin q) :
    (tupleLiteral k query t).variable =
      query t * a + (tuple a q k t).val := rfl

end EthInapproximability.CurrentPaper.SourceClauseRowSchedule
