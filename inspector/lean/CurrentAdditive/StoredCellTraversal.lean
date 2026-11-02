import CurrentAdditive.StoredQueryMapFacts
import CurrentAdditive.StoredCellQueries

/-! The literal five nested loops of the current successor table: final
source records, coordinates, metadata records, base records, selector records.
Each map preserves every list position and uses the actual counted list.
The concrete cell evaluator will instantiate this fixed traversal below. -/

namespace CurrentAdditive.StoredCellTraversal
open EthInapproximability.CurrentPaper PhysicalProducer
open StoredQuery
noncomputable section

def left : Nat → Producer
  | 0 => StoredRetainedGetter.identity
  | n+1 => PhysicalProducer.compose (left n) (projection (0 : Fin 2))

def rightAt (n : Nat) := PhysicalProducer.compose (left n) (projection (1 : Fin 2))

def sourceFor (depth : Nat) (j : Fin 7) :=
  PhysicalProducer.compose
    (PhysicalProducer.compose (left depth) (projection (2 : Fin 4))) (projection j)

def selectorRouter := DynamicGetterOrdinary.bankFields
  [left 5,rightAt 3,rightAt 2,rightAt 1,rightAt 0]

theorem selectorRouter_result (C row label metadata base selector : List Bool) :
    selectorRouter.result (BitMachineBankCodec.encode ![
      BitMachineBankCodec.encode ![BitMachineBankCodec.encode ![
        BitMachineBankCodec.encode ![BitMachineBankCodec.encode ![C,row],label],metadata],base],selector])=
      BitMachineBankCodec.encode ![C,label,metadata,base,selector] := by
  simp only [selectorRouter,DynamicGetterOrdinary.bankFields_result,List.flatMap_cons,
    List.flatMap_nil,left,rightAt,PhysicalProducer.compose,projection,Function.comp_apply,
    StoredRetainedGetter.identity,id_eq,BankFieldProjection.result_encode,
    Matrix.cons_val_zero,Matrix.cons_val_one,List.append_nil]
  simp [BitMachineBankCodec.encode_eq_list]

def selectorCall (cell : Query) := StoredQuery.compose (total selectorRouter) cell
def baseCall (cell : Query) :=
  StoredQuery.compose (pair StoredCellQueries.original (total (sourceFor 4 5)))
    (mapItems (selectorCall cell) false)
def metadataCall (cell : Query) :=
  StoredQuery.compose (pair StoredCellQueries.original (total (sourceFor 3 4)))
    (mapItems (baseCall cell) false)
def coordinateCall (cell : Query) :=
  StoredQuery.compose (pair StoredCellQueries.original (total (sourceFor 2 3)))
    (mapItems (metadataCall cell) false)
def rowCall (cell : Query) :=
  StoredQuery.compose (pair StoredCellQueries.original (total (projection (1 : Fin 2))))
    (mapItems (coordinateCall cell) false)
def query (cell : Query) := mapItems (rowCall cell) false

end
end CurrentAdditive.StoredCellTraversal

#print axioms CurrentAdditive.StoredCellTraversal.query
