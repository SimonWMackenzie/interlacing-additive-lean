import CurrentAdditive.StoredCellQueryFacts

namespace CurrentAdditive.StoredCellRead
open Paper2 EthInapproximability.CurrentPaper StoredQuery StoredCellQueries
noncomputable section

def caller := slot (0 : Fin 2)
def request := slot (1 : Fin 2)
def row := field (0 : Fin 2) request
def col := field (1 : Fin 2) request
def previous := StoredQuery.compose caller oldState
def vector := field (0 : Fin 3) previous
def width := StoredQuery.compose (field (2 : Fin 3) previous) (total StoredCellPrimitives.countBits)
def product := StoredQuery.compose (pair row width) (total LawJobBinaryProduct.multiply)
def address := StoredQuery.compose (pair product col) (total LawJobBinaryProduct.add)
def query := bitAt vector address

theorem result {nx ny : Nat} (μX : PositiveRationalLaw (Fin nx))
    (μY : PositiveRationalLaw (Fin ny)) (R : Fin nx → Fin ny → Bool)
    (x : List Bool) (r : Fin nx) (c : Fin ny)
    (hstate : oldState.result x=some (StoredCellBytes.baseState (μX := μX) (μY := μY) R)) :
    query.result (BitMachineBankCodec.encode ![x,BitMachineBankCodec.encode ![r.val.bits,c.val.bits]])=
      some [R r c] := by
  let y := BitMachineBankCodec.encode ![x,BitMachineBankCodec.encode ![r.val.bits,c.val.bits]]
  have hc : caller.result y=some x := by
    simpa only [caller,y,BankFieldProjection.result_encode,Matrix.cons_val_zero] using slot_result (0 : Fin 2) y
  have hrq : request.result y=some (BitMachineBankCodec.encode ![r.val.bits,c.val.bits]) := by
    simpa only [request,y,BankFieldProjection.result_encode,Matrix.cons_val_one] using slot_result (1 : Fin 2) y
  have hr := field_packet (0 : Fin 2) request y _ hrq
  have hcol := field_packet (1 : Fin 2) request y _ hrq
  have hp : previous.result y=some (StoredCellBytes.baseState (μX := μX) (μY := μY) R) :=
    compose_result caller oldState y x _ hc hstate
  have hv : vector.result y=some (MatrixMaterialization.rowMajor R) :=
    field_packet (0 : Fin 3) previous y _ hp
  have hlaw := field_packet (2 : Fin 3) previous y _ hp
  have hw : width.result y=some ny.bits := by
    apply compose_result (field (2 : Fin 3) previous) (total StoredCellPrimitives.countBits) y
      (StoredWeightedState.lawBytes μY) ny.bits hlaw
    exact congrArg some (StoredCellPrimitives.countBits_law μY)
  have hprod : product.result y=some (r.val*ny).bits := by
    apply compose_result (pair row width) (total LawJobBinaryProduct.multiply) y
      (BitMachineBankCodec.encode ![r.val.bits,ny.bits]) (r.val*ny).bits
    · exact pair_result row width y _ _ hr hw
    · exact congrArg some (LawJobBinaryProduct.multiply_nats r.val ny)
  have haddr : address.result y=some (r.val*ny+c.val).bits := by
    apply compose_result (pair product col) (total LawJobBinaryProduct.add) y
      (BitMachineBankCodec.encode ![(r.val*ny).bits,c.val.bits]) (r.val*ny+c.val).bits
    · exact pair_result product col y _ _ hprod hcol
    · simpa only [total,LawJobBinaryProduct.add_packet,EncodedCommunication.bitsValue_bits]
  have hi : r.val*ny+c.val<(MatrixMaterialization.rowMajor R).length := by
    rw [MatrixMaterialization.rowMajor_length]
    have h := Nat.mul_le_mul_right ny (show r.val+1 ≤ nx by omega)
    have := c.isLt
    nlinarith
  have hfetch := StoredBinaryBitLookup.result_packet (MatrixMaterialization.rowMajor R)
    (r.val*ny+c.val).bits (by simpa only [EncodedCommunication.bitsValue_bits] using hi)
  have hentry := MatrixMaterialization.rowMajor_entry R r c
  have he : (MatrixMaterialization.rowMajor R)[r.val*ny+c.val]=R r c := by
    simpa only [List.getElem?_eq_getElem hi,Option.some.injEq] using hentry
  have hres : (total StoredBinaryBitLookup.producer).result
      (BitMachineBankCodec.encode ![MatrixMaterialization.rowMajor R,(r.val*ny+c.val).bits])=
        some [R r c] := by
    simpa only [total,StoredBinaryBitLookup.packet,EncodedCommunication.bitsValue_bits,he] using congrArg some hfetch
  exact compose_result (pair vector address) (total StoredBinaryBitLookup.producer) y _ _
    (pair_result vector address y _ _ hv haddr) hres

end
end CurrentAdditive.StoredCellRead

#print axioms CurrentAdditive.StoredCellRead.query
#print axioms CurrentAdditive.StoredCellRead.result
