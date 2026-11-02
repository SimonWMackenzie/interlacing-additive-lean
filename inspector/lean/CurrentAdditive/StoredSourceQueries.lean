import CurrentAdditive.StoredCellColumnFacts
import CurrentAdditive.WordEqualityOrdinary

/-! The fixed source-column arm. Every ordinary outer head is physically
decoded and compared with the first head; the actual comparison bits are
conjoined before the activity position and gamma tail are read. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CurrentAdditive.StoredSourceQueries
open EthInapproximability.CurrentPaper StoredQuery StoredCellQueries
noncomputable section
attribute [local instance] Classical.propDecidable

def equalityResult (x : List Bool) : Option (List Bool) :=
  (BitMachineBankCodec.decode 2 x).map fun S => [decide (S 0=S 1)]

def equality : Query where
  result := equalityResult
  machine := WordEqualityOrdinary.machine
  coefficient := WordEqualityOrdinary.coefficient
  degree := WordEqualityOrdinary.degree
  outputs x y h := by
    cases hd : BitMachineBankCodec.decode 2 x with
    | none => simp [equalityResult,hd] at h
    | some S =>
      have hy : [decide (S 0=S 1)]=y := by simpa [equalityResult,hd] using h
      subst y
      have he : x=WordEqualityOrdinary.input (S 0) (S 1) := by
        rw [← BitMachineBankCodec.encode_decode hd]
        congr 1
        funext j;fin_cases j <;> rfl
      rw [he]
      exact WordEqualityOrdinary.outputs_polynomial (S 0) (S 1)

theorem equality_packet (a b : List Bool) :
    equality.result (BitMachineBankCodec.encode ![a,b])=some [decide (a=b)] := by
  simp [equality,equalityResult]

/-- Callback input is Bank2[Bank2[first head,companion table],outer label]. -/
def callbackContext := slot (0 : Fin 2)
def callbackLabel := slot (1 : Fin 2)
def callbackFirst := field (0 : Fin 2) callbackContext
def callbackTable := field (1 : Fin 2) callbackContext
def callbackHead := field (0 : Fin 2) (lookup callbackTable callbackLabel)
def compareHead := compose (pair callbackHead callbackFirst) equality

def ordinaryComparisonPacket := pair (pair firstCoordinate (companion 1)) ordinaryOuterWord
def ordinaryComparisons := compose ordinaryComparisonPacket (mapItems compareHead false)
def ordinaryDiagonal := compose ordinaryComparisons (total StoredCellPrimitives.conjunction)
def diagonal := branch columnTag ordinaryDiagonal (total (StoredCellPrimitives.constantBit true))
def position := branch diagonal neutralPosition activityPosition
def tailIndex := StoredQuery.add q1Bits position
def column := lookup globalGammaWord tailIndex
def request := pair sourceRow column

theorem compareHead_packet {m n : Nat} (a : Fin m) (p : Fin m × Fin n) :
    compareHead.result (FeatureMapPairLoader.packet
      (BitMachineBankCodec.encode ![a.val.bits,
        SourceListEncoding.encode (StoredCellBytes.productCompanions m n)])
      (finProdFinEquiv p).val.bits)=some [decide (p.1=a)] := by
  let x := FeatureMapPairLoader.packet
    (BitMachineBankCodec.encode ![a.val.bits,
      SourceListEncoding.encode (StoredCellBytes.productCompanions m n)])
    (finProdFinEquiv p).val.bits
  have hc : callbackContext.result x=some (BitMachineBankCodec.encode ![a.val.bits,
      SourceListEncoding.encode (StoredCellBytes.productCompanions m n)]) := by
    simpa [callbackContext,x,FeatureMapPairLoader.packet] using slot_result (0 : Fin 2) x
  have hi : callbackLabel.result x=some (finProdFinEquiv p).val.bits := by
    simpa [callbackLabel,x,FeatureMapPairLoader.packet] using slot_result (1 : Fin 2) x
  have ha := field_packet (0 : Fin 2) callbackContext x _ hc
  have ht := field_packet (1 : Fin 2) callbackContext x _ hc
  have hp := product_lookup callbackTable callbackLabel x p ht hi
  have hh := field_packet (0 : Fin 2) (lookup callbackTable callbackLabel) x _ hp
  have he : decide (p.1.val.bits=a.val.bits)=decide (p.1=a) := by
    congr 1
    apply propext
    constructor
    · intro h
      apply Fin.ext
      have h' := congrArg EncodedCommunication.bitsValue h
      simpa only [EncodedCommunication.bitsValue_bits] using h'
    · intro h;rw [h]
  have hpair := pair_result callbackHead callbackFirst x _ _ hh ha
  exact compose_result _ _ x _ _ hpair (by simpa only [he] using equality_packet p.1.val.bits a.val.bits)

end
end CurrentAdditive.StoredSourceQueries

#print axioms CurrentAdditive.StoredSourceQueries.request
#print axioms CurrentAdditive.StoredSourceQueries.compareHead_packet
