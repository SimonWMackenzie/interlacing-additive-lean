import CurrentAdditive.StoredQueryBranch
import CurrentAdditive.StoredQueryMap
import CurrentAdditive.StoredCellBytes
import CurrentAdditive.StoredCellPrimitives

/-! Fixed access expressions shared by the template and source arms of the
current two-family stored-cell evaluator. Every selection invokes the actual
bounded binary/V2 getter; these definitions accept no callback. -/

namespace CurrentAdditive.StoredCellQueries
open EthInapproximability.CurrentPaper
open StoredQuery
noncomputable section

def original := total StoredRetainedGetter.identity
def field {K : Nat} (j : Fin K) (A : Query) :=
  compose A (total (PhysicalProducer.projection j))
def slot {K : Nat} (j : Fin K) := field j original

def context := slot (0 : Fin 5)
def finalLabel := slot (1 : Fin 5)
def metadataWord := slot (2 : Fin 5)
def baseWord := slot (3 : Fin 5)
def selectorWord := slot (4 : Fin 5)
def stepContext := field (0 : Fin 4) context
def oldState := field (1 : Fin 4) context
def sources := field (2 : Fin 4) context
def companions := field (3 : Fin 4) context
def source (j : Fin 7) := field j sources
def companion (j : Fin 6) := field j companions
def publicField (j : Fin 7) := field j stepContext

def finalPair := lookup (companion 5) finalLabel
def coordinate := field (0 : Fin 2) finalPair
def columnLabel := field (1 : Fin 2) finalPair
def metadataLabel := lookup metadataWord coordinate
def metadataPair := lookup (companion 2) metadataLabel
def metadataTag := field (0 : Fin 2) metadataPair
def metadataIndex := field (1 : Fin 2) metadataPair

def columnFamily := lookup (companion 4) columnLabel
def columnTag := field (0 : Fin 2) columnFamily
def columnIndex := field (1 : Fin 2) columnFamily

/-- False selects the ordinary (outer-source,gamma) family. True selects
the diagonal (q2-coordinate,gamma) family. -/
def columnPair := branch columnTag
  (lookup (companion 3) columnIndex) (lookup (companion 1) columnIndex)

def ordinaryOuterWord := lookup (source 2) (field (0 : Fin 2) columnPair)
def globalGammaWord := lookup (source 0) (field (1 : Fin 2) columnPair)
def zero := total DynamicGetterPrimitives.empty
def firstOuterLabel := lookup ordinaryOuterWord zero
def firstOuterPair := lookup (companion 1) firstOuterLabel
def firstCoordinate := branch columnTag
  (field (0 : Fin 2) firstOuterPair) (field (0 : Fin 2) columnPair)

def chosenOuterLabel := lookup ordinaryOuterWord metadataIndex
def chosenOuterPair := lookup (companion 1) chosenOuterLabel
def templateColumnPair := branch columnTag chosenOuterPair columnPair
def templateWord := lookup (source 1) (lookup selectorWord coordinate)
def templateInnerLabel := lookup templateWord (field (0 : Fin 2) templateColumnPair)
def templateInnerPair := lookup (companion 0) templateInnerLabel
def templateGammaWord := lookup (source 0) (field (1 : Fin 2) templateColumnPair)
def templateRequest := pair (field (1 : Fin 2) templateInnerPair)
  (lookup templateGammaWord (field (0 : Fin 2) templateInnerPair))

def sourceRow := lookup baseWord coordinate
def activityWord := lookup (publicField 6) metadataIndex
def activityPosition := lookup activityWord firstCoordinate
def neutralPosition := compose (publicField 2) (total StoredCellPrimitives.unaryBits)
def q1Bits := compose (publicField 0) (total StoredCellPrimitives.unaryBits)

theorem original_result (x : List Bool) : original.result x=some x := rfl

theorem field_result {K : Nat} (j : Fin K) (A : Query) (x y : List Bool)
    (ha : A.result x=some y) :
    (field j A).result x=some (BankFieldProjection.result j y) := by
  simp [field,StoredQuery.compose,ha,total,PhysicalProducer.projection]

theorem slot_result {K : Nat} (j : Fin K) (x : List Bool) :
    (slot j).result x=some (BankFieldProjection.result j x) := by
  exact field_result j original x x rfl

theorem lookup_ofFn (S I : Query) (x bits : List Bool) {n : Nat} (f : Fin n → List Bool)
    (i : Fin n) (hs : S.result x=some (SourceListEncoding.encode (List.ofFn f)))
    (hi : I.result x=some bits) (hv : EncodedCommunication.bitsValue bits=i.val) :
    (lookup S I).result x=some (f i) := by
  have hbound : EncodedCommunication.bitsValue bits<(List.ofFn f).length := by
    simpa only [List.length_ofFn,hv] using i.isLt
  have h := StoredQuery.lookup_result S I x bits (List.ofFn f) hs hi hbound
  simpa only [List.getElem_ofFn,hv,Fin.eta] using h

theorem compose_result (A B : Query) (x y z : List Bool)
    (ha : A.result x=some y) (hb : B.result y=some z) :
    (StoredQuery.compose A B).result x=some z := by
  simp [StoredQuery.compose,ha,hb]

end
end CurrentAdditive.StoredCellQueries

#print axioms CurrentAdditive.StoredCellQueries.templateRequest
#print axioms CurrentAdditive.StoredCellQueries.lookup_ofFn
