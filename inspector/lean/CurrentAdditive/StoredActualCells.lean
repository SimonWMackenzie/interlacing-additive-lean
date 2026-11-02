import CurrentAdditive.StoredActualCell
import CurrentAdditive.StoredCellTraversal
import CurrentAdditive.StoredQueryOfFnMap

set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option quotPrecheck false
namespace CurrentAdditive.StoredActualCells
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction StoredQuery
open StoredCellQueries
noncomputable section

def query := StoredCellTraversal.query StoredActualCell.query
def machine := query.machine
def coefficient := query.coefficient
def degree := query.degree

def push (C w : List Bool) := BitMachineBankCodec.encode ![C,w]

theorem singleton_flatten {n : Nat} (f : Fin n → Bool) :
    (List.ofFn (fun i=>[f i])).flatten=List.ofFn f := by
  have h : (List.ofFn f).map (fun b=>[b])=List.ofFn (fun i=>[f i]) := by
    simp only [List.map_ofFn,Function.comp_def]
  rw [←h,List.flatten_eq_flatMap,List.flatMap_map]
  simp

section Input
variable {D q₁ q₂ s w Q nx ny ni : Nat}
  [NeZero q₁] [NeZero q₂] [NeZero s] [NeZero w] [NeZero Q]
  {μX : PositiveRationalLaw (Fin nx)} {μY : PositiveRationalLaw (Fin ny)}
  {μI : PositiveRationalLaw (Fin ni)}
  (src : SourceData (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (st : src.Streams (w := w) (μI := μI))
  (out : ExactList D Q (Fin w × src.Column) (product (uniform w) src.columnLaw))
  (R : Fin nx → Fin ny → Bool) (activity : Fin ni → Fin q₂ → Option (Fin s))

local notation "C" => StoredCellBytes.context src st out R activity
local notation "MW" => fun j : Fin st.metadata.size => StoredCellBytes.tuple
  (fun p => (finSumFinEquiv (st.metadata.decode j p)).val)
local notation "BW" => fun j : Fin st.base.size => StoredCellBytes.tuple
  (fun p => (st.base.decode j p).val)
local notation "SW" => fun j : Fin st.selector.size => StoredCellBytes.tuple
  (fun p => (st.selector.decode j p).val)
local notation "FL" => fun a : Fin w × src.Column =>
  (finProdFinEquiv (a.1,src.columnOrder a.2)).val.bits
local notation "cell" => fun (a : Fin w × src.Column) (m : Fin st.metadata.size)
  (b : Fin st.base.size) (z : Fin st.selector.size) => src.B R activity
  (SourceData.Streams.decode src st (m,(b,z)) a.1) a.2

theorem selector_result (row : List Bool) (a : Fin w × src.Column)
    (m : Fin st.metadata.size) (b : Fin st.base.size) (z : Fin st.selector.size) :
    (StoredCellTraversal.selectorCall StoredActualCell.query).result
      (push (push (push (push (push C row) (FL a)) (MW m)) (BW b)) (SW z))=
      some [cell a m b z] := by
  apply compose_result (total StoredCellTraversal.selectorRouter) StoredActualCell.query _
    (StoredCellBytes.input src st out R activity a m b z) _
  · exact congrArg some (StoredCellTraversal.selectorRouter_result C row (FL a) (MW m) (BW b) (SW z))
  · exact StoredActualCell.result src st out R activity a m b z

theorem base_result (row : List Bool) (a : Fin w × src.Column)
    (m : Fin st.metadata.size) (b : Fin st.base.size) :
    (StoredCellTraversal.baseCall StoredActualCell.query).result
      (push (push (push (push C row) (FL a)) (MW m)) (BW b))=
      some (List.ofFn (fun z : Fin st.selector.size => cell a m b z)) := by
  let B := push (push (push (push C row) (FL a)) (MW m)) (BW b)
  have hs : (total (StoredCellTraversal.sourceFor 4 5)).result B=
      some (SourceListEncoding.encode (List.ofFn SW)) := by
    simp [total,StoredCellTraversal.sourceFor,StoredCellTraversal.left,push,B,
      PhysicalProducer.compose,PhysicalProducer.projection,StoredRetainedGetter.identity,
      StoredCellBytes.context,StoredCellBytes.sources,StoredCellBytes.selectorWords,StoredCellBytes.words]
  have hr := pair_result StoredCellQueries.original (total (StoredCellTraversal.sourceFor 4 5))
    B B (SourceListEncoding.encode (List.ofFn SW)) rfl hs
  have hm := map_ofFn_result (StoredCellTraversal.selectorCall StoredActualCell.query) false B
    SW (fun z=>[cell a m b z]) (fun z=>selector_result src st out R activity row a m b z)
  apply compose_result _ _ B _ _ hr
  simpa only [Bool.false_eq_true,if_false,singleton_flatten] using hm

theorem metadata_result (row : List Bool) (a : Fin w × src.Column)
    (m : Fin st.metadata.size) :
    (StoredCellTraversal.metadataCall StoredActualCell.query).result
      (push (push (push C row) (FL a)) (MW m))=
      some ((List.ofFn (fun b : Fin st.base.size =>
        List.ofFn (fun z : Fin st.selector.size => cell a m b z))).flatten) := by
  let M := push (push (push C row) (FL a)) (MW m)
  have hs : (total (StoredCellTraversal.sourceFor 3 4)).result M=
      some (SourceListEncoding.encode (List.ofFn BW)) := by
    simp [total,StoredCellTraversal.sourceFor,StoredCellTraversal.left,push,M,
      PhysicalProducer.compose,PhysicalProducer.projection,StoredRetainedGetter.identity,
      StoredCellBytes.context,StoredCellBytes.sources,StoredCellBytes.baseWords,StoredCellBytes.words]
  have hr := pair_result StoredCellQueries.original (total (StoredCellTraversal.sourceFor 3 4))
    M M (SourceListEncoding.encode (List.ofFn BW)) rfl hs
  have hm := map_ofFn_result (StoredCellTraversal.baseCall StoredActualCell.query) false M
    BW (fun b=>List.ofFn (fun z : Fin st.selector.size=>cell a m b z))
    (fun b=>base_result src st out R activity row a m b)
  exact compose_result _ _ M _ _ hr hm

theorem coordinate_result (row : List Bool) (a : Fin w × src.Column) :
    (StoredCellTraversal.coordinateCall StoredActualCell.query).result
      (push (push C row) (FL a))=
      some ((List.ofFn (fun m : Fin st.metadata.size =>
        (List.ofFn (fun b : Fin st.base.size =>
          List.ofFn (fun z : Fin st.selector.size => cell a m b z))).flatten)).flatten) := by
  let P := push (push C row) (FL a)
  have hs : (total (StoredCellTraversal.sourceFor 2 3)).result P=
      some (SourceListEncoding.encode (List.ofFn MW)) := by
    simp [total,StoredCellTraversal.sourceFor,StoredCellTraversal.left,push,P,
      PhysicalProducer.compose,PhysicalProducer.projection,StoredRetainedGetter.identity,
      StoredCellBytes.context,StoredCellBytes.sources,StoredCellBytes.metadataWords,StoredCellBytes.words]
  have hr := pair_result StoredCellQueries.original (total (StoredCellTraversal.sourceFor 2 3))
    P P (SourceListEncoding.encode (List.ofFn MW)) rfl hs
  have hm := map_ofFn_result (StoredCellTraversal.metadataCall StoredActualCell.query) false P
    MW (fun m=>(List.ofFn (fun b : Fin st.base.size =>
      List.ofFn (fun z : Fin st.selector.size=>cell a m b z))).flatten)
    (fun m=>metadata_result src st out R activity row a m)
  exact compose_result _ _ P _ _ hr hm

theorem row_result (r : Fin out.size) :
    (StoredCellTraversal.rowCall StoredActualCell.query).result
      (push C (StoredCellBytes.tuple (fun p =>
        (finProdFinEquiv ((out.decode r p).1,src.columnOrder (out.decode r p).2)).val)))=
      some (StoredSuccessorOrderedSpec.rowWord src st out R activity r) := by
  let rw := StoredCellBytes.tuple (fun p =>
    (finProdFinEquiv ((out.decode r p).1,src.columnOrder (out.decode r p).2)).val)
  let P := push C rw
  have hs : (total (PhysicalProducer.projection (1 : Fin 2))).result P=some rw := by
    simp [total,PhysicalProducer.projection,P,push]
  have hr := pair_result StoredCellQueries.original (total (PhysicalProducer.projection (1 : Fin 2)))
    P P rw rfl hs
  have hm := map_ofFn_result (StoredCellTraversal.coordinateCall StoredActualCell.query) false P
    (fun p : Fin Q => FL (out.decode r p))
    (fun p => (List.ofFn (fun m : Fin st.metadata.size =>
      (List.ofFn (fun b : Fin st.base.size =>
        List.ofFn (fun z : Fin st.selector.size=>cell (out.decode r p) m b z))).flatten)).flatten)
    (fun p=>coordinate_result src st out R activity rw (out.decode r p))
  exact compose_result _ _ P _ _ hr hm

def input : List Bool := push C (SourceListEncoding.encode (StoredCellBytes.finalWords src out))

theorem result : query.result (input src st out R activity)=
    some (MatrixMaterialization.rowMajor (src.numberedEntry st out R activity)) := by
  have hm := map_ofFn_result (StoredCellTraversal.rowCall StoredActualCell.query) false C
    (fun r : Fin out.size => StoredCellBytes.tuple (fun p =>
      (finProdFinEquiv ((out.decode r p).1,src.columnOrder (out.decode r p).2)).val))
    (fun r=>StoredSuccessorOrderedSpec.rowWord src st out R activity r)
    (fun r=>row_result src st out R activity r)
  have hc : (List.ofFn (fun r => StoredSuccessorOrderedSpec.rowWord src st out R activity r)).flatten=
      MatrixMaterialization.rowMajor (src.numberedEntry st out R activity) :=
    StoredSuccessorOrderedSpec.cells_rowMajor src st out R activity
  simpa only [query,StoredCellTraversal.query,input,push,StoredCellBytes.finalWords,
    StoredCellBytes.words,FeatureMapPairLoader.packet,hc,
    Bool.false_eq_true,if_false] using hm

attribute [local irreducible] query

theorem outputs : machine.OutputsWithin (input src st out R activity)
    (MatrixMaterialization.rowMajor (src.numberedEntry st out R activity))
    (coefficient*((input src st out R activity).length+1)^degree) :=
  query.outputs _ _ (result src st out R activity)

end Input
end
end CurrentAdditive.StoredActualCells

#print axioms CurrentAdditive.StoredActualCells.outputs
