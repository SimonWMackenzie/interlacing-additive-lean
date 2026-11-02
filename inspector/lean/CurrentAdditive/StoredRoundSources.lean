import CurrentAdditive.StoredPhaseTuples
import CurrentAdditive.StoredCellBytes

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
namespace CurrentAdditive.StoredRoundProjection
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction
open StoredRoundData
noncomputable section

def sourcePacket (a : Data) := BitMachineBankCodec.encode
  ![StoredSourcePhase.tupleBytes (call a 0),StoredSourcePhase.tupleBytes (call a 1),
    StoredSourcePhase.tupleBytes (call a 2),StoredSourcePhase.tupleBytes (call a 3),
    StoredSourcePhase.tupleBytes (call a 4),StoredSourcePhase.tupleBytes (call a 5),
    StoredSourcePhase.tupleBytes (call a 6)]

def rowLaw (a : Data) := StoredSourcePhase.lawBytes (call a 6)

theorem gamma_tuples (a : Data) : StoredSourcePhase.tupleBytes (call a 0)=
    SourceListEncoding.encode (StoredCellBytes.gammaWords (src a)) :=
  run_tuples (a.parameters.q₁+a.parameters.s+1) a.parameters.R.cols a.parameters.R.colLaw

theorem inner_tuples (a : Data) : StoredSourcePhase.tupleBytes (call a 1)=
    SourceListEncoding.encode (StoredCellBytes.innerWords (src a)) :=
  call_tuples a.parameters.q₂ (a.parameters.q₁*a.parameters.R.rows) finProdFinEquiv
    (product (uniform a.parameters.q₁) a.parameters.R.rowLaw)

theorem outer_tuples (a : Data) : StoredSourcePhase.tupleBytes (call a 2)=
    SourceListEncoding.encode (StoredCellBytes.outerWords (src a)) :=
  call_tuples a.parameters.s (a.parameters.q₂*(src a).gamma.size) finProdFinEquiv
    (product (uniform a.parameters.q₂) (src a).gamma.law)

theorem metadata_tuples (a : Data) : StoredSourcePhase.tupleBytes (call a 3)=
    SourceListEncoding.encode (StoredCellBytes.metadataWords (src a) (streams a)) :=
  call_tuples a.parameters.w (a.parameters.s+a.parameters.ni) finSumFinEquiv
    (mixture (uniform a.parameters.s) a.parameters.μI)

theorem base_tuples (a : Data) : StoredSourcePhase.tupleBytes (call a 4)=
    SourceListEncoding.encode (StoredCellBytes.baseWords (src a) (streams a)) :=
  run_tuples a.parameters.w a.parameters.R.rows a.parameters.R.rowLaw

theorem selector_tuples (a : Data) : StoredSourcePhase.tupleBytes (call a 5)=
    SourceListEncoding.encode (StoredCellBytes.selectorWords (src a) (streams a)) :=
  run_tuples a.parameters.w (src a).inner.size (src a).inner.law

theorem final_tuples (a : Data) : StoredSourcePhase.tupleBytes (call a 6)=
    SourceListEncoding.encode (StoredCellBytes.finalWords (src a) (final a)) :=
  call_tuples a.parameters.Q
    (a.parameters.w*((src a).outer.size*(src a).gamma.size+a.parameters.q₂*(src a).gamma.size))
    ((Equiv.prodCongr (Equiv.refl _) (src a).columnOrder).trans finProdFinEquiv)
    (product (uniform a.parameters.w) (src a).columnLaw)

theorem sourcePacket_eq (a : Data) :
    sourcePacket a=StoredCellBytes.sources (src a) (streams a) (final a) := by
  unfold sourcePacket StoredCellBytes.sources
  rw [gamma_tuples,inner_tuples,outer_tuples,metadata_tuples,base_tuples,selector_tuples,final_tuples]

theorem rowLaw_eq (a : Data) : rowLaw a=StoredWeightedState.lawBytes (final a).law := rfl

theorem record_tuples (a : Data) (i : Fin 7) :
    BankFieldProjection.result (2 : Fin 3)
      (BankFieldProjection.result (1 : Fin 2) (record a i))=
        StoredSourcePhase.tupleBytes (call a i) := by
  simp [record,StoredSourcePhase.output]

theorem record_law (a : Data) (i : Fin 7) :
    BankFieldProjection.result (1 : Fin 3)
      (BankFieldProjection.result (1 : Fin 2) (record a i))=
        StoredSourcePhase.lawBytes (call a i) := by
  simp [record,StoredSourcePhase.output]

end
end CurrentAdditive.StoredRoundProjection

#print axioms CurrentAdditive.StoredRoundProjection.sourcePacket_eq
#print axioms CurrentAdditive.StoredRoundProjection.rowLaw_eq
