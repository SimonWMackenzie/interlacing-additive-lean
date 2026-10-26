import CurrentAdditive.StoredRoundSources

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
namespace CurrentAdditive.StoredRoundProjection
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction
open StoredRoundData
noncomputable section

theorem productCompanions_eq {m n : Nat} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) : V40LawJobOrder.companions μ ν=
      SourceListEncoding.encode (StoredCellBytes.productCompanions m n) :=
  V40LawJobOrder.companions_exact μ ν

theorem mixtureCompanions_eq {m n : Nat} (μ : PositiveRationalLaw (Fin m))
    (ν : PositiveRationalLaw (Fin n)) : V40LawMixtureOrder.companions μ ν=
      SourceListEncoding.encode (StoredCellBytes.sumCompanions m n) := by
  rw [V40LawMixtureOrder.companions_exact]
  have hcast (h : m ≤ m+n) (i : Fin m) :
      finSumFinEquiv.symm (Fin.castLE h i)=Sum.inl i := by
    have he : Fin.castLE h i=i.castAdd n := by apply Fin.ext;rfl
    rw [he]
    exact finSumFinEquiv_symm_apply_castAdd i
  simp [StoredCellBytes.sumCompanions,List.ofFn_add,
    hcast,finSumFinEquiv_symm_apply_natAdd]

def builderComp (a : Data) (i : Fin 7) := BankFieldProjection.result (2 : Fin 3)
  (V40ActualSevenRequests.output a.parameters i)

def columnTree (a : Data) := BankFieldProjection.result (0 : Fin 2) (builderComp a 6)

def companionPacket (a : Data) := BitMachineBankCodec.encode
  ![builderComp a 1,builderComp a 2,builderComp a 3,
    BankFieldProjection.result (0 : Fin 3) (columnTree a),
    BankFieldProjection.result (2 : Fin 3) (columnTree a),
    BankFieldProjection.result (1 : Fin 2) (builderComp a 6)]

theorem inner_comp (a : Data) : builderComp a 1=SourceListEncoding.encode
    (StoredCellBytes.productCompanions a.parameters.q₁ a.parameters.R.rows) := by
  simp only [builderComp,V40ActualSevenRequests.output,V40UniformLawJobs.output,
    BankFieldProjection.result_encode,Matrix.cons_val_two,V40UniformLawJobs.companions,
    Bool.false_eq_true,if_false]
  exact productCompanions_eq _ _

theorem outer_comp (a : Data) : builderComp a 2=SourceListEncoding.encode
    (StoredCellBytes.productCompanions a.parameters.q₂ (src a).gamma.size) := by
  simp only [builderComp,V40ActualSevenRequests.output,V40UniformLawJobs.output,
    BankFieldProjection.result_encode,Matrix.cons_val_two,V40UniformLawJobs.companions,
    Bool.false_eq_true,if_false]
  exact productCompanions_eq _ _

theorem metadata_comp (a : Data) : builderComp a 3=SourceListEncoding.encode
    (StoredCellBytes.sumCompanions a.parameters.s a.parameters.ni) := by
  simp only [builderComp,V40ActualSevenRequests.output,V40UniformLawJobs.output,
    BankFieldProjection.result_encode,Matrix.cons_val_two,V40UniformLawJobs.companions,
    if_true]
  exact mixtureCompanions_eq _ _

theorem columnTree_eq (a : Data) : columnTree a=
    V40FinalSourceRequest.columnComp (V40ActualSevenRequests.finalData a.parameters) := by
  simp [columnTree,builderComp,V40ActualSevenRequests.output,V40FinalSourceRequest.output,
    V40LawJobsClock.packet_eq]

theorem column_ordinary_comp (a : Data) : BankFieldProjection.result (0 : Fin 3) (columnTree a)=
    SourceListEncoding.encode (StoredCellBytes.productCompanions (src a).outer.size (src a).gamma.size) := by
  rw [columnTree_eq]
  simp only [V40FinalSourceRequest.columnComp,BankFieldProjection.result_encode,Matrix.cons_val_zero,
    V40SourceColumnLaw.firstComp]
  exact productCompanions_eq _ _

theorem column_diagonal_comp (a : Data) : BankFieldProjection.result (1 : Fin 3) (columnTree a)=
    SourceListEncoding.encode (StoredCellBytes.productCompanions a.parameters.q₂ (src a).gamma.size) := by
  rw [columnTree_eq]
  simp only [V40FinalSourceRequest.columnComp,BankFieldProjection.result_encode,Matrix.cons_val_one,
    V40SourceColumnLaw.secondComp]
  exact productCompanions_eq _ _

theorem column_diagonal_reuses_outer (a : Data) :
    BankFieldProjection.result (1 : Fin 3) (columnTree a)=builderComp a 2 := by
  rw [column_diagonal_comp,outer_comp]

theorem column_mixture_comp (a : Data) : BankFieldProjection.result (2 : Fin 3) (columnTree a)=
    SourceListEncoding.encode (StoredCellBytes.sumCompanions
      ((src a).outer.size*(src a).gamma.size) (a.parameters.q₂*(src a).gamma.size)) := by
  rw [columnTree_eq]
  simp only [V40FinalSourceRequest.columnComp,BankFieldProjection.result_encode,Matrix.cons_val_two,
    V40SourceColumnLaw.mixComp]
  exact mixtureCompanions_eq _ _

theorem uniform_comp (a : Data) : BankFieldProjection.result (1 : Fin 2) (builderComp a 6)=
    SourceListEncoding.encode (StoredCellBytes.productCompanions a.parameters.w
      ((src a).outer.size*(src a).gamma.size+a.parameters.q₂*(src a).gamma.size)) := by
  simp [builderComp,V40ActualSevenRequests.output,V40FinalSourceRequest.output,
    V40LawJobsClock.packet_eq,V40FinalSourceRequest.uniformComp,productCompanions_eq]
  rfl

theorem companionPacket_eq (a : Data) :
    companionPacket a=StoredCellBytes.companions (src a) (ni := a.parameters.ni) (w := a.parameters.w) := by
  unfold companionPacket StoredCellBytes.companions
  rw [inner_comp,outer_comp,metadata_comp,column_ordinary_comp,column_mixture_comp,uniform_comp]

theorem record_builderComp (a : Data) (i : Fin 7) :
    BankFieldProjection.result (2 : Fin 3)
      (BankFieldProjection.result (0 : Fin 2) (record a i))=builderComp a i := by
  simp [record,builderComp]

end
end CurrentAdditive.StoredRoundProjection

#print axioms CurrentAdditive.StoredRoundProjection.companionPacket_eq
