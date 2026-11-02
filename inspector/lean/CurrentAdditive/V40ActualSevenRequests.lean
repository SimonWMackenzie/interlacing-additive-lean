import CurrentAdditive.V40DirectLawRequest
import CurrentAdditive.V40FinalSourceRequest
import CurrentAdditive.V40SuccessorColumnLaw

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40ActualSevenRequests
open EthInapproximability.CurrentPaper
open Paper2 V39GeneratedConstruction V40LawJobsClock
noncomputable section

structure Data where
  q₁ : ℕ
  q₂ : ℕ
  s : ℕ
  w : ℕ
  Q : ℕ
  ni : ℕ
  hq₁ : 0<q₁
  hq₂ : 0<q₂
  hs : 0<s
  hw : 0<w
  hQ : 0<Q
  μI : PositiveRationalLaw (Fin ni)
  R : StoredMatrix

instance (a : Data) : NeZero a.q₁ := ⟨Nat.ne_of_gt a.hq₁⟩
instance (a : Data) : NeZero a.q₂ := ⟨Nat.ne_of_gt a.hq₂⟩
instance (a : Data) : NeZero a.s := ⟨Nat.ne_of_gt a.hs⟩
instance (a : Data) : NeZero a.w := ⟨Nat.ne_of_gt a.hw⟩
instance (a : Data) : NeZero a.Q := ⟨Nat.ne_of_gt a.hQ⟩

def src (a : Data) := sourceData (q₁ := a.q₁) (q₂ := a.q₂) (s := a.s)
  (executableCodeD 8192) a.R.rowLaw a.R.colLaw
def streams (a : Data) := SourceData.streams (w := a.w) (μI := a.μI) (executableCodeD 8192) (src a)

def gammaData (a : Data) : V40DirectLawRequest.Data := ⟨a.q₁+a.s+1,a.R.cols,a.R.colLaw⟩
def innerData (a : Data) : V40UniformLawJobs.Data := ⟨a.q₂,a.q₁,a.R.rows,a.hq₁,a.R.rowLaw⟩
def outerData (a : Data) : V40UniformLawJobs.Data := ⟨a.s,a.q₂,(src a).gamma.size,a.hq₂,(src a).gamma.law⟩
def metadataData (a : Data) : V40UniformLawJobs.Data := ⟨a.w,a.s,a.ni,a.hs,a.μI⟩
def baseData (a : Data) : V40DirectLawRequest.Data := ⟨a.w,a.R.rows,a.R.rowLaw⟩
def selectorData (a : Data) : V40DirectLawRequest.Data := ⟨a.w,(src a).inner.size,(src a).inner.law⟩
def finalData (a : Data) : V40FinalSourceRequest.Data :=
  ⟨a.Q,a.w,a.q₂,(src a).outer.size,(src a).gamma.size,a.hw,a.hq₂,(src a).outer.law,(src a).gamma.law⟩
def successorData (a : Data) : V40SuccessorColumnLaw.Data :=
  ⟨a.Q,(streams a).metadata.size,(streams a).base.size,(streams a).selector.size,a.hQ,
    (streams a).metadata.law,(streams a).base.law,(streams a).selector.law⟩

/-- The seven fixed request builders, in their actual construction order. -/
def machine (i : Fin 7) : BitMachine.Machine := match i.val with
  | 0 => V40DirectLawRequest.machine
  | 1 => V40UniformLawJobs.machine false
  | 2 => V40UniformLawJobs.machine false
  | 3 => V40UniformLawJobs.machine true
  | 4 => V40DirectLawRequest.machine
  | 5 => V40DirectLawRequest.machine
  | _ => V40FinalSourceRequest.machine
def input (a : Data) (i : Fin 7) : List Bool := match i.val with
  | 0 => V40DirectLawRequest.input (gammaData a)
  | 1 => V40UniformLawJobs.input (innerData a)
  | 2 => V40UniformLawJobs.input (outerData a)
  | 3 => V40UniformLawJobs.input (metadataData a)
  | 4 => V40DirectLawRequest.input (baseData a)
  | 5 => V40DirectLawRequest.input (selectorData a)
  | _ => V40FinalSourceRequest.input (finalData a)
def output (a : Data) (i : Fin 7) : List Bool := match i.val with
  | 0 => V40DirectLawRequest.output (gammaData a)
  | 1 => V40UniformLawJobs.output false (innerData a)
  | 2 => V40UniformLawJobs.output false (outerData a)
  | 3 => V40UniformLawJobs.output true (metadataData a)
  | 4 => V40DirectLawRequest.output (baseData a)
  | 5 => V40DirectLawRequest.output (selectorData a)
  | _ => V40FinalSourceRequest.output (finalData a)

theorem enlarge (M : BitMachine.Machine) (x y : List Bool) (c d C D : ℕ)
    (h : M.OutputsWithin x y (c*(x.length+1)^d)) (hc : c≤C) (hd : d≤D) :
    M.OutputsWithin x y (C*(x.length+1)^D) :=
  BitMachine.outputsWithin_mono _ h
    (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hd))

/-- One byte polynomial is chosen before all public counts, stored matrices,
actual source arrays, and the seven call positions. The source arrays here
are the literal executableCodeD8192 arrays through SourceData/Streams. -/
theorem requests_outputs : ∃ C d : ℕ, ∀ (a : Data) (i : Fin 7),
    (machine i).OutputsWithin (input a i) (output a i)
      (C*((input a i).length+1)^d) := by
  obtain ⟨c₀,d₀,h₀⟩ := V40DirectLawRequest.realizes
  obtain ⟨cp,dp,hp⟩ := V40UniformLawJobs.realizes false
  obtain ⟨cm,dm,hm⟩ := V40UniformLawJobs.realizes true
  obtain ⟨cf,df,hf⟩ := V40FinalSourceRequest.realizes
  refine ⟨c₀+cp+cm+cf,d₀+dp+dm+df,?_⟩
  intro a i
  fin_cases i
  · exact enlarge _ _ _ _ _ _ _ (h₀ (gammaData a)) (by omega) (by omega)
  · exact enlarge _ _ _ _ _ _ _ (hp (innerData a)) (by omega) (by omega)
  · exact enlarge _ _ _ _ _ _ _ (hp (outerData a)) (by omega) (by omega)
  · exact enlarge _ _ _ _ _ _ _ (hm (metadataData a)) (by omega) (by omega)
  · exact enlarge _ _ _ _ _ _ _ (h₀ (baseData a)) (by omega) (by omega)
  · exact enlarge _ _ _ _ _ _ _ (h₀ (selectorData a)) (by omega) (by omega)
  · exact enlarge _ _ _ _ _ _ _ (hf (finalData a)) (by omega) (by omega)

def rawRequest (a : Data) (i : Fin 7) := BankFieldProjection.result (1 : Fin 3) (output a i)

theorem gamma_request (a : Data) : rawRequest a 0=V40LawCodeDPacket.codeDInput
    (a.q₁+a.s+1) (IndexedLaw.indexedAlphabet a.R.colLaw.weight) := by
  simp [rawRequest,output,V40DirectLawRequest.output,gammaData]
theorem inner_request (a : Data) : rawRequest a 1=V40LawCodeDPacket.codeDInput
    a.q₂ (IndexedLaw.indexedAlphabet (reindex finProdFinEquiv (product (uniform a.q₁) a.R.rowLaw)).weight) := by
  simp [rawRequest,output,V40UniformLawJobs.output,V40UniformLawJobs.law,innerData,
    V40LawCodeDPacket.codeDInput,StoredWeightedState.lawBytes,StoredWeightedState.lawAlphabet,
    IndexedLaw.indexedAlphabet,packet_eq] <;> rfl
theorem outer_request (a : Data) : rawRequest a 2=V40LawCodeDPacket.codeDInput
    a.s (IndexedLaw.indexedAlphabet (reindex finProdFinEquiv (product (uniform a.q₂) (src a).gamma.law)).weight) := by
  simp [rawRequest,output,V40UniformLawJobs.output,V40UniformLawJobs.law,outerData,
    V40LawCodeDPacket.codeDInput,StoredWeightedState.lawBytes,StoredWeightedState.lawAlphabet,
    IndexedLaw.indexedAlphabet,packet_eq] <;> rfl
theorem metadata_request (a : Data) : rawRequest a 3=V40LawCodeDPacket.codeDInput
    a.w (IndexedLaw.indexedAlphabet (reindex finSumFinEquiv (mixture (uniform a.s) a.μI)).weight) := by
  simp [rawRequest,output,V40UniformLawJobs.output,V40UniformLawJobs.law,metadataData,
    V40LawCodeDPacket.codeDInput,StoredWeightedState.lawBytes,StoredWeightedState.lawAlphabet,
    IndexedLaw.indexedAlphabet,packet_eq] <;> rfl
theorem base_request (a : Data) : rawRequest a 4=V40LawCodeDPacket.codeDInput
    a.w (IndexedLaw.indexedAlphabet a.R.rowLaw.weight) := by
  simp [rawRequest,output,V40DirectLawRequest.output,baseData]
theorem selector_request (a : Data) : rawRequest a 5=V40LawCodeDPacket.codeDInput
    a.w (IndexedLaw.indexedAlphabet (src a).inner.law.weight) := by
  simp [rawRequest,output,V40DirectLawRequest.output,selectorData]
theorem final_request (a : Data) : rawRequest a 6=V40LawCodeDPacket.codeDInput
    a.Q (IndexedLaw.indexedAlphabet (reindex
      ((Equiv.prodCongr (Equiv.refl _) (src a).columnOrder).trans finProdFinEquiv)
      (product (uniform a.w) (src a).columnLaw)).weight) := by
  have hl := V40FinalSourceRequest.actual_law (w := a.w) (Q := a.Q) (src a)
  change V40FinalSourceRequest.law (finalData a)=_ at hl
  simp only [rawRequest,output,V40FinalSourceRequest.output,BankFieldProjection.result_encode,
    Matrix.cons_val_one,V40FinalSourceRequest.request,hl]
  simp [finalData,V40LawCodeDPacket.codeDInput,StoredWeightedState.lawBytes,
    StoredWeightedState.lawAlphabet,IndexedLaw.indexedAlphabet,packet_eq]
  rfl

theorem successor_column (a : Data) (activity : Fin a.ni → Fin a.q₂ → Option (Fin a.s)) :
    V40SuccessorColumnLaw.law (successorData a)=
    (executableStep (q₁ := a.q₁) (q₂ := a.q₂) (s := a.s) (w := a.w) (Q := a.Q)
      a.μI activity a.R.numbered).colLaw := by
  exact V40SuccessorColumnLaw.actual_column (src a) (streams a)

#print axioms requests_outputs
#print axioms final_request
#print axioms successor_column
end
end CurrentAdditive.V40ActualSevenRequests
