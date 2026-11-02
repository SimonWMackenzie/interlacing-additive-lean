import CurrentAdditive.StoredSourcePhase
import CurrentAdditive.V40ActualSevenRequests
import CurrentAdditive.StoredStepContext

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
namespace CurrentAdditive.StoredRoundData
open Paper2 EthInapproximability.CurrentPaper V39GeneratedConstruction
noncomputable section

structure Data where
  parameters : V40ActualSevenRequests.Data
  activity : Fin parameters.ni → Fin parameters.q₂ → Option (Fin parameters.s)

def input (a : Data) := StoredStepContext.packet a.parameters.q₁ a.parameters.w a.parameters.Q
  a.parameters.μI a.activity a.parameters.R
def src (a : Data) := V40ActualSevenRequests.src a.parameters
def streams (a : Data) := V40ActualSevenRequests.streams a.parameters
def final (a : Data) := SourceData.final (Q := a.parameters.Q) (w := a.parameters.w)
  (executableCodeD 8192) (src a)

def gamma (a : Data) : StoredSourcePhase.Data :=
  ⟨a.parameters.q₁+a.parameters.s+1,a.parameters.R.cols,a.parameters.R.colLaw⟩
def inner (a : Data) : StoredSourcePhase.Data :=
  ⟨a.parameters.q₂,a.parameters.q₁*a.parameters.R.rows,
    reindex finProdFinEquiv (product (uniform a.parameters.q₁) a.parameters.R.rowLaw)⟩
def outer (a : Data) : StoredSourcePhase.Data :=
  ⟨a.parameters.s,a.parameters.q₂*(src a).gamma.size,
    reindex finProdFinEquiv (product (uniform a.parameters.q₂) (src a).gamma.law)⟩
def metadata (a : Data) : StoredSourcePhase.Data :=
  ⟨a.parameters.w,a.parameters.s+a.parameters.ni,
    reindex finSumFinEquiv (mixture (uniform a.parameters.s) a.parameters.μI)⟩
def base (a : Data) : StoredSourcePhase.Data :=
  ⟨a.parameters.w,a.parameters.R.rows,a.parameters.R.rowLaw⟩
def selector (a : Data) : StoredSourcePhase.Data :=
  ⟨a.parameters.w,(src a).inner.size,(src a).inner.law⟩
def seventh (a : Data) : StoredSourcePhase.Data :=
  ⟨a.parameters.Q,a.parameters.w*((src a).outer.size*(src a).gamma.size+a.parameters.q₂*(src a).gamma.size),
    reindex ((Equiv.prodCongr (Equiv.refl _) (src a).columnOrder).trans finProdFinEquiv)
      (product (uniform a.parameters.w) (src a).columnLaw)⟩

def call (a : Data) (i : Fin 7) : StoredSourcePhase.Data := match i.val with
  | 0 => gamma a
  | 1 => inner a
  | 2 => outer a
  | 3 => metadata a
  | 4 => base a
  | 5 => selector a
  | _ => seventh a

def record (a : Data) (i : Fin 7) := BitMachineBankCodec.encode
  ![V40ActualSevenRequests.output a.parameters i,StoredSourcePhase.output (call a i)]

def state (a : Data) (k : Nat) := BitMachineBankCodec.encode
  (fun j : Fin 8 => if j.val=0 then input a else
    if h : 0<j.val ∧ j.val≤k then record a ⟨j.val-1,by have:=j.isLt;omega⟩ else [])

theorem state_input (a : Data) (k : Nat) :
    BankFieldProjection.result (0 : Fin 8) (state a k)=input a := by simp [state]

theorem state_record (a : Data) (i : Fin 7) (k : Nat) (hi : i.val<k) :
    BankFieldProjection.result (⟨i.val+1,by have:=i.isLt;omega⟩ : Fin 8) (state a k)=record a i := by
  simp [state,hi,show i.val+1≤k by omega]

theorem phase_input_eq (a : StoredSourcePhase.Data) : StoredSourcePhase.input a=
    V40LawCodeDPacket.codeDInput a.q (IndexedLaw.indexedAlphabet a.law.weight) := by
  simp [StoredSourcePhase.input,V40LawCodeDPacket.codeDInput,StoredWeightedState.lawBytes,
    StoredWeightedState.lawAlphabet,IndexedLaw.indexedAlphabet,V40LawJobsClock.packet_eq]

theorem request_eq (a : Data) (i : Fin 7) :
    V40ActualSevenRequests.rawRequest a.parameters i=StoredSourcePhase.input (call a i) := by
  rw [phase_input_eq]
  fin_cases i
  · simpa only [call,gamma] using V40ActualSevenRequests.gamma_request a.parameters
  · simpa only [call,inner] using V40ActualSevenRequests.inner_request a.parameters
  · simpa only [call,outer,src] using V40ActualSevenRequests.outer_request a.parameters
  · simpa only [call,metadata] using V40ActualSevenRequests.metadata_request a.parameters
  · simpa only [call,base] using V40ActualSevenRequests.base_request a.parameters
  · simpa only [call,selector,src] using V40ActualSevenRequests.selector_request a.parameters
  · simpa only [call,seventh,src] using V40ActualSevenRequests.final_request a.parameters

end
end CurrentAdditive.StoredRoundData

#print axioms CurrentAdditive.StoredRoundData.request_eq
