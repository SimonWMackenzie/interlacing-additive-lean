import CurrentAdditive.V39WPreparedTable
import CurrentAdditive.V39WHeaderExact

/-! Preparation, actual current table evaluation, and physical dimension/
threshold serialization on one fixed bank and one fixed instruction table.
The complete final bank is explicit; the output is an encoded instance. -/
namespace CurrentAdditive.V39WEncodedTable
noncomputable section
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384
open Paper2 Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding EncodedCommunication
open Paper2.RecursiveEntries
open V39WEntry
open V39WTablePrepare (WriterStack sourceWords)

abbrev Stack := Fin 14 ⊕ (HeaderJoin.JH Kw ⊕ Fin 1)
local instance : DecidableEq (HeaderJoin.JH Kw) := Classical.decEq _
local instance : DecidableEq Stack := Classical.decEq _
def prepSlots : V39WTablePrepare.Stack ↪ Stack where
  toFun
    | .inl i => .inl i
    | .inr (.inl j) => .inr (.inl (.inl j))
    | .inr (.inr i) => .inr (.inr i)
  inj' := by
    intro a b h
    rcases a with i | (j | i) <;> rcases b with i | (j | i) <;> simp_all
def headerSlots : HeaderJoin.JH Kw ↪ Stack :=
  ⟨fun j => .inr (.inl j),by intro a b h; cases h; rfl⟩
def outputPort : Stack := headerSlots HeaderJoin.wOut
def thresholdPort : Stack := headerSlots HeaderJoin.thrM

def prepareProgram := fun l => stackStmt prepSlots (V39WPreparedTable.program l)
def headerProgram := fun l => stackStmt headerSlots (HeaderJoin.hjProg Kw l)
def headerControl := ((none:Option Bool),HeaderA.progCtl)
def program := BitMachineRawSequence.program prepareProgram headerProgram
  (BitMachineRawSequence.leftLabel (.inl (0:Fin 4) : CopyAll.Lab 3))
  V39WPreparedTable.control headerControl
def start := FetchIndexed.labelOf program (BitMachineRawSequence.leftLabel V39WPreparedTable.start)
def control := (V39WPreparedTable.control,headerControl)

def bankIn (S : Fin 14 → List Bool) (WB : WriterStack → List Bool) (thr : Nat) : Stack → List Bool :=
  Sum.elim S (Sum.elim (HeaderJoin.hjIn WB thr) (fun _ => []))
def initial (S : Fin 14 → List Bool) (thr : Nat) : Stack → List Bool := bankIn S (fun _ => []) thr
def final (S : Fin 14 → List Bool) (WB : WriterStack → List Bool)
    (rows cols thr : Nat) (table : List Bool) : Stack → List Bool :=
  Sum.elim S (Sum.elim (V39WHeaderExact.finalBank WB rows cols thr table []) (fun _ => []))

theorem bank_prep (S : Fin 14 → List Bool) (T U : WriterStack → List Bool) (thr : Nat) :
    bank prepSlots (bankIn S T thr) (V39WTablePrepare.final S U)=bankIn S U thr := by
  funext z
  rcases z with i | ((j | h) | i)
  · exact bank_at prepSlots _ _ (.inl i)
  · exact bank_at prepSlots _ _ (.inr (.inl j))
  · rw [bank_outside prepSlots _ _ _ (by
      rintro ⟨a,ha⟩
      rcases a with i | (j | i) <;> cases ha)]
    rfl
  · exact bank_at prepSlots _ _ (.inr (.inr i))

theorem bank_header (S : Fin 14 → List Bool) (WB : WriterStack → List Bool)
    (thr : Nat) (F : HeaderJoin.JH Kw → List Bool) :
    bank headerSlots (bankIn S WB thr) F = Sum.elim S (Sum.elim F (fun _ => [])) := by
  funext z
  rcases z with i | (j | i)
  · rw [bank_outside headerSlots _ _ _ (by rintro ⟨j,h⟩; cases h)]
    rfl
  · exact bank_at headerSlots _ _ j
  · rw [bank_outside headerSlots _ _ _ (by rintro ⟨j,h⟩; cases h)]
    rfl

theorem final_word (S : Fin 14 → List Bool) (WB : WriterStack → List Bool)
    (rows cols thr : Nat) (table : List Bool) :
    final S WB rows cols thr table outputPort=
      encodeInstance ⟨rows,cols,thr,table⟩ := by
  change V39WHeaderExact.finalBank WB rows cols thr table [] HeaderJoin.wOut=_
  rw [V39WHeaderExact.final_out]
  simp [encodeInstance]

variable {p s q₁ q₂ w Q : Nat} [NeZero q₁] [NeZero q₂]
  [NeZero w] [NeZero Q] [NeZero s]

theorem physical_encoded (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hp : 0 < p) (hs : 4 ≤ s) (r : Nat)
    (hq : q₂ = LiteralEdgeEncoder.Width s g.edges.length r)
    (ξ : Tails (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin g.vertices)) s q₁ q₂ w Q)
    (K m thr : Nat)
    (xs : Fin m → V39RecursiveGenerator.Row g.vertices p q₁ q₂ s w Q K)
    (ys : Fin m → V39RecursiveGenerator.Column g.vertices p q₁ q₂ s w Q K) :
    let S := sourceWords g r K m xs ys
    let activity := V39EdgeSourceFront.edgeActivity g hg (by omega) r hq
    let f : Fin m → Fin m → Bool := fun i j => V39RecursiveTable.matrix activity K (xs i) (ys j)
    let WB := (MatrixTableWriter.ready (bankW g r K m m xs ys) m m 0 0 0 0 []
      (MatrixMaterialization.rowMajor f)).contents
    ∃ t ≤ V39WTablePrepare.clock S+
        MatrixTableWriter.writerBound m m (Tent g hg hs r hq ξ K m m xs ys)+
        V39WHeaderExact.clock m m thr+2, ∃ v,
      ((advance program)^[t])
        (⟨some start,control,initial S thr⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,v,final S WB m m thr (MatrixMaterialization.rowMajor f)⟩ := by
  intro S activity f WB
  obtain ⟨a,ha,va,hprepare⟩ := V39WPreparedTable.physical_table g hg hp hs r hq ξ K m xs ys
  have hpL := HeaderJoin.liftG prepSlots V39WPreparedTable.program (initial S thr)
    (V39WTablePrepare.initial S) (V39WTablePrepare.final S WB)
    (by intro z; rcases z with i | (j | i) <;> rfl) _ _ _ _ hprepare
  rw [show initial S thr=bankIn S (fun _ => []) thr from rfl,bank_prep] at hpL
  obtain ⟨b,hb,hheader⟩ := V39WHeaderExact.physical_header WB m m thr
    (MatrixMaterialization.rowMajor f) [] rfl rfl (by simp only [List.append_nil]; rfl)
  have hhL := HeaderJoin.liftG headerSlots (HeaderJoin.hjProg Kw) (bankIn S WB thr)
    (HeaderJoin.hjIn WB thr) (V39WHeaderExact.finalBank WB m m thr (MatrixMaterialization.rowMajor f) [])
    (by intro j; rfl) _ _ _ _ hheader
  rw [bank_header] at hhL
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs prepareProgram headerProgram
    V39WPreparedTable.start (BitMachineRawSequence.leftLabel (.inl (0:Fin 4) : CopyAll.Lab 3))
    V39WPreparedTable.control va headerControl headerControl _ _ _ a b hpL hhL
  change a ≤ V39WTablePrepare.clock S+
    MatrixTableWriter.writerBound m m (Tent g hg hs r hq ξ K m m xs ys)+1 at ha
  exact ⟨t,by omega,(V39WPreparedTable.control,headerControl),by
    simpa only [program,start,control,final,FetchIndexed.labelOf] using hr⟩

#print axioms bank_prep
#print axioms final_word
#print axioms physical_encoded
end
end CurrentAdditive.V39WEncodedTable
