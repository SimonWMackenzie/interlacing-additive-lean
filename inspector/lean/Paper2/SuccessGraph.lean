import Paper2.SuccessFull

/-! Unit 3, segment (5): the producer of the unary edge count `m` in the master region.

The master region of the writer bank holds, inside `SrcU.JJ0 g r`, the literal public graph
bytes `EncodedGraph.encode g` (the start bank of the admitted `PublicGraphEndpointMachine`) and
the unary edge count `m = g.edges.length` (decode cell 2). Here `m` is PRODUCED from the literal
graph bytes by the admitted `PublicGraphEndpointMachine.physical_run_public` on a private side
region `PS = PublicGraphEndpointMachine.Stack`:

`graphProg = copy (graph bytes → PS input) ; PublicGraphEndpointMachine.program (on PS) ;
copy (PS unary-`m` cell → master decode cell 2)` (ONE fixed program; every handoff one charged
step; both copies source-preserving; the side region ends EXACTLY at the admitted
`PublicGraphEndpointMachine.resultBank g hg`).

`success_run_graph`: `fullProg2 = graphProg ; fullProg` (lifted), from the admitted success start
bank beside `preJHm g r thr output = preJH0 g r thr output` with the unary-`m` cell BLANK, and a
blank side region, halts with `EncodedSelectedOutput.outputBits hn edge Δ γ k tp ++ output` in
the header output cell (all conclusions of `SuccessInstall.success_run_installed`). -/

set_option maxHeartbeats 64000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.SuccessGraph

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open GeneratorCode GeneratorSerialization GeneratorSource GeneratorFullSample
open RecursiveSamplingProgram RecursiveSamplingLaws RecursiveLabelCodecScratch
open RecursiveEntries RecursiveSampling RecursiveRequestCodeShape
open SourceProfileParameters SourceRecursiveNoSampling TotalFiniteConstructorScratch
open Paper2.HeaderJoin (JH hjIn hjProg wOut thrM scrH)
open Paper2.SuccessXfer (OS JT xLmax)
open Paper2.SuccessRun (preJH hCtl succProg)
open Paper2.SuccessInstall (mC preJH0 master0 auxPre0 instBd install fullProg)

abbrev PS := PublicGraphEndpointMachine.Stack
abbrev JT2 := JT ⊕ PS

/-- Master cell holding the literal graph bytes (endpoint-machine input cell). -/
def zG : SrcX.JX := .inl (.inr (.inl (.inr (.inl (.inl (.inl (.inl (.inl 0))))))))
/-- Master decode cell 2 (unary `m`). -/
def zM : SrcX.JX := .inl (.inr (.inl (.inl 2)))

def gIn : PS := .inl (.inl 0)
def mOut : PS := .inl (.inr 1)
def scr2 : JT2 := .inl (.inr (.inr 0))

def lj (a : JH WEntry.Kw) : JT2 := .inl (.inr (.inl a))

def cp1 : Fin 1 → (Fin 3 ↪ JT2) := fun _ =>
  ⟨![lj (mC zG), .inr gIn, scr2], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [lj, scr2]⟩

def cp3 : Fin 1 → (Fin 3 ↪ JT2) := fun _ =>
  ⟨![.inr mOut, lj (mC zM), scr2], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [lj, scr2]⟩

def ιP : PS ↪ JT2 := ⟨Sum.inr, Sum.inr_injective⟩
def ιL : JT ↪ JT2 := ⟨Sum.inl, Sum.inl_injective⟩

theorem bank_P (X : JT → List Bool) (Y Z : PS → List Bool) :
    bank ιP (Sum.elim X Y) Z = Sum.elim X Z := by
  funext c
  rcases c with c | c
  · exact bank_outside ιP _ Z (.inl c) (by rintro ⟨k, hk⟩; cases hk)
  · exact bank_at ιP _ Z c

theorem bank_L (X Z : JT → List Bool) (Y : PS → List Bool) :
    bank ιL (Sum.elim X Y) Z = Sum.elim Z Y := by
  funext c
  rcases c with c | c
  · exact bank_at ιL _ Z c
  · exact bank_outside ιL _ Z (.inr c) (by rintro ⟨k, hk⟩; cases hk)

def graphL := fun l => stackStmt ιP (PublicGraphEndpointMachine.program l)
def fullL := fun l => stackStmt ιL (fullProg l)

def gCtl := ((none : Option Bool), PublicGraphEndpointMachine.parserControl)

def g1 := BitMachineRawSequence.program (CopyAll.prog cp1) graphL
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) (none : Option Bool) gCtl
def graphProg := BitMachineRawSequence.program g1 (CopyAll.prog cp3) (.inl ⟨0, by omega⟩)
  ((none : Option Bool), gCtl) (none : Option Bool)

def fStart := SamplerFallbackJoin.labelOf fullL
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)))
def fCtl := (((none : Option Bool), (none : Option Bool)),
  (SuccessOrient.startControl, ((none : Option Bool), hCtl)))

/-- ONE fixed program: produce `m`, then the whole success branch. -/
def fullProg2 := BitMachineRawSequence.program graphProg fullL fStart
  (((none : Option Bool), gCtl), (none : Option Bool)) fCtl

/-- The writer start bank with the unary-`m` cell blank. -/
def preJHm (g : EncodedGraph.Graph) (r thr : ℕ) (output : List Bool) :
    JH WEntry.Kw → List Bool :=
  Function.update (preJH0 g r thr output) (mC zM) []

theorem preJH0_zG (g : EncodedGraph.Graph) (r thr : ℕ) (output : List Bool) :
    preJH0 g r thr output (mC zG) = EncodedGraph.encode g := by
  change auxPre0 g r (WEntry.eqv.symm (WEntry.eqv _)) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem preJH0_zM (g : EncodedGraph.Graph) (r thr : ℕ) (output : List Bool) :
    preJH0 g r thr output (mC zM) = List.replicate g.edges.length true := by
  change auxPre0 g r (WEntry.eqv.symm (WEntry.eqv _)) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem zG_ne_zM : mC zG ≠ mC zM := by
  simp [mC, SuccessXfer.wAux, RLoop.mX, zG, zM]

theorem graph_run (g : EncodedGraph.Graph) (hg : g.Valid) (X : OS → List Bool)
    (r thr : ℕ) (output : List Bool) :
    ∃ t ≤ (1 * (2 * (EncodedGraph.encode g).length + 3) + 1) +
        103 * ((EncodedGraph.encode g).length + 1) ^ 3 + 1 +
        (1 * (2 * g.edges.length + 3) + 1) + 1, ∃ v : Option Bool,
      ((advance graphProg)^[t])
          (⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
              (.inl ⟨0, by omega⟩))),
            (((none : Option Bool), gCtl), (none : Option Bool)),
            Sum.elim (Sum.elim X (Sum.elim (preJHm g r thr output) (fun _ => [])))
              (fun _ => [])⟩ : TM2.Cfg (fun _ : JT2 => Bool) _ _) =
        ⟨none, (((none : Option Bool), gCtl), v),
          Sum.elim (Sum.elim X (Sum.elim (preJH0 g r thr output) (fun _ => [])))
            (PublicGraphEndpointMachine.resultBank g hg)⟩ := by
  let T0 : JT2 → List Bool :=
    Sum.elim (Sum.elim X (Sum.elim (preJHm g r thr output) (fun _ => []))) (fun _ => [])
  -- (1) copy the graph bytes into the side region
  have hG : T0 (lj (mC zG)) = EncodedGraph.encode g := by
    change preJHm g r thr output (mC zG) = _
    rw [preJHm, Function.update_of_ne zG_ne_zM, preJH0_zG]
  obtain ⟨t1, ht1, v1, hr1⟩ := CopyAll.all_run cp1
    (by intro i j h; fin_cases i; fin_cases j; cases h)
    (by intro i j h; fin_cases i; fin_cases j; cases h)
    (by intro i j _; fin_cases i; fin_cases j; rfl)
    T0 (by intro i; fin_cases i; rfl) (EncodedGraph.encode g).length
    (by intro i; fin_cases i; exact le_of_eq (congrArg List.length hG)) none
  have hD1 : CopyAll.done cp1 1 T0 =
      Sum.elim (Sum.elim X (Sum.elim (preJHm g r thr output) (fun _ => [])))
        (PublicGraphEndpointMachine.initialBank (EncodedGraph.encode g)) := by
    funext x
    by_cases hx : x = .inr gIn
    · subst hx
      change CopyAll.done cp1 1 T0 (cp1 0 1) = _
      rw [CopyAll.done_dst cp1 (by intro i j _; fin_cases i; fin_cases j; rfl) T0 0]
      change T0 (lj (mC zG)) ++ [] = _
      rw [hG, List.append_nil]
      rfl
    · rw [CopyAll.done_off cp1 T0 x (by intro j h; fin_cases j; exact hx h.symm)]
      rcases x with x | x
      · rfl
      · change [] = PublicGraphEndpointMachine.initialBank (EncodedGraph.encode g) x
        rcases x with (y | y) | y
        · fin_cases y
          · exact absurd rfl hx
          all_goals rfl
        · fin_cases y <;> rfl
        · fin_cases y <;> rfl
  rw [hD1] at hr1
  -- (2) the admitted public-graph endpoint machine on the side region
  obtain ⟨t2, ht2, hr2⟩ := PublicGraphEndpointMachine.physical_run_public g hg
  have r2 := BitMachineStackRun.run ιP
    (Sum.elim (Sum.elim X (Sum.elim (preJHm g r thr output) (fun _ => []))) (fun _ => []))
    PublicGraphEndpointMachine.program (PublicGraphEndpointMachine.start (EncodedGraph.encode g))
    t2
  change _ = stackCfg ιP _ (PublicGraphEndpointMachine.run t2 _) at r2
  rw [hr2] at r2
  simp only [stackCfg, PublicGraphEndpointMachine.start] at r2
  rw [bank_P, bank_P] at r2
  obtain ⟨u1, hu1, ru1⟩ := BitMachineRawSequence.runs (CopyAll.prog cp1) graphL
    (.inl ⟨0, by omega⟩) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (none : Option Bool) v1 gCtl (none, SourceNormalizationMachineDecode.doneControl true)
    _ _ _ t1 t2 hr1 r2
  -- (3) copy unary m into the master decode cell 2
  let T2 : JT2 → List Bool :=
    Sum.elim (Sum.elim X (Sum.elim (preJHm g r thr output) (fun _ => [])))
      (PublicGraphEndpointMachine.resultBank g hg)
  have hM : T2 (.inr mOut) = List.replicate g.edges.length true := rfl
  obtain ⟨t3, ht3, v3, hr3⟩ := CopyAll.all_run cp3
    (by intro i j h; fin_cases i; fin_cases j; cases h)
    (by intro i j h; fin_cases i; fin_cases j; cases h)
    (by intro i j _; fin_cases i; fin_cases j; rfl)
    T2 (by intro i; fin_cases i; rfl) g.edges.length
    (by
      intro i
      fin_cases i
      change (T2 (.inr mOut)).length ≤ _
      rw [hM, List.length_replicate]) none
  have hD3 : CopyAll.done cp3 1 T2 =
      Sum.elim (Sum.elim X (Sum.elim (preJH0 g r thr output) (fun _ => [])))
        (PublicGraphEndpointMachine.resultBank g hg) := by
    funext x
    by_cases hx : x = lj (mC zM)
    · subst hx
      change CopyAll.done cp3 1 T2 (cp3 0 1) = _
      rw [CopyAll.done_dst cp3 (by intro i j _; fin_cases i; fin_cases j; rfl) T2 0]
      change T2 (.inr mOut) ++ preJHm g r thr output (mC zM) = preJH0 g r thr output (mC zM)
      rw [hM, preJHm, Function.update_self, List.append_nil, preJH0_zM]
    · rw [CopyAll.done_off cp3 T2 x (by intro j h; fin_cases j; exact hx h.symm)]
      rcases x with (x | x | x) | x
      · rfl
      · change preJHm g r thr output x = preJH0 g r thr output x
        rw [preJHm, Function.update_of_ne]
        intro h
        exact hx (by rw [h]; rfl)
      · rfl
      · rfl
  rw [hD3] at hr3
  obtain ⟨u, hu, ru⟩ := BitMachineRawSequence.runs g1 (CopyAll.prog cp3)
    (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩)) (.inl ⟨0, by omega⟩)
    ((none : Option Bool), gCtl) ((none : Option Bool),
      (none, SourceNormalizationMachineDecode.doneControl true))
    (none : Option Bool) v3 _ _ _ u1 t3 ru1 hr3
  refine ⟨u, ?_, v3, ru⟩
  omega

end

#print axioms preJH0_zG
#print axioms preJH0_zM
#print axioms graph_run

end Paper2.SuccessGraph
