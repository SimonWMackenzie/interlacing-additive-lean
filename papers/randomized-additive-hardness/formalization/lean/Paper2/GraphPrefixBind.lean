import Paper2.PublicGraphEndpointMachine
import Paper2.CanonicalEdgePair

/-! Unit 3, segment (7) (map item 5 / "segment 3" of the map): the admitted
`PublicGraphEndpointMachine.physical_run_public` bound to the canonical
prefix parser (`CanonicalEdgePair.physical_prefix_pair`) as ONE fixed
program on ONE bank, with a charged conversion. From the literal public graph
bytes `EncodedGraph.encode g` and a unary edge-occurrence index `e` the
program
1. runs the admitted public-graph endpoint machine (copy + graph parser) to
   the canonical unary endpoint tape `word (graphEdge g hg)` and unary
   `n = g.vertices`;
2. copies (source-preserving) the endpoint tape into the parser's input
   cell and the unary `n` into its bound cell;
3. builds the parser's field count `2 (e + 1)` from the unary `e` (two
   source-preserving copies, two pushes);
4. runs the fixed prefix parser.
It halts with the selected edge's endpoint tokens `finCodec n` of
`graphEdge g hg e true` and `… e false` at the front of the parser output
cell. Every step is charged; the graph tape is copied, never consumed; no
graph function is hidden in the controller. The index `e` is an entry cell
(it is produced upstream by the coordinate decoding of `scanAtCanonical`,
which is NOT part of this segment). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.GraphPrefixBind

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)
open Paper2.CanonicalEdgeTape Paper2.CanonicalEdgePrefix Paper2.CanonicalEdgePair
open Paper2.UnaryFieldListParserScratch (tokens)

abbrev GS := PublicGraphEndpointMachine.Stack
/-- The bank: the endpoint machine's bank, the six parser cells, the unary
edge index and one copy scratch cell. -/
abbrev K := GS ⊕ (Fin 6 ⊕ Fin 2)

def verticesC : K := .inl (.inl (.inr 0))
def streamC : K := .inl (.inl (.inr 4))
def pC (i : Fin 6) : K := .inr (.inl i)
def eC : K := .inr (.inr 0)
def scrC : K := .inr (.inr 1)

def iG : GS ↪ K := ⟨Sum.inl, Sum.inl_injective⟩
def iP : Fin 6 ↪ K := ⟨fun i => pC i, fun a b h => by simpa [pC] using h⟩

def slots (a b : K) (h : Function.Injective ![a, b, scrC]) : Fin 3 ↪ K := ⟨![a, b, scrC], h⟩

def streamSlots : Fin 3 ↪ K := slots streamC (pC 0) (by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [streamC, pC, scrC])
def vertSlots : Fin 3 ↪ K := slots verticesC (pC 1) (by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [verticesC, pC, scrC])
def countSlots : Fin 3 ↪ K := slots eC (pC 2) (by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [eC, pC, scrC])

def pushT (k : K) : Unit → TM2.Stmt (fun _ : K => Bool) Unit Unit :=
  fun _ => push k (fun _ => true) halt

theorem pushT_run (k : K) (S : K → List Bool) :
    ((advance (pushT k))^[1]) (⟨some (), (), S⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, (), Function.update S k (true :: S k)⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, pushT]

def pge := fun l => stackStmt iG (PublicGraphEndpointMachine.program l)
def parserP := fun l => stackStmt iP (Paper2.UnaryFieldListParserScratch.program l)
def cpStream := MatrixStage4ScalarPreparationOps.copyProgram streamSlots
def cpVert := MatrixStage4ScalarPreparationOps.copyProgram vertSlots
def cpCount := MatrixStage4ScalarPreparationOps.copyProgram countSlots

abbrev oc := (none : Option Bool)
def c0 := ((none : Option Bool), PublicGraphEndpointMachine.parserControl)
def g1 := BitMachineRawSequence.program pge cpStream .scan c0 oc
def g2 := BitMachineRawSequence.program g1 cpVert .scan (c0, oc) oc
def g3 := BitMachineRawSequence.program g2 cpCount .scan ((c0, oc), oc) oc
def g4 := BitMachineRawSequence.program g3 cpCount .scan (((c0, oc), oc), oc) oc
def g5 := BitMachineRawSequence.program g4 (pushT (pC 2)) () ((((c0, oc), oc), oc), oc) ()
def g6 := BitMachineRawSequence.program g5 (pushT (pC 2)) () (((((c0, oc), oc), oc), oc), ())
  ()
/-- The binding program: ONE fixed program. -/
def program := BitMachineRawSequence.program g6 parserP .start
  ((((((c0, oc), oc), oc), oc), ()), ()) oc

def labelOf {L σ Kk : Type*} (_P : L → TM2.Stmt (fun _ : Kk => Bool) L σ) (l : L) : L := l

def startLabel := labelOf program
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
    (leftLabel BitMachineCopy.Label.scan))))))))

def startCtl := (((((((c0, oc), oc), oc), oc), ()), ()), oc)

/-- Banks with the endpoint machine's result on the left. -/
def Wv (g : EncodedGraph.Graph) (hg : g.Valid) (e : ℕ) (pv : Fin 6 → List Bool) :
    K → List Bool :=
  Sum.elim (PublicGraphEndpointMachine.resultBank g hg)
    (Sum.elim pv ![List.replicate e true, []])

/-- Entry bank: the literal public graph bytes (endpoint machine start bank),
the unary edge index `e`, everything else blank. -/
def initBank (g : EncodedGraph.Graph) (e : ℕ) : K → List Bool :=
  Sum.elim (PublicGraphEndpointMachine.initialBank (EncodedGraph.encode g))
    (Sum.elim (fun _ => []) ![List.replicate e true, []])

theorem upd_p (g : EncodedGraph.Graph) (hg : g.Valid) (e : ℕ) (pv : Fin 6 → List Bool)
    (i : Fin 6) (x : List Bool) :
    Function.update (Wv g hg e pv) (pC i) x = Wv g hg e (Function.update pv i x) := by
  rw [Wv, pC, Sum.update_elim_inr, Sum.update_elim_inl]; rfl

theorem lift {Kk L V : Type*} [DecidableEq Kk] (ι : Kk ↪ K)
    (P : L → TM2.Stmt (fun _ : Kk => Bool) L V)
    (W : K → List Bool) (S T : Kk → List Bool) (hS : ∀ k, S k = W (ι k)) (l : L) (v v' : V)
    (t : ℕ)
    (hrun : ((advance P)^[t]) (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) =
      ⟨none, v', T⟩) :
    ((advance (fun l => stackStmt ι (P l)))^[t])
        (⟨some l, v, W⟩ : TM2.Cfg (fun _ : K => Bool) L V) =
      ⟨none, v', bank ι W T⟩ := by
  have hs := BitMachineStackRun.run ι W P (⟨some l, v, S⟩ : TM2.Cfg (fun _ : Kk => Bool) L V) t
  rw [hrun] at hs
  simp only [stackCfg] at hs
  rwa [bank_eq_self ι W S hS] at hs

theorem count_word (e : ℕ) :
    true :: true :: (List.replicate e true ++ (List.replicate e true ++ [])) =
      List.replicate (2 * (e + 1)) true := by
  rw [List.append_nil, ← List.replicate_add,
    show 2 * (e + 1) = (e + e) + 1 + 1 by omega, List.replicate_succ, List.replicate_succ]

/-- Segment (7): public graph bytes → canonical unary endpoint tape → selected
edge endpoints, ONE fixed program, exact exit bank, explicit clock. -/
theorem bind_run (g : EncodedGraph.Graph) (hg : g.Valid) (e : Fin g.edges.length) :
    let edge := graphEdge g hg
    ∃ t ≤ 103 * ((EncodedGraph.encode g).length + 1)^3 +
        (2 * (word edge).length + 2) + (2 * g.vertices + 2) +
        (2 * e.val + 2) + (2 * e.val + 2) + 1 + 1 +
        UnaryFieldListParserScratch.fuel g.vertices (2 * (e.val + 1)) (word edge) + 7,
      ((advance program)^[t])
        (⟨some startLabel, startCtl, initBank g e.val⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, startCtl, Wv g hg e.val
          (UnaryFieldListParserScratch.contents (tokens (suffix edge e))
            (List.replicate g.vertices true) [] []
            ((RecursiveLabelCodecScratch.finCodec g.vertices).encode (edge e true) ++
              (RecursiveLabelCodecScratch.finCodec g.vertices).encode (edge e false) ++
              tokens (preceding edge e).reverse) [true])⟩ := by
  intro edge
  -- phase 1: the admitted endpoint machine, transported by `iG`
  obtain ⟨t1, ht1, p1⟩ := PublicGraphEndpointMachine.physical_run_public g hg
  simp only [PublicGraphEndpointMachine.run, PublicGraphEndpointMachine.start] at p1
  have l1 := lift iG PublicGraphEndpointMachine.program (initBank g e.val) _ _
    (fun _ => rfl) _ _ _ _ p1
  have hb1 : bank iG (initBank g e.val) (PublicGraphEndpointMachine.resultBank g hg) =
      Wv g hg e.val (fun _ => []) := by
    funext j
    rcases j with j | j
    · exact bank_at iG _ _ j
    · exact bank_outside iG _ _ _ (by rintro ⟨k, hk⟩; exact Sum.inl_ne_inr hk)
  rw [hb1] at l1
  -- phase 2: copy the endpoint tape into the parser input cell
  have p2 := MatrixStage4ScalarPreparationOps.copy_run streamSlots
    (Wv g hg e.val (fun _ => [])) rfl
  have e20 : Wv g hg e.val (fun _ => []) (streamSlots 0) = word edge := rfl
  have e21 : Wv g hg e.val (fun _ => []) (streamSlots 1) = [] := rfl
  rw [e20, e21, List.append_nil, show streamSlots 1 = pC 0 from rfl, upd_p] at p2
  let pv2 : Fin 6 → List Bool := Function.update (fun _ => []) 0 (word edge)
  -- phase 3: copy unary n into the parser bound cell
  have p3 := MatrixStage4ScalarPreparationOps.copy_run vertSlots (Wv g hg e.val pv2) rfl
  have e30 : Wv g hg e.val pv2 (vertSlots 0) = List.replicate g.vertices true := rfl
  have e31 : Wv g hg e.val pv2 (vertSlots 1) = [] := rfl
  rw [e30, e31, List.append_nil, show vertSlots 1 = pC 1 from rfl, upd_p,
    List.length_replicate] at p3
  let pv3 : Fin 6 → List Bool := Function.update pv2 1 (List.replicate g.vertices true)
  -- phase 4/5: two copies of unary e into the count cell
  have p4 := MatrixStage4ScalarPreparationOps.copy_run countSlots (Wv g hg e.val pv3) rfl
  have e40 : Wv g hg e.val pv3 (countSlots 0) = List.replicate e.val true := rfl
  have e41 : Wv g hg e.val pv3 (countSlots 1) = [] := rfl
  rw [e40, e41, show countSlots 1 = pC 2 from rfl, upd_p, List.length_replicate] at p4
  let pv4 : Fin 6 → List Bool := Function.update pv3 2 (List.replicate e.val true ++ [])
  have p5 := MatrixStage4ScalarPreparationOps.copy_run countSlots (Wv g hg e.val pv4) rfl
  have e50 : Wv g hg e.val pv4 (countSlots 0) = List.replicate e.val true := rfl
  have e51 : Wv g hg e.val pv4 (countSlots 1) = List.replicate e.val true ++ [] := rfl
  rw [e50, e51, show countSlots 1 = pC 2 from rfl, upd_p, List.length_replicate] at p5
  let pv5 : Fin 6 → List Bool :=
    Function.update pv4 2 (List.replicate e.val true ++ (List.replicate e.val true ++ []))
  -- phase 6/7: two pushes
  have p6 := pushT_run (pC 2) (Wv g hg e.val pv5)
  rw [upd_p] at p6
  let pv6 : Fin 6 → List Bool := Function.update pv5 2 (true :: Wv g hg e.val pv5 (pC 2))
  have p7 := pushT_run (pC 2) (Wv g hg e.val pv6)
  rw [upd_p] at p7
  let pv7 : Fin 6 → List Bool := Function.update pv6 2 (true :: Wv g hg e.val pv6 (pC 2))
  have hpv7 : pv7 = UnaryFieldListParserScratch.contents (word edge)
      (List.replicate g.vertices true) (List.replicate (2 * (e.val + 1)) true) [] [] [] := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · show true :: true :: (List.replicate e.val true ++ (List.replicate e.val true ++ [])) = _
      rw [count_word]; rfl
    · rfl
    · rfl
    · rfl
  -- phase 8: the prefix parser, transported by `iP`
  have p8 := physical_prefix_pair edge e
  simp only [UnaryFieldListParserScratch.run, UnaryFieldListParserScratch.initial,
    UnaryFieldListParserScratch.cfg] at p8
  have l8 := lift iP UnaryFieldListParserScratch.program (Wv g hg e.val pv7) _ _
    (fun i => by rw [hpv7]; rfl) _ _ _ _ p8
  have hb8 : bank iP (Wv g hg e.val pv7) (UnaryFieldListParserScratch.contents
      (tokens (suffix edge e)) (List.replicate g.vertices true) [] []
      ((RecursiveLabelCodecScratch.finCodec g.vertices).encode (edge e true) ++
        (RecursiveLabelCodecScratch.finCodec g.vertices).encode (edge e false) ++
        tokens (preceding edge e).reverse) [true]) =
      Wv g hg e.val (UnaryFieldListParserScratch.contents (tokens (suffix edge e))
        (List.replicate g.vertices true) [] []
        ((RecursiveLabelCodecScratch.finCodec g.vertices).encode (edge e true) ++
          (RecursiveLabelCodecScratch.finCodec g.vertices).encode (edge e false) ++
          tokens (preceding edge e).reverse) [true]) := by
    funext j
    rcases j with j | j | j
    · exact bank_outside iP _ _ _ (by rintro ⟨k, hk⟩; exact Sum.inr_ne_inl hk)
    · exact bank_at iP _ _ j
    · exact bank_outside iP _ _ _ (by
        rintro ⟨k, hk⟩
        exact Sum.inl_ne_inr (Sum.inr_injective hk))
  rw [hb8] at l8
  -- sequencing
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs pge cpStream _ .scan c0 _ oc oc
    _ _ _ _ _ l1 p2
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs g1 cpVert _ .scan (c0, oc) _ oc oc
    _ _ _ _ _ q1 p3
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs g2 cpCount _ .scan ((c0, oc), oc) _ oc oc
    _ _ _ _ _ q2 p4
  obtain ⟨u4, hu4, q4⟩ := BitMachineRawSequence.runs g3 cpCount _ .scan (((c0, oc), oc), oc) _
    oc oc _ _ _ _ _ q3 p5
  obtain ⟨u5, hu5, q5⟩ := BitMachineRawSequence.runs g4 (pushT (pC 2)) _ ()
    ((((c0, oc), oc), oc), oc) _ () () _ _ _ _ _ q4 p6
  obtain ⟨u6, hu6, q6⟩ := BitMachineRawSequence.runs g5 (pushT (pC 2)) _ ()
    (((((c0, oc), oc), oc), oc), ()) _ () () _ _ _ _ _ q5 p7
  obtain ⟨u7, hu7, q7⟩ := BitMachineRawSequence.runs g6 parserP _ .start
    ((((((c0, oc), oc), oc), oc), ()), ()) _ oc oc _ _ _ _ _ q6 l8
  refine ⟨u7, ?_, q7⟩
  have hfuel := clock_eq edge e
  omega

end

#print axioms pushT_run
#print axioms upd_p
#print axioms lift
#print axioms count_word
#print axioms bind_run

end Paper2.GraphPrefixBind
