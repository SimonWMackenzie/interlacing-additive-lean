import Paper2.GraphPrefixBind
import Paper2.RawRowSplit
import Paper2.CanonicalEndpointRankMachine

/-! Unit 3, segment (1): the endpoint-rank controller's two endpoint operand
words, produced physically from the literal public graph bytes.

ONE fixed program on the bank `KE = GraphPrefixBind.K ⊕ Fin 2`:
1. the admitted `GraphPrefixBind.program` (public endpoint machine + prefix
   parser, reused by name, transported by `Sum.inl`) from the literal bytes
   `EncodedGraph.encode g` and unary edge-occurrence index `e`;
2. push the terminator `false` on cell `V`, then the admitted
   `RawRowSplit.readU` moves the first unary token of the parser output cell
   onto it: `V = unaryWord (graphEdge g hg e true).val`;
3. the same for `U = unaryWord (graphEdge g hg e false).val`.
Every phase and handoff is charged (production `BitMachineRawSequence`).
The parser output cell keeps the remaining tokens
`tokens (preceding edge e).reverse` (named, exact). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.EndpointOperands

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)
open Paper2.CanonicalEdgeTape Paper2.CanonicalEdgePrefix Paper2.CanonicalEdgePair
open Paper2.UnaryFieldListParserScratch (tokens)

abbrev KE := GraphPrefixBind.K ⊕ Fin 2

def uC : KE := .inr 0
def vC : KE := .inr 1
def srcC : KE := .inl (GraphPrefixBind.pC 4)

def iK : GraphPrefixBind.K ↪ KE := ⟨Sum.inl, Sum.inl_injective⟩

def bindP := fun l => stackStmt iK (GraphPrefixBind.program l)

def pushF (k : KE) : Unit → TM2.Stmt (fun _ : KE => Bool) Unit (Option Bool) :=
  fun _ => push k (fun _ => false) halt

def q1 := BitMachineRawSequence.program (pushF vC) (RawRowSplit.readU srcC vC) ()
  (none : Option Bool) (none : Option Bool)
def q2 := BitMachineRawSequence.program q1 (pushF uC) ()
  ((none : Option Bool), (none : Option Bool)) (none : Option Bool)
def q3 := BitMachineRawSequence.program q2 (RawRowSplit.readU srcC uC) ()
  (((none : Option Bool), (none : Option Bool)), (none : Option Bool)) (none : Option Bool)
def program := BitMachineRawSequence.program bindP q3 (leftLabel (leftLabel (leftLabel ())))
  GraphPrefixBind.startCtl
  ((((none : Option Bool), (none : Option Bool)), (none : Option Bool)), (none : Option Bool))

def entry (g : EncodedGraph.Graph) (e : ℕ) : KE → List Bool :=
  Sum.elim (GraphPrefixBind.initBank g e) ![[], []]

theorem pushF_run (k : KE) (S : KE → List Bool) (v : Option Bool) :
    ((advance (pushF k))^[1]) (⟨some (), v, S⟩ : TM2.Cfg (fun _ : KE => Bool) _ _) =
      ⟨none, v, Function.update S k (false :: S k)⟩ := rfl

theorem finCodec_append (a : ℕ) (x : Fin a) (R : List Bool) :
    (RecursiveLabelCodecScratch.finCodec a).encode x ++ R =
      List.replicate x.val true ++ false :: R := by
  simp [RecursiveLabelCodecScratch.finCodec]

/-- Exact exit bank and explicit clock. -/
theorem operands_run (g : EncodedGraph.Graph) (hg : g.Valid) (e : Fin g.edges.length) :
    let edge := graphEdge g hg
    ∃ t ≤ (103 * ((EncodedGraph.encode g).length + 1)^3 +
        (2 * (word edge).length + 2) + (2 * g.vertices + 2) +
        (2 * e.val + 2) + (2 * e.val + 2) + 1 + 1 +
        UnaryFieldListParserScratch.fuel g.vertices (2 * (e.val + 1)) (word edge) + 7) +
        ((edge e true).val + (edge e false).val + 7) + 1,
      ∃ c,
      ((advance program)^[t])
        (⟨some (leftLabel GraphPrefixBind.startLabel),
          (GraphPrefixBind.startCtl,
            ((((none : Option Bool), (none : Option Bool)), (none : Option Bool)),
              (none : Option Bool))),
          entry g e.val⟩ : TM2.Cfg (fun _ : KE => Bool) _ _) =
        ⟨none, c, Sum.elim (GraphPrefixBind.Wv g hg e.val
          (UnaryFieldListParserScratch.contents (tokens (suffix edge e))
            (List.replicate g.vertices true) [] []
            (tokens (preceding edge e).reverse) [true]))
          ![CanonicalEndpointRankMachine.unaryWord (edge e false).val,
            CanonicalEndpointRankMachine.unaryWord (edge e true).val]⟩ := by
  intro edge
  obtain ⟨t0, ht0, h0⟩ := GraphPrefixBind.bind_run g hg e
  have ht0' : t0 ≤ 103 * ((EncodedGraph.encode g).length + 1)^3 +
        (2 * (word edge).length + 2) + (2 * g.vertices + 2) +
        (2 * e.val + 2) + (2 * e.val + 2) + 1 + 1 +
        UnaryFieldListParserScratch.fuel g.vertices (2 * (e.val + 1)) (word edge) + 7 := ht0
  -- transport the admitted binding run by `Sum.inl`
  have hs := BitMachineStackRun.run iK (entry g e.val) GraphPrefixBind.program
    (⟨some GraphPrefixBind.startLabel, GraphPrefixBind.startCtl,
      GraphPrefixBind.initBank g e.val⟩ : TM2.Cfg (fun _ : GraphPrefixBind.K => Bool) _ _) t0
  rw [h0] at hs
  have hin : bank iK (entry g e.val) (GraphPrefixBind.initBank g e.val) = entry g e.val :=
    bank_eq_self iK _ _ (fun _ => rfl)
  let P := UnaryFieldListParserScratch.contents (tokens (suffix edge e))
    (List.replicate g.vertices true) [] []
    ((RecursiveLabelCodecScratch.finCodec g.vertices).encode (edge e true) ++
      (RecursiveLabelCodecScratch.finCodec g.vertices).encode (edge e false) ++
      tokens (preceding edge e).reverse) [true]
  have hout : bank iK (entry g e.val) (GraphPrefixBind.Wv g hg e.val P) =
      Sum.elim (GraphPrefixBind.Wv g hg e.val P) ![[], []] := by
    funext j
    rcases j with j | j
    · exact bank_at iK _ _ j
    · exact bank_outside iK _ _ _ (by rintro ⟨k, hk⟩; exact Sum.inl_ne_inr hk)
  simp only [stackCfg] at hs
  rw [hin, hout] at hs
  have hA : ((advance bindP)^[t0]) (⟨some GraphPrefixBind.startLabel, GraphPrefixBind.startCtl,
      entry g e.val⟩ : TM2.Cfg (fun _ : KE => Bool) _ _) =
      ⟨none, GraphPrefixBind.startCtl, Sum.elim (GraphPrefixBind.Wv g hg e.val P) ![[], []]⟩ := hs
  -- the operand phases
  let S0 : KE → List Bool := Sum.elim (GraphPrefixBind.Wv g hg e.val P) ![[], []]
  let tv := (edge e true).val
  let tu := (edge e false).val
  let rest := tokens (preceding edge e).reverse
  have hsrc0 : S0 srcC = List.replicate tv true ++ false ::
      (List.replicate tu true ++ false :: rest) := by
    show P 4 = _
    simp only [P, UnaryFieldListParserScratch.contents]
    simp [RecursiveLabelCodecScratch.finCodec, tv, tu, rest]
  have hne1 : srcC ≠ vC := by simp [srcC, vC]
  have hne2 : srcC ≠ uC := by simp [srcC, uC]
  have r1 := pushF_run vC S0 none
  let S1 := Function.update S0 vC (false :: S0 vC)
  have r2 := RawRowSplit.readU_run srcC vC hne1 tv (List.replicate tu true ++ false :: rest)
    (S1 vC) S1 none (by simp [S1, hne1, hsrc0]) rfl
  let S2 := Function.update (Function.update S1 srcC (List.replicate tu true ++ false :: rest))
    vC (List.replicate tv true ++ S1 vC)
  obtain ⟨u1, hu1, e1⟩ := BitMachineRawSequence.runs (pushF vC) (RawRowSplit.readU srcC vC)
    () () none none none (some false) S0 S1 S2 1 (tv + 1) r1 r2
  have r3 := pushF_run uC S2 none
  let S3 := Function.update S2 uC (false :: S2 uC)
  obtain ⟨u2, hu2, e2⟩ := BitMachineRawSequence.runs q1 (pushF uC) (leftLabel ()) ()
    ((none : Option Bool), (none : Option Bool)) (none, some false) none none S0 S2 S3 u1 1 e1 r3
  have hsrc3 : S3 srcC = List.replicate tu true ++ false :: rest := by
    simp [S3, S2, S1, hne1, hne2, uC, vC, srcC]
  have r4 := RawRowSplit.readU_run srcC uC hne2 tu rest (S3 uC) S3 none hsrc3 rfl
  let S4 := Function.update (Function.update S3 srcC rest) uC (List.replicate tu true ++ S3 uC)
  obtain ⟨u3, hu3, e3⟩ := BitMachineRawSequence.runs q2 (RawRowSplit.readU srcC uC)
    (leftLabel (leftLabel ())) () (((none : Option Bool), (none : Option Bool)), (none : Option Bool))
    ((none, none), none) none (some false) S0 S3 S4 u2 (tu + 1) e2 r4
  obtain ⟨u4, hu4, e4⟩ := BitMachineRawSequence.runs bindP q3 GraphPrefixBind.startLabel
    (leftLabel (leftLabel (leftLabel ()))) GraphPrefixBind.startCtl GraphPrefixBind.startCtl
    ((((none : Option Bool), (none : Option Bool)), (none : Option Bool)), (none : Option Bool))
    (((none, none), none), some false) (entry g e.val) S0 S4 t0 u3 hA e3
  refine ⟨u4, by omega, (GraphPrefixBind.startCtl,
    ((((none : Option Bool), (none : Option Bool)), (none : Option Bool)), some false)), ?_⟩
  refine e4.trans ?_
  have hS0v : S0 vC = [] := rfl
  have hS0u : S0 uC = [] := rfl
  have huv : uC ≠ vC := by simp [uC, vC]
  have hus : uC ≠ srcC := by simp [uC, srcC]
  have hvs : vC ≠ srcC := by simp [vC, srcC]
  have key : S4 = Function.update (Function.update (Function.update S0 srcC rest) vC
      (CanonicalEndpointRankMachine.unaryWord tv)) uC
      (CanonicalEndpointRankMachine.unaryWord tu) := by
    funext j
    simp only [S4, S3, S2, S1, Function.update_apply]
    by_cases h1 : j = uC
    · subst h1
      simp [huv, hus, hS0u, CanonicalEndpointRankMachine.unaryWord]
    · by_cases h2 : j = vC
      · subst h2
        simp [huv.symm, hvs, hS0v, CanonicalEndpointRankMachine.unaryWord]
      · by_cases h3 : j = srcC
        · subst h3
          simp [hus.symm, hvs.symm]
        · simp [h1, h2, h3]
  rw [key]
  congr 1
  show Function.update (Function.update (Function.update
      (Sum.elim (GraphPrefixBind.Wv g hg e.val P) ![[], []]) (.inl (GraphPrefixBind.pC 4)) rest)
      (.inr 1) _) (.inr 0) _ = _
  rw [Sum.update_elim_inl, GraphPrefixBind.upd_p, Sum.update_elim_inr, Sum.update_elim_inr]
  congr 1
  · congr 1
    funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> rfl

#print axioms operands_run

end

end Paper2.EndpointOperands
