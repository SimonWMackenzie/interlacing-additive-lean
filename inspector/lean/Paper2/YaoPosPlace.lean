import Paper2.YaoPosLookup
import Paper2.YaoCloneSrc
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! Lane a-yao-owner-1: (i) ambient placement of the Y3 position lookup on
seven named cells of an arbitrary bank (admitted
`BitMachineStackEmbedding.outputs`), exact whole-bank exit; (ii) the
exactly-once property of the Y10 clone order (`toEdge` is a bijection onto
the admitted `HypergraphClones.Edge`). -/

namespace Paper2.YaoPositionLookup

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.UnaryFieldListParserScratch
open Paper2.YaoSourceCodec
open Paper2.YaoLookup

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

noncomputable def placedProgram {J : Type*} [DecidableEq J] (ι : Fin 7 ↪ J) (l : Label) :
    TM2.Stmt (fun _ : J => Bool) Label (Option Bool) :=
  BitMachineStackEmbedding.stmt ι id id id none (program l)

/-- Y3 core placed in an ambient bank: cells `ι 0..6` = body, `a*K`, `K`,
vertex, scratch, flag, output.  Every other ambient cell is untouched; the
body/counter cells end empty, the vertex word is preserved, and the output
cell holds unary `positionEval`. -/
theorem placed_position_lookup {J : Type*} [DecidableEq J] (ι : Fin 7 ↪ J)
    (W : J → List Bool) {t v e : ℕ} (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (a : Fin (paddedEdgeCount e)) (vertex : Fin v)
    (h0 : W (ι 0) = tokens (List.ofFn (flatten edges)))
    (h1 : W (ι 1) = List.replicate (a.val * arity t) true)
    (h2 : W (ι 2) = List.replicate (arity t) true)
    (h3 : W (ι 3) = List.replicate vertex.val true)
    (h4 : W (ι 4) = []) (h5 : W (ι 5) = []) (h6 : W (ι 6) = []) :
    ∃ n ≤ 2 * (a.val * arity t) + 5 * (tokens (List.ofFn (flatten edges))).length +
        arity t * (3 * vertex.val + 6) + arity t + 6,
      ((advance (placedProgram ι))^[n])
        (⟨some .skipLoop, none, W⟩ : TM2.Cfg (fun _ : J => Bool) Label (Option Bool)) =
        ⟨none, none, Function.update (Function.update (Function.update (Function.update W
          (ι 0) []) (ι 1) []) (ι 2) [])
          (ι 6) (List.replicate (positionEval (paddedEdgesEval edges) a vertex).val true)⟩ := by
  classical
  obtain ⟨m, hm, hrun⟩ := physical_position_lookup edges a vertex none
  let c := cfg (some .skipLoop) none (tokens (List.ofFn (flatten edges)))
    (rep (a.val * arity t)) (rep (arity t)) (rep vertex.val) [] [] []
  have hbank : BitMachineStackEmbedding.bank ι W c.stk = W := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    fin_cases k <;> simp [c, cfg, rep, h0, h1, h2, h3, h4, h5, h6]
  have hhalt : (((advance program)^[m]) c).l = none := by
    change (run m c).l = none
    rw [hrun]
    rfl
  obtain ⟨n, hn, he⟩ := BitMachineStackEmbedding.outputs ι W id id id (fun _ => rfl) none
    program (placedProgram ι) (by intro l; rfl) c m hhalt
  have hlocal : ((advance program)^[m]) c = cfg none none [] [] [] (rep vertex.val) [] []
      (rep (positionEval (paddedEdgesEval edges) a vertex).val) := hrun
  rw [hlocal] at he
  change ((advance (placedProgram ι))^[n])
      ⟨some .skipLoop, none, BitMachineStackEmbedding.bank ι W c.stk⟩ =
      ⟨none, none, BitMachineStackEmbedding.bank ι W
        (cfg none none [] [] [] (rep vertex.val) [] []
          (rep (positionEval (paddedEdgesEval edges) a vertex).val)).stk⟩ at he
  have hupdate : (cfg none none [] [] [] (rep vertex.val) [] []
      (rep (positionEval (paddedEdgesEval edges) a vertex).val)).stk =
      Function.update (Function.update (Function.update (Function.update c.stk 0 []) 1 [])
        2 []) 6 (rep (positionEval (paddedEdgesEval edges) a vertex).val) := by
    funext k
    fin_cases k <;> simp [c, cfg]
  rw [hbank, hupdate, BitMachineStackEmbedding.bank_update, BitMachineStackEmbedding.bank_update,
    BitMachineStackEmbedding.bank_update, BitMachineStackEmbedding.bank_update, hbank] at he
  exact ⟨n, hn.trans hm, he⟩

#print axioms placed_position_lookup

end Paper2.YaoPositionLookup

namespace Paper2.YaoCloneSource

open Paper2.HypergraphClones

set_option linter.unusedSimpArgs false

theorem nodup_allFuns (m : ℕ) : (n : ℕ) → (allFuns m n).Nodup
  | 0 => by simp [allFuns]
  | n + 1 => by
      simp only [allFuns]
      rw [List.nodup_flatMap]
      refine ⟨fun a _ => (nodup_allFuns m n).map (fun f g h => by
        have := congrArg Fin.tail h
        simpa [Fin.tail_cons] using this), ?_⟩
      refine (List.nodup_finRange m).pairwise_of_forall_ne ?_
      intro a _ b _ hab
      rw [Function.onFun, List.disjoint_left]
      intro f hfa hfb
      simp only [List.mem_map] at hfa hfb
      obtain ⟨g, _, rfl⟩ := hfa
      obtain ⟨g', _, hg'⟩ := hfb
      have := congrFun hg' 0
      simp at this
      exact hab this.symm

theorem nodup_allLifts {K v e S : ℕ} (edges : Fin e → Fin K → Fin v) :
    (allLifts edges S).Nodup := by
  unfold allLifts
  rw [List.nodup_flatMap]
  refine ⟨fun i _ => ((nodup_allFuns _ _).filter _).map (fun r r' h => by simpa using h), ?_⟩
  refine (List.nodup_finRange e).pairwise_of_forall_ne ?_
  intro i _ j _ hij
  rw [Function.onFun, List.disjoint_left]
  intro p hpi hpj
  simp only [List.mem_map] at hpi hpj
  obtain ⟨r, _, rfl⟩ := hpi
  obtain ⟨r', _, hr'⟩ := hpj
  exact hij (congrArg Prod.fst hr').symm

/-- Exactly-once enumeration: the explicit order is injective. -/
theorem toEdge_injective {K v e S : ℕ} (edges : Fin e → Fin K → Fin v) :
    Function.Injective (toEdge (S := S) edges) := by
  intro k k' h
  have h1 : ((allLifts edges S).get k).1 = ((allLifts edges S).get k').1 :=
    congrArg Sigma.fst h
  have h2 : ((allLifts edges S).get k).2 = ((allLifts edges S).get k').2 := by
    unfold toEdge at h
    have := Sigma.ext_iff.mp h
    obtain ⟨hfst, hsnd⟩ := this
    have hv := (Subtype.heq_iff_coe_eq (by intro x; rw [hfst])).mp hsnd
    exact hv
  have hp : (allLifts edges S).get k = (allLifts edges S).get k' := Prod.ext h1 h2
  exact (List.Nodup.get_inj_iff (nodup_allLifts edges)).mp hp

theorem toEdge_bijective {K v e S : ℕ} (edges : Fin e → Fin K → Fin v) :
    Function.Bijective (toEdge (S := S) edges) :=
  ⟨toEdge_injective edges, toEdge_surjective edges⟩

#print axioms toEdge_injective
#print axioms toEdge_bijective

end Paper2.YaoCloneSource
