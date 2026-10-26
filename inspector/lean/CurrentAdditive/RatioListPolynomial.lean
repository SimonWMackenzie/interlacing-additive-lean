import CurrentAdditive.RatioListClockCaps
import CurrentAdditive.RatioListFullRun

set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 100
set_option maxRecDepth 10000
noncomputable section
namespace CurrentAdditive.RatioListPolynomial
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout MinimumRatioContext CurrentAdditive.GaussListContext
open RatioListClockBounds RatioListClockCaps EntryClockPoly

syntax "solve_list_poly" : tactic
macro_rules
  | `(tactic| solve_list_poly) => `(tactic| first
      | exact PolyIn.self
      | exact PolyIn.const _
      | (apply PolyIn.add <;> solve_list_poly)
      | (apply PolyIn.mul <;> solve_list_poly)
      | (apply PolyIn.pow <;> solve_list_poly))

theorem itemCap_poly : PolyIn (fun n : Nat => n) itemCap := by
  unfold itemCap lookupCap massCap appendCap invokeCap wordCap outputCap
  solve_list_poly

def prepCap (L : Nat) :=
  invokeCap GaussRowCount.machine L (GaussRowCount.polynomialClock L) +
  invokeCap SourceFieldWriter.unaryFieldMachine L
    ((UnaryBinaryEncoding.coefficient+10)*(L+1)^2)+1
def loopCap (L : Nat) := (L+1)*(50*(L+1)^3+itemCap L+3*L+15)
def fullCap (L : Nat) := prepCap L+loopCap L+1

theorem fullCap_poly : PolyIn (fun n : Nat => n) fullCap := by
  unfold fullCap prepCap loopCap GaussRowCount.polynomialClock GaussRowCount.itemEnvelope
  unfold itemCap lookupCap massCap appendCap invokeCap wordCap outputCap
  solve_list_poly

theorem prepare_le (xs cs : List (List Bool)) (lambda : List Bool) :
    RatioListPreparation.clock xs ≤ prepCap (inputLength xs cs lambda) := by
  let L := inputLength xs cs lambda
  change RatioListPreparation.clock xs ≤ prepCap L
  have hL : (SourceListEncoding.encode xs).length ≤ L := by dsimp [L,inputLength]; omega
  have hn : xs.length ≤ L := (GaussRowCount.rows_le_input xs).trans hL
  have hc := invoke_le GaussRowCount.machine (SourceListEncoding.encode xs)
    (GaussRowCount.polynomialClock (SourceListEncoding.encode xs).length) L
    (GaussRowCount.polynomialClock L) hL (GaussRowCount.polynomialClock_mono hL)
  have hh := invoke_le SourceFieldWriter.unaryFieldMachine (List.replicate xs.length true)
    ((UnaryBinaryEncoding.coefficient+10)*(xs.length+1)^2) L
    ((UnaryBinaryEncoding.coefficient+10)*(L+1)^2) (by simpa using hn) (by gcongr)
  unfold RatioListPreparation.clock prepCap
  omega

theorem request_scratch (xs cs pre : List (List Bool)) (lambda word : List Bool)
    (tail : List (List Bool)) :
    (∑ i : Fin 10,((RatioRequestList.postCut xs cs lambda pre word tail)
      (StatefulListScheduler.cleanBank i)).length) =
      (SourceListEncoding.fields tail).length+word.length := by
  have he (i : Fin 10) :
      ((RatioRequestList.postCut xs cs lambda pre word tail)
        (StatefulListScheduler.cleanBank i)).length =
      (if i=0 then (SourceListEncoding.fields tail).length else 0) +
        (if i=5 then word.length else 0) := by
    fin_cases i <;>
      simp [RatioRequestList.postCut,RatioRequestList.selectedCut,
        RatioRequestFrame.selected,RatioPhysicalFold.selected,
        RatioPhysicalFold.boundary,RatioPhysicalFold.blank,StatefulListScheduler.initialBank,
        StatefulListScheduler.cleanBank,LargeContextListScheduler.cleanBank,
        Function.update_apply,Fin.ext_iff,low,Fin.ofNat]
  simp_rw [he]
  simp [Finset.sum_add_distrib]

theorem pair_scratch (xs cs pre : List (List Bool)) (word : List Bool)
    (tail : List (List Bool)) :
    (∑ i : Fin 10,((RatioPairList.postCut xs cs pre word tail)
      (StatefulListScheduler.cleanBank i)).length) =
      (SourceListEncoding.fields tail).length+2*word.length := by
  have he (i : Fin 10) :
      ((RatioPairList.postCut xs cs pre word tail)
        (StatefulListScheduler.cleanBank i)).length =
      (if i=0 then (SourceListEncoding.fields tail).length else 0) +
        (if i=5 then word.length else 0)+(if i=6 then word.length else 0) := by
    fin_cases i <;>
      simp [RatioPairList.postCut,RatioPairList.selectedCut,
        RatioRequestFrame.selected,RatioPhysicalFold.selected,
        RatioPhysicalFold.boundary,RatioPhysicalFold.blank,StatefulListScheduler.initialBank,
        StatefulListScheduler.cleanBank,LargeContextListScheduler.cleanBank,
        Function.update_apply,Fin.ext_iff,low,Fin.ofNat]
  simp_rw [he]
  simp [Finset.sum_add_distrib]
  omega

theorem cut_lengths (xs pre : List (List Bool)) (word : List Bool)
    (tail : List (List Bool)) (hsplit : pre ++ word :: tail=xs) :
    word.length ≤ (SourceListEncoding.encode xs).length ∧
      (SourceListEncoding.fields tail).length ≤ (SourceListEncoding.encode xs).length := by
  constructor
  · apply word_le_packet xs word
    rw [← hsplit]; simp
  · have hf : (SourceListEncoding.fields xs).length ≤ (SourceListEncoding.encode xs).length := by
      simp [SourceListEncoding.encode]
    have he : SourceListEncoding.fields xs = SourceListEncoding.fields pre ++
        (EncodedCommunication.natField word.length ++ word ++ SourceListEncoding.fields tail) := by
      rw [← hsplit,IndexedV2Clock.fields_append]
      rfl
    rw [he] at hf
    simp only [SourceListEncoding.fields,List.length_append] at hf
    omega

theorem request_clock_le (xs cs : List (List Bool)) (lambda : List Bool)
    (hlen : cs.length=xs.length) :
    RatioRequestList.clock xs cs lambda hlen ≤ loopCap (inputLength xs cs lambda) := by
  classical
  let L := inputLength xs cs lambda
  have hsrc : (SourceListEncoding.encode xs).length ≤ L := by dsimp [L,inputLength]; omega
  have hget : ∀ pre word tail,pre ++ word :: tail=xs →
      RatioIndexedScheduler.getterBudget pre word tail ≤ 50*(L+1)^3 := by
    intro pre word tail hs
    have hg := StatefulListScheduler.getterBudget_cubic pre word tail
    rw [hs] at hg
    exact hg.trans (by gcongr)
  have hcb : ∀ pre word tail,pre ++ word :: tail=xs →
      (RatioRequestList.contract xs cs lambda hlen).time pre word tail ≤ itemCap L := by
    intro pre word tail hs
    have ht := (Classical.choose_spec (RatioRequestList.cut_run xs cs lambda hlen pre word tail hs)).1
    change RatioRequestList.cutTime xs cs lambda hlen pre word tail ≤ itemCap L
    rw [RatioRequestList.cutTime,dif_pos hs]
    exact ht.trans (request_cut_cap xs cs lambda hlen pre word tail hs)
  have hscratch : ∀ pre word tail,pre ++ word :: tail=xs →
      (∑ i : Fin 10,(((RatioRequestList.contract xs cs lambda hlen).state pre word tail)
        (StatefulListScheduler.cleanBank i)).length) ≤ 3*L := by
    intro pre word tail hs
    change (∑ i : Fin 10,((RatioRequestList.postCut xs cs lambda pre word tail)
      (StatefulListScheduler.cleanBank i)).length) ≤ _
    rw [request_scratch]
    have hl := cut_lengths xs pre word tail hs
    omega
  have hb := budget_bound RatioUpdateAppendItem.program RatioUpdateAppendItem.start
    RatioUpdateAppendItem.control xs (RatioRequestListSpec.outputAt xs.length cs lambda)
    (SourceListEncoding.encode cs) (RatioRequestList.contract xs cs lambda hlen)
    (50*(L+1)^3) (itemCap L) (3*L) hget hcb hscratch [] xs (by simp)
  have hn : xs.length ≤ L := (GaussRowCount.rows_le_input xs).trans hsrc
  exact hb.trans (by unfold loopCap; gcongr)

theorem pair_clock_le (xs cs : List (List Bool)) (hlen : cs.length=xs.length) :
    RatioPairList.clock xs cs hlen ≤ loopCap (inputLength xs cs []) := by
  classical
  let L := inputLength xs cs []
  have hsrc : (SourceListEncoding.encode xs).length ≤ L := by dsimp [L,inputLength]; omega
  have hget : ∀ pre word tail,pre ++ word :: tail=xs →
      RatioIndexedScheduler.getterBudget pre word tail ≤ 50*(L+1)^3 := by
    intro pre word tail hs
    have hg := StatefulListScheduler.getterBudget_cubic pre word tail
    rw [hs] at hg
    exact hg.trans (by gcongr)
  have hcb : ∀ pre word tail,pre ++ word :: tail=xs →
      (RatioPairList.contract xs cs hlen).time pre word tail ≤ itemCap L := by
    intro pre word tail hs
    have ht := (Classical.choose_spec (RatioPairList.cut_run xs cs hlen pre word tail hs)).1
    change RatioPairList.cutTime xs cs hlen pre word tail ≤ itemCap L
    rw [RatioPairList.cutTime,dif_pos hs]
    exact ht.trans (pair_cut_cap xs cs hlen pre word tail hs)
  have hscratch : ∀ pre word tail,pre ++ word :: tail=xs →
      (∑ i : Fin 10,(((RatioPairList.contract xs cs hlen).state pre word tail)
        (StatefulListScheduler.cleanBank i)).length) ≤ 3*L := by
    intro pre word tail hs
    change (∑ i : Fin 10,((RatioPairList.postCut xs cs pre word tail)
      (StatefulListScheduler.cleanBank i)).length) ≤ _
    rw [pair_scratch]
    have hl := cut_lengths xs pre word tail hs
    omega
  have hb := budget_bound RatioPairItem.program RatioPairItem.start RatioPairItem.control xs
    (RatioPairListSpec.outputAt xs.length cs) (SourceListEncoding.encode cs)
    (RatioPairList.contract xs cs hlen) (50*(L+1)^3) (itemCap L) (3*L)
    hget hcb hscratch [] xs (by simp)
  have hn : xs.length ≤ L := (GaussRowCount.rows_le_input xs).trans hsrc
  exact hb.trans (by unfold loopCap; gcongr)

#print axioms request_clock_le
#print axioms pair_clock_le
#print axioms fullCap_poly

theorem uniform_complete_list_clock : ∃ C d : Nat,
    (∀ (xs cs : List (List Bool)) (lambda : List Bool) (hlen : cs.length=xs.length),
      RatioListPreparation.clock xs+RatioRequestList.clock xs cs lambda hlen+1 ≤
        C*(inputLength xs cs lambda+1)^d) ∧
    (∀ (xs cs : List (List Bool)) (hlen : cs.length=xs.length),
      RatioListPreparation.clock xs+RatioPairList.clock xs cs hlen+1 ≤
        C*(inputLength xs cs []+1)^d) := by
  obtain ⟨C,d,hC⟩ := fullCap_poly
  refine ⟨C,d,?_,?_⟩
  · intro xs cs lambda hlen
    have hp := prepare_le xs cs lambda
    have hl := request_clock_le xs cs lambda hlen
    exact (show _ ≤ fullCap (inputLength xs cs lambda) by unfold fullCap; omega).trans (hC _)
  · intro xs cs hlen
    have hp := prepare_le xs cs []
    have hl := pair_clock_le xs cs hlen
    exact (show _ ≤ fullCap (inputLength xs cs []) by unfold fullCap; omega).trans (hC _)

/-- One pair of constants precedes every source, coefficient list and scalar.
This is the actual complete request-list program, with no prepared header,
count, callback, or run-time premise. -/
theorem uniform_requests : ∃ C d : Nat,
    ∀ (xs cs : List (List Bool)) (lambda : List Bool) (hlen : cs.length=xs.length),
    ∃ t ≤ C*(inputLength xs cs lambda+1)^d, ∃ v,
      ((advance RatioListFullRun.requestProgram)^[t])
        (⟨some RatioListFullRun.requestFullStart,RatioListFullRun.requestFullControl,
          RatioRequestFrame.boundary (SourceListEncoding.encode xs) []
            (SourceListEncoding.encode cs) lambda 0 0⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,v,RatioRequestFrame.boundary (SourceListEncoding.encode xs)
          (SourceListEncoding.encode (RatioRequestListSpec.requests xs cs lambda))
          (SourceListEncoding.encode cs) lambda xs.length 0⟩ := by
  classical
  obtain ⟨C,d,hC,_⟩ := uniform_complete_list_clock
  refine ⟨C,d,?_⟩
  intro xs cs lambda hlen
  obtain ⟨t,ht,v,hr⟩ := RatioListFullRun.requests xs cs lambda hlen
  exact ⟨t,ht.trans (hC xs cs lambda hlen),v,hr⟩

theorem uniform_pairs : ∃ C d : Nat,
    ∀ (xs cs : List (List Bool)) (hlen : cs.length=xs.length),
    ∃ t ≤ C*(inputLength xs cs []+1)^d, ∃ v,
      ((advance RatioListFullRun.pairProgram)^[t])
        (⟨some RatioListFullRun.pairFullStart,RatioListFullRun.pairFullControl,
          RatioRequestFrame.boundary (SourceListEncoding.encode xs) []
            (SourceListEncoding.encode cs) [] 0 0⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,v,RatioRequestFrame.boundary (SourceListEncoding.encode xs)
          (SourceListEncoding.encode (RatioPairListSpec.pairs xs cs))
          (SourceListEncoding.encode cs) [] xs.length 0⟩ := by
  classical
  obtain ⟨C,d,_,hC⟩ := uniform_complete_list_clock
  refine ⟨C,d,?_⟩
  intro xs cs hlen
  obtain ⟨t,ht,v,hr⟩ := RatioListFullRun.pairs xs cs hlen
  exact ⟨t,ht.trans (hC xs cs hlen),v,hr⟩

#print axioms uniform_requests
#print axioms uniform_pairs
end CurrentAdditive.RatioListPolynomial
