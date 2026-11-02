import CurrentAdditive.RatioPairList
import CurrentAdditive.RatioRequestList
import CurrentAdditive.StatefulFoldClock
import CurrentAdditive.GaussRowCount
import EthInapproximability.CurrentPaper.EntryClockPolyFrame

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
namespace CurrentAdditive.RatioListClockBounds
open EthInapproximability.CurrentPaper CurrentAdditive.GaussListContext
open Turing BitMachineEncoding

theorem budget_bound {N : Nat} {L V : Type} [DecidableEq L] [Fintype L]
    [DecidableEq V] [Fintype V]
    (callback : L → TM2.Stmt (fun _ : StatefulListScheduler.StackN N => Bool) L V)
    (start : L) (init : V) (xs : List (List Bool))
    (outputAt : List (List Bool) → List Bool) (context : List Bool)
    (C : RatioIndexedScheduler.CallbackContract callback start init xs outputAt context)
    (G Q R : Nat)
    (hget : ∀ pre word tail,pre ++ word :: tail=xs →
      RatioIndexedScheduler.getterBudget pre word tail ≤ G)
    (hcb : ∀ pre word tail,pre ++ word :: tail=xs → C.time pre word tail ≤ Q)
    (hscratch : ∀ pre word tail,pre ++ word :: tail=xs →
      (∑ i : Fin 10,((C.state pre word tail) (StatefulListScheduler.cleanBank i)).length) ≤ R)
    (pre tail : List (List Bool)) (hsplit : pre ++ tail=xs) :
    RatioIndexedScheduler.remainingBudget callback start init xs outputAt context C pre tail ≤
      (tail.length+1)*(G+Q+R+15) := by
  induction tail generalizing pre with
  | nil => simp [RatioIndexedScheduler.remainingBudget]
  | cons word tail ih =>
      have hg := hget pre word tail hsplit
      have hc := hcb pre word tail hsplit
      have hs := hscratch pre word tail hsplit
      have ht := ih (pre ++ [word]) (by simpa [List.append_assoc] using hsplit)
      simp only [RatioIndexedScheduler.remainingBudget,RatioIndexedScheduler.cycleBudget,
        List.length_cons]
      nlinarith

theorem fields_bound (xs : List (List Bool)) (B : Nat)
    (hb : ∀ w ∈ xs,w.length ≤ B) :
    (SourceListEncoding.fields xs).length ≤ xs.length*(3*B+1) := by
  induction xs with
  | nil => simp [SourceListEncoding.fields]
  | cons w ws ih =>
      have hw := hb w (by simp)
      have ht := ih (by intro v hv; exact hb v (by simp [hv]))
      have hf := EncodedGraph.natField_length_upper w.length
      simp only [SourceListEncoding.fields,List.length_append,List.length_cons]
      nlinarith

theorem word_le_packet (xs : List (List Bool)) (w : List Bool) (hw : w ∈ xs) :
    w.length ≤ (SourceListEncoding.encode xs).length :=
  (IndexedV2Clock.fields_item_length_le xs w hw).trans (by simp [SourceListEncoding.encode])

theorem coefficient_le (cs : List (List Bool)) (i : Nat) :
    (RatioRequestListSpec.coefficient cs i).length ≤ (SourceListEncoding.encode cs).length := by
  by_cases hi : i < cs.length
  · have hm : cs[i] ∈ cs := List.getElem_mem hi
    simpa [RatioRequestListSpec.coefficient,List.getElem?_eq_getElem hi]
      using word_le_packet cs cs[i] hm
  · simp [RatioRequestListSpec.coefficient,List.getElem?_eq_none (Nat.le_of_not_gt hi)]

def inputLength (xs cs : List (List Bool)) (lambda : List Bool) : Nat :=
  (SourceListEncoding.encode xs).length+(SourceListEncoding.encode cs).length+lambda.length

theorem request_length (old lambda c : List Bool) :
    (RatioRequestSerializer.bytes old lambda c).length =
      2*old.length+2*lambda.length+2*c.length+3 := by
  simp [RatioRequestSerializer.bytes,EncodedCommunication.field_length]
  omega

theorem request_prefix_bound (xs cs pre : List (List Bool)) (lambda : List Bool)
    (hpre : ∀ w ∈ pre,w ∈ xs) (hlen : pre.length ≤ xs.length) :
    (RatioRequestListSpec.outputAt xs.length cs lambda pre).length ≤
      100*(inputLength xs cs lambda+1)^2 := by
  let L := inputLength xs cs lambda
  have hx : xs.length ≤ L := (GaussRowCount.rows_le_input xs).trans (by dsimp [L,inputLength]; omega)
  have hp : pre.length ≤ L := hlen.trans hx
  have hw : ∀ w ∈ pre,w.length ≤ L := by
    intro w hm
    exact (word_le_packet xs w (hpre w hm)).trans (by dsimp [L,inputLength]; omega)
  have hc (i : Nat) : (RatioRequestListSpec.coefficient cs i).length ≤ L :=
    (coefficient_le cs i).trans (by dsimp [L,inputLength]; omega)
  have hlambda : lambda.length ≤ L := by dsimp [L,inputLength]; omega
  have hr : ∀ w ∈ RatioRequestListSpec.requests pre cs lambda,w.length ≤ 6*L+3 := by
    intro w hm
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
    have hip : i < pre.length := by simpa [RatioRequestListSpec.requests] using hi
    rw [← he]
    simp only [RatioRequestListSpec.requests,List.getElem_mapIdx]
    rw [request_length]
    have ho := hw pre[i] (List.getElem_mem hip)
    have hci := hc i
    omega
  have hf := fields_bound (RatioRequestListSpec.requests pre cs lambda) (6*L+3) hr
  have hn := EncodedGraph.natField_length_upper xs.length
  simp only [RatioRequestListSpec.request_length] at hf
  unfold RatioRequestListSpec.outputAt
  simp only [List.length_append]
  dsimp only [L] at *
  nlinarith

theorem pair_prefix_bound (xs cs pre : List (List Bool))
    (hpre : ∀ w ∈ pre,w ∈ xs) (hlen : pre.length ≤ xs.length) :
    (RatioPairListSpec.outputAt xs.length cs pre).length ≤
      100*(inputLength xs cs []+1)^2 := by
  let L := inputLength xs cs []
  have hx : xs.length ≤ L := (GaussRowCount.rows_le_input xs).trans (by dsimp [L,inputLength]; omega)
  have hp : pre.length ≤ L := hlen.trans hx
  have hw : ∀ w ∈ pre,w.length ≤ L := by
    intro w hm
    exact (word_le_packet xs w (hpre w hm)).trans (by dsimp [L,inputLength]; omega)
  have hc (i : Nat) : (RatioPairListSpec.coefficient cs i).length ≤ L :=
    (coefficient_le cs i).trans (by dsimp [L,inputLength]; omega)
  have hr : ∀ w ∈ RatioPairListSpec.pairs pre cs,w.length ≤ 4*L+2 := by
    intro w hm
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
    have hip : i < pre.length := by simpa [RatioPairListSpec.pairs] using hi
    rw [← he]
    simp only [RatioPairListSpec.pairs,List.getElem_mapIdx,RatioPairItem.pairWord,
      RatioPairSerializer.bytes,List.length_append,EncodedCommunication.field_length]
    have ho := hw pre[i] (List.getElem_mem hip)
    have hm := BankFieldProjection.result_length (1 : Fin 2) pre[i]
    have hci := hc i
    change (BankFieldProjection.result (1 : Fin 2) pre[i]).length ≤ _ at hm
    dsimp only [RatioPairItem.massWord]
    omega
  have hf := fields_bound (RatioPairListSpec.pairs pre cs) (4*L+2) hr
  have hn := EncodedGraph.natField_length_upper xs.length
  have hplen : (RatioPairListSpec.pairs pre cs).length=pre.length := by simp [RatioPairListSpec.pairs]
  rw [hplen] at hf
  unfold RatioPairListSpec.outputAt
  simp only [List.length_append]
  dsimp only [L] at *
  nlinarith

#print axioms request_prefix_bound
#print axioms pair_prefix_bound
end CurrentAdditive.RatioListClockBounds
