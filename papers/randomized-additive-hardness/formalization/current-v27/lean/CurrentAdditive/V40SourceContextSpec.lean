import CurrentAdditive.D22PacketPrimitives
import CurrentAdditive.StoredStepContext
import CurrentAdditive.EdgeIndexedLawProduction

/-! The numerical item test used by the physical source-context writer.
The public order consists of four-s groups, each containing n vertices
followed by s-3 auxiliary items.  No law table is an input. -/
namespace CurrentAdditive.V40SourceContextSpec
noncomputable section
open EthInapproximability.CurrentPaper LiteralEdgeEncoder
open D22PolynomialExpression
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def auxiliaryCount (s : Nat) := s-3
def blockSize (s n : Nat) := n+auxiliaryCount s
def vertexFlag (s n i : Nat) : Nat :=
  if (i+auxiliaryCount s)/blockSize s n ≤ i/blockSize s n then 1 else 0
def auxiliaryFlag (s n i : Nat) : Nat :=
  if i/blockSize s n+1 ≤ (i+auxiliaryCount s)/blockSize s n then 1 else 0
def denominator (s n i : Nat) := 8*s*(n*vertexFlag s n i+auxiliaryCount s*auxiliaryFlag s n i)

theorem quot_vertex (s n : Nat) (hn : 0<n) (g : Fin (4*s)) (v : Fin n) :
    (itemNumber s n (g,.inl v)).val/blockSize s n=g.val ∧
    ((itemNumber s n (g,.inl v)).val+auxiliaryCount s)/blockSize s n=g.val := by
  have hd : 0<blockSize s n := by unfold blockSize; omega
  have hv : v.val<blockSize s n := by unfold blockSize; omega
  have hva : v.val+auxiliaryCount s<blockSize s n := by unfold blockSize; omega
  simp only [itemNumber_vertex]
  change (v.val+blockSize s n*g.val)/blockSize s n=g.val ∧
    (v.val+blockSize s n*g.val+auxiliaryCount s)/blockSize s n=g.val
  constructor
  · rw [Nat.add_mul_div_left _ _ hd,Nat.div_eq_of_lt hv,Nat.zero_add]
  · rw [show v.val+blockSize s n*g.val+auxiliaryCount s=
      v.val+auxiliaryCount s+blockSize s n*g.val by omega]
    rw [Nat.add_mul_div_left _ _ hd,Nat.div_eq_of_lt hva,Nat.zero_add]

theorem quot_auxiliary (s n : Nat) (hn : 0<n) (g : Fin (4*s)) (a : Fin (s-3)) :
    (itemNumber s n (g,.inr a)).val/blockSize s n=g.val ∧
    ((itemNumber s n (g,.inr a)).val+auxiliaryCount s)/blockSize s n=g.val+1 := by
  have hd : 0<blockSize s n := by unfold blockSize; omega
  have ha : n+a.val<blockSize s n := by unfold blockSize auxiliaryCount; omega
  have ha' : a.val<blockSize s n := by unfold blockSize auxiliaryCount; omega
  simp only [itemNumber_auxiliary]
  change (n+a.val+blockSize s n*g.val)/blockSize s n=g.val ∧
    (n+a.val+blockSize s n*g.val+auxiliaryCount s)/blockSize s n=g.val+1
  constructor
  · rw [Nat.add_mul_div_left _ _ hd,Nat.div_eq_of_lt ha,Nat.zero_add]
  · rw [show n+a.val+blockSize s n*g.val+auxiliaryCount s=
      a.val+blockSize s n*(g.val+1) by unfold blockSize; ring]
    rw [Nat.add_mul_div_left _ _ hd,Nat.div_eq_of_lt ha',Nat.zero_add]

theorem denominator_vertex (s n : Nat) (hn : 0<n) (g : Fin (4*s)) (v : Fin n) :
    denominator s n (itemNumber s n (g,.inl v)).val=8*s*n := by
  obtain ⟨h0,h1⟩:=quot_vertex s n hn g v
  unfold denominator vertexFlag auxiliaryFlag
  rw [h0,h1]
  simp

theorem denominator_auxiliary (s n : Nat) (hn : 0<n) (g : Fin (4*s)) (a : Fin (s-3)) :
    denominator s n (itemNumber s n (g,.inr a)).val=8*s*(s-3) := by
  obtain ⟨h0,h1⟩:=quot_auxiliary s n hn g a
  unfold denominator vertexFlag auxiliaryFlag
  rw [h0,h1]
  simp [auxiliaryCount]

theorem denominator_pos (s n : Nat) (hs : 4 ≤ s) (hn : 0<n)
    (i : Fin (4*s*(n+(s-3)))) : 0<denominator s n i.val := by
  obtain ⟨⟨g,z⟩,rfl⟩:=(itemNumber s n).surjective i
  cases z with
  | inl v => rw [denominator_vertex s n hn g v]; positivity
  | inr a =>
    rw [denominator_auxiliary s n hn g a]
    have : 0<s-3 := by omega
    positivity

theorem indexed_weight (s n : Nat) (hs : 4 ≤ s) (hn : 0<n)
    (i : Fin (4*s*(n+(s-3)))) :
    (indexedItemLaw s n hs hn).weight i=((denominator s n i.val:Nat):ℚ)⁻¹ := by
  obtain ⟨⟨g,z⟩,rfl⟩:=(itemNumber s n).surjective i
  cases z with
  | inl v => rw [indexedItemLaw_vertex,denominator_vertex s n hn g v]; push_cast; congr 1 <;> ring
  | inr a => rw [indexedItemLaw_auxiliary,denominator_auxiliary s n hn g a]; push_cast; congr 1 <;> ring

def entries (s n j : Nat) : List (List Bool) :=
  (List.range j).map (fun i => CodeDTargetV2.alphabetEntry (i,((denominator s n i:Nat):ℚ)⁻¹))

theorem lawBytes_eq (s n : Nat) (hs : 4 ≤ s) (hn : 0<n) :
    StoredWeightedState.lawBytes (indexedItemLaw s n hs hn)=
      SourceListEncoding.encode (entries s n (4*s*(n+(s-3)))) := by
  simp only [StoredWeightedState.lawBytes,StoredWeightedState.lawAlphabet,
    CodeDTargetV2.alphabetBytes,Array.toList_ofFn,List.map_ofFn,Function.comp_def]
  congr 1
  simp only [entries,indexed_weight]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

#print axioms indexed_weight
#print axioms lawBytes_eq
end
end CurrentAdditive.V40SourceContextSpec
