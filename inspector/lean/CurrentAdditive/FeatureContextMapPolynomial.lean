import CurrentAdditive.FeatureMapCaps

set_option maxHeartbeats 2500000
set_option maxRecDepth 10000
set_option maxSynthPendingDepth 100
noncomputable section
namespace CurrentAdditive.FeatureContextMapPolynomial
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussListContext FeatureMapPairLoader FeatureMapInvoke FeatureMapSizeBounds
open CurrentAdditive.MinimumRatioContext EntryClockPoly FeatureMapCaps

syntax "solve_map_poly" : tactic
macro_rules
| `(tactic| solve_map_poly) => `(tactic|
  first
  | assumption
  | exact PolyIn.self
  | apply PolyIn.const
  | apply PolyIn.add <;> solve_map_poly
  | apply PolyIn.mul <;> solve_map_poly
  | apply PolyIn.pow <;> solve_map_poly)

theorem fullCap_poly {ι : Type*} (U F : ι → Nat) (hF : PolyIn U F)
    (M : BitMachine.Machine) (framed : Bool) :
    PolyIn U (fun i => fullCap M framed (F i)) := by
  have ht : PolyIn U (fun i => timeCap (F i)) := by unfold timeCap; solve_map_poly
  have hc : PolyIn U (fun i => countTimeCap (F i)) := by unfold countTimeCap; solve_map_poly
  have hh : PolyIn U (fun i => headerTimeCap (F i)) := by unfold headerTimeCap; solve_map_poly
  have hi := invoke_poly U (evaluator M framed) F (fun i => timeCap (F i)) hF ht
  have hiC := invoke_poly U FeatureMapListCount.machine F (fun i => countTimeCap (F i)) hF hc
  have hiH := invoke_poly U (FeatureMapHeaders.machine framed) F (fun i => headerTimeCap (F i)) hF hh
  unfold fullCap initializeCap cycleCap callbackCap coreCap loadedCap outputCap pieceCap
  solve_map_poly

def totalBudget (M : BitMachine.Machine) (framed : Bool) (context : List Bool)
    (xs : List (List Bool)) (f : List Bool → List Bool) (b : List Bool → Nat) :=
  FeatureMapInitialize.budget framed context xs+
    ContextMapClockModel.sumCap M framed context (FeatureMapHeaders.output framed xs.length) f b [] xs+1

theorem sum_le (M : BitMachine.Machine) (framed : Bool) (context : List Bool)
    (xs pre suf : List (List Bool)) (hs : pre++suf=xs)
    (f : List Bool → List Bool) (b : List Bool → Nat) (P Q n : Nat)
    (hP : ∀ w∈xs,b w ≤ P) (hQ : ∀ w∈xs,(f w).length ≤ Q)
    (hL : inputSize context xs ≤ n) (hPn : P ≤ n) (hQn : Q ≤ n) :
    ContextMapClockModel.sumCap M framed context (FeatureMapHeaders.output framed xs.length)
      f b pre suf ≤ (suf.length+1)*(cycleCap M framed n+1) := by
  induction suf generalizing pre with
  | nil => simp [ContextMapClockModel.sumCap]
  | cons w tail ih =>
    have hc := cycle_le M framed context xs pre w tail hs f b P Q n hP hQ hL hPn hQn
    have hn : (pre++[w])++tail=xs := by simpa [List.append_assoc] using hs
    have ht := ih (pre++[w]) hn
    simp only [ContextMapClockModel.sumCap,List.length_cons]
    nlinarith

theorem total_le (M : BitMachine.Machine) (framed : Bool) (context : List Bool)
    (xs : List (List Bool)) (f : List Bool → List Bool) (b : List Bool → Nat)
    (P Q n : Nat) (hP : ∀ w∈xs,b w ≤ P) (hQ : ∀ w∈xs,(f w).length ≤ Q)
    (hL : inputSize context xs ≤ n) (hPn : P ≤ n) (hQn : Q ≤ n) :
    totalBudget M framed context xs f b ≤ fullCap M framed n := by
  have hi := initialize_le framed context xs n hL
  have hs := sum_le M framed context xs [] xs (by simp) f b P Q n hP hQ hL hPn hQn
  have hcount := ((basic_bounds context xs).2.2).trans hL
  have hm := Nat.mul_le_mul_right (cycleCap M framed n+1) (Nat.add_le_add_right hcount 1)
  exact Nat.add_le_add_right (Nat.add_le_add hi (hs.trans hm)) 1

/-- Pure whole-map clock bound. The original item machine is fixed before
all input words and all callback/output bounds. No successful-map premise
or desired output certificate occurs in this scalar theorem. -/
theorem uniform_budget (M : BitMachine.Machine) (framed : Bool) : ∃ K E : Nat,
    ∀ (context : List Bool) (xs : List (List Bool))
      (f : List Bool → List Bool) (b : List Bool → Nat) (P Q : Nat),
      (∀ w∈xs,b w ≤ P) → (∀ w∈xs,(f w).length ≤ Q) →
      totalBudget M framed context xs f b ≤ K*(inputSize context xs+P+Q+1)^E := by
  obtain ⟨K,E,h⟩ := fullCap_poly (fun n : Nat => n) (fun n => n) PolyIn.self M framed
  refine ⟨K,E,?_⟩
  intro context xs f b P Q hP hQ
  exact (total_le M framed context xs f b P Q (inputSize context xs+P+Q)
    hP hQ (by omega) (by omega) (by omega)).trans (h _)

def coefficient (M : BitMachine.Machine) (framed : Bool) := Classical.choose (uniform_budget M framed)
def exponent (M : BitMachine.Machine) (framed : Bool) :=
  Classical.choose (Classical.choose_spec (uniform_budget M framed))

theorem budget_le_uniform (M : BitMachine.Machine) (framed : Bool)
    (context : List Bool) (xs : List (List Bool))
    (f : List Bool → List Bool) (b : List Bool → Nat) (P Q : Nat)
    (hP : ∀ w∈xs,b w ≤ P) (hQ : ∀ w∈xs,(f w).length ≤ Q) :
    totalBudget M framed context xs f b ≤
      coefficient M framed*(inputSize context xs+P+Q+1)^exponent M framed :=
  Classical.choose_spec (Classical.choose_spec (uniform_budget M framed)) context xs f b P Q hP hQ

/-- A uniform actual per-item machine clock also bounds every intermediate
answer length by physical output growth. Substituting it into the pure map
clock gives one polynomial in the original encoded context/list packet. -/
theorem uniform_from_callback (M : BitMachine.Machine) (framed : Bool) (a e : Nat) :
    ∃ K E : Nat,∀ (context : List Bool) (xs : List (List Bool))
      (f : List Bool → List Bool) (b : List Bool → Nat),
      (∀ w∈xs,M.OutputsWithin (packet context w) (f w) (b w)) →
      (∀ w∈xs,b w ≤ a*((packet context w).length+1)^e) →
      totalBudget M framed context xs f b ≤ K*(inputSize context xs+1)^E := by
  let p (n : Nat) := a*(n+1)^e
  let sizeCap (n : Nat) := n+p n+(n+p n*M.pushBound)
  have hp : PolyIn (fun n : Nat => n) p := by unfold p; solve_map_poly
  have hn : PolyIn (fun n : Nat => n) sizeCap := by unfold sizeCap; solve_map_poly
  obtain ⟨K,E,hK⟩ := fullCap_poly (fun n : Nat => n) sizeCap hn M framed
  refine ⟨K,E,?_⟩
  intro context xs f b hM hb
  let L := inputSize context xs
  let P := p L
  let Q := L+P*M.pushBound
  have hP (w : List Bool) (hw : w∈xs) : b w ≤ P := by
    apply (hb w hw).trans
    dsimp only [P,p]
    gcongr
    exact packet_item_le context xs w hw
  have hQ (w : List Bool) (hw : w∈xs) : (f w).length ≤ Q :=
    (BitMachine.output_length_bound M (hM w hw)).trans
      (Nat.add_le_add (packet_item_le context xs w hw) (Nat.mul_le_mul_right M.pushBound (hP w hw)))
  exact (total_le M framed context xs f b P Q (sizeCap L) hP hQ
    (by dsimp [sizeCap,L]; omega) (by dsimp [sizeCap,P]; omega)
    (by dsimp [sizeCap,Q,P]; omega)).trans (hK L)

#print axioms uniform_budget
#print axioms budget_le_uniform
#print axioms uniform_from_callback
end CurrentAdditive.FeatureContextMapPolynomial
