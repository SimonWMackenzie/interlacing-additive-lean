import Paper2.GeneratorCode
import Mathlib.Tactic

/-! A fixed, suffix-preserving binary serialization of first-order generator
syntax. This proves an encoded-data interface, not physical decoder runtime. -/

namespace Paper2.GeneratorSerialization

open Paper2.GeneratorCode

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

def unary (n : Nat) : List Bool := List.replicate n true ++ [false]

theorem unary_length (n : Nat) : (unary n).length = n + 1 := by
  simp [unary]

theorem decodeUnary_unary (n : Nat) (rest : List Bool) :
    RecursiveLabelCodecScratch.decodeUnary (unary n ++ rest) = some (n, rest) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have h : RecursiveLabelCodecScratch.decodeUnary
          (List.replicate n true ++ false :: rest) = some (n, rest) := by
        simpa [unary] using ih
      simp [unary, List.replicate_succ, List.append_assoc,
        RecursiveLabelCodecScratch.decodeUnary, h]

def takeExact : Nat → List Bool → Option (List Bool × List Bool)
  | 0, bits => some ([], bits)
  | _ + 1, [] => none
  | n + 1, b :: bits => do
      let (taken, rest) ← takeExact n bits
      pure (b :: taken, rest)

theorem takeExact_append (bits rest : List Bool) :
    takeExact bits.length (bits ++ rest) = some (bits, rest) := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [takeExact, ih]

def encodeCode : Code → List Bool
  | .emit bits => [false, false, false] ++ unary bits.length ++ bits
  | .ticket n => [false, false, true] ++ unary n
  | .bit => [false, true, false]
  | .append left right => [false, true, true] ++ encodeCode left ++ encodeCode right
  | .branch3 n a b first second third =>
      [true, false, false] ++ unary n ++ unary a ++ unary b ++
        encodeCode first ++ encodeCode second ++ encodeCode third

def codeSize : Code → Nat
  | .emit bits => 3 + (bits.length + 1) + bits.length
  | .ticket n => 3 + (n + 1)
  | .bit => 3
  | .append left right => 3 + codeSize left + codeSize right
  | .branch3 n a b first second third =>
      3 + (n + 1) + (a + 1) + (b + 1) +
        codeSize first + codeSize second + codeSize third

theorem encodeCode_length (c : Code) : (encodeCode c).length = codeSize c := by
  induction c with
  | emit bits => simp [encodeCode, codeSize, unary_length]; omega
  | ticket n => simp [encodeCode, codeSize, unary_length]; omega
  | bit => rfl
  | append left right ihl ihr => simp [encodeCode, codeSize, ihl, ihr]; omega
  | branch3 n a b first second third ihf ihs iht =>
      simp [encodeCode, codeSize, unary_length, ihf, ihs, iht]
      omega

def depth : Code → Nat
  | .emit _ | .ticket _ | .bit => 1
  | .append left right => 1 + max (depth left) (depth right)
  | .branch3 _ _ _ first second third =>
      1 + max (depth first) (max (depth second) (depth third))

theorem depth_pos (c : Code) : 0 < depth c := by
  cases c <;> simp [depth]

def decodeFuel : Nat → List Bool → Option (Code × List Bool)
  | 0, _ => none
  | fuel + 1, bits =>
      match bits with
      | false :: false :: false :: tail => do
          let (n, rest) ← RecursiveLabelCodecScratch.decodeUnary tail
          let (word, rest) ← takeExact n rest
          pure (.emit word, rest)
      | false :: false :: true :: tail => do
          let (n, rest) ← RecursiveLabelCodecScratch.decodeUnary tail
          pure (.ticket n, rest)
      | false :: true :: false :: tail => some (.bit, tail)
      | false :: true :: true :: tail => do
          let (left, rest) ← decodeFuel fuel tail
          let (right, rest) ← decodeFuel fuel rest
          pure (.append left right, rest)
      | true :: false :: false :: tail => do
          let (n, rest) ← RecursiveLabelCodecScratch.decodeUnary tail
          let (a, rest) ← RecursiveLabelCodecScratch.decodeUnary rest
          let (b, rest) ← RecursiveLabelCodecScratch.decodeUnary rest
          let (first, rest) ← decodeFuel fuel rest
          let (second, rest) ← decodeFuel fuel rest
          let (third, rest) ← decodeFuel fuel rest
          pure (.branch3 n a b first second third, rest)
      | _ => none

theorem decodeFuel_roundtrip (c : Code) (rest : List Bool) (fuel : Nat)
    (hf : depth c ≤ fuel) :
    decodeFuel fuel (encodeCode c ++ rest) = some (c, rest) := by
  induction c generalizing rest fuel with
  | emit bits =>
      cases fuel with
      | zero => simp [depth] at hf
      | succ fuel =>
          simp [encodeCode, decodeFuel, decodeUnary_unary, takeExact_append,
            List.append_assoc]
  | ticket n =>
      cases fuel with
      | zero => simp [depth] at hf
      | succ fuel => simp [encodeCode, decodeFuel, decodeUnary_unary]
  | bit =>
      cases fuel with
      | zero => simp [depth] at hf
      | succ fuel => simp [encodeCode, decodeFuel]
  | append left right ihl ihr =>
      cases fuel with
      | zero => simp [depth] at hf
      | succ fuel =>
          have hl : depth left ≤ fuel := by simp [depth] at hf; omega
          have hr : depth right ≤ fuel := by simp [depth] at hf; omega
          simp [encodeCode, decodeFuel, List.append_assoc, ihl _ fuel hl,
            ihr _ fuel hr]
  | branch3 n a b first second third ihf ihs iht =>
      cases fuel with
      | zero => simp [depth] at hf
      | succ fuel =>
          have hfirst : depth first ≤ fuel := by simp [depth] at hf; omega
          have hsecond : depth second ≤ fuel := by simp [depth] at hf; omega
          have hthird : depth third ≤ fuel := by simp [depth] at hf; omega
          simp [encodeCode, decodeFuel, decodeUnary_unary,
            List.append_assoc, ihf _ fuel hfirst, ihs _ fuel hsecond,
            iht _ fuel hthird]

theorem encodeCode_injective : Function.Injective encodeCode := by
  intro c d h
  let fuel := max (depth c) (depth d)
  have hc : depth c ≤ fuel := Nat.le_max_left _ _
  have hd : depth d ≤ fuel := Nat.le_max_right _ _
  have heq : some (c, ([] : List Bool)) = some (d, ([] : List Bool)) := by
    calc
      some (c, ([] : List Bool)) = decodeFuel fuel (encodeCode c ++ []) :=
        (decodeFuel_roundtrip c [] fuel hc).symm
      _ = decodeFuel fuel (encodeCode d ++ []) := by rw [h]
      _ = some (d, ([] : List Bool)) := decodeFuel_roundtrip d [] fuel hd
  exact congrArg Prod.fst (Option.some.inj heq)

def encodeCodes : List Code → List Bool
  | [] => []
  | c :: cs => encodeCode c ++ encodeCodes cs

def codesSize : List Code → Nat
  | [] => 0
  | c :: cs => codeSize c + codesSize cs

theorem encodeCodes_length (cs : List Code) :
    (encodeCodes cs).length = codesSize cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [encodeCodes, codesSize, encodeCode_length, ih]

def decodeCodes (fuel : Nat) : Nat → List Bool → Option (List Code × List Bool)
  | 0, bits => some ([], bits)
  | n + 1, bits => do
      let (c, rest) ← decodeFuel fuel bits
      let (cs, rest) ← decodeCodes fuel n rest
      pure (c :: cs, rest)

theorem decodeCodes_roundtrip (cs : List Code) (rest : List Bool) (fuel : Nat)
    (hf : ∀ c ∈ cs, depth c ≤ fuel) :
    decodeCodes fuel cs.length (encodeCodes cs ++ rest) = some (cs, rest) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      have hc : depth c ≤ fuel := hf c (by simp)
      have hcs : ∀ d ∈ cs, depth d ≤ fuel := by
        intro d hd
        exact hf d (by simp [hd])
      simp [decodeCodes, encodeCodes, List.append_assoc,
        decodeFuel_roundtrip c _ fuel hc, ih hcs]

def encodeState (s : State) : List Bool :=
  unary s.todo.length ++ encodeCodes s.todo ++ unary s.output.length ++ s.output

def stateSize (s : State) : Nat :=
  (s.todo.length + 1) + codesSize s.todo + (s.output.length + 1) + s.output.length

theorem encodeState_length (s : State) :
    (encodeState s).length = stateSize s := by
  simp [encodeState, stateSize, unary_length, encodeCodes_length]
  omega

def decodeState (fuel : Nat) (bits : List Bool) : Option (State × List Bool) := do
  let (n, rest) ← RecursiveLabelCodecScratch.decodeUnary bits
  let (todo, rest) ← decodeCodes fuel n rest
  let (m, rest) ← RecursiveLabelCodecScratch.decodeUnary rest
  let (output, rest) ← takeExact m rest
  pure (⟨todo, output⟩, rest)

def stateFuel (s : State) : Nat := (s.todo.map depth).sum

theorem depth_le_stateFuel (s : State) (c : Code) (hc : c ∈ s.todo) :
    depth c ≤ stateFuel s := by
  unfold stateFuel
  have hm : depth c ∈ s.todo.map depth := List.mem_map.mpr ⟨c, hc, rfl⟩
  exact List.le_sum_of_mem hm

theorem decodeState_roundtrip (s : State) (rest : List Bool) (fuel : Nat)
    (hf : stateFuel s ≤ fuel) :
    decodeState fuel (encodeState s ++ rest) = some (s, rest) := by
  have hcodes : ∀ c ∈ s.todo, depth c ≤ fuel := by
    intro c hc
    exact (depth_le_stateFuel s c hc).trans hf
  cases s with
  | mk todo output =>
      simp [encodeState, decodeState, List.append_assoc, decodeUnary_unary,
        decodeCodes_roundtrip todo _ fuel hcodes, takeExact_append]

theorem encodeState_injective : Function.Injective encodeState := by
  intro s t h
  let fuel := max (stateFuel s) (stateFuel t)
  have hs : stateFuel s ≤ fuel := Nat.le_max_left _ _
  have ht : stateFuel t ≤ fuel := Nat.le_max_right _ _
  have heq : some (s, ([] : List Bool)) = some (t, ([] : List Bool)) := by
    calc
      some (s, ([] : List Bool)) = decodeState fuel (encodeState s ++ []) :=
        (decodeState_roundtrip s [] fuel hs).symm
      _ = decodeState fuel (encodeState t ++ []) := by rw [h]
      _ = some (t, ([] : List Bool)) := decodeState_roundtrip t [] fuel ht
  exact congrArg Prod.fst (Option.some.inj heq)

#print axioms decodeFuel_roundtrip
#print axioms encodeCode_injective
#print axioms encodeCode_length
#print axioms decodeCodes_roundtrip
#print axioms decodeState_roundtrip
#print axioms encodeState_injective
#print axioms encodeState_length

end Paper2.GeneratorSerialization
