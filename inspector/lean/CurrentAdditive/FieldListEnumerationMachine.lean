import CurrentAdditive.SeedCallbackMachine
import CurrentAdditive.SeedPrinterInputBridge
import EthInapproximability.CurrentPaper.SamplerMachineCounterMap
import CurrentAdditive.CanonicalPackedFieldOrder
import CurrentAdditive.CanonicalNumericEntry

/-! Install the checked one-seed callback in the inherited physical binary
counter mapper. The selected lower-modulus bank and unary output length are
explicit preinitialized inputs. -/

namespace CurrentAdditive.FiniteFieldMachine.FieldListEnumerationMachine

set_option maxRecDepth 4096

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.SamplerEnumeration
open EthInapproximability.CurrentPaper.SamplerMachineIncrement
open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
open CurrentAdditive.FiniteFieldConstructor.BitPrinter
open CurrentAdditive.FiniteFieldMachine.SeedCallbackMachine

def row (d tail n : ℕ) (q : List Bool) : List Bool :=
  let modulus := CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail
  word d modulus n
    (EncodedCommunication.bitsValue (q.drop d))
    (EncodedCommunication.bitsValue (q.take d))

def inputBank (d tail n : ℕ) : SeedCallbackMachine.Stack → List Bool :=
  let modulus := CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail
  (SeedCallbackMachine.cfg none SeedCallbackMachine.initial
    [] [] [] []
    (SamplerMachine.encodeWord (HornerNatBridge.lowerWord d modulus))
    [] [] [] [] [] [] [] (List.replicate n true) []).stk

theorem mapper_bank (d tail n : ℕ) (q out : List Bool) :
    SamplerMachineCounterMap.bank SeedCallbackMachine.source
      SeedCallbackMachine.output (inputBank d tail n) q out =
    (SeedCallbackMachine.cfg none SeedCallbackMachine.initial
      [] [] [] []
      (SamplerMachine.encodeWord (HornerNatBridge.lowerWord d
        (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail)))
      [] [] [] [] [] [] q (List.replicate n true) out).stk := by
  funext k
  rcases k with ((((k | k) | k) | k) | k) <;> (try fin_cases k) <;>
    rfl

theorem decode_pair (d : ℕ) (q : List Bool) (hq : q.length = 2 * d) :
    ∃ x y : Fin (2 ^ d),
      q = SamplerMachine.encodeWord (xBits d y) ++
        SamplerMachine.encodeWord (xBits d x) ∧
      x.val = EncodedCommunication.bitsValue (q.drop d) ∧
      y.val = EncodedCommunication.bitsValue (q.take d) := by
  have hylen : (q.take d).length = d := by
    simp [List.length_take, hq]
    omega
  have hxlen : (q.drop d).length = d := by
    simp [List.length_drop, hq]
    omega
  let y : Fin (2 ^ d) :=
    ⟨EncodedCommunication.bitsValue (q.take d), by
      simpa only [hylen] using bitsValue_lt (q.take d)⟩
  let x : Fin (2 ^ d) :=
    ⟨EncodedCommunication.bitsValue (q.drop d), by
      simpa only [hxlen] using bitsValue_lt (q.drop d)⟩
  have hy : SamplerMachine.encodeWord (xBits d y) = q.take d := by
    rw [StreamingBitMachine.encodeWord_xBits]
    simpa only [hylen] using CounterNatBridge.natBits_bitsValue (q.take d)
  have hx : SamplerMachine.encodeWord (xBits d x) = q.drop d := by
    rw [StreamingBitMachine.encodeWord_xBits]
    simpa only [hxlen] using CounterNatBridge.natBits_bitsValue (q.drop d)
  refine ⟨x, y, ?_, rfl, rfl⟩
  rw [hy, hx]
  exact (List.take_append_drop d q).symm

theorem callback_contract (d tail n : ℕ)
    (htail : tail < 2 ^ d) (hd : 0 < d) :
    ∀ q out : List Bool, q.length = 2 * d →
      ∃ (t : ℕ) (v : SeedCallbackMachine.Control),
        t ≤ SeedCallbackMachine.callbackBound d n ∧
        ((advance SeedCallbackMachine.program)^[t])
          ⟨some (.inr (.inl SamplerMachineFactorSplit.Label.scanU)),
            SeedCallbackMachine.initial,
            SamplerMachineCounterMap.bank SeedCallbackMachine.source
              SeedCallbackMachine.output (inputBank d tail n) q out⟩ =
          ⟨none, v,
            SamplerMachineCounterMap.bank SeedCallbackMachine.source
              SeedCallbackMachine.output (inputBank d tail n) q
                ((row d tail n q).reverse ++ out)⟩ := by
  intro q out hq
  obtain ⟨x, y, hxy, hx, hy⟩ := decode_pair d q hq
  obtain ⟨t, ht, hr⟩ :=
    SeedCallbackMachine.run_seed_callback d tail n htail hd x y out
  have hrow : row d tail n q =
      word d (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail)
        n x.val y.val := by simp [row, hx, hy]
  refine ⟨t, SeedCallbackMachine.initial, ht, ?_⟩
  rw [mapper_bank, mapper_bank]
  dsimp only [SeedCallbackMachine.run] at hr
  rw [hrow]
  simpa only [hxy, SeedCallbackMachine.cfg] using hr

/-- The inherited binary-counter mapper is installed with the fully checked
field-word callback. It physically enumerates every `2d`-bit pair counter in
row-major order, preserving the selected lower-modulus and unary-length
banks. Its output stack contains the reverse of the flattened word list. -/
theorem map_all_field_words (d tail n : ℕ)
    (htail : tail < 2 ^ d) (hd : 0 < d) :
    ∃ (t : ℕ) (v : SeedCallbackMachine.Control) (last : List Bool),
      t ≤ 2 ^ (2 * d) *
        (SeedCallbackMachine.callbackBound d n + 8 * d + 6) ∧
      last.length = 2 * d ∧
      SamplerMachineCounterMap.run SeedCallbackMachine.program
        SeedCallbackMachine.source
        (.inr (.inl SamplerMachineFactorSplit.Label.scanU))
        SeedCallbackMachine.initial t
        (SamplerMachineCounterMap.cfg SeedCallbackMachine.source
          SeedCallbackMachine.output (inputBank d tail n)
          (some (.inl (.inr (.inl SamplerMachineFactorSplit.Label.scanU))))
          (SeedCallbackMachine.initial, false, none)
          (List.replicate (2 * d) false) [] []) =
      SamplerMachineCounterMap.cfg SeedCallbackMachine.source
        SeedCallbackMachine.output (inputBank d tail n)
        none (v, true, none) last
        (((SamplerEnumeration.counterWords (2 * d)).flatMap
          (row d tail n)).reverse) [] := by
  obtain ⟨t, v, last, ht, hlast, _, hr, _⟩ :=
    SamplerMachineCounterMap.map_allWords
      SeedCallbackMachine.program SeedCallbackMachine.source
      SeedCallbackMachine.output
      (.inr (.inl SamplerMachineFactorSplit.Label.scanU))
      SeedCallbackMachine.initial (inputBank d tail n)
      (by decide) (2 * d) (SeedCallbackMachine.callbackBound d n)
      (row d tail n) (callback_contract d tail n htail hd) []
  refine ⟨t, v, last, ?_, hlast, ?_⟩
  · simpa only [show 4 * (2 * d) = 8 * d by omega] using ht
  · simpa only [List.append_nil] using hr

/-- The counter mapper's flattened word sequence is the canonical packed
field-bit array used by the complete matrix constructor. Pair labels are
identified by their quotient/remainder numeric values. -/
theorem flatMap_row_eq_packed (d tail n : ℕ) :
    (SamplerEnumeration.counterWords (2 * d)).flatMap (row d tail n) =
      CurrentAdditive.FiniteFieldConstructor.CanonicalTable.packedFieldBits
        d (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail) n := by
  have hc : SamplerEnumeration.counterWords (2 * d) =
      List.ofFn (fun j : Fin ((2 ^ d) ^ 2) =>
        EthInapproximability.CurrentPaper.SamplerSeedEnumeration.counterAt d j) := by
    rw [EthInapproximability.CurrentPaper.SamplerSeedEnumeration.counterWords_seedOrder]
    congr 1
    funext j
    exact (EthInapproximability.CurrentPaper.SamplerSeedEnumeration.counterAt_eq d j).symm
  rw [hc, CurrentAdditive.FiniteFieldConstructor.CanonicalTable.packedFieldBits_eq_flatten_words]
  simp only [List.flatMap_def, List.map_ofFn, Function.comp_def]
  congr 1
  congr 1
  funext j
  obtain ⟨hy, hx⟩ := CounterNatBridge.counter_pair_values d j
  obtain ⟨hcx, hcy⟩ :=
    CurrentAdditive.FiniteFieldConstructor.CanonicalTable.seed_pair_decode_numeric d j
  simp only [row, EthInapproximability.CurrentPaper.SamplerSeedEnumeration.counterAt,
    hx, hy, hcx, hcy]

end CurrentAdditive.FiniteFieldMachine.FieldListEnumerationMachine
