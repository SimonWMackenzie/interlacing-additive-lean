import CurrentAdditive.FieldListEnumerationMachine

/-! A literal terminal transfer puts the counter mapper's reversed global
stack into canonical row-major order on a fresh output stack. The selected
modulus and unary word length are supplied as explicit input banks. -/

namespace CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineComposition
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FiniteFieldMachine
open CurrentAdditive.FiniteFieldMachine.FieldListEnumerationMachine

abbrev InnerStack := SamplerMachineCounterMap.Stack SeedCallbackMachine.Stack
abbrev InnerLabel := SamplerMachineCounterMap.Label SeedCallbackMachine.Label
abbrev InnerControl := SamplerMachineCounterMap.Control SeedCallbackMachine.Control
abbrev InnerConfig := TM2.Cfg (fun _ : InnerStack => Bool) InnerLabel InnerControl

def innerProgram : InnerLabel → TM2.Stmt (fun _ : InnerStack => Bool) InnerLabel InnerControl :=
  SamplerMachineCounterMap.program SeedCallbackMachine.program
    SeedCallbackMachine.source (.inr (.inl SamplerMachineFactorSplit.Label.scanU))
    SeedCallbackMachine.initial

abbrev Stack := InnerStack ⊕ Unit
abbrev Label := InnerLabel ⊕ Unit
abbrev Control := InnerControl × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def innerOutput : Stack := .inl (.inl SeedCallbackMachine.output)
def output : Stack := .inr ()
def initial : Control := ((SeedCallbackMachine.initial, false, none), none)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some ()) (innerProgram l)
  | .inr () => pop innerOutput (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (push output (fun s => s.2.getD false) (goto (fun _ => .inr ())))
        (load (fun _ => initial) halt))

def cfg (l : Option Label) (s : Control)
    (S : InnerStack → List Bool) (done : List Bool) : Config :=
  ⟨l, s, Sum.elim S (fun _ => done)⟩

private instance finiteDecEq (m : Nat) : DecidableEq (Fin m) := instDecidableEqFin m

def stackDecEq : DecidableEq Stack :=
  @instDecidableEqSum InnerStack Unit (inferInstanceAs (DecidableEq InnerStack))
    (inferInstanceAs (DecidableEq Unit))

def run (t : ℕ) (q : Config) :=
  ((@advance Stack Label Control stackDecEq program)^[t]) q

theorem run_eq_any (D : DecidableEq Stack) (t : ℕ) (q : Config) :
    run t q = ((@advance Stack Label Control D program)^[t]) q := by
  have h : stackDecEq = D := Subsingleton.elim _ _
  unfold run
  rw [h]

private theorem run_add (t s : ℕ) (q : Config) :
    run (t + s) q = run t (run s q) :=
  Function.iterate_add_apply _ _ _ _

private theorem run_succ {c e : Config} (h : TM2.step program c = some e) (t : ℕ) :
    run (t + 1) c = run t e := by
  rw [run_eq_any (inferInstance : DecidableEq Stack),
    run_eq_any (inferInstance : DecidableEq Stack)]
  simp only [Function.iterate_succ_apply, advance, h, Option.getD_some]

theorem step_reverse_cons (s : Control) (S : InnerStack → List Bool)
    (bits done : List Bool) (b : Bool)
    (hS : S (.inl SeedCallbackMachine.output) = b :: bits) :
    TM2.step program (cfg (some (.inr ())) s S done) =
      some (cfg (some (.inr ())) (s.1, some b)
        (Function.update S (.inl SeedCallbackMachine.output) bits) (b :: done)) := by
  simp only [TM2.step, TM2.stepAux, program, cfg, innerOutput, output,
    Sum.elim_inl, hS, List.head?_cons, List.tail_cons,
    Option.isSome_some, Option.getD_some, Bool.cond_true]
  congr 1
  apply congrArg (fun T : Stack → List Bool =>
    (⟨some (.inr ()), (s.1, some b), T⟩ : Config))
  funext k
  rcases k with k | k
  · simp only [Sum.elim_inl]
    by_cases hk : k = (.inl SeedCallbackMachine.output : InnerStack)
    · subst k
      simp only [Function.update_of_ne
        (show (Sum.inl (.inl SeedCallbackMachine.output) : Stack) ≠ .inr () by simp),
        Function.update_self]
    · have hk' : (Sum.inl k : Stack) ≠
          (.inl (.inl SeedCallbackMachine.output) : Stack) := by
        simpa only [ne_eq, Sum.inl.injEq] using hk
      simp only [Function.update_of_ne
        (show (Sum.inl k : Stack) ≠ .inr () by simp),
        Function.update_of_ne hk', Sum.elim_inl]
      exact (Function.update_of_ne hk bits S).symm
  · cases k
    simp only [Function.update_self,
      Function.update_of_ne
        (show (Sum.inr () : Stack) ≠ .inl (.inl SeedCallbackMachine.output) by simp),
      Sum.elim_inr]

theorem step_reverse_nil (s : Control) (S : InnerStack → List Bool)
    (done : List Bool) (hS : S (.inl SeedCallbackMachine.output) = []) :
    TM2.step program (cfg (some (.inr ())) s S done) =
      some (cfg none initial S done) := by
  simp only [TM2.step, TM2.stepAux, program, cfg, innerOutput, output,
    Sum.elim_inl, hS, List.head?_nil, List.tail_nil,
    Option.isSome_none, Bool.cond_false]
  congr 1
  apply congrArg (fun T : Stack → List Bool =>
    (⟨none, initial, T⟩ : Config))
  funext k
  rcases k with k | k
  · simp only [Sum.elim_inl]
    by_cases hk : k = (.inl SeedCallbackMachine.output : InnerStack)
    · subst k
      simp only [Function.update_self, hS]
    · have hk' : (Sum.inl k : Stack) ≠
          (.inl (.inl SeedCallbackMachine.output) : Stack) := by
        simpa only [ne_eq, Sum.inl.injEq] using hk
      simp only [Function.update_of_ne hk', Sum.elim_inl]
  · cases k
    simp only [Function.update_of_ne
      (show (Sum.inr () : Stack) ≠ .inl (.inl SeedCallbackMachine.output) by simp),
      Sum.elim_inr]

theorem reverse_run (s : Control) (S : InnerStack → List Bool)
    (bits done : List Bool)
    (hS : S (.inl SeedCallbackMachine.output) = bits) :
    run (bits.length + 1)
      (cfg (some (.inr ())) s S done) =
      cfg none initial
        (Function.update S (.inl SeedCallbackMachine.output) [])
        (bits.reverse ++ done) := by
  induction bits generalizing s S done with
  | nil =>
      have he : Function.update S (.inl SeedCallbackMachine.output) [] = S := by
        rw [← hS, Function.update_eq_self]
      simpa [he] using run_succ (step_reverse_nil s S done hS) 0
  | cons b bits ih =>
      rw [List.length_cons, run_succ (step_reverse_cons s S bits done b hS)]
      have hS' : (Function.update S (.inl SeedCallbackMachine.output) bits)
          (.inl SeedCallbackMachine.output) = bits := by simp
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        Function.update_idem] using
        ih (s.1, some b) (Function.update S (.inl SeedCallbackMachine.output) bits)
          (b :: done) hS'

def mapStart (d tail n : ℕ) : InnerConfig :=
  SamplerMachineCounterMap.cfg SeedCallbackMachine.source SeedCallbackMachine.output
    (inputBank d tail n)
    (some (.inl (.inr (.inl SamplerMachineFactorSplit.Label.scanU))))
    (SeedCallbackMachine.initial, false, none)
    (List.replicate (2 * d) false) [] []

def mapEnd (d tail n : ℕ) (v : SeedCallbackMachine.Control)
    (last reversed : List Bool) : InnerConfig :=
  SamplerMachineCounterMap.cfg SeedCallbackMachine.source SeedCallbackMachine.output
    (inputBank d tail n) none (v, true, none) last reversed []

theorem mapStart_call
    (l : Option InnerLabel) (s : InnerControl) (S : InnerStack → List Bool) :
    liftCfg (some ()) (none : Option Bool) (fun _ : Unit => [])
      (⟨l, s, S⟩ : InnerConfig) =
      cfg (match l with | none => some (.inr ()) | some a => some (.inl a))
        (s, none) S [] := by
  cases l <;> rfl

theorem map_call (d tail n : ℕ)
    (htail : tail < 2 ^ d) (hd : 0 < d) :
    ∃ (t : ℕ) (v : SeedCallbackMachine.Control) (last : List Bool),
      t ≤ 2 ^ (2 * d) *
        (SeedCallbackMachine.callbackBound d n + 8 * d + 6) ∧
      last.length = 2 * d ∧
      run t (cfg (some (.inl (.inl (.inr (.inl
        SamplerMachineFactorSplit.Label.scanU))))) initial (mapStart d tail n).stk []) =
        cfg (some (.inr ())) ((v, true, none), none)
          (mapEnd d tail n v last
            (CurrentAdditive.FiniteFieldConstructor.CanonicalTable.packedFieldBits d
              (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail) n).reverse).stk
          [] := by
  obtain ⟨t, v, last, ht, hlast, hr⟩ := map_all_field_words d tail n htail hd
  rw [flatMap_row_eq_packed] at hr
  let c := mapStart d tail n
  have hrun : ((advance innerProgram)^[t]) c =
      mapEnd d tail n v last
        (CurrentAdditive.FiniteFieldConstructor.CanonicalTable.packedFieldBits d
          (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail) n).reverse := by
    simpa only [c, mapStart, mapEnd, innerProgram,
      SamplerMachineCounterMap.run] using hr
  have hhalt : (((advance innerProgram)^[t]) c).l = none := by
    rw [hrun]; rfl
  obtain ⟨t', ht', hcall⟩ := BitMachineSubroutine.lift_outputs
    innerProgram program (some ()) (fun _ => rfl)
    (none : Option Bool) (fun _ : Unit => []) c t hhalt
  rw [hrun] at hcall
  have hcall' : run t' (liftCfg (some ()) none (fun _ : Unit => []) c) =
      liftCfg (some ()) none (fun _ : Unit => [])
        (mapEnd d tail n v last
          (CurrentAdditive.FiniteFieldConstructor.CanonicalTable.packedFieldBits d
            (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail) n).reverse) := by
    rw [run_eq_any
      (@instDecidableEqSum InnerStack Unit
        (inferInstanceAs (DecidableEq InnerStack))
        (inferInstanceAs (DecidableEq Unit)))]
    exact hcall
  rw [mapStart_call, mapStart_call] at hcall'
  exact ⟨t', v, last, ht'.trans ht, hlast, hcall'⟩

theorem mapEnd_output (d tail n : ℕ) (v : SeedCallbackMachine.Control)
    (last reversed : List Bool) :
    (mapEnd d tail n v last reversed).stk (.inl SeedCallbackMachine.output) =
      reversed := by
  rfl

def timeBound (d _tail n : ℕ) : ℕ :=
  2 ^ (2 * d) * (SeedCallbackMachine.callbackBound d n + 8 * d + 6) +
    (2 ^ d) ^ 2 * n + 1

/-- A finite TM2 program physically emits the exact canonical packed array
for the selected monic modulus. Its only preinitialized data are the
lower-modulus bit word and unary output length in `inputBank`. -/
theorem run_packed_field_bits (d tail n : ℕ)
    (htail : tail < 2 ^ d) (hd : 0 < d) :
    ∃ (t : ℕ) (v : SeedCallbackMachine.Control) (last : List Bool),
      t ≤ timeBound d tail n ∧ last.length = 2 * d ∧
      run t (cfg (some (.inl (.inl (.inr (.inl
        SamplerMachineFactorSplit.Label.scanU))))) initial (mapStart d tail n).stk []) =
        cfg none initial
          (Function.update
            (mapEnd d tail n v last
              (CurrentAdditive.FiniteFieldConstructor.CanonicalTable.packedFieldBits d
                (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail) n).reverse).stk
            (.inl SeedCallbackMachine.output) [])
          (CurrentAdditive.FiniteFieldConstructor.CanonicalTable.packedFieldBits d
            (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail) n) := by
  let bits := CurrentAdditive.FiniteFieldConstructor.CanonicalTable.packedFieldBits d
    (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail) n
  obtain ⟨t, v, last, ht, hlast, hr⟩ := map_call d tail n htail hd
  have hS := mapEnd_output d tail n v last bits.reverse
  have hrev := reverse_run ((v, true, none), none)
    (mapEnd d tail n v last bits.reverse).stk bits.reverse [] hS
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hrev
  refine ⟨bits.length + 1 + t, v, last, ?_, hlast, ?_⟩
  · rw [CurrentAdditive.FiniteFieldConstructor.CanonicalTable.packedFieldBits_length]
    unfold timeBound
    omega
  · rw [run_add, hr, hrev]

/-- The literal transition bound for the selected-modulus field list is
quadratic in the field size and in the bit width, and linear in the word
length. This excludes the separately implemented modulus search. -/
theorem timeBound_le (d tail n : ℕ) (hd : 0 < d) (hn : 0 < n) :
    timeBound d tail n ≤ 25 * (2 ^ d) ^ 2 * n * (d + 1) ^ 2 := by
  have hdd : d ≤ d * d := by
    nlinarith [Nat.mul_le_mul_left d hd]
  have hpoly : d * (4 * d + 5) + 4 * d + 11 ≤ 7 * (d + 1) ^ 2 := by
    nlinarith
  have htail : 17 * d + 24 ≤ 18 * (d + 1) ^ 2 := by
    nlinarith
  have htailn : 18 * (d + 1) ^ 2 ≤ n * (18 * (d + 1) ^ 2) := by
    calc
      18 * (d + 1) ^ 2 = 1 * (18 * (d + 1) ^ 2) := by omega
      _ ≤ n * (18 * (d + 1) ^ 2) := Nat.mul_le_mul_right _ hn
  have hper : SeedCallbackMachine.callbackBound d n + 8 * d + 6 + n + 1 ≤
      25 * n * (d + 1) ^ 2 := by
    dsimp [SeedCallbackMachine.callbackBound]
    have hmul := Nat.mul_le_mul_left n hpoly
    nlinarith
  have hR : 1 ≤ (2 ^ d) ^ 2 := by
    have hp : 0 < (2 ^ d) ^ 2 := by positivity
    omega
  have hpow : 2 ^ (2 * d) = (2 ^ d) ^ 2 := by
    rw [show 2 * d = d * 2 by omega, pow_mul]
  unfold timeBound
  rw [hpow]
  have hmul := Nat.mul_le_mul_left ((2 ^ d) ^ 2) hper
  nlinarith

end CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine
