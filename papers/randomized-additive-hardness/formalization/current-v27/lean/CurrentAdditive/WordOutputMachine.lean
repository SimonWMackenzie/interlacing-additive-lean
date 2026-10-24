import CurrentAdditive.StreamingRun

/-! One-seed output cleanup: the streaming controller accumulates its bits
as a stack, and this finite TM2 controller copies them into ordinary word
order. Field search and seed enumeration remain separate. -/

namespace CurrentAdditive.FiniteFieldMachine.WordOutputMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineComposition
open EthInapproximability.CurrentPaper.SamplerMachine
open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
open CurrentAdditive.FiniteFieldConstructor.BitPrinter
open CurrentAdditive.FiniteFieldMachine.HornerNatBridge

abbrev Stack := StreamingBitMachine.Stack ⊕ Unit
abbrev Label := StreamingBitMachine.Label ⊕ Unit
abbrev Control := StreamingBitMachine.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (StreamingBitMachine.initial, none)
def finalWord : Stack := .inr ()
def streamOut : Stack := .inl StreamingBitMachine.output

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some ()) (StreamingBitMachine.program l)
  | .inr () => pop streamOut (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (push finalWord (fun s => s.2.getD false) (goto (fun _ => .inr ())))
        (load (fun _ => initial) halt))

def cfg (l : Option Label) (s : Control)
    (a y wa wo c m fuel x sx sa out final : List Bool) : Config :=
  ⟨l, s, Sum.elim
    (StreamingBitMachine.cfg none s.1 a y wa wo c m fuel x sx sa out).stk
    (fun _ => final)⟩

def run (t : ℕ) (q : Config) := ((advance program)^[t]) q

private theorem run_succ {q r : Config} (h : TM2.step program q = some r) (t : ℕ) :
    run (t + 1) q = run t r := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add (t u : ℕ) (q : Config) :
    run (t + u) q = run u (run t q) := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply]

private theorem step_reverse_cons (s : Control) (b : Bool)
    (a y wa wo c m fuel x sx sa out final : List Bool) :
    TM2.step program (cfg (some (.inr ())) s
      a y wa wo c m fuel x sx sa (b :: out) final) =
    some (cfg (some (.inr ())) (s.1, some b)
      a y wa wo c m fuel x sx sa out (b :: final)) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg,
    streamOut, finalWord, StreamingBitMachine.output, StreamingBitMachine.cfg,
    StreamingBitMachine.foreign, Sum.elim_inl, Sum.elim_inr]
  simp only [show (4 : Fin 5) ≠ 0 by decide,
    show (4 : Fin 5) ≠ 1 by decide,
    show (4 : Fin 5) ≠ 2 by decide,
    show (4 : Fin 5) ≠ 3 by decide,
    if_neg, ↓reduceIte, List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

private theorem step_reverse_nil (s : Control)
    (a y wa wo c m fuel x sx sa final : List Bool) :
    TM2.step program (cfg (some (.inr ())) s
      a y wa wo c m fuel x sx sa [] final) =
    some (cfg none initial a y wa wo c m fuel x sx sa [] final) := by
  dsimp only [TM2.step, TM2.stepAux, program, cfg,
    streamOut, StreamingBitMachine.output, StreamingBitMachine.cfg, StreamingBitMachine.foreign,
    Sum.elim_inl, Sum.elim_inr]
  simp only [show (4 : Fin 5) ≠ 0 by decide,
    show (4 : Fin 5) ≠ 1 by decide,
    show (4 : Fin 5) ≠ 2 by decide,
    show (4 : Fin 5) ≠ 3 by decide,
    if_neg, ↓reduceIte, List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with (k | k) | k <;> (try fin_cases k) <;> rfl

theorem reverse_run (s : Control)
    (a y wa wo c m fuel x sx sa out final : List Bool) :
    run (out.length + 1) (cfg (some (.inr ())) s
      a y wa wo c m fuel x sx sa out final) =
    cfg none initial a y wa wo c m fuel x sx sa []
      (out.reverse ++ final) := by
  induction out generalizing s final with
  | nil => simpa using (run_succ
      (step_reverse_nil s a y wa wo c m fuel x sx sa final) 0)
  | cons b out ih =>
      rw [List.length_cons, run_succ
        (step_reverse_cons s b a y wa wo c m fuel x sx sa out final)]
      simpa only [List.reverse_cons, List.append_assoc,
        List.singleton_append] using ih (s.1, some b) (b :: final)

theorem stream_call (d tail n : ℕ) (htail : tail < 2 ^ d)
    (hd : 0 < d) (x y : Fin (2 ^ d)) :
    let modulus := CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail
    let c := lowerWord d modulus
    ∃ t ≤ n * (d * (4 * d + 5) + 4 * d + 6) + 1,
      run t (cfg (some (.inl (.inr .check))) initial
        (encodeWord (xBits d ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩))
        (encodeWord (xBits d y)) [] [] (encodeWord c) []
        (List.replicate n true) (encodeWord (xBits d x)) [] [] [] []) =
      cfg (some (.inr ())) initial
        (encodeWord (xBits d ⟨power d modulus y.val n,
          power_lt d modulus y.val n hd
            (monicBits_lt d tail htail) (monicBits_topBit d tail htail)
            y.isLt⟩))
        (encodeWord (xBits d y)) [] [] (encodeWord c) [] []
        (encodeWord (xBits d x)) [] []
        (word d modulus n x.val y.val).reverse [] := by
  intro modulus c
  obtain ⟨t, ht, hr⟩ := StreamingRun.run_bitPrinter_word
    d tail n htail hd x y
  have hh : (StreamingBitMachine.run t
      (StreamingBitMachine.cfg (some (.inr .check)) StreamingBitMachine.initial
        (encodeWord (xBits d ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩))
        (encodeWord (xBits d y)) [] [] (encodeWord c) []
        (List.replicate n true) (encodeWord (xBits d x)) [] [] [])).l = none := by
    rw [hr]; rfl
  obtain ⟨t', ht', hrun⟩ := BitMachineSubroutine.lift_outputs
    StreamingBitMachine.program program (some ()) (fun _ => rfl)
    (none : Option Bool) (fun _ : Unit => [])
    (StreamingBitMachine.cfg (some (.inr .check)) StreamingBitMachine.initial
      (encodeWord (xBits d ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩))
      (encodeWord (xBits d y)) [] [] (encodeWord c) []
      (List.replicate n true) (encodeWord (xBits d x)) [] [] []) t hh
  change ∃ t' ≤ _, run t' _ = _
  refine ⟨t', ht'.trans ht, ?_⟩
  change ((advance program)^[t']) _ = _
  change ((advance program)^[t']) _ =
    liftCfg (some ()) (none : Option Bool) (fun _ : Unit => [])
      (StreamingBitMachine.run t _) at hrun
  rw [hr] at hrun
  exact hrun

/-- The normal-order word is written on a separate output stack. This is a
complete per-seed physical printer from prepared banks, with no reversed
output convention left to its caller. -/
theorem run_bitPrinter_word_ordered (d tail n : ℕ)
    (htail : tail < 2 ^ d) (hd : 0 < d)
    (x y : Fin (2 ^ d)) :
    let modulus := CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail
    let c := lowerWord d modulus
    ∃ t ≤ n * (d * (4 * d + 5) + 4 * d + 7) + 2,
      run t (cfg (some (.inl (.inr .check))) initial
        (encodeWord (xBits d ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩))
        (encodeWord (xBits d y)) [] [] (encodeWord c) []
        (List.replicate n true) (encodeWord (xBits d x)) [] [] [] []) =
      cfg none initial
        (encodeWord (xBits d ⟨power d modulus y.val n,
          power_lt d modulus y.val n hd
            (monicBits_lt d tail htail) (monicBits_topBit d tail htail)
            y.isLt⟩))
        (encodeWord (xBits d y)) [] [] (encodeWord c) [] []
        (encodeWord (xBits d x)) [] [] []
        (word d modulus n x.val y.val) := by
  intro modulus c
  obtain ⟨ts, hts, hs⟩ := stream_call d tail n htail hd x y
  have hr := reverse_run initial
    (encodeWord (xBits d ⟨power d modulus y.val n,
      power_lt d modulus y.val n hd
        (monicBits_lt d tail htail) (monicBits_topBit d tail htail)
        y.isLt⟩))
    (encodeWord (xBits d y)) [] [] (encodeWord c) [] []
    (encodeWord (xBits d x)) [] []
    (word d modulus n x.val y.val).reverse []
  simp only [List.length_reverse, word_length, List.reverse_reverse,
    List.append_nil] at hr
  refine ⟨ts + (n + 1), ?_, ?_⟩
  · calc
      ts + (n + 1) ≤
          (n * (d * (4 * d + 5) + 4 * d + 6) + 1) + (n + 1) :=
        Nat.add_le_add_right hts _
      _ = n * (d * (4 * d + 5) + 4 * d + 7) + 2 := by ring
  · rw [run_add, hs, hr]

#print axioms run_bitPrinter_word_ordered

end CurrentAdditive.FiniteFieldMachine.WordOutputMachine
