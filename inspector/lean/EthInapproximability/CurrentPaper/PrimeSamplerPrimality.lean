import EthInapproximability.CurrentPaper.PrimeSamplerDivision
import EthInapproximability.CurrentPaper.PrimeSamplerTrial
import EthInapproximability.CurrentPaper.BitMachineBroadcast
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# Unary primality testing by literal trial division

Source: frozen v8 `B-effectivity-details.tex`,
`lem:paper-explicit-balanced-family`. The seven Boolean stacks implement
trial division while retaining the original candidate for the outer search.
Neither a candidate nor a divisor is stored in finite control.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerPrimality

open Turing TM2.Stmt BitMachineEncoding BitMachineComposition

inductive OuterLabel where
  | initScan | initRestore | checkOne | checkTwo | trial | afterDivision
  | restoreDivisor | copyScan | copyRestore
  deriving DecidableEq, Fintype

abbrev Stack := Fin 7
abbrev Label := PrimeSamplerDivision.Label ⊕ OuterLabel
abbrev Control := PrimeSamplerDivision.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control
abbrev Statement := TM2.Stmt (fun _ : Stack => Bool) Label Control

def outer (l : OuterLabel) : Label := .inr l

def unitControl : (Control × Unit) ≃ Control where
  toFun := Prod.fst
  invFun v := (v, ())
  left_inv := by intro v; cases v with | mk v w => cases w; rfl
  right_inv := by intro v; rfl

def setPop (v : Control) (b : Option Bool) : Control := (v.1, b)

def finish (answer : Bool) : Statement := push 3 (fun _ => answer) halt

def outerProgram : OuterLabel → Statement
  | .initScan => BitMachineBroadcast.scanStep 4 5 (outer .initScan) (outer .initRestore)
  | .initRestore => BitMachineBroadcast.restoreStep 5 [4, 0, 6]
      (outer .initRestore) (outer .checkOne)
  | .checkOne => pop 6 setPop
      (branch (fun v => v.2.isSome) (goto (fun _ => outer .checkTwo)) (finish false))
  | .checkTwo => pop 6 setPop
      (branch (fun v => v.2.isSome)
        (push 1 (fun _ => true) (push 1 (fun _ => true) (goto (fun _ => outer .trial))))
        (finish false))
  | .trial => pop 6 setPop
      (branch (fun v => v.2.isSome)
        (load (fun _ => (true, none)) (goto (fun _ => .inl .scan))) (finish true))
  | .afterDivision => pop 3 setPop
      (branch (fun v => v.2.getD false) (finish false) (goto (fun _ => outer .restoreDivisor)))
  | .restoreDivisor => pop 2 setPop
      (branch (fun v => v.2.isSome)
        (push 1 (fun _ => true) (goto (fun _ => outer .restoreDivisor)))
        (push 1 (fun _ => true) (goto (fun _ => outer .copyScan))))
  | .copyScan => BitMachineBroadcast.scanStep 4 5 (outer .copyScan) (outer .copyRestore)
  | .copyRestore => BitMachineBroadcast.restoreStep 5 [4, 0]
      (outer .copyRestore) (outer .trial)

def program : Label → Statement
  | .inl l => renameStmt (finSumFinEquiv : (Fin 4 ⊕ Fin 3) ≃ Fin 7)
      (Equiv.refl _) unitControl
      (liftStmt (some OuterLabel.afterDivision) (PrimeSamplerDivision.program l))
  | .inr l => outerProgram l

noncomputable def machine : BitMachine.Machine :=
  ofFinite (4 : Stack) 3 (outer .initScan) (true, none) program

structure Data where
  dividend : List Bool := []
  left : List Bool := []
  used : List Bool := []
  output : List Bool := []
  candidate : List Bool := []
  work : List Bool := []
  fuel : List Bool := []

def Data.stacks (d : Data) : Stack → List Bool :=
  ![d.dividend, d.left, d.used, d.output, d.candidate, d.work, d.fuel]

def cfg (l : Option Label) (v : Control) (d : Data) : Config := ⟨l, v, d.stacks⟩

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem run_succ {c c' : Config} (h : advance program c = c') (n : Nat) :
    run (n + 1) c = run n c' :=
  (Function.iterate_succ_apply _ _ _).trans (congrArg (run n) h)

theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (m : Nat) :
    run (n + m) c = run m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run m) h

theorem init_copy (bits : List Bool) (v : Control) :
    run (2 * bits.length + 2) (cfg (some (outer .initScan)) v {candidate := bits}) =
      cfg (some (outer .checkOne)) (v.1, none)
        {candidate := bits, dividend := bits, fuel := bits} := by
  let bank := ({candidate := bits} : Data).stacks
  have hs := BitMachineBroadcast.scan_run program (4 : Stack) 5 (by decide)
    (outer .initScan) (outer .initRestore) rfl v.1 v.2 bits [] bank
  have hi : BitMachineBroadcast.contents 4 5 bank bits [] = bank := by
    funext k
    fin_cases k <;> rfl
  rw [hi] at hs
  simp only [List.append_nil] at hs
  have hr := BitMachineBroadcast.restore_run program (5 : Stack) [4, 0, 6]
    (by decide) (by decide) (outer .initRestore) (outer .checkOne) rfl v.1 none
    bits.reverse (Function.update bank 4 [])
  simp only [List.length_reverse, List.reverse_reverse] at hr
  have he := (BitMachineBroadcast.run_add program hs (bits.length + 1)).trans hr
  have hf : Function.update
      (BitMachineBroadcast.prepend [4, 0, 6] bits (Function.update bank 4 [])) 5 [] =
      ({candidate := bits, dividend := bits, fuel := bits} : Data).stacks := by
    funext k
    fin_cases k <;> simp [BitMachineBroadcast.prepend, bank, Data.stacks]
  rw [hf] at he
  simpa only [BitMachineBroadcast.run, run, cfg, Nat.two_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using he

theorem copy_candidate (bits : List Bool) (v : Control) (d : Data) :
    run (2 * bits.length + 2)
      (cfg (some (outer .copyScan)) v {d with dividend := [], candidate := bits, work := []}) =
      cfg (some (outer .trial)) (v.1, none)
        {d with dividend := bits, candidate := bits, work := []} := by
  let bank := ({d with dividend := [], candidate := bits, work := []} : Data).stacks
  have hs := BitMachineBroadcast.scan_run program (4 : Stack) 5 (by decide)
    (outer .copyScan) (outer .copyRestore) rfl v.1 v.2 bits [] bank
  have hi : BitMachineBroadcast.contents 4 5 bank bits [] = bank := by
    funext k
    fin_cases k <;> rfl
  rw [hi] at hs
  simp only [List.append_nil] at hs
  have hr := BitMachineBroadcast.restore_run program (5 : Stack) [4, 0]
    (by decide) (by decide) (outer .copyRestore) (outer .trial) rfl v.1 none
    bits.reverse (Function.update bank 4 [])
  simp only [List.length_reverse, List.reverse_reverse] at hr
  have he := (BitMachineBroadcast.run_add program hs (bits.length + 1)).trans hr
  have hf : Function.update
      (BitMachineBroadcast.prepend [4, 0] bits (Function.update bank 4 [])) 5 [] =
      ({d with dividend := bits, candidate := bits, work := []} : Data).stacks := by
    funext k
    fin_cases k <;> simp [BitMachineBroadcast.prepend, bank, Data.stacks]
  rw [hf] at he
  simpa only [BitMachineBroadcast.run, run, cfg, Nat.two_mul, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using he

def divisionFrame (candidate fuel : List Bool) (c : PrimeSamplerDivision.Config) : Config :=
  renameCfg (finSumFinEquiv : (Fin 4 ⊕ Fin 3) ≃ Fin 7) (Equiv.refl _) unitControl
    (liftCfg (some OuterLabel.afterDivision) () (fun j => ![candidate, [], fuel] j) c)

theorem divide_run (n d : Nat) (hd : 0 < d) (candidate fuel : List Bool) :
    ∃ t ≤ (d + 3) * n + 1,
      run t (cfg (some (.inl .scan)) (true, none)
        {dividend := List.replicate n true, left := List.replicate d true,
          candidate := candidate, fuel := fuel}) =
      cfg (some (outer .afterDivision)) (decide (n % d = 0), none)
        {left := List.replicate (d - n % d) true, used := List.replicate (n % d) true,
          output := [decide (n % d = 0)], candidate := candidate, fuel := fuel} := by
  obtain ⟨t, ht, he⟩ := PrimeSamplerDivision.remainder_run d n 0 hd []
  simp only [Nat.add_zero, Nat.sub_zero, List.replicate_zero, decide_true] at he
  obtain ⟨u, hu, hr⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    (finSumFinEquiv : (Fin 4 ⊕ Fin 3) ≃ Fin 7) (Equiv.refl _) unitControl
    PrimeSamplerDivision.program program (some OuterLabel.afterDivision) (fun _ => rfl)
    () (fun j => ![candidate, [], fuel] j)
    (PrimeSamplerDivision.cfg (some .scan) (true, none) (List.replicate n true)
      (List.replicate d true) [] []) t (by rw [show ((advance PrimeSamplerDivision.program)^[t]) _ = _ from he]; rfl)
  change run u (divisionFrame candidate fuel _) =
    divisionFrame candidate fuel (PrimeSamplerDivision.run t _) at hr
  rw [he] at hr
  have hi : divisionFrame candidate fuel
      (PrimeSamplerDivision.cfg (some .scan) (true, none) (List.replicate n true)
        (List.replicate d true) [] []) =
      cfg (some (.inl .scan)) (true, none)
        {dividend := List.replicate n true, left := List.replicate d true,
          candidate := candidate, fuel := fuel} := by
    unfold divisionFrame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : divisionFrame candidate fuel
      (PrimeSamplerDivision.cfg none (decide (n % d = 0), none) []
        (List.replicate (d - n % d) true) (List.replicate (n % d) true)
        [decide (n % d = 0)]) =
      cfg (some (outer .afterDivision)) (decide (n % d = 0), none)
        {left := List.replicate (d - n % d) true, used := List.replicate (n % d) true,
          output := [decide (n % d = 0)], candidate := candidate, fuel := fuel} := by
    unfold divisionFrame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨u, hu.trans ht, by simpa only [hi, hf] using hr⟩

theorem trial_cons (v : Control) (fuel : List Bool) (d : Data) :
    advance program (cfg (some (outer .trial)) v {d with fuel := true :: fuel}) =
      cfg (some (.inl .scan)) (true, none) {d with fuel := fuel} := by
  simp [advance, TM2.step, program, outer, outerProgram, TM2.stepAux, cfg, Data.stacks, setPop]
  funext k
  fin_cases k <;> rfl

theorem trial_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .trial)) v {d with fuel := []}) =
      cfg none (v.1, none) {d with fuel := [], output := true :: d.output} := by
  simp [advance, TM2.step, program, outer, outerProgram, TM2.stepAux, cfg, Data.stacks, setPop, finish]
  funext k
  fin_cases k <;> rfl

theorem after_composite (v : Control) (d : Data) :
    advance program (cfg (some (outer .afterDivision)) v {d with output := [true]}) =
      cfg none (v.1, some true) {d with output := [false]} := by
  simp [advance, TM2.step, program, outer, outerProgram, TM2.stepAux, cfg, Data.stacks, setPop, finish]
  funext k
  fin_cases k <;> rfl

theorem after_nondivisor (v : Control) (d : Data) :
    advance program (cfg (some (outer .afterDivision)) v {d with output := [false]}) =
      cfg (some (outer .restoreDivisor)) (v.1, some false) {d with output := []} := by
  simp [advance, TM2.step, program, outer, outerProgram, TM2.stepAux, cfg, Data.stacks, setPop]
  funext k
  fin_cases k <;> rfl

theorem divisor_cons (v : Control) (used : List Bool) (d : Data) :
    advance program (cfg (some (outer .restoreDivisor)) v {d with used := true :: used}) =
      cfg (some (outer .restoreDivisor)) (v.1, some true)
        {d with used := used, left := true :: d.left} := by
  simp [advance, TM2.step, program, outer, outerProgram, TM2.stepAux, cfg, Data.stacks, setPop]
  funext k
  fin_cases k <;> rfl

theorem divisor_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .restoreDivisor)) v {d with used := []}) =
      cfg (some (outer .copyScan)) (v.1, none) {d with used := [], left := true :: d.left} := by
  simp [advance, TM2.step, program, outer, outerProgram, TM2.stepAux, cfg, Data.stacks, setPop]
  funext k
  fin_cases k <;> rfl

theorem restore_divisor_run (a b : Nat) (v : Control) (d : Data) :
    run (b + 1) (cfg (some (outer .restoreDivisor)) v
      {d with left := List.replicate a true, used := List.replicate b true}) =
      cfg (some (outer .copyScan)) (v.1, none)
        {d with left := List.replicate (a + b + 1) true, used := []} := by
  induction b generalizing a v with
  | zero =>
      simpa [List.replicate_succ] using
        (run_succ (divisor_nil v {d with left := List.replicate a true}) 0)
  | succ b ih =>
      rw [List.replicate_succ, run_succ
        (divisor_cons v (List.replicate b true) {d with left := List.replicate a true})]
      simpa only [List.replicate_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (a + 1) (v.1, some true)

def trialTail (n d : Nat) : Nat → Bool
  | 0 => true
  | fuel + 1 => decide (n % d ≠ 0) && trialTail n (d + 1) fuel

theorem trialTail_eq_all (n d fuel : Nat) :
    trialTail n d fuel = (List.range fuel).all (fun i => decide (n % (d + i) ≠ 0)) := by
  induction fuel generalizing d with
  | zero => rfl
  | succ fuel ih =>
      rw [trialTail, List.range_succ_eq_map, List.all_cons, List.all_map]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using congrArg
        (fun b => decide (n % d ≠ 0) && b) (ih (d + 1))

theorem trialTail_two (n : Nat) (hn : 2 ≤ n) :
    trialTail n 2 (n - 2) = PrimeSamplerTrial.trialPrime n := by
  simp [PrimeSamplerTrial.trialPrime, hn, trialTail_eq_all, Nat.add_comm]

def loopData (n d fuel : Nat) : Data :=
  {dividend := List.replicate n true, left := List.replicate d true,
    candidate := List.replicate n true, fuel := List.replicate fuel true}

def SafeResult (n : Nat) (answer : Bool) (c : Config) : Prop :=
  c.l = none ∧ c.stk 3 = [answer] ∧ c.stk 4 = List.replicate n true ∧
    ∀ j, (c.stk j).length ≤ n + 2

theorem trial_loop (n d fuel : Nat) (hd : 2 ≤ d) (hfit : d + fuel ≤ n) (v : Control) :
    ∃ t ≤ fuel * (10 * (n + 1)^2) + 1, ∃ c,
      run t (cfg (some (outer .trial)) v (loopData n d fuel)) = c ∧
      SafeResult n (trialTail n d fuel) c := by
  induction fuel generalizing d v with
  | zero =>
      have he := run_succ (trial_nil v (loopData n d 0)) 0
      refine ⟨1, by simp, _, he, ?_⟩
      refine ⟨rfl, rfl, rfl, ?_⟩
      intro j
      fin_cases j <;> simp [run, cfg, Data.stacks, loopData] <;> omega
  | succ fuel ih =>
      have hdpos : 0 < d := by omega
      have hrem : n % d < d := Nat.mod_lt _ hdpos
      have hnrem : n % d ≤ n := Nat.mod_le _ _
      obtain ⟨t, ht, he⟩ := divide_run n d hdpos (List.replicate n true) (List.replicate fuel true)
      have hs := run_succ (trial_cons v (List.replicate fuel true) (loopData n d fuel)) t
      have hpref : run (t + 1) (cfg (some (outer .trial)) v (loopData n d (fuel + 1))) =
          cfg (some (outer .afterDivision)) (decide (n % d = 0), none)
            {left := List.replicate (d - n % d) true, used := List.replicate (n % d) true,
              output := [decide (n % d = 0)], candidate := List.replicate n true,
              fuel := List.replicate fuel true} := by
        simpa only [loopData, List.replicate_succ] using hs.trans he
      by_cases hdiv : n % d = 0
      · simp only [hdiv, decide_true] at hpref
        have hc := run_succ (after_composite (true, none)
          {left := List.replicate (d - 0) true, used := List.replicate 0 true,
            candidate := List.replicate n true, fuel := List.replicate fuel true}) 0
        refine ⟨t + 1 + 1, ?_, _, (run_add hpref 1).trans hc, ?_⟩
        · nlinarith [Nat.zero_le (fuel * (10 * (n + 1)^2))]
        · refine ⟨rfl, ?_, rfl, ?_⟩
          · simp [run, cfg, Data.stacks, trialTail, hdiv]
          · intro j
            fin_cases j <;> simp [run, cfg, Data.stacks] <;> omega
      · have hflag : decide (n % d = 0) = false := by simp [hdiv]
        rw [hflag] at hpref
        let base : Data :=
          {left := List.replicate (d - n % d) true,
           used := List.replicate (n % d) true, candidate := List.replicate n true,
           fuel := List.replicate fuel true}
        have hc := run_succ (after_nondivisor (false, none) base) 0
        have hc' := (run_add hpref 1).trans hc
        have hr := restore_divisor_run (d - n % d) (n % d) (false, some false) base
        have hsum : d - n % d + n % d + 1 = d + 1 := by omega
        rw [hsum] at hr
        have hr' := (run_add hc' (n % d + 1)).trans hr
        have hcopy := copy_candidate (List.replicate n true) (false, none)
          {left := List.replicate (d + 1) true, candidate := List.replicate n true,
            fuel := List.replicate fuel true}
        simp only [List.length_replicate] at hcopy
        have hcopy' := (run_add hr' (2 * n + 2)).trans hcopy
        obtain ⟨u, hu, c, hec, hsafe⟩ := ih (d + 1) (by omega) (by omega) (false, none)
        have he' := (run_add hcopy' u).trans hec
        refine ⟨((t + 1 + 1) + (n % d + 1)) + (2 * n + 2) + u, ?_, c, he', ?_⟩
        · nlinarith
        · simpa [trialTail, hdiv] using hsafe

theorem checkOne_cons (v : Control) (fuel : List Bool) (d : Data) :
    advance program (cfg (some (outer .checkOne)) v {d with fuel := true :: fuel}) =
      cfg (some (outer .checkTwo)) (v.1, some true) {d with fuel := fuel} := by
  simp [advance, TM2.step, program, outer, outerProgram, TM2.stepAux, cfg, Data.stacks, setPop]
  funext k
  fin_cases k <;> rfl

theorem checkOne_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .checkOne)) v {d with fuel := []}) =
      cfg none (v.1, none) {d with fuel := [], output := false :: d.output} := by
  simp [advance, TM2.step, program, outer, outerProgram, TM2.stepAux, cfg, Data.stacks, setPop, finish]
  funext k
  fin_cases k <;> rfl

theorem checkTwo_cons (v : Control) (fuel : List Bool) (d : Data) :
    advance program (cfg (some (outer .checkTwo)) v {d with fuel := true :: fuel}) =
      cfg (some (outer .trial)) (v.1, some true)
        {d with fuel := fuel, left := true :: true :: d.left} := by
  simp [advance, TM2.step, program, outer, outerProgram, TM2.stepAux, cfg, Data.stacks, setPop]
  funext k
  fin_cases k <;> rfl

theorem checkTwo_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .checkTwo)) v {d with fuel := []}) =
      cfg none (v.1, none) {d with fuel := [], output := false :: d.output} := by
  simp [advance, TM2.step, program, outer, outerProgram, TM2.stepAux, cfg, Data.stacks, setPop, finish]
  funext k
  fin_cases k <;> rfl

theorem checked_run (n : Nat) (v : Control) :
    ∃ t ≤ 20 * (n + 1)^3, ∃ c,
      run t (cfg (some (outer .checkOne)) v
        {dividend := List.replicate n true, candidate := List.replicate n true,
          fuel := List.replicate n true}) = c ∧
      SafeResult n (PrimeSamplerTrial.trialPrime n) c := by
  cases n with
  | zero =>
      have he := run_succ (checkOne_nil v {}) 0
      refine ⟨1, by norm_num, _, he, rfl, rfl, rfl, ?_⟩
      intro j
      fin_cases j <;> simp [run, cfg, Data.stacks]
  | succ n =>
      cases n with
      | zero =>
          have hs := run_succ (checkOne_cons v []
            {dividend := [true], candidate := [true]}) 1
          have hf := run_succ (checkTwo_nil (v.1, some true)
            {dividend := [true], candidate := [true]}) 0
          refine ⟨2, by norm_num, _, hs.trans hf, rfl, rfl, rfl, ?_⟩
          intro j
          fin_cases j <;> simp [run, cfg, Data.stacks]
      | succ n =>
          let base : Data :=
            {dividend := List.replicate (n + 2) true, candidate := List.replicate (n + 2) true}
          have hs := run_succ (checkOne_cons v (List.replicate (n + 1) true) base) 1
          have hf := run_succ (checkTwo_cons (v.1, some true) (List.replicate n true) base) 0
          have he : run 2 (cfg (some (outer .checkOne)) v
              {dividend := List.replicate (n + 2) true, candidate := List.replicate (n + 2) true,
                fuel := List.replicate (n + 2) true}) =
              cfg (some (outer .trial)) (v.1, some true) (loopData (n + 2) 2 n) := by
            simpa [base, loopData, List.replicate_succ] using hs.trans hf
          obtain ⟨t, ht, c, hrun, hresult⟩ := trial_loop (n + 2) 2 n (by omega) (by omega) (v.1, some true)
          refine ⟨2 + t, by nlinarith [Nat.zero_le (n^2)], c, (run_add he t).trans hrun, ?_⟩
          have htail := trialTail_two (n + 2) (by omega)
          simp only [Nat.add_sub_cancel] at htail
          rw [htail] at hresult
          exact hresult

/-- The actual unary-input primality routine, preserving the original
candidate and exposing a bound on every bank for physical cleanup by callers. -/
theorem candidate_run (n : Nat) :
    ∃ t ≤ 40 * (n + 1)^3, ∃ c,
      run t (cfg (some (outer .initScan)) (true, none) {candidate := List.replicate n true}) = c ∧
      SafeResult n (PrimeSamplerTrial.trialPrime n) c := by
  have hi := init_copy (List.replicate n true) (true, none)
  simp only [List.length_replicate] at hi
  obtain ⟨t, ht, c, he, hsafe⟩ := checked_run n (true, none)
  refine ⟨(2 * n + 2) + t, ?_, c, (run_add hi t).trans he, hsafe⟩
  nlinarith [Nat.zero_le (n^2), Nat.zero_le (n^3)]

theorem raw_initial (n : Nat) :
    rawInit (4 : Stack) (outer .initScan) (true, none) (List.replicate n true) =
      cfg (some (outer .initScan)) (true, none) {candidate := List.replicate n true} := by
  unfold rawInit cfg
  congr 1
  funext j
  fin_cases j <;> rfl

theorem machine_candidate_run (n : Nat) :
    ∃ t ≤ 40 * (n + 1)^3,
      let c := machine.run t (machine.init (List.replicate n true))
      c.l = none ∧ c.stk machine.output = [PrimeSamplerTrial.trialPrime n] ∧
        c.stk machine.input = List.replicate n true ∧
        ∀ j, (c.stk j).length ≤ n + 2 := by
  obtain ⟨t, ht, c, he, hsafe⟩ := candidate_run n
  have hi := ofFinite_init (4 : Stack) 3 (outer .initScan) (true, none) program (List.replicate n true)
  have hr := ofFinite_run (4 : Stack) 3 (outer .initScan) (true, none) program
    (rawInit 4 (outer .initScan) (true, none) (List.replicate n true)) t
  have hr' := (congrArg (machine.run t) hi).trans hr
  rw [raw_initial] at hr'
  change machine.run t (machine.init (List.replicate n true)) =
    renameCfg (Fintype.equivFin Stack) (Fintype.equivFin Label)
      (Fintype.equivFin Control) (run t _) at hr'
  rw [he] at hr'
  refine ⟨t, ht, ?_⟩
  dsimp only
  rw [hr']
  refine ⟨?_, ?_, ?_, ?_⟩
  · change c.l.map (Fintype.equivFin Label) = none
    rw [hsafe.1]
    rfl
  · simpa only [renameCfg, machine, ofFinite, Equiv.symm_apply_apply] using hsafe.2.1
  · simpa only [renameCfg, machine, ofFinite, Equiv.symm_apply_apply] using hsafe.2.2.1
  · intro j
    exact hsafe.2.2.2 ((Fintype.equivFin Stack).symm j)

theorem machine_outputs (n : Nat) :
    machine.OutputsWithin (List.replicate n true) [PrimeSamplerTrial.trialPrime n]
      (40 * (n + 1)^3) := by
  obtain ⟨t, ht, hh, ho, _⟩ := machine_candidate_run n
  exact ⟨t, ht, hh, ho⟩

end EthInapproximability.CurrentPaper.PrimeSamplerPrimality
