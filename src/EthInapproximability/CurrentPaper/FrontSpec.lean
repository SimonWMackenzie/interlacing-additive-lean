import EthInapproximability.CurrentPaper.FrontScan

/-!
# The all-input front: correctness and clock (unit 4, B4-S7 part F)

`Front.front N Mmain := composition CNFValidator.machine (composition (scanMachine N) Mmain)`.
On EVERY bitstring it outputs the exact encoded SAT answer, provided the main arm `Mmain`
answers correctly on the canonical words of valid formulas with at least `N` variables. That
provision is the single explicit hypothesis `hmain`; it is exactly what the main arm
(source list H-B1, per-branch tables H-B2 with S3-S5, estimator back end) must deliver.
-/

namespace EthInapproximability.CurrentPaper.Front

open Turing BitMachineEncoding EncodedCNF SmallArm

variable {N : ℕ}

theorem capN_val (c : Fin (N + 1)) : capN (N := N) c.val = c := by
  apply Fin.ext; simp only [capN]; omega

theorem fold_fst (l : List Bool) (x : St N) (cnt : Fin (N + 1)) :
    (l.foldl cstep (x, cnt)).1 = l.foldl dstep x := by
  induction l generalizing x cnt with
  | nil => rfl
  | cons b l ih => exact ih _ _

theorem delta_not_unary (x : St N) (hx : x.ph ≠ .unary) (b : Bool) :
    (delta x (some b)).ph ≠ .unary := by
  rcases x with ⟨ph, v, w, s, li, cs, al⟩
  cases ph <;> cases b <;> simp_all [delta, litDone_ph, payStep]

theorem fold_snd_rest (l : List Bool) (x : St N) (cnt : Fin (N + 1)) (hx : x.ph ≠ .unary) :
    (l.foldl cstep (x, cnt)).2 = cnt := by
  induction l generalizing x with
  | nil => rfl
  | cons b l ih =>
      simp only [List.foldl_cons, cstep]
      have hc : cntUpd x cnt (some b) = cnt := by
        cases b <;> simp [cntUpd, hx]
      rw [hc]
      exact ih _ (delta_not_unary x hx b)

theorem fold_unary (n : ℕ) (x : St N) (cnt : Fin (N + 1)) (hx : x.ph = .unary) :
    (EncodedGraph.unary n).foldl cstep (x, cnt) = ({x with ph := .cnt}, capN (cnt.val + n)) := by
  unfold EncodedGraph.unary
  induction n generalizing cnt with
  | zero =>
      simp [cstep, delta, hx, cntUpd, capN_val]
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, List.foldl_cons]
      have h1 : cstep (x, cnt) true = (x, capN (cnt.val + 1)) := by
        simp [cstep, delta, hx, cntUpd]
      rw [h1, ih]
      congr 1
      apply Fin.ext; simp only [capN]; omega

theorem fold_count (f : Formula) :
    ((encode f).foldl cstep (init (N := N), capN 0)).2 = capN f.variables := by
  rw [show encode f = EncodedGraph.unary f.variables ++
      (EncodedCommunication.natField f.clauses.length ++ clauseFields f.clauses) by
    simp [encode, List.append_assoc]]
  rw [List.foldl_append, fold_unary f.variables init (capN 0) rfl,
    fold_snd_rest _ _ _ (by simp)]
  apply Fin.ext; simp only [capN]; omega

/-- The routing target of the scanner, as a function of the ORIGINAL raw word. -/
noncomputable def scanTarget (N : ℕ) (input : List Bool) : List Bool :=
  match EncodedCNF.decode input with
  | none => phi N false
  | some f => if f.variables < N then phi N (EncodedETHTail.satAnswer input) else input

theorem emit_step (b : Bool) (v : Ctl N) (S : Stack → List Bool) :
    TM2.stepAux (emit N b) v S = ⟨none, v, Function.update S 1 (phi N b ++ S 1)⟩ := by
  rw [emit, stepAux_pushAll]
  rfl

theorem final_small (x : St N) (cnt : Fin (N + 1)) (o : Option Bool) (S : Stack → List Bool)
    (hS0 : S 0 = []) (hc : cnt.val < N) :
    advance (program N) (⟨some .scan, (x, cnt, o), S⟩ : Config N) =
      ⟨none, (delta x none, cnt, none),
        Function.update (Function.update S 0 []) 1 (phi N (answer (delta x none)) ++ S 1)⟩ := by
  have hdone : isDone (delta x none) = true := by simp [delta, isDone]
  cases hb : answer (delta x none) <;>
    simp [advance, TM2.step, TM2.stepAux, program, hS0, hdone, hc, hb, emit_step, cntUpd,
      Function.update_apply]

theorem final_large (x : St N) (cnt : Fin (N + 1)) (o : Option Bool) (S : Stack → List Bool)
    (hS0 : S 0 = []) (hc : ¬ cnt.val < N) :
    advance (program N) (⟨some .scan, (x, cnt, o), S⟩ : Config N) =
      ⟨some .move, (delta x none, cnt, none), Function.update S 0 []⟩ := by
  have hdone : isDone (delta x none) = true := by simp [delta, isDone]
  simp [advance, TM2.step, TM2.stepAux, program, hS0, hdone, hc, cntUpd]

theorem scan_outputs (hN : 1 ≤ N) (input : List Bool) :
    (scanMachine N).OutputsWithin (CNFValidator.result input) (scanTarget N input)
      (2 * input.length + 3) := by
  unfold scanMachine
  cases hd : EncodedCNF.decode input with
  | none =>
      have hr : CNFValidator.result input = [false] := CNFValidator.result_of_malformed hd
      rw [hr]
      apply outputsWithin_of_raw_run (0 : Stack) 1 Label.flag (initCtl N) (program N)
        [false] (scanTarget N input) 1 (2 * input.length + 3) (by omega)
      · simp [advance, TM2.step, TM2.stepAux, program, rawInit, emit_step]
      · simp [advance, TM2.step, TM2.stepAux, program, rawInit, emit_step, scanTarget, hd]
  | some f =>
      have hr : CNFValidator.result input = true :: input := CNFValidator.result_of_decoded hd
      obtain ⟨hvalid, henc⟩ := EncodedCNF.decode_spec hd
      rw [hr]
      -- one transition: pop the validity flag
      have h0 : advance (program N)
          (rawInit (0 : Stack) Label.flag (initCtl N) (true :: input)) =
          ⟨some .scan, (init, capN 0, some true),
            Function.update (fun k => if k = (0 : Stack) then true :: input else []) 0 input⟩ := by
        simp [advance, TM2.step, TM2.stepAux, program, rawInit, initCtl]
      obtain ⟨o', hscan, hnd⟩ := scan_run input (init (N := N)) (capN 0) (some true) rfl
        (Function.update (fun k => if k = (0 : Stack) then true :: input else []) 0 input)
        (by simp)
      set x := (input.foldl cstep (init (N := N), capN 0)).1 with hxdef
      set cnt := (input.foldl cstep (init (N := N), capN 0)).2 with hcdef
      have hx : x = input.foldl dstep init := fold_fst _ _ _
      have hcnt : cnt = capN f.variables := by rw [hcdef, ← henc]; exact fold_count f
      let B : Stack → List Bool := fun k => if k = 0 then [] else if k = 2 then
        input.reverse ++
          (Function.update (fun k => if k = (0 : Stack) then true :: input else []) 0 input) 2
        else (Function.update (fun k => if k = (0 : Stack) then true :: input else []) 0 input) k
      have hB0 : B 0 = [] := rfl
      have hB1 : B 1 = [] := by simp [B]
      have hB2 : B 2 = input.reverse := by simp [B]
      have hdone : isDone (delta x none) = true := by simp [delta, isDone]
      by_cases hsmall : f.variables < N
      · have hc : cnt.val < N := by rw [hcnt]; simp only [capN]; omega
        have hans : answer (delta x none) = EncodedETHTail.satAnswer input := by
          rw [hx, ← henc]; exact answer_eq f hvalid (by omega)
        have hl := final_small x cnt o' B hB0 hc
        have hrun : (advance (program N))^[1 + input.length + 1]
            (rawInit (0 : Stack) Label.flag (initCtl N) (true :: input)) =
            ⟨none, (delta x none, cnt, none),
              Function.update (Function.update B 0 []) 1
                (phi N (answer (delta x none)) ++ B 1)⟩ := by
          rw [Function.iterate_add_apply _ (1 + input.length) 1,
            Function.iterate_add_apply _ 1 input.length]
          simp only [Function.iterate_one]
          rw [h0, hscan]
          exact hl
        apply outputsWithin_of_raw_run (0 : Stack) 1 Label.flag (initCtl N) (program N)
          (true :: input) (scanTarget N input) (1 + input.length + 1) (2 * input.length + 3)
          (by omega)
        · rw [hrun]
        · rw [hrun]
          simp [scanTarget, hd, hsmall, hans, hB1]
      · have hc : ¬ cnt.val < N := by rw [hcnt]; simp only [capN]; omega
        have hlast := final_large x cnt o' B hB0 hc
        obtain ⟨v', hmove⟩ := move_run input.reverse [] (delta x none, cnt, none)
          (Function.update B 0 []) (by simp [Function.update_apply, hB2])
          (by simp [Function.update_apply, hB1])
        have hrun : (advance (program N))^[(input.reverse.length + 1) + (1 + input.length + 1)]
            (rawInit (0 : Stack) Label.flag (initCtl N) (true :: input)) =
            ⟨none, v', fun k => if k = 2 then [] else if k = 1 then input.reverse.reverse ++ []
              else (Function.update B 0 []) k⟩ := by
          rw [Function.iterate_add_apply _ (input.reverse.length + 1) (1 + input.length + 1),
            Function.iterate_add_apply _ (1 + input.length) 1,
            Function.iterate_add_apply _ 1 input.length]
          simp only [Function.iterate_one]
          rw [h0, hscan, hlast, hmove]
        apply outputsWithin_of_raw_run (0 : Stack) 1 Label.flag (initCtl N) (program N)
          (true :: input) (scanTarget N input) ((input.reverse.length + 1) + (1 + input.length + 1))
          (2 * input.length + 3) (by simp; omega)
        · rw [hrun]
        · rw [hrun]
          simp [scanTarget, hd, hsmall]

/-- The front machine: validator, router, main arm; two charged handoffs. -/
noncomputable def front (N : ℕ) (Mmain : BitMachine.Machine) : BitMachine.Machine :=
  BitMachineComposition.composition CNFValidator.machine
    (BitMachineComposition.composition (scanMachine N) Mmain)

theorem scanTarget_length (hN : 1 ≤ N) (input : List Bool) :
    (scanTarget N input).length ≤ input.length + (phi N true).length + (phi N false).length := by
  unfold scanTarget
  split
  · omega
  · split
    · cases EncodedETHTail.satAnswer input <;> omega
    · omega

/-- **B4-S7 part F.** For every threshold `N ≥ 1` and every main arm `Mmain` that answers
exactly on canonical words of valid formulas with at least `N` variables, the fixed machine
`front N Mmain` outputs `[satAnswer w]` on EVERY bitstring `w`. -/
theorem front_outputs (hN : 1 ≤ N) (Mmain : BitMachine.Machine) (Tmain : List Bool → ℕ)
    (hmain : ∀ f : Formula, f.Valid → N ≤ f.variables →
      Mmain.OutputsWithin (encode f) [EncodedETHTail.satAnswer (encode f)] (Tmain (encode f)))
    (w : List Bool) :
    (front N Mmain).OutputsWithin w [EncodedETHTail.satAnswer w]
      (250 * (w.length + 1) ^ 3 + 2 * (w.length + 1) + 2 + (2 * w.length + 3) +
        2 * (w.length + (phi N true).length + (phi N false).length) + 2 +
        (Tmain w + Tmain (phi N true) + Tmain (phi N false))) := by
  have hV := CNFValidator.Runtime.outputs w
  have hS := scan_outputs hN w
  have hres : (CNFValidator.result w).length ≤ w.length + 1 := by
    unfold CNFValidator.result; split <;> simp
  have hM : Mmain.OutputsWithin (scanTarget N w) [EncodedETHTail.satAnswer w]
      (Tmain w + Tmain (phi N true) + Tmain (phi N false)) := by
    unfold scanTarget
    cases hd : EncodedCNF.decode w with
    | none =>
        simp only
        have h := hmain (phiFormula N false) (phiFormula_valid hN false) le_rfl
        rw [show encode (phiFormula N false) = phi N false from rfl, satAnswer_phi hN,
          EncodedETHTail.satAnswer_malformed hd] at *
        exact BitMachine.outputsWithin_mono _ h (by omega)
    | some f =>
        obtain ⟨hvalid, henc⟩ := EncodedCNF.decode_spec hd
        simp only
        split
        · rename_i hsmall
          cases hb : EncodedETHTail.satAnswer w
          · have h := hmain (phiFormula N false) (phiFormula_valid hN false) le_rfl
            rw [show encode (phiFormula N false) = phi N false from rfl, satAnswer_phi hN] at h
            exact BitMachine.outputsWithin_mono _ h (by omega)
          · have h := hmain (phiFormula N true) (phiFormula_valid hN true) le_rfl
            rw [show encode (phiFormula N true) = phi N true from rfl, satAnswer_phi hN] at h
            exact BitMachine.outputsWithin_mono _ h (by omega)
        · rename_i hlarge
          have h := hmain f hvalid (by omega)
          rw [henc] at h
          exact BitMachine.outputsWithin_mono _ h (by omega)
  have h2 := BitMachineComposition.composition_outputsWithin (scanMachine N) Mmain hS hM
  have h1 := BitMachineComposition.composition_outputsWithin CNFValidator.machine
    (BitMachineComposition.composition (scanMachine N) Mmain) hV h2
  apply BitMachine.outputsWithin_mono _ h1
  have ht := scanTarget_length hN w
  omega

end EthInapproximability.CurrentPaper.Front
