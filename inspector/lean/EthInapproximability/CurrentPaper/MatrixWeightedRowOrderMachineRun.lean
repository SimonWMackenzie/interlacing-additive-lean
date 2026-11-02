import EthInapproximability.CurrentPaper.MatrixWeightedRowOrderMachine

/-! # Charged full-bank execution of the physical item-order controller -/

namespace EthInapproximability.CurrentPaper.MatrixWeightedRowOrderMachineRun

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixWeightedRowOrderMachine

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem run_succ {c d : Config} (h : advance program c = d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, h]

/-- Lift a genuinely executed local subroutine into the fixed 23-stack
controller, retaining every unselected stack. The premise is the local
machine's full-bank run, not a desired output word. -/
theorem framed_run {K L V : Type*} [DecidableEq K]
    (ι : K ↪ Stack) (labels : L → Label) (embed : V → State)
    (read : State → V) (hread : Function.LeftInverse read embed)
    (next : Option Label)
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (hP : ∀ l, program (labels l) =
      stmt ι labels embed read next (P l))
    (S : Stack → List Bool)
    (c d : TM2.Cfg (fun _ : K => Bool) L V) (first : L) (bound : ℕ)
    (hstart : c.l = some first)
    (hbank : ∀ k, c.stk k = S (ι k))
    (hrun : ((advance P)^[bound]) c = d) (hhalt : d.l = none) :
    ∃ t ≤ bound,
      run t ⟨some (labels first), embed c.var, S⟩ =
        ⟨next, embed d.var, bank ι S d.stk⟩ := by
  have hloc : (((advance P)^[bound]) c).l = none := by rw [hrun]; exact hhalt
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs
    ι S labels embed read hread next P program hP c bound hloc
  refine ⟨t, ht, ?_⟩
  have hi : BitMachineStackEmbedding.cfg ι S labels embed next c =
      ⟨some (labels first), embed c.var, S⟩ := by
    unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
      BitMachineInline.cfg
    simp only [hstart]
    congr 1
    exact bank_eq_self ι S c.stk hbank
  rw [hi, hrun] at he
  simpa [run, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hhalt] using he

theorem split_stage (aux : Bool) (S : Stack → List Bool)
    (label width : ℕ) (hw : 0 < width)
    (h0 : S 0 = List.replicate label true)
    (h1 : S 1 = List.replicate width true)
    (hrest : ∀ k : MatrixWeightedRowOrderSplit.Stack,
      k ≠ 0 → k ≠ 1 → S (splitSlots k) = []) :
    ∃ t ≤ 10 * label + 3 * width + 7,
      run t ⟨some (start aux), initial, S⟩ =
        ⟨some (.afterSplit aux), .split (none,false),
          Function.update
            (Function.update S 9 (List.replicate (label % width) true))
            10 (List.replicate (label / width) true)⟩ := by
  let c : TM2.Cfg (fun _ : MatrixWeightedRowOrderSplit.Stack => Bool)
      MatrixWeightedRowOrderSplit.Label MatrixWeightedRowOrderSplit.Control :=
    ⟨some (.inl .scan), (none,false),
      MatrixWeightedRowOrderSplit.initialBank label width⟩
  let d : TM2.Cfg (fun _ : MatrixWeightedRowOrderSplit.Stack => Bool)
      MatrixWeightedRowOrderSplit.Label MatrixWeightedRowOrderSplit.Control :=
    ⟨none, (none,false), MatrixWeightedRowOrderSplit.finalBank label width⟩
  have hb (k : MatrixWeightedRowOrderSplit.Stack) : c.stk k = S (splitSlots k) := by
    have h2 := hrest (2 : Fin 8) (by decide) (by decide)
    have h3 := hrest (3 : Fin 8) (by decide) (by decide)
    have h4 := hrest (4 : Fin 8) (by decide) (by decide)
    have h5 := hrest (5 : Fin 8) (by decide) (by decide)
    have h6 := hrest (6 : Fin 8) (by decide) (by decide)
    have h7 := hrest (7 : Fin 8) (by decide) (by decide)
    fin_cases k <;> simp [c, MatrixWeightedRowOrderSplit.initialBank,
      splitSlots, h0, h1] at *
    all_goals simp_all
  obtain ⟨u, hu, hr⟩ := MatrixWeightedRowOrderSplit.split_run label width hw
  have hrun : ((advance MatrixWeightedRowOrderSplit.program)^[u]) c = d := hr
  obtain ⟨t, ht, he⟩ := framed_run splitSlots (Label.split aux)
    State.split splitState (by intro v; rfl) (some (.afterSplit aux))
    MatrixWeightedRowOrderSplit.program (by intro l; rfl) S c d
    (.inl .scan) u rfl hb hrun rfl
  refine ⟨t, ht.trans hu, ?_⟩
  have hfinal : MatrixWeightedRowOrderSplit.finalBank label width =
      Function.update
        (Function.update (MatrixWeightedRowOrderSplit.initialBank label width)
          5 (List.replicate (label % width) true))
        6 (List.replicate (label / width) true) := by
    funext k
    fin_cases k <;> rfl
  dsimp only [d] at he
  rw [hfinal, bank_update, bank_update] at he
  have hinit : bank splitSlots S
      (MatrixWeightedRowOrderSplit.initialBank label width) = S := by
    exact bank_eq_self splitSlots S _ hb
  rw [hinit] at he
  simpa only [start, initial, c, d, splitSlots] using he

theorem copy_stage (ι : Fin 3 ↪ Stack)
    (labels : BitMachineCopy.Label → Label) (next : Label)
    (hP : ∀ l, program (labels l) = stmt ι labels
      State.copy copyState (some next) (BitMachineCopy.program l))
    (S : Stack → List Bool) (source target : List Bool)
    (hs : S (ι 0) = source) (ht : S (ι 1) = target)
    (hw : S (ι 2) = []) :
    ∃ t ≤ 2 * source.length + 2,
      run t ⟨some (labels .scan), .copy none, S⟩ =
        ⟨some next, .copy none,
          Function.update S (ι 1) (source ++ target)⟩ := by
  let c := BitMachineCopy.cfg (some .scan) none source target []
  let d := BitMachineCopy.cfg none none source (source ++ target) []
  have hb (k : Fin 3) : c.stk k = S (ι k) := by
    fin_cases k <;> simp [c, BitMachineCopy.cfg,
      BitMachineCopy.stackContents, hs, ht, hw]
  have hr : ((advance BitMachineCopy.program)^[2 * source.length + 2]) c = d := by
    exact BitMachineCopy.run_correct none source target
  obtain ⟨t, ht', he⟩ := framed_run ι labels State.copy copyState
    (by intro v; rfl) (some next) BitMachineCopy.program hP S c d
    .scan (2 * source.length + 2) rfl hb hr rfl
  refine ⟨t, ht', ?_⟩
  dsimp only [d] at he
  have hu : d.stk = Function.update c.stk (1 : Fin 3)
      (source ++ target) := by
    funext k
    fin_cases k <;> rfl
  rw [hu, bank_update, bank_eq_self ι S c.stk hb] at he
  exact he

theorem address_stage (ι : Fin 6 ↪ Stack)
    (labels : MatrixAddressMachine.Label → Label) (next : Option Label)
    (hP : ∀ l, program (labels l) = stmt ι labels
      State.address addressState next (MatrixAddressMachine.program l))
    (S : Stack → List Bool) (row width column : ℕ) (out : List Bool)
    (h0 : S (ι 0) = List.replicate row true)
    (h1 : S (ι 1) = List.replicate width true)
    (h2 : S (ι 2) = List.replicate column true)
    (h3 : S (ι 3) = []) (h4 : S (ι 4) = [])
    (h5 : S (ι 5) = out) :
    ∃ t ≤ MatrixAddressMachine.exactTime row width column,
      run t ⟨some (labels .outer), .address false, S⟩ =
        ⟨next, .address false,
          Function.update S (ι 5)
            (List.replicate (row * width + column) true ++ out)⟩ := by
  let c := MatrixAddressMachine.cfg (some .outer) false
    (List.replicate row true) (List.replicate width true)
    (List.replicate column true) [] [] out
  let d := MatrixAddressMachine.cfg none false
    (List.replicate row true) (List.replicate width true)
    (List.replicate column true) [] []
    (List.replicate (row * width + column) true ++ out)
  have hb (k : Fin 6) : c.stk k = S (ι k) := by
    fin_cases k <;> simp [c, MatrixAddressMachine.cfg,
      h0, h1, h2, h3, h4, h5]
  have hr : ((advance MatrixAddressMachine.program)^[MatrixAddressMachine.exactTime
      row width column]) c = d := by
    exact MatrixAddressMachine.address_run row width column false out
  obtain ⟨t, ht, he⟩ := framed_run ι labels State.address addressState
    (by intro v; rfl) next MatrixAddressMachine.program hP S c d
    .outer (MatrixAddressMachine.exactTime row width column) rfl hb hr rfl
  refine ⟨t, ht, ?_⟩
  dsimp only [d] at he
  have hu : d.stk = Function.update c.stk (5 : Fin 6)
      (List.replicate (row * width + column) true ++ out) := by
    funext k
    fin_cases k <;> rfl
  rw [hu, bank_update, bank_eq_self ι S c.stk hb] at he
  exact he

theorem lookup_stage {nv nb : ℕ}
    (order : Construction.ItemOrder nv nb) (j : Fin (nv + nb))
    (S : Stack → List Bool) (out : List Bool)
    (h0 : S 13 = List.replicate j.val true)
    (h1 : S 4 = MatrixWeightedRowOrderLookup.orderWord order)
    (h2 : S 17 = []) (h3 : S 18 = []) (h4 : S 19 = out) :
    ∃ t ≤ 2 * (MatrixWeightedRowOrderLookup.orderWord order).length +
          2 * j.val + 3,
      run t ⟨some (.lookup .select), .lookup none, S⟩ =
        ⟨some .afterLookup, .lookup none,
          Function.update S 19 (List.replicate (order j).val true ++ out)⟩ := by
  let c := MatrixWeightedRowOrderLookup.cfg (some .select) none
    (List.replicate j.val true) (MatrixWeightedRowOrderLookup.orderWord order)
    [] [] out
  let d := MatrixWeightedRowOrderLookup.cfg none none
    (List.replicate j.val true) (MatrixWeightedRowOrderLookup.orderWord order)
    [] [] (List.replicate (order j).val true ++ out)
  have hb (k : MatrixWeightedRowOrderLookup.Stack) :
      c.stk k = S (lookupSlots k) := by
    fin_cases k <;> simp [c, MatrixWeightedRowOrderLookup.cfg,
      lookupSlots, h0, h1, h2, h3, h4]
  obtain ⟨u, hu, hr⟩ := MatrixWeightedRowOrderLookup.orderWord_run order j out
  have hrun : ((advance MatrixWeightedRowOrderLookup.program)^[u]) c = d := hr
  obtain ⟨t, ht, he⟩ := framed_run lookupSlots Label.lookup
    State.lookup lookupState (by intro v; rfl) (some .afterLookup)
    MatrixWeightedRowOrderLookup.program (by intro l; rfl) S c d
    .select u rfl hb hrun rfl
  refine ⟨t, ht.trans hu, ?_⟩
  dsimp only [d] at he
  have hup : d.stk = Function.update c.stk (4 : Fin 5)
      (List.replicate (order j).val true ++ out) := by
    funext k
    fin_cases k <;> rfl
  rw [hup, bank_update, bank_eq_self lookupSlots S c.stk hb] at he
  exact he

theorem after_split_step (aux : Bool) (S : Stack → List Bool)
    (h : S 12 = []) :
    run 1 ⟨some (.afterSplit aux), .split (none,false), S⟩ =
      ⟨some (if aux then .offsetCopy .scan else .offsetAddress .outer),
        if aux then .copy none else .address false,
        Function.update S 12 [true]⟩ := by
  simp [run, advance, program, h, TM2.step]

theorem after_offset_step (S : Stack → List Bool) :
    run 1 ⟨some .afterOffset, .copy none, S⟩ =
      ⟨some (.offsetAddress .outer), .address false, S⟩ := by
  simp [run, advance, program, TM2.step]

theorem after_address_step (S : Stack → List Bool) :
    run 1 ⟨some .afterAddress, .address false, S⟩ =
      ⟨some (.lookup .select), .lookup none, S⟩ := by
  simp [run, advance, program, TM2.step]

theorem after_lookup_step (S : Stack → List Bool) :
    run 1 ⟨some .afterLookup, .lookup none, S⟩ =
      ⟨some (.sourceCopy .scan), .copy none, S⟩ := by
  simp [run, advance, program, TM2.step]

theorem after_source_step (S : Stack → List Bool) :
    run 1 ⟨some .afterSource, .copy none, S⟩ =
      ⟨some (.rowAddress .outer), .address false, S⟩ := by
  simp [run, advance, program, TM2.step]

def inputBank (label width nv sL : ℕ) (table out : List Bool) :
    Stack → List Bool :=
  ![List.replicate label true, List.replicate width true,
    List.replicate nv true, List.replicate sL true, table, out,
    [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []]

def terminalBank (label width nv sL : ℕ) (table out : List Bool)
    (aux : Bool) (j rank : ℕ) : Stack → List Bool :=
  ![List.replicate label true, List.replicate width true,
    List.replicate nv true, List.replicate sL true, table,
    List.replicate (sL + rank * width + label % width) true ++ out,
    [], [], [], List.replicate (label % width) true,
    List.replicate (label / width) true, [], [true],
    List.replicate j true,
    (if aux then List.replicate nv true else []),
    [], [], [], [], List.replicate rank true, [], [], []]

theorem offset_stage (aux : Bool) (S : Stack → List Bool) (nv : ℕ)
    (h2 : S 2 = List.replicate nv true)
    (h6 : S 6 = []) (h12 : S 12 = []) (h14 : S 14 = []) :
    ∃ t ≤ if aux then 2 * nv + 4 else 1,
      run t ⟨some (.afterSplit aux), .split (none,false), S⟩ =
        ⟨some (.offsetAddress .outer), .address false,
          Function.update (Function.update S 12 [true]) 14
            (if aux then List.replicate nv true else [])⟩ := by
  cases aux
  · refine ⟨1, le_refl _, ?_⟩
    rw [after_split_step false S h12]
    have he : Function.update (Function.update S 12 [true]) 14 [] =
        Function.update S 12 [true] := by
      funext k
      fin_cases k <;> simp [h14]
    simpa [he]
  · let S1 := Function.update S 12 [true]
    have hstep := after_split_step true S h12
    have hs : S1 (offsetCopySlots 0) = List.replicate nv true := by
      simp [S1, offsetCopySlots, h2]
    have ht : S1 (offsetCopySlots 1) = [] := by
      simp [S1, offsetCopySlots, h14]
    have hw : S1 (offsetCopySlots 2) = [] := by
      simp [S1, offsetCopySlots, h6]
    obtain ⟨tc, htc, hc⟩ := copy_stage offsetCopySlots Label.offsetCopy
      .afterOffset (by intro l; rfl) S1 (List.replicate nv true) [] hs ht hw
    simp only [List.length_replicate] at htc
    refine ⟨1 + tc + 1, ?_, ?_⟩
    · simp only [ite_true]
      omega
    have hfirst : run (1 + tc) ⟨some (.afterSplit true), .split (none,false), S⟩ =
        ⟨some .afterOffset, .copy none,
          Function.update S1 14 (List.replicate nv true)⟩ := by
      rw [run_add hstep tc]
      simpa only [S1, List.append_nil] using hc
    rw [run_add hfirst 1, after_offset_step]
    simp [S1]

theorem run_to_lookup {nv nb : ℕ}
    (order : Construction.ItemOrder nv nb) (j : Fin (nv + nb))
    (label width sL : ℕ) (aux : Bool) (hw : 0 < width)
    (hj : j.val = label / width + (if aux then nv else 0))
    (oldOut : List Bool) :
    ∃ t ≤ 10 * label + 3 * width + 7 +
      (if aux then 2 * nv + 4 else 1) +
      MatrixAddressMachine.exactTime (label / width) 1
        (if aux then nv else 0) + 1,
      run t ⟨some (start aux), initial,
        inputBank label width nv sL
          (MatrixWeightedRowOrderLookup.orderWord order) oldOut⟩ =
      ⟨some (.lookup .select), .lookup none,
        Function.update (Function.update
          (Function.update
            (Function.update
              (Function.update (inputBank label width nv sL
                (MatrixWeightedRowOrderLookup.orderWord order) oldOut)
                9 (List.replicate (label % width) true))
              10 (List.replicate (label / width) true))
            12 [true])
          14 (if aux then List.replicate nv true else []))
          13 (List.replicate j.val true)⟩ := by
  let S0 := inputBank label width nv sL
    (MatrixWeightedRowOrderLookup.orderWord order) oldOut
  let S1 := Function.update (Function.update S0 9
    (List.replicate (label % width) true)) 10
    (List.replicate (label / width) true)
  let S2 := Function.update (Function.update S1 12 [true]) 14
    (if aux then List.replicate nv true else [])
  let S3 := Function.update S2 13 (List.replicate j.val true)
  have hrest : ∀ k : MatrixWeightedRowOrderSplit.Stack,
      k ≠ 0 → k ≠ 1 → S0 (splitSlots k) = [] := by
    intro k hk0 hk1
    fin_cases k <;> simp_all [S0, inputBank, splitSlots]
  obtain ⟨ts, hts, hs⟩ := split_stage aux S0 label width hw
    (by rfl) (by rfl) hrest
  have h2 : S1 2 = List.replicate nv true := by
    simp [S1, S0, inputBank]
  have h6 : S1 6 = [] := by simp [S1, S0, inputBank]
  have h12 : S1 12 = [] := by simp [S1, S0, inputBank]
  have h14 : S1 14 = [] := by simp [S1, S0, inputBank]
  obtain ⟨toff, htoff, ho⟩ := offset_stage aux S1 nv h2 h6 h12 h14
  have hrow : S2 (offsetAddressSlots 0) =
      List.replicate (label / width) true := by
    simp [S2, S1, S0, inputBank, offsetAddressSlots]
  have hwidth : S2 (offsetAddressSlots 1) = List.replicate 1 true := by
    simp [S2, S1, S0, inputBank, offsetAddressSlots]
  have hcol : S2 (offsetAddressSlots 2) =
      List.replicate (if aux then nv else 0) true := by
    cases aux <;> simp [S2, S1, S0, inputBank, offsetAddressSlots]
  have hwork1 : S2 (offsetAddressSlots 3) = [] := by
    simp [S2, S1, S0, inputBank, offsetAddressSlots]
  have hwork2 : S2 (offsetAddressSlots 4) = [] := by
    simp [S2, S1, S0, inputBank, offsetAddressSlots]
  have hout : S2 (offsetAddressSlots 5) = [] := by
    simp [S2, S1, S0, inputBank, offsetAddressSlots]
  obtain ⟨ta, hta, ha⟩ := address_stage offsetAddressSlots
    Label.offsetAddress (some .afterAddress) (by intro l; rfl)
    S2 (label / width) 1 (if aux then nv else 0) []
    hrow hwidth hcol hwork1 hwork2 hout
  have hindex : (label / width) * 1 + (if aux then nv else 0) = j.val := by
    simpa using hj.symm
  have ha' : run ta ⟨some (.offsetAddress .outer), .address false, S2⟩ =
      ⟨some .afterAddress, .address false, S3⟩ := by
    simpa only [S3, offsetAddressSlots, hindex, List.append_nil] using ha
  refine ⟨ts + toff + ta + 1, ?_, ?_⟩
  · omega
  · have hso : run (ts + toff) ⟨some (start aux), initial, S0⟩ =
        ⟨some (.offsetAddress .outer), .address false, S2⟩ := by
      rw [run_add hs toff]
      simpa only [S1, S2] using ho
    have hsoa : run (ts + toff + ta) ⟨some (start aux), initial, S0⟩ =
        ⟨some .afterAddress, .address false, S3⟩ := by
      rw [run_add hso ta]
      exact ha'
    rw [run_add hsoa 1, after_address_step]

/-- General physical row ordinal computation from an explicit serialized
item-order table. `j` is justified by the unary quotient and group offset;
no order entry is preloaded in any register. -/
theorem run {nv nb : ℕ}
    (order : Construction.ItemOrder nv nb) (j : Fin (nv + nb))
    (label width sL : ℕ) (aux : Bool) (hw : 0 < width)
    (hj : j.val = label / width + (if aux then nv else 0))
    (oldOut : List Bool) :
    ∃ t ≤ 10 * label + 3 * width + 7 +
      (if aux then 2 * nv + 4 else 1) +
      MatrixAddressMachine.exactTime (label / width) 1
        (if aux then nv else 0) + 1 +
      (2 * (MatrixWeightedRowOrderLookup.orderWord order).length +
        2 * j.val + 3) + 1 +
      (2 * sL + 2) + 1 +
      MatrixAddressMachine.exactTime (order j).val width (label % width),
      MatrixWeightedRowOrderMachine.run t
        ⟨some (start aux), initial,
          inputBank label width nv sL
            (MatrixWeightedRowOrderLookup.orderWord order) oldOut⟩ =
      ⟨none, .address false,
        terminalBank label width nv sL
          (MatrixWeightedRowOrderLookup.orderWord order) oldOut
          aux j.val (order j).val⟩ := by
  let table := MatrixWeightedRowOrderLookup.orderWord order
  let S0 := inputBank label width nv sL table oldOut
  let S1 := Function.update (Function.update S0 9
    (List.replicate (label % width) true)) 10
    (List.replicate (label / width) true)
  let S2 := Function.update (Function.update S1 12 [true]) 14
    (if aux then List.replicate nv true else [])
  let S3 := Function.update S2 13 (List.replicate j.val true)
  let S4 := Function.update S3 19 (List.replicate (order j).val true)
  let S5 := Function.update S4 5 (List.replicate sL true ++ oldOut)
  let S6 := Function.update S5 5
    (List.replicate ((order j).val * width + label % width) true ++
      (List.replicate sL true ++ oldOut))
  obtain ⟨tp, htp, hp⟩ := run_to_lookup order j label width sL aux hw hj oldOut
  have hp' : MatrixWeightedRowOrderMachine.run tp
      ⟨some (start aux), initial, S0⟩ =
      ⟨some (.lookup .select), .lookup none, S3⟩ := by
    simpa only [S3, S2, S1, S0, table] using hp
  have hindex : S3 13 = List.replicate j.val true := by
    simp [S3]
  have htable : S3 4 = table := by
    simp [S3, S2, S1, S0, inputBank]
  have hs17 : S3 17 = [] := by simp [S3, S2, S1, S0, inputBank]
  have hs18 : S3 18 = [] := by simp [S3, S2, S1, S0, inputBank]
  have hs19 : S3 19 = [] := by simp [S3, S2, S1, S0, inputBank]
  obtain ⟨tl, htl, hl⟩ := lookup_stage order j S3 []
    hindex htable hs17 hs18 hs19
  have hl' : MatrixWeightedRowOrderMachine.run tl
      ⟨some (.lookup .select), .lookup none, S3⟩ =
      ⟨some .afterLookup, .lookup none, S4⟩ := by
    simpa only [S4, List.append_nil] using hl
  have hsource : S4 (sourceCopySlots 0) = List.replicate sL true := by
    simp [S4, S3, S2, S1, S0, inputBank, sourceCopySlots]
  have htarget : S4 (sourceCopySlots 1) = oldOut := by
    simp [S4, S3, S2, S1, S0, inputBank, sourceCopySlots]
  have hscratch : S4 (sourceCopySlots 2) = [] := by
    simp [S4, S3, S2, S1, S0, inputBank, sourceCopySlots]
  obtain ⟨tc, htc, hc⟩ := copy_stage sourceCopySlots
    Label.sourceCopy .afterSource (by intro l; rfl)
    S4 (List.replicate sL true) oldOut hsource htarget hscratch
  have hc' : MatrixWeightedRowOrderMachine.run tc
      ⟨some (.sourceCopy .scan), .copy none, S4⟩ =
      ⟨some .afterSource, .copy none, S5⟩ := by
    simpa only [S5, sourceCopySlots] using hc
  have hrow : S5 (rowAddressSlots 0) =
      List.replicate (order j).val true := by
    simp [S5, S4, rowAddressSlots]
  have hwidth : S5 (rowAddressSlots 1) = List.replicate width true := by
    simp [S5, S4, S3, S2, S1, S0, inputBank, rowAddressSlots]
  have hcol : S5 (rowAddressSlots 2) =
      List.replicate (label % width) true := by
    simp [S5, S4, S3, S2, S1, rowAddressSlots]
  have hw1 : S5 (rowAddressSlots 3) = [] := by
    simp [S5, S4, S3, S2, S1, S0, inputBank, rowAddressSlots]
  have hw2 : S5 (rowAddressSlots 4) = [] := by
    simp [S5, S4, S3, S2, S1, S0, inputBank, rowAddressSlots]
  have hout : S5 (rowAddressSlots 5) =
      List.replicate sL true ++ oldOut := by
    simp [S5, rowAddressSlots]
  obtain ⟨ta, hta, ha⟩ := address_stage rowAddressSlots
    Label.rowAddress none (by intro l; rfl) S5
    (order j).val width (label % width)
    (List.replicate sL true ++ oldOut)
    hrow hwidth hcol hw1 hw2 hout
  have ha' : MatrixWeightedRowOrderMachine.run ta
      ⟨some (.rowAddress .outer), .address false, S5⟩ =
      ⟨none, .address false, S6⟩ := by
    simpa only [S6, rowAddressSlots] using ha
  have hterminal : S6 = terminalBank label width nv sL table oldOut
      aux j.val (order j).val := by
    funext k
    fin_cases k <;>
      simp [S6, S5, S4, S3, S2, S1, S0, terminalBank,
        inputBank]
    rw [← List.append_assoc, List.replicate_append_replicate]
    congr 1
    ac_rfl
  refine ⟨tp + tl + 1 + tc + 1 + ta, ?_, ?_⟩
  · simp only [List.length_replicate] at htc
    omega
  · have hpl : MatrixWeightedRowOrderMachine.run (tp + tl)
        ⟨some (start aux), initial, S0⟩ =
        ⟨some .afterLookup, .lookup none, S4⟩ := by
      rw [run_add hp' tl]
      exact hl'
    have hpl1 : MatrixWeightedRowOrderMachine.run (tp + tl + 1)
        ⟨some (start aux), initial, S0⟩ =
        ⟨some (.sourceCopy .scan), .copy none, S4⟩ := by
      rw [run_add hpl 1, after_lookup_step]
    have hplc : MatrixWeightedRowOrderMachine.run (tp + tl + 1 + tc)
        ⟨some (start aux), initial, S0⟩ =
        ⟨some .afterSource, .copy none, S5⟩ := by
      rw [run_add hpl1 tc]
      exact hc'
    have hplc1 : MatrixWeightedRowOrderMachine.run (tp + tl + 1 + tc + 1)
        ⟨some (start aux), initial, S0⟩ =
        ⟨some (.rowAddress .outer), .address false, S5⟩ := by
      rw [run_add hplc 1, after_source_step]
    rw [run_add hplc1 ta, ha', hterminal]

end EthInapproximability.CurrentPaper.MatrixWeightedRowOrderMachineRun
