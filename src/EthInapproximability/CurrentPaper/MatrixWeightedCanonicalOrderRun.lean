import EthInapproximability.CurrentPaper.MatrixWeightedCanonicalOrderMachine

/-! Charged execution of the canonical copy-major item-order serializer. -/

namespace EthInapproximability.CurrentPaper.MatrixWeightedCanonicalOrderRun

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixWeightedCanonicalOrderMachine

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem run_succ {c d : Config} (h : advance program c = d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, h]

theorem framed_run {K L V : Type*} [DecidableEq K]
    (ι : K ↪ Stack) (labels : L → Label) (embed : V → Control)
    (read : Control → V) (hread : Function.LeftInverse read embed)
    (next : Option Label)
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (hP : ∀ l, program (labels l) = stmt ι labels embed read next (P l))
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

theorem copy_stage (ι : Fin 3 ↪ Stack)
    (labels : BitMachineCopy.Label → Label) (next : Label)
    (hP : ∀ l, program (labels l) = stmt ι labels
      id id (some next) (BitMachineCopy.program l))
    (S : Stack → List Bool) (source target : List Bool)
    (s : Option Bool)
    (hs : S (ι 0) = source) (ht : S (ι 1) = target)
    (hw : S (ι 2) = []) :
    ∃ t ≤ 2 * source.length + 2,
      run t ⟨some (labels .scan), s, S⟩ =
        ⟨some next, none,
          Function.update S (ι 1) (source ++ target)⟩ := by
  let c := BitMachineCopy.cfg (some .scan) s source target []
  let d := BitMachineCopy.cfg none none source (source ++ target) []
  have hb (k : Fin 3) : c.stk k = S (ι k) := by
    fin_cases k <;> simp [c, BitMachineCopy.cfg,
      BitMachineCopy.stackContents, hs, ht, hw]
  have hr : ((advance BitMachineCopy.program)^[2 * source.length + 2]) c = d := by
    exact BitMachineCopy.run_correct s source target
  obtain ⟨t, ht', he⟩ := framed_run ι labels id id
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

theorem outer_cons (aux : Bool) (S : Stack → List Bool)
    (n : ℕ) (s : Control) (h : S 3 = List.replicate (n + 1) true) :
    run 1 ⟨some (.outer aux), s, S⟩ =
      ⟨some (.innerCopy aux .scan), some true,
        Function.update S 3 (List.replicate n true)⟩ := by
  simp [run, advance, program, TM2.step, h, List.replicate_succ]

theorem outer_nil (aux : Bool) (S : Stack → List Bool)
    (s : Control) (h : S 3 = []) :
    run 1 ⟨some (.outer aux), s, S⟩ =
      ⟨some (if aux then .reverse else .resetRank), none, S⟩ := by
  simp [run, advance, program, TM2.step, h]

theorem inner_cons (aux : Bool) (S : Stack → List Bool)
    (n : ℕ) (s : Control) (h : S 4 = List.replicate (n + 1) true) :
    run 1 ⟨some (.inner aux), s, S⟩ =
      ⟨some (.rankCopy aux .scan), some true,
        Function.update S 4 (List.replicate n true)⟩ := by
  simp [run, advance, program, TM2.step, h, List.replicate_succ]

theorem inner_nil (aux : Bool) (S : Stack → List Bool)
    (s : Control) (h : S 4 = []) :
    run 1 ⟨some (.inner aux), s, S⟩ =
      ⟨some (.skipCopy aux .scan), none, S⟩ := by
  simp [run, advance, program, TM2.step, h]

theorem after_rank (aux : Bool) (S : Stack → List Bool) (s : Control) :
    run 1 ⟨some (.afterRank aux), s, S⟩ =
      ⟨some (.inner aux), s,
        Function.update (Function.update S 7 (false :: S 7))
          5 (true :: S 5)⟩ := by
  simp [run, advance, program, TM2.step]

theorem after_skip (aux : Bool) (S : Stack → List Bool) (s : Control) :
    run 1 ⟨some (.afterSkip aux), s, S⟩ =
      ⟨some (.outer aux), s, S⟩ := by
  simp [run, advance, program, TM2.step]

theorem reset_cons (S : Stack → List Bool) (n : ℕ)
    (s : Control) (h : S 5 = List.replicate (n + 1) true) :
    run 1 ⟨some .resetRank, s, S⟩ =
      ⟨some .resetRank, some true,
        Function.update S 5 (List.replicate n true)⟩ := by
  simp [run, advance, program, TM2.step, h, List.replicate_succ]

theorem reset_nil (S : Stack → List Bool) (s : Control) (h : S 5 = []) :
    run 1 ⟨some .resetRank, s, S⟩ =
      ⟨some (.resetCopy .scan), none, S⟩ := by
  simp [run, advance, program, TM2.step, h]

theorem reverse_cons (S : Stack → List Bool) (b : Bool)
    (rest : List Bool) (s : Control) (h : S 7 = b :: rest) :
    run 1 ⟨some .reverse, s, S⟩ =
      ⟨some .reverse, some b,
        Function.update (Function.update S 7 rest) 8 (b :: S 8)⟩ := by
  simp [run, advance, program, TM2.step, h]

theorem reverse_nil (S : Stack → List Bool) (s : Control) (h : S 7 = []) :
    run 1 ⟨some .reverse, s, S⟩ = ⟨none, none, S⟩ := by
  simp [run, advance, program, TM2.step, h]

def innerBank (B : Stack → List Bool) (n r : ℕ) (acc : List Bool) :
    Stack → List Bool :=
  Function.update (Function.update (Function.update B 4
    (List.replicate n true)) 5 (List.replicate r true)) 7 acc

def innerCost (r : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => (2 * r + 4) + innerCost (r + 1) n

def innerAccum (r : ℕ) : ℕ → List Bool → List Bool
  | 0, acc => acc
  | n + 1, acc =>
      innerAccum (r + 1) n (false :: List.replicate r true ++ acc)

def innerStream (r : ℕ) : ℕ → List Bool
  | 0 => []
  | n + 1 => EncodedGraph.unary r ++ innerStream (r + 1) n

theorem innerAccum_eq (r n : ℕ) (acc : List Bool) :
    innerAccum r n acc = (innerStream r n).reverse ++ acc := by
  induction n generalizing r acc with
  | zero => simp [innerAccum, innerStream]
  | succ n ih =>
      rw [innerAccum, innerStream, List.reverse_append, ih]
      simp [EncodedGraph.unary, List.reverse_append, List.append_assoc]

theorem inner_loop (aux : Bool) (B : Stack → List Bool)
    (r n : ℕ) (acc : List Bool) (h6 : B 6 = []) :
    ∃ t ≤ innerCost r n,
      run t ⟨some (.inner aux), none, innerBank B n r acc⟩ =
      ⟨some (.skipCopy aux .scan), none,
        innerBank B 0 (r + n) (innerAccum r n acc)⟩ := by
  induction n generalizing r acc with
  | zero =>
      refine ⟨1, by simp [innerCost], ?_⟩
      have h4 : innerBank B 0 r acc 4 = [] := by simp [innerBank]
      rw [inner_nil aux _ none h4]
      simp [innerBank, innerAccum]
  | succ n ih =>
      let S0 := innerBank B (n + 1) r acc
      let S1 := Function.update S0 4 (List.replicate n true)
      have h4 : S0 4 = List.replicate (n + 1) true := by simp [S0, innerBank]
      have hp := inner_cons aux S0 n none h4
      have hs : S1 (rankCopySlots 0) = List.replicate r true := by
        simp [S1, S0, innerBank, rankCopySlots]
      have ht : S1 (rankCopySlots 1) = acc := by
        simp [S1, S0, innerBank, rankCopySlots]
      have hw : S1 (rankCopySlots 2) = [] := by
        simp [S1, S0, innerBank, rankCopySlots, h6]
      obtain ⟨tc, htc, hc⟩ := copy_stage rankCopySlots
        (Label.rankCopy aux) (.afterRank aux) (by intro l; rfl)
        S1 (List.replicate r true) acc (some true) hs ht hw
      have hca : run (tc + 1)
          ⟨some (.rankCopy aux .scan), some true, S1⟩ =
          ⟨some (.inner aux), none,
            innerBank B n (r + 1)
              (false :: List.replicate r true ++ acc)⟩ := by
        rw [run_add hc 1, after_rank]
        congr 1
        funext k
        fin_cases k <;>
          simp [S1, S0, innerBank, rankCopySlots,
            List.replicate_succ, Nat.add_comm]
      obtain ⟨ti, hti, hi⟩ := ih (r + 1)
        (false :: List.replicate r true ++ acc)
      refine ⟨1 + (tc + 1) + ti, ?_, ?_⟩
      · simp only [innerCost, List.length_replicate] at *
        omega
      · have hpc : run (1 + (tc + 1))
            ⟨some (.inner aux), none, S0⟩ =
            ⟨some (.inner aux), none,
              innerBank B n (r + 1)
                (false :: List.replicate r true ++ acc)⟩ := by
          rw [run_add hp (tc + 1)]
          exact hca
        rw [run_add hpc ti]
        simpa only [innerAccum, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hi

def outerBank (B : Stack → List Bool) (copies rank : ℕ)
    (acc : List Bool) : Stack → List Bool :=
  Function.update (Function.update (Function.update
    (Function.update B 3 (List.replicate copies true)) 4 [])
    5 (List.replicate rank true)) 7 acc

def outerCost (rank count skip : ℕ) : ℕ → ℕ
  | 0 => 1
  | copies + 1 =>
      (2 * count + 2 * skip + 6) + innerCost rank count +
        outerCost (rank + count + skip) count skip copies

def outerAccum (rank count skip : ℕ) : ℕ → List Bool → List Bool
  | 0, acc => acc
  | copies + 1, acc =>
      outerAccum (rank + count + skip) count skip copies
        (innerAccum rank count acc)

def outerStream (rank count skip : ℕ) : ℕ → List Bool
  | 0 => []
  | copies + 1 =>
      innerStream rank count ++
        outerStream (rank + count + skip) count skip copies

theorem outerAccum_eq (rank count skip copies : ℕ) (acc : List Bool) :
    outerAccum rank count skip copies acc =
      (outerStream rank count skip copies).reverse ++ acc := by
  induction copies generalizing rank acc with
  | zero => simp [outerAccum, outerStream]
  | succ copies ih =>
      rw [outerAccum, outerStream, List.reverse_append,
        ih, innerAccum_eq]
      simp [List.append_assoc]

theorem outer_loop (aux : Bool) (B : Stack → List Bool)
    (copies rank count skip : ℕ) (acc : List Bool)
    (hsource : B (groupSource aux) = List.replicate count true)
    (hskip : B (skipSource aux) = List.replicate skip true)
    (h6 : B 6 = []) :
    ∃ t ≤ outerCost rank count skip copies,
      run t ⟨some (.outer aux), none, outerBank B copies rank acc⟩ =
      ⟨some (if aux then .reverse else .resetRank), none,
        outerBank B 0 (rank + copies * (count + skip))
          (outerAccum rank count skip copies acc)⟩ := by
  induction copies generalizing rank acc with
  | zero =>
      refine ⟨1, by simp [outerCost], ?_⟩
      have h3 : outerBank B 0 rank acc 3 = [] := by simp [outerBank]
      rw [outer_nil aux _ none h3]
      simp [outerBank, outerAccum]
  | succ copies ih =>
      let S0 := outerBank B (copies + 1) rank acc
      let S1 := Function.update S0 3 (List.replicate copies true)
      have h3 : S0 3 = List.replicate (copies + 1) true := by
        simp [S0, outerBank]
      have hp := outer_cons aux S0 copies none h3
      have hs : S1 (innerCopySlots aux 0) =
          List.replicate count true := by
        cases aux <;> simpa [S1, S0, outerBank, innerCopySlots,
          groupSource] using hsource
      have ht : S1 (innerCopySlots aux 1) = [] := by
        simp [S1, S0, outerBank, innerCopySlots]
      have hw : S1 (innerCopySlots aux 2) = [] := by
        simp [S1, S0, outerBank, innerCopySlots, h6]
      obtain ⟨tc, htc, hc⟩ := copy_stage (innerCopySlots aux)
        (Label.innerCopy aux) (.inner aux) (by intro l; rfl)
        S1 (List.replicate count true) [] (some true) hs ht hw
      have hc' : run tc ⟨some (.innerCopy aux .scan), some true, S1⟩ =
          ⟨some (.inner aux), none, innerBank S1 count rank acc⟩ := by
        rw [show Function.update S1 (innerCopySlots aux 1)
            (List.replicate count true ++ []) =
            innerBank S1 count rank acc by
          funext k
          fin_cases k <;>
            simp [S1, S0, outerBank, innerBank, innerCopySlots]] at hc
        exact hc
      have h6' : S1 6 = [] := by simp [S1, S0, outerBank, h6]
      obtain ⟨ti, hti, hi⟩ := inner_loop aux S1 rank count acc h6'
      let acc' := innerAccum rank count acc
      let S2 := innerBank S1 0 (rank + count) acc'
      have hss : S2 (skipCopySlots aux 0) =
          List.replicate skip true := by
        cases aux <;> simpa [S2, acc', innerBank, S1, S0,
          outerBank, skipCopySlots, skipSource] using hskip
      have hst : S2 (skipCopySlots aux 1) =
          List.replicate (rank + count) true := by
        simp [S2, innerBank, skipCopySlots]
      have hsw : S2 (skipCopySlots aux 2) = [] := by
        simp [S2, innerBank, S1, S0, outerBank, skipCopySlots, h6]
      obtain ⟨tk, htk, hk⟩ := copy_stage (skipCopySlots aux)
        (Label.skipCopy aux) (.afterSkip aux) (by intro l; rfl)
        S2 (List.replicate skip true)
        (List.replicate (rank + count) true) none hss hst hsw
      let S3 := outerBank B copies (rank + count + skip) acc'
      have hk' : run (tk + 1)
          ⟨some (.skipCopy aux .scan), none, S2⟩ =
          ⟨some (.outer aux), none, S3⟩ := by
        rw [run_add hk 1, after_skip]
        congr 1
        funext k
        fin_cases k <;>
          simp [S3, S2, S1, S0, acc', outerBank, innerBank,
            skipCopySlots, List.replicate_append_replicate,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      obtain ⟨tr, htr, hr⟩ := ih (rank + count + skip) acc'
      refine ⟨1 + tc + ti + tk + 1 + tr, ?_, ?_⟩
      · simp only [outerCost, List.length_replicate] at *
        omega
      · have hpc : run (1 + tc)
            ⟨some (.outer aux), none, S0⟩ =
            ⟨some (.inner aux), none,
              innerBank S1 count rank acc⟩ := by
          rw [run_add hp tc]
          exact hc'
        have hpci : run (1 + tc + ti)
            ⟨some (.outer aux), none, S0⟩ =
            ⟨some (.skipCopy aux .scan), none, S2⟩ := by
          rw [run_add hpc ti]
          exact hi
        have hpciK : run (1 + tc + ti + tk + 1)
            ⟨some (.outer aux), none, S0⟩ =
            ⟨some (.outer aux), none, S3⟩ := by
          rw [show 1 + tc + ti + tk + 1 =
              (1 + tc + ti) + (tk + 1) by omega,
            run_add hpci (tk + 1)]
          exact hk'
        rw [run_add hpciK tr]
        have harith : rank + (copies + 1) * (count + skip) =
            rank + count + skip + copies * (count + skip) := by ring
        simpa only [S0, S3, acc', outerAccum, harith] using hr

theorem reset_loop (B : Stack → List Bool) (r : ℕ)
    (s : Control) :
    run (r + 1)
      ⟨some .resetRank, s,
        Function.update B 5 (List.replicate r true)⟩ =
      ⟨some (.resetCopy .scan), none, Function.update B 5 []⟩ := by
  induction r generalizing s with
  | zero =>
      simpa using reset_nil (Function.update B 5 []) s (by simp)
  | succ r ih =>
      have hs := reset_cons (Function.update B 5
        (List.replicate (r + 1) true)) r s (by simp)
      rw [show r + 1 + 1 = 1 + (r + 1) by omega,
        run_add hs (r + 1)]
      simpa only [Function.update_idem] using ih (some true)

theorem reverse_loop (B : Stack → List Bool) (xs out : List Bool)
    (s : Control) :
    run (xs.length + 1)
      ⟨some .reverse, s,
        Function.update (Function.update B 7 xs) 8 out⟩ =
      ⟨none, none,
        Function.update (Function.update B 7 []) 8 (xs.reverse ++ out)⟩ := by
  induction xs generalizing out s with
  | nil =>
      simpa using reverse_nil (Function.update (Function.update B 7 []) 8 out)
        s (by simp)
  | cons b xs ih =>
      have hs := reverse_cons
        (Function.update (Function.update B 7 (b :: xs)) 8 out)
        b xs s (by simp)
      rw [show (b :: xs).length + 1 = 1 + (xs.length + 1) by simp; omega,
        run_add hs (xs.length + 1)]
      have he : Function.update
          (Function.update
            (Function.update (Function.update B 7 (b :: xs)) 8 out)
            7 xs) 8
            (b :: (Function.update (Function.update B 7 (b :: xs)) 8 out) 8) =
          Function.update (Function.update B 7 xs) 8 (b :: out) := by
        funext k
        fin_cases k <;> simp
      rw [he, ih (b :: out)]
      simp [List.reverse_cons, List.append_assoc]

def totalCost (v a K : ℕ) : ℕ :=
  (2 * K + 2) + outerCost 0 v a K +
    (K * (v + a) + 1) + (2 * v + 2) +
    (2 * K + 2) + outerCost v a v K +
    (outerAccum v a v K (outerAccum 0 v a K [])).length + 1

def outputBank (v a K : ℕ) : Stack → List Bool :=
  ![List.replicate v true, List.replicate a true,
    List.replicate K true, [], [],
    List.replicate (v + K * (a + v)) true, [], [],
    outerStream 0 v a K ++ outerStream v a v K]

/-- The one fixed controller enumerates both grouped carriers and writes the
copy-major rank table, with all nine terminal stacks specified. -/
theorem complete_run (v a K : ℕ) :
    ∃ t ≤ totalCost v a K,
      run t ⟨some start, none, initialBank v a K⟩ =
        ⟨none, none, outputBank v a K⟩ := by
  let I := initialBank v a K
  let accV := outerAccum 0 v a K []
  let accA := outerAccum v a v K accV
  let rV := K * (v + a)
  let rA := v + K * (a + v)
  let B0 := outerBank I K 0 []
  let B1 := outerBank I 0 rV accV
  let B2 := Function.update B1 5 []
  let B3 := outerBank I K v accV
  let B4 := outerBank I 0 rA accA
  have hK : I (outerCopySlots 0) = List.replicate K true := by
    rfl
  have houter : I (outerCopySlots 1) = [] := by rfl
  have hwork : I (outerCopySlots 2) = [] := by rfl
  obtain ⟨t0, ht0, h0⟩ := copy_stage outerCopySlots
    (Label.outerCopy false) (.outer false) (by intro l; rfl)
    I (List.replicate K true) [] none hK houter hwork
  have h0' : run t0 ⟨some start, none, I⟩ =
      ⟨some (.outer false), none, B0⟩ := by
    have hb : Function.update I (outerCopySlots 1)
        (List.replicate K true ++ []) = B0 := by
      funext k
      fin_cases k <;> simp [B0, outerBank, I, initialBank, outerCopySlots]
    rw [hb] at h0
    simpa only [start] using h0
  obtain ⟨tv, htv, hv⟩ := outer_loop false I K 0 v a []
    (by rfl) (by rfl) (by rfl)
  have hv' : run tv ⟨some (.outer false), none, B0⟩ =
      ⟨some .resetRank, none, B1⟩ := by
    simpa [B0, B1, accV, rV] using hv
  have hreset : run (rV + 1) ⟨some .resetRank, none, B1⟩ =
      ⟨some (.resetCopy .scan), none, B2⟩ := by
    have he : Function.update B1 5 (List.replicate rV true) = B1 := by
      funext k
      fin_cases k <;> simp [B1, outerBank]
    simpa only [he, B2] using reset_loop B1 rV none
  have hV : B2 (resetCopySlots 0) = List.replicate v true := by
    simp [B2, B1, outerBank, I, initialBank, resetCopySlots]
  have hrank : B2 (resetCopySlots 1) = [] := by
    simp [B2, resetCopySlots]
  have hscratch : B2 (resetCopySlots 2) = [] := by
    simp [B2, B1, outerBank, I, initialBank, resetCopySlots]
  obtain ⟨t1, ht1, h1⟩ := copy_stage resetCopySlots
    Label.resetCopy (.outerCopy true .scan) (by intro l; rfl)
    B2 (List.replicate v true) [] none hV hrank hscratch
  let B2' := Function.update B2 5 (List.replicate v true)
  have h1' : run t1 ⟨some (.resetCopy .scan), none, B2⟩ =
      ⟨some (.outerCopy true .scan), none, B2'⟩ := by
    simpa only [B2', resetCopySlots, List.append_nil] using h1
  have hK' : B2' (outerCopySlots 0) = List.replicate K true := by
    simp [B2', B2, B1, outerBank, I, initialBank, outerCopySlots]
  have houter' : B2' (outerCopySlots 1) = [] := by
    simp [B2', B2, B1, outerBank, outerCopySlots]
  have hwork' : B2' (outerCopySlots 2) = [] := by
    simp [B2', B2, B1, outerBank, I, initialBank, outerCopySlots]
  obtain ⟨t2, ht2, h2⟩ := copy_stage outerCopySlots
    (Label.outerCopy true) (.outer true) (by intro l; rfl)
    B2' (List.replicate K true) [] none hK' houter' hwork'
  have h2' : run t2 ⟨some (.outerCopy true .scan), none, B2'⟩ =
      ⟨some (.outer true), none, B3⟩ := by
    have he : Function.update B2' 3 (List.replicate K true) = B3 := by
      funext k
      fin_cases k <;>
        simp [B2', B2, B1, B3, outerBank, I, initialBank]
    have h2simple : run t2 ⟨some (.outerCopy true .scan), none, B2'⟩ =
        ⟨some (.outer true), none,
          Function.update B2' 3 (List.replicate K true)⟩ := by
      simpa only [outerCopySlots, List.append_nil] using h2
    rw [he] at h2simple
    exact h2simple
  obtain ⟨ta, hta, ha⟩ := outer_loop true I K v a v accV
    (by rfl) (by rfl) (by rfl)
  have ha' : run ta ⟨some (.outer true), none, B3⟩ =
      ⟨some .reverse, none, B4⟩ := by
    simpa [B3, B4, accA, rA] using ha
  have hrev : run (accA.length + 1) ⟨some .reverse, none, B4⟩ =
      ⟨none, none,
        Function.update (Function.update B4 7 []) 8 accA.reverse⟩ := by
    have he : Function.update (Function.update B4 7 accA) 8 [] = B4 := by
      funext k
      fin_cases k <;> simp [B4, outerBank, I, initialBank]
    simpa only [he, List.append_nil] using reverse_loop B4 accA [] none
  have hfinal : Function.update (Function.update B4 7 []) 8 accA.reverse =
      outputBank v a K := by
    have hwords : accA.reverse =
        outerStream 0 v a K ++ outerStream v a v K := by
      change (outerAccum v a v K (outerAccum 0 v a K [])).reverse = _
      rw [outerAccum_eq, outerAccum_eq]
      simp [List.reverse_append, List.append_assoc]
    funext k
    fin_cases k <;>
      simp [B4, outerBank, I, initialBank, outputBank,
        hwords, rA]
  refine ⟨t0 + tv + (rV + 1) + t1 + t2 + ta + (accA.length + 1), ?_, ?_⟩
  · change t0 + tv + (rV + 1) + t1 + t2 + ta +
        (accA.length + 1) ≤
        (2 * K + 2) + outerCost 0 v a K +
        (rV + 1) + (2 * v + 2) +
        (2 * K + 2) + outerCost v a v K +
        (accA.length + 1)
    simp only [List.length_replicate] at ht0 ht1 ht2
    omega
  · have h01 : run (t0 + tv) ⟨some start, none, I⟩ =
        ⟨some .resetRank, none, B1⟩ := by
      rw [run_add h0' tv]
      exact hv'
    have h012 : run (t0 + tv + (rV + 1))
        ⟨some start, none, I⟩ =
        ⟨some (.resetCopy .scan), none, B2⟩ := by
      rw [run_add h01 (rV + 1)]
      exact hreset
    have h0123 : run (t0 + tv + (rV + 1) + t1)
        ⟨some start, none, I⟩ =
        ⟨some (.outerCopy true .scan), none, B2'⟩ := by
      rw [run_add h012 t1]
      exact h1'
    have h01234 : run (t0 + tv + (rV + 1) + t1 + t2)
        ⟨some start, none, I⟩ =
        ⟨some (.outer true), none, B3⟩ := by
      rw [run_add h0123 t2]
      exact h2'
    have h012345 : run (t0 + tv + (rV + 1) + t1 + t2 + ta)
        ⟨some start, none, I⟩ =
        ⟨some .reverse, none, B4⟩ := by
      rw [run_add h01234 ta]
      exact ha'
    rw [run_add h012345 (accA.length + 1), hrev, hfinal]

theorem innerStream_eq_fields (r n : ℕ) :
    innerStream r n = MatrixWeightedRowOrderLookup.fields
      ((List.range n).map (fun i => r + i)) := by
  induction n generalizing r with
  | zero => simp [innerStream, MatrixWeightedRowOrderLookup.fields]
  | succ n ih =>
      rw [innerStream, List.range_succ_eq_map]
      simp [MatrixWeightedRowOrderLookup.fields, List.map_map,
        ih, EncodedGraph.unary, Function.comp_def,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def rankBlocks (rank count skip K : ℕ) : List ℕ :=
  (List.range K).flatMap fun copy =>
    (List.range count).map fun i => rank + copy * (count + skip) + i

theorem outerStream_eq_fields (rank count skip K : ℕ) :
    outerStream rank count skip K =
      MatrixWeightedRowOrderLookup.fields (rankBlocks rank count skip K) := by
  induction K generalizing rank with
  | zero => simp [outerStream, rankBlocks,
      MatrixWeightedRowOrderLookup.fields]
  | succ K ih =>
      rw [outerStream, innerStream_eq_fields, ih]
      simp [rankBlocks, MatrixWeightedRowOrderLookup.fields,
        List.range_succ_eq_map, List.flatMap_map, List.map_map,
        Function.comp_def, Nat.mul_add, Nat.succ_mul, Nat.add_mul, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]

theorem outputBank_table (v a K : ℕ) :
    outputBank v a K 8 = canonicalWord v a K := by
  change outerStream 0 v a K ++ outerStream v a v K = canonicalWord v a K
  rw [outerStream_eq_fields, outerStream_eq_fields]
  simp [canonicalWord, vertexRanks, auxiliaryRanks, rankBlocks,
    MatrixWeightedRowOrderLookup.fields, List.flatMap_append,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end EthInapproximability.CurrentPaper.MatrixWeightedCanonicalOrderRun
