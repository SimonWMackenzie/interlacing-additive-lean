import EthInapproximability.CurrentPaper.PrimeSamplerEntrySemantics
import EthInapproximability.CurrentPaper.BitMachineBroadcast

/-!
# A physical prime-polynomial entry accessor

Source: frozen v8 `B-effectivity-details.tex`, the explicit balanced-family
accessor. Raw unary banks hold a valid label, modulus, number of coefficients,
coordinate, and alphabet size. The machine extracts the coefficients, moves
the resulting stream, evaluates it by physical Horner steps, and reduces the
answer modulo the alphabet size. Every transfer and arithmetic loop is charged.
This raw-bank interface does not assert a binary-query running-time bound.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerEntryMachine

open Turing BitMachineEncoding BitMachineComposition BitMachineSubroutine

inductive Admin where
  | coordinate | modulus | reverse | stream
  deriving DecidableEq, Fintype

abbrev Stack := Fin 11
abbrev Label := PrimeSamplerDigits.Label ⊕
  (PrimeSamplerHornerMachine.Label ⊕ (MatrixUnaryDivision.Label ⊕ Admin))
abbrev Control := Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def unitControl : Control × Unit ≃ Control where
  toFun := Prod.fst
  invFun v := (v,())
  left_inv v := by rcases v with ⟨v,u⟩; cases u; rfl
  right_inv _ := rfl

def hornerLabels : PrimeSamplerHornerMachine.Label ⊕
    (PrimeSamplerDigits.Label ⊕ (MatrixUnaryDivision.Label ⊕ Admin)) ≃ Label where
  toFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inr l)
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inl l
    | .inr (.inr l) => .inr (.inr l)
  left_inv l := by rcases l with l | (l | l) <;> rfl
  right_inv l := by rcases l with l | (l | l) <;> rfl

def divisionLabels : MatrixUnaryDivision.Label ⊕
    (PrimeSamplerDigits.Label ⊕ (PrimeSamplerHornerMachine.Label ⊕ Admin)) ≃ Label where
  toFun
    | .inl l => .inr (.inr (.inl l))
    | .inr (.inl l) => .inl l
    | .inr (.inr (.inl l)) => .inr (.inl l)
    | .inr (.inr (.inr l)) => .inr (.inr (.inr l))
  invFun
    | .inl l => .inr (.inl l)
    | .inr (.inl l) => .inr (.inr (.inl l))
    | .inr (.inr (.inl l)) => .inl l
    | .inr (.inr (.inr l)) => .inr (.inr (.inr l))
  left_inv l := by rcases l with l | (l | (l | l)) <;> rfl
  right_inv l := by rcases l with l | (l | (l | l)) <;> rfl

def divisionPermutation : Stack ≃ Stack where
  toFun i := ![1,10,3,4,7,8,0,2,5,6,9] i
  invFun i := ![6,0,7,2,3,8,9,4,5,10,1] i
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def divisionStacks : Fin 6 ⊕ Fin 5 ≃ Stack :=
  finSumFinEquiv.trans divisionPermutation

def admin (l : Admin) : Label := .inr (.inr (.inr l))
def hornerStart : Label := .inr (.inl (.inr .scan))
def divisionStart : Label := .inr (.inr (.inl .start))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt (finSumFinEquiv : Fin 8 ⊕ Fin 3 ≃ Stack) (Equiv.refl _)
      unitControl (liftStmt (some (.inr (.inr Admin.coordinate))) (PrimeSamplerDigits.program l))
  | .inr (.inl l) => renameStmt (finSumFinEquiv : Fin 10 ⊕ Fin 1 ≃ Stack)
      hornerLabels unitControl
      (liftStmt (some (.inr (.inl MatrixUnaryDivision.Label.start)))
        (PrimeSamplerHornerMachine.program l))
  | .inr (.inr (.inl l)) => renameStmt divisionStacks divisionLabels (Equiv.refl _)
      (liftStmt (none : Option (PrimeSamplerDigits.Label ⊕
        (PrimeSamplerHornerMachine.Label ⊕ Admin))) (MatrixUnaryDivision.program l))
  | .inr (.inr (.inr .coordinate)) =>
      BitMachineBroadcast.restoreStep 8 [0] (admin .coordinate) (admin .modulus)
  | .inr (.inr (.inr .modulus)) =>
      BitMachineBroadcast.restoreStep 1 [6] (admin .modulus) (admin .reverse)
  | .inr (.inr (.inr .reverse)) =>
      BitMachineBroadcast.restoreStep 7 [2] (admin .reverse) (admin .stream)
  | .inr (.inr (.inr .stream)) =>
      BitMachineBroadcast.restoreStep 2 [9] (admin .stream) hornerStart

def cfg (l : Option Label) (bank : Stack → List Bool) : Config :=
  ⟨l,(false,none),bank⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c
def unary (n : ℕ) : List Bool := List.replicate n true

theorem run_add {c d : Config} {t : ℕ} (h : run t c=d) (u : ℕ) :
    run (t+u) c=run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def digitFrame (j m : ℕ) (c : PrimeSamplerDigits.Config) : Config :=
  renameCfg (finSumFinEquiv : Fin 8 ⊕ Fin 3 ≃ Stack) (Equiv.refl _) unitControl
    (liftCfg (some (.inr (.inr Admin.coordinate))) () (fun i => ![unary j,[],unary m] i) c)

theorem extract_run (p t l j m : ℕ) (hl : l<p^t) :
    ∃ n ≤ t*(10*l+3*p+10)+1,
      run n (cfg (some (.inl (.inr .loop)))
        ![unary l,unary p,[],[],[],[],unary t,[],unary j,[],unary m]) =
      cfg (some (admin .coordinate))
        ![[],unary p,[],[],[],[],[],PrimeSamplerDigits.digits p t l [],unary j,[],unary m] := by
  obtain ⟨a,ha,he⟩ := PrimeSamplerDigits.extraction_exact l p (unary t) []
  simp only [show (unary t).length=t from List.length_replicate] at ha he
  obtain ⟨n,hn,hr⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    (finSumFinEquiv : Fin 8 ⊕ Fin 3 ≃ Stack) (Equiv.refl _) unitControl
    PrimeSamplerDigits.program program (some (.inr (.inr Admin.coordinate)))
    (fun _ => rfl) () (fun i => ![unary j,[],unary m] i)
    (PrimeSamplerDigits.ready l p (unary t) []) a
    (by rw [show ((advance PrimeSamplerDigits.program)^[a]) _ = _ from he]; rfl)
  change run n (digitFrame j m _) = digitFrame j m (PrimeSamplerDigits.run _ _) at hr
  rw [he] at hr
  have hz : l/p^t=0 := Nat.div_eq_of_lt hl
  simp only [hz,List.replicate_zero] at hr
  have hi : digitFrame j m (PrimeSamplerDigits.ready l p (unary t) []) =
      cfg (some (.inl (.inr .loop)))
        ![unary l,unary p,[],[],[],[],unary t,[],unary j,[],unary m] := by
    unfold digitFrame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : digitFrame j m (PrimeSamplerDigits.cfg none (false,none)
      {divisor:=unary p,digits:=PrimeSamplerDigits.digits p t l []}) =
      cfg (some (admin .coordinate))
        ![[],unary p,[],[],[],[],[],PrimeSamplerDigits.digits p t l [],unary j,[],unary m] := by
    unfold digitFrame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  simp only [unary] at hf
  exact ⟨n,hn.trans ha,by simpa only [hi,hf] using hr⟩

theorem move_run (source target : Stack) (hne : source ≠ target)
    (label next : Label)
    (hp : program label = BitMachineBroadcast.restoreStep source [target] label next)
    (bank : Stack → List Bool) :
    run ((bank source).length+1) (cfg (some label) bank) =
      cfg (some next)
        (Function.update (BitMachineBroadcast.prepend [target] (bank source).reverse bank) source []) := by
  have h := BitMachineBroadcast.restore_run program source [target] (by simp)
    (by simpa using hne) label next hp false none (bank source) bank
  simpa only [Function.update_eq_self,BitMachineBroadcast.run,run,cfg] using h

theorem transfer_run (p j m : ℕ) (stream : List Bool) :
    run (j+p+2*stream.length+4)
      (cfg (some (admin .coordinate))
        ![[],unary p,[],[],[],[],[],stream,unary j,[],unary m]) =
      cfg (some hornerStart)
        ![unary j,[],[],[],[],[],unary p,[],[],stream,unary m] := by
  have h1 := move_run 8 0 (by decide) (admin .coordinate) (admin .modulus) rfl
    ![[],unary p,[],[],[],[],[],stream,unary j,[],unary m]
  have hb1 : Function.update (BitMachineBroadcast.prepend [0]
      (unary j).reverse ![[],unary p,[],[],[],[],[],stream,unary j,[],unary m]) 8 [] =
      (![unary j,unary p,[],[],[],[],[],stream,[],[],unary m] : Stack → List Bool) := by
    funext k
    fin_cases k <;> simp [BitMachineBroadcast.prepend,unary]
  change run ((unary j).length+1) _ = cfg _ _ at h1
  change run ((unary j).length+1) _ = cfg _
    (Function.update (BitMachineBroadcast.prepend [0] (unary j).reverse
      ![[],unary p,[],[],[],[],[],stream,unary j,[],unary m]) 8 []) at h1
  rw [hb1] at h1
  have h2 := move_run 1 6 (by decide) (admin .modulus) (admin .reverse) rfl
    ![unary j,unary p,[],[],[],[],[],stream,[],[],unary m]
  have hb2 : Function.update (BitMachineBroadcast.prepend [6]
      (unary p).reverse ![unary j,unary p,[],[],[],[],[],stream,[],[],unary m]) 1 [] =
      (![unary j,[],[],[],[],[],unary p,stream,[],[],unary m] : Stack → List Bool) := by
    funext k
    fin_cases k <;> simp [BitMachineBroadcast.prepend,unary]
  change run ((unary p).length+1) _ = cfg _ _ at h2
  change run ((unary p).length+1) _ = cfg _
    (Function.update (BitMachineBroadcast.prepend [6] (unary p).reverse
      ![unary j,unary p,[],[],[],[],[],stream,[],[],unary m]) 1 []) at h2
  rw [hb2] at h2
  have h3 := move_run 7 2 (by decide) (admin .reverse) (admin .stream) rfl
    ![unary j,[],[],[],[],[],unary p,stream,[],[],unary m]
  have hb3 : Function.update (BitMachineBroadcast.prepend [2]
      stream.reverse ![unary j,[],[],[],[],[],unary p,stream,[],[],unary m]) 7 [] =
      (![unary j,[],stream.reverse,[],[],[],unary p,[],[],[],unary m] : Stack → List Bool) := by
    funext k
    fin_cases k <;> simp [BitMachineBroadcast.prepend]
  change run (stream.length+1) _ = cfg _ _ at h3
  change run (stream.length+1) _ = cfg _
    (Function.update (BitMachineBroadcast.prepend [2] stream.reverse
      ![unary j,[],[],[],[],[],unary p,stream,[],[],unary m]) 7 []) at h3
  rw [hb3] at h3
  have h4 := move_run 2 9 (by decide) (admin .stream) hornerStart rfl
    ![unary j,[],stream.reverse,[],[],[],unary p,[],[],[],unary m]
  have hb4 : Function.update (BitMachineBroadcast.prepend [9]
      stream.reverse.reverse ![unary j,[],stream.reverse,[],[],[],unary p,[],[],[],unary m]) 2 [] =
      (![unary j,[],[],[],[],[],unary p,[],[],stream,unary m] : Stack → List Bool) := by
    funext k
    fin_cases k <;> simp [BitMachineBroadcast.prepend]
  change run (stream.reverse.length+1) _ = cfg _ _ at h4
  change run (stream.reverse.length+1) _ = cfg _
    (Function.update (BitMachineBroadcast.prepend [9] stream.reverse.reverse
      ![unary j,[],stream.reverse,[],[],[],unary p,[],[],[],unary m]) 2 []) at h4
  rw [hb4] at h4
  simp only [show (unary j).length=j from List.length_replicate] at h1
  simp only [show (unary p).length=p from List.length_replicate] at h2
  simp only [List.length_reverse] at h4
  rw [show j+p+2*stream.length+4 = (j+1)+((p+1)+((stream.length+1)+(stream.length+1))) by omega,
    run_add h1,run_add h2,run_add h3,h4]

def hornerFrame (m : ℕ) (c : PrimeSamplerHornerMachine.Config) : Config :=
  renameCfg (finSumFinEquiv : Fin 10 ⊕ Fin 1 ≃ Stack) hornerLabels unitControl
    (liftCfg (some (.inr (.inl MatrixUnaryDivision.Label.start))) () (fun _ => unary m) c)

theorem horner_run (p t l j m : ℕ) (hp : 0<p) (hj : j<p) :
    ∃ n ≤ t*(400*(p+1)^2)+1,
      run n (cfg (some hornerStart)
        ![unary j,[],[],[],[],[],unary p,[],[],PrimeSamplerDigits.digits p t l [],unary m]) =
      cfg (some divisionStart)
        ![unary j,unary (PrimeSamplerEntryAlgorithm.horner p j t l),[],[],[],[],unary p,[],[],[],unary m] := by
  obtain ⟨a,ha,he⟩ := PrimeSamplerHornerMachine.evaluation_exact p j 0
    (PrimeSamplerEntryAlgorithm.coefficients p t l) hp hj hp
    (PrimeSamplerEntryAlgorithm.coefficients_lt p t l hp)
  simp only [PrimeSamplerEntryAlgorithm.coefficients_length,
    PrimeSamplerEntryAlgorithm.evaluate_coefficients] at ha he
  obtain ⟨n,hn,hr⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    (finSumFinEquiv : Fin 10 ⊕ Fin 1 ≃ Stack) hornerLabels unitControl
    PrimeSamplerHornerMachine.program program
    (some (.inr (.inl MatrixUnaryDivision.Label.start))) (fun _ => rfl) ()
    (fun _ => unary m)
    (PrimeSamplerHornerMachine.ready p j 0
      (PrimeSamplerHornerMachine.encode (PrimeSamplerEntryAlgorithm.coefficients p t l))) a
    (by rw [show ((advance PrimeSamplerHornerMachine.program)^[a]) _ = _ from he]; rfl)
  change run n (hornerFrame m _) = hornerFrame m (PrimeSamplerHornerMachine.run _ _) at hr
  rw [he] at hr
  have hi : hornerFrame m (PrimeSamplerHornerMachine.ready p j 0
      (PrimeSamplerHornerMachine.encode (PrimeSamplerEntryAlgorithm.coefficients p t l))) =
      cfg (some hornerStart)
        ![unary j,[],[],[],[],[],unary p,[],[],PrimeSamplerDigits.digits p t l [],unary m] := by
    rw [PrimeSamplerEntrySemantics.digits_eq_encode,List.append_nil]
    unfold hornerFrame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : hornerFrame m (PrimeSamplerHornerMachine.cfg none (false,none)
      {coordinate:=unary j,accumulator:=unary (PrimeSamplerEntryAlgorithm.horner p j t l),
        modulus:=unary p}) =
      cfg (some divisionStart)
        ![unary j,unary (PrimeSamplerEntryAlgorithm.horner p j t l),[],[],[],[],unary p,[],[],[],unary m] := by
    unfold hornerFrame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  simp only [unary] at hf
  exact ⟨n,hn.trans ha,by simpa only [hi,hf] using hr⟩

def divisionFrame (p j : ℕ) (c : MatrixUnaryDivision.Config) : Config :=
  renameCfg divisionStacks divisionLabels (Equiv.refl _)
    (liftCfg (none : Option (PrimeSamplerDigits.Label ⊕
      (PrimeSamplerHornerMachine.Label ⊕ Admin))) none
      (fun i => ![unary j,[],[],unary p,[]] i) c)

theorem reduction_run (p j a m : ℕ) :
    ∃ n ≤ 8*a+3*m+4,
      run n (cfg (some divisionStart)
        ![unary j,unary a,[],[],[],[],unary p,[],[],[],unary m]) =
      cfg none ![unary j,[],[],[],unary (a%m),[],unary p,unary (a/m),[],[],unary m] := by
  have he := MatrixUnaryDivision.division_total_run a m
  change MatrixUnaryDivision.run (MatrixUnaryDivision.totalTime a m)
    (MatrixUnaryDivision.cfg (some .start) false (unary a) (unary m) [] [] [] []) =
    MatrixUnaryDivision.cfg none false [] (unary m) [] (unary (a%m)) (unary (a/m)) [] at he
  obtain ⟨n,hn,hr⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    divisionStacks divisionLabels (Equiv.refl _) MatrixUnaryDivision.program program
    (none : Option (PrimeSamplerDigits.Label ⊕ (PrimeSamplerHornerMachine.Label ⊕ Admin)))
    (fun _ => rfl) none (fun i => ![unary j,[],[],unary p,[]] i)
    (MatrixUnaryDivision.cfg (some .start) false (unary a) (unary m) [] [] [] [])
    (MatrixUnaryDivision.totalTime a m)
    (by rw [show ((advance MatrixUnaryDivision.program)^[_]) _ = _ from he]; rfl)
  change run n (divisionFrame p j _) = divisionFrame p j (MatrixUnaryDivision.run _ _) at hr
  rw [he] at hr
  have hi : divisionFrame p j (MatrixUnaryDivision.cfg (some .start) false
      (unary a) (unary m) [] [] [] []) =
      cfg (some divisionStart)
        ![unary j,unary a,[],[],[],[],unary p,[],[],[],unary m] := by
    unfold divisionFrame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hf : divisionFrame p j (MatrixUnaryDivision.cfg none false [] (unary m)
      [] (unary (a%m)) (unary (a/m)) []) =
      cfg none ![unary j,[],[],[],unary (a%m),[],unary p,unary (a/m),[],[],unary m] := by
    unfold divisionFrame renameCfg liftCfg cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  exact ⟨n,hn.trans (MatrixUnaryDivision.totalTime_bound a m),by simpa only [hi,hf] using hr⟩

def timeBound (p t l j m : ℕ) : ℕ :=
  (t*(10*l+3*p+10)+1)+(j+p+2*t*p+4)+(t*(400*(p+1)^2)+1)+(8*p+3*m+4)

/-- The complete literal entry computation. The only input promises are the
ordinary finite-domain bounds; there is no supplied evaluation or runtime
certificate. -/
theorem entry_run (p t l j m : ℕ) (hp : 0<p) (hj : j<p) (hl : l<p^t) :
    ∃ n ≤ timeBound p t l j m,
      let c := run n (cfg (some (.inl (.inr .loop)))
        ![unary l,unary p,[],[],[],[],unary t,[],unary j,[],unary m])
      c.l=none ∧ c.stk 4=unary (PrimeSampler.entry p t m l j) := by
  obtain ⟨a,ha,he⟩ := extract_run p t l j m hl
  have htransfer := transfer_run p j m (PrimeSamplerDigits.digits p t l [])
  obtain ⟨b,hb,hh⟩ := horner_run p t l j m hp hj
  obtain ⟨c,hc,hr⟩ := reduction_run p j (PrimeSamplerEntryAlgorithm.horner p j t l) m
  have hlength := PrimeSamplerEntrySemantics.digit_stream_length p t l hp
  have hvalue := PrimeSamplerEntryAlgorithm.horner_lt p j t l hp
  refine ⟨a+((j+p+2*(PrimeSamplerDigits.digits p t l []).length+4)+(b+c)),?_,?_⟩
  · unfold timeBound
    have htwice : 2*(PrimeSamplerDigits.digits p t l []).length≤2*t*p := by
      nlinarith [hlength]
    omega
  · dsimp only
    rw [run_add he,run_add htransfer,run_add hh,hr]
    constructor
    · rfl
    · change unary (PrimeSamplerEntryAlgorithm.horner p j t l%m) = _
      rw [←PrimeSamplerEntryAlgorithm.entry_eq]
      rfl

theorem timeBound_polynomial (p t l j m : ℕ) :
    timeBound p t l j m ≤ 500*(t+l+p+j+m+1)^3 := by
  let S := t+l+p+j+m+1
  have ht : t≤S := by dsimp [S]; omega
  have hl : l≤S := by dsimp [S]; omega
  have hp : p≤S := by dsimp [S]; omega
  have hj : j≤S := by dsimp [S]; omega
  have hm : m≤S := by dsimp [S]; omega
  have hp1 : p+1≤S := by dsimp [S]; omega
  have hS : 1≤S := by dsimp [S]; omega
  have hb : 10*l+3*p+10≤23*S := by omega
  have hprod := Nat.mul_le_mul ht hb
  have htp := Nat.mul_le_mul ht hp
  have hp2 : (p+1)^2≤S^2 := Nat.pow_le_pow_left hp1 2
  have hhorner := Nat.mul_le_mul ht (Nat.mul_le_mul_left 400 hp2)
  have hS2 : S≤S^2 := by nlinarith
  have hS3 : S^2≤S^3 := by
    have hx := Nat.mul_le_mul_left (S^2) hS
    nlinarith [hx]
  change timeBound p t l j m ≤ 500*S^3
  unfold timeBound
  nlinarith

/-- Polynomial in the numerical parameters, hence suitable for exponential
full materialization after bounding the finite carriers. This statement is
deliberately not polynomial in the binary query length. -/
theorem entry_run_polynomial (p t l j m : ℕ) (hp : 0<p) (hj : j<p) (hl : l<p^t) :
    ∃ n ≤ 500*(t+l+p+j+m+1)^3,
      let c := run n (cfg (some (.inl (.inr .loop)))
        ![unary l,unary p,[],[],[],[],unary t,[],unary j,[],unary m])
      c.l=none ∧ c.stk 4=unary (PrimeSampler.entry p t m l j) := by
  obtain ⟨n,hn,h⟩ := entry_run p t l j m hp hj hl
  exact ⟨n,hn.trans (timeBound_polynomial p t l j m),h⟩

end EthInapproximability.CurrentPaper.PrimeSamplerEntryMachine
