import CurrentAdditive.FieldUnaryBankPrep

/-! Exact charged unary preparation runs for the local field initializer. -/

namespace CurrentAdditive.FieldSearchCompletion.FieldUnaryBankPrep

set_option maxHeartbeats 1000000

private theorem replicate_append_cons (k : Nat) (b : Bool) (xs : List Bool) :
    List.replicate k b ++ b :: xs = b :: (List.replicate k b ++ xs) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]

private theorem replicate_add_two (k : Nat) (b : Bool) :
    List.replicate (k + 2) b = b :: b :: List.replicate k b := by
  simp [List.replicate_add, replicate_append_cons]

theorem scanD_run (d : Nat) (s : Control)
    (length tempD tempN counter divisor shift half pair printerLength halfWork :
      List Bool) :
    run d (cfg (some .scanD) s (List.replicate d true) length tempD tempN
      counter divisor shift half pair printerLength halfWork) =
    cfg (some .scanD) (if d = 0 then s else some true) [] length
      (List.replicate d true ++ tempD) tempN
      (List.replicate d false ++ counter) divisor
      (List.replicate d true ++ shift) half
      (List.replicate (2*d) false ++ pair) printerLength
      (List.replicate d true ++ halfWork) := by
  induction d generalizing s tempD counter shift pair halfWork with
  | zero => simp [run, cfg, bank]
  | succ d ih =>
    simp only [List.replicate_succ]
    rw [show d + 1 = 1 + d by omega, run_add,
      run_one (step_scanD_cons length tempD tempN counter divisor shift half
        pair printerLength halfWork (List.replicate d true) s)]
    rw [ih]
    simp [replicate_append_cons, Nat.mul_add, List.replicate_add, Nat.add_comm]

theorem restoreD_run (d : Nat) (s : Control)
    (degree length tempN counter divisor shift half pair printerLength halfWork :
      List Bool) :
    run d (cfg (some .restoreD) s degree length (List.replicate d true) tempN
      counter divisor shift half pair printerLength halfWork) =
    cfg (some .restoreD) (if d = 0 then s else some true)
      (List.replicate d true ++ degree) length [] tempN counter divisor shift
      half pair printerLength halfWork := by
  induction d generalizing s degree with
  | zero => simp [run, cfg, bank]
  | succ d ih =>
    simp only [List.replicate_succ]
    rw [show d + 1 = 1 + d by omega, run_add,
      run_one (step_restoreD_cons degree length (List.replicate d true)
        tempN counter divisor shift half pair printerLength halfWork s)]
    rw [ih]
    simp [replicate_append_cons]

theorem scanN_run (n : Nat) (s : Control)
    (degree tempD tempN counter divisor shift half pair printerLength halfWork :
      List Bool) :
    run n (cfg (some .scanN) s degree (List.replicate n true) tempD tempN
      counter divisor shift half pair printerLength halfWork) =
    cfg (some .scanN) (if n = 0 then s else some true) degree [] tempD
      (List.replicate n true ++ tempN) counter divisor shift half pair
      (List.replicate n true ++ printerLength) halfWork := by
  induction n generalizing s tempN printerLength with
  | zero => simp [run, cfg, bank]
  | succ n ih =>
    simp only [List.replicate_succ]
    rw [show n + 1 = 1 + n by omega, run_add,
      run_one (step_scanN_cons degree (List.replicate n true) tempD tempN
        counter divisor shift half pair printerLength halfWork s)]
    rw [ih]
    simp [replicate_append_cons]

theorem restoreN_run (n : Nat) (s : Control)
    (degree length tempD counter divisor shift half pair printerLength halfWork :
      List Bool) :
    run n (cfg (some .restoreN) s degree length tempD (List.replicate n true)
      counter divisor shift half pair printerLength halfWork) =
    cfg (some .restoreN) (if n = 0 then s else some true) degree
      (List.replicate n true ++ length) tempD [] counter divisor shift half pair
      printerLength halfWork := by
  induction n generalizing s length with
  | zero => simp [run, cfg, bank]
  | succ n ih =>
    simp only [List.replicate_succ]
    rw [show n + 1 = 1 + n by omega, run_add,
      run_one (step_restoreN_cons degree length tempD (List.replicate n true)
        counter divisor shift half pair printerLength halfWork s)]
    rw [ih]
    simp [replicate_append_cons]

theorem halve_even_run (k : Nat) (s : Control)
    (degree length tempD tempN counter divisor shift half pair printerLength :
      List Bool) :
    run (k + 1)
      (cfg (some .halve) s degree length tempD tempN counter divisor shift
        half pair printerLength (List.replicate (2*k) true)) =
    cfg (some .scanN) none degree length tempD tempN counter divisor shift
      (List.replicate k true ++ half) pair printerLength [] := by
  induction k generalizing s half with
  | zero => simpa using run_one (step_halve_nil degree length tempD tempN
      counter divisor shift half pair printerLength s)
  | succ k ih =>
    have hrep : List.replicate (2*(k+1)) true =
        true :: true :: List.replicate (2*k) true := by
      rw [show 2*(k+1) = 2*k+2 by omega, replicate_add_two]
    rw [hrep, show k + 1 + 1 = 1 + (k + 1) by omega, run_add,
      run_one (step_halve_pair degree length tempD tempN counter divisor shift
        half pair printerLength (List.replicate (2*k) true) s)]
    rw [ih]
    simp only [replicate_append_cons, List.replicate_succ, List.cons_append]

theorem halve_odd_run (k : Nat) (s : Control)
    (degree length tempD tempN counter divisor shift half pair printerLength :
      List Bool) :
    run (k + 1)
      (cfg (some .halve) s degree length tempD tempN counter divisor shift
        half pair printerLength (List.replicate (2*k+1) true)) =
    cfg (some .scanN) none degree length tempD tempN counter divisor shift
      (List.replicate k true ++ half) pair printerLength [] := by
  induction k generalizing s half with
  | zero => simpa using run_one (step_halve_one degree length tempD tempN
      counter divisor shift half pair printerLength s)
  | succ k ih =>
    have hrep : List.replicate (2*(k+1)+1) true =
        true :: true :: List.replicate (2*k+1) true := by
      rw [show 2*(k+1)+1 = (2*k+1)+2 by omega, replicate_add_two]
    rw [hrep, show k + 1 + 1 = 1 + (k + 1) by omega, run_add,
      run_one (step_halve_pair degree length tempD tempN counter divisor shift
        half pair printerLength (List.replicate (2*k+1) true) s)]
    rw [ih]
    simp only [replicate_append_cons, List.replicate_succ, List.cons_append]

theorem halve_run (d : Nat) (s : Control)
    (degree length tempD tempN counter divisor shift half pair printerLength :
      List Bool) :
    run (d / 2 + 1)
      (cfg (some .halve) s degree length tempD tempN counter divisor shift
        half pair printerLength (List.replicate d true)) =
    cfg (some .scanN) none degree length tempD tempN counter divisor shift
      (List.replicate (d/2) true ++ half) pair printerLength [] := by
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · have he : d = 2*(d/2) := by omega
    have hr := halve_even_run (d/2) s degree length tempD tempN counter
      divisor shift half pair printerLength
    rw [←he] at hr
    exact hr
  · have ho : d = 2*(d/2)+1 := by omega
    have hr := halve_odd_run (d/2) s degree length tempD tempN counter
      divisor shift half pair printerLength
    rw [←ho] at hr
    exact hr

def initial (d n : Nat) : Config :=
  cfg (some .scanD) none (List.replicate d true) (List.replicate n true)
    [] [] [] [] [] [] [] [] []

def degreeReady (d n : Nat) : Config :=
  cfg (some .scanN) none (List.replicate d true) (List.replicate n true)
    [] [] (List.replicate d false) [] (List.replicate (d-1) true)
    (List.replicate (d/2) true) (List.replicate (2*d) false) [] []

theorem run_degree_stage (d n : Nat) (hd : 0 < d) :
    run (2*d + d/2 + 4) (initial d n) = degreeReady d n := by
  have hshift : List.replicate d true = true :: List.replicate (d-1) true := by
    cases d with
    | zero => omega
    | succ k =>
        rw [show k + 1 - 1 = k by omega, List.replicate_succ]
  let q0 := initial d n
  let q1 := cfg (some .scanD) (some true) [] (List.replicate n true)
    (List.replicate d true) [] (List.replicate d false) []
    (List.replicate d true) [] (List.replicate (2*d) false) []
    (List.replicate d true)
  let q2 := cfg (some .restoreD) none [] (List.replicate n true)
    (List.replicate d true) [] (List.replicate d false) []
    (List.replicate d true) [] (List.replicate (2*d) false) []
    (List.replicate d true)
  let q3 := cfg (some .restoreD) (some true) (List.replicate d true)
    (List.replicate n true) [] [] (List.replicate d false) []
    (List.replicate d true) [] (List.replicate (2*d) false) []
    (List.replicate d true)
  let q4 := cfg (some .dropShift) none (List.replicate d true)
    (List.replicate n true) [] [] (List.replicate d false) []
    (List.replicate d true) [] (List.replicate (2*d) false) []
    (List.replicate d true)
  let q5 := cfg (some .halve) (some true) (List.replicate d true)
    (List.replicate n true) [] [] (List.replicate d false) []
    (List.replicate (d-1) true) [] (List.replicate (2*d) false) []
    (List.replicate d true)
  have h1 : run d q0 = q1 := by
    simpa [q0, q1, initial, Nat.ne_of_gt hd] using
      scanD_run d none (List.replicate n true) [] [] [] [] [] [] [] [] []
  have h2 : run 1 q1 = q2 := by
    exact run_one (step_scanD_nil (List.replicate n true)
      (List.replicate d true) [] (List.replicate d false) []
      (List.replicate d true) [] (List.replicate (2*d) false) []
      (List.replicate d true) (some true))
  have h3 : run d q2 = q3 := by
    simpa [q2, q3, Nat.ne_of_gt hd] using
      restoreD_run d none [] (List.replicate n true) []
        (List.replicate d false) [] (List.replicate d true) []
        (List.replicate (2*d) false) [] (List.replicate d true)
  have h4 : run 1 q3 = q4 := by
    exact run_one (step_restoreD_nil (List.replicate d true)
      (List.replicate n true) [] (List.replicate d false) []
      (List.replicate d true) [] (List.replicate (2*d) false) []
      (List.replicate d true) (some true))
  have h5 : run 1 q4 = q5 := by
    have hs := run_one (step_dropShift (List.replicate d true)
      (List.replicate n true) [] [] (List.replicate d false) []
      (List.replicate (d-1) true) [] (List.replicate (2*d) false) []
      (List.replicate d true) none)
    simpa only [q4, q5, hshift] using hs
  have h6 : run (d/2+1) q5 = degreeReady d n := by
    simpa only [q5, degreeReady, List.append_nil] using
      halve_run d (some true) (List.replicate d true)
        (List.replicate n true) [] [] (List.replicate d false) []
        (List.replicate (d-1) true) [] (List.replicate (2*d) false) []
  have ht : 2*d+d/2+4 = d+1+d+1+1+(d/2+1) := by omega
  have hchain :
      run (d+1+d+1+1+(d/2+1)) q0 =
        run (d/2+1) (run 1 (run 1 (run d (run 1 (run d q0))))) := by
    rw [run_add (d+1+d+1+1) (d/2+1),
      run_add (d+1+d+1) 1, run_add (d+1+d) 1,
      run_add (d+1) d, run_add d 1]
  change run (2*d+d/2+4) q0 = degreeReady d n
  rw [ht, hchain, h1, h2, h3, h4, h5]
  exact h6

def prepared (d n : Nat) : Config :=
  cfg none none (List.replicate d true) (List.replicate n true)
    [] [] (List.replicate d false) [false]
    (List.replicate (d-1) true) (List.replicate (d/2) true)
    (List.replicate (2*d) false) (List.replicate n true) []

theorem run_length_stage (d n : Nat) :
    run (2*n+3) (degreeReady d n) = prepared d n := by
  let q0 := degreeReady d n
  let q1 := cfg (some .scanN) (if n = 0 then none else some true)
    (List.replicate d true) [] [] (List.replicate n true)
    (List.replicate d false) [] (List.replicate (d-1) true)
    (List.replicate (d/2) true) (List.replicate (2*d) false)
    (List.replicate n true) []
  let q2 := cfg (some .restoreN) none (List.replicate d true) [] []
    (List.replicate n true) (List.replicate d false) []
    (List.replicate (d-1) true) (List.replicate (d/2) true)
    (List.replicate (2*d) false) (List.replicate n true) []
  let q3 := cfg (some .restoreN) (if n = 0 then none else some true)
    (List.replicate d true) (List.replicate n true) [] []
    (List.replicate d false) [] (List.replicate (d-1) true)
    (List.replicate (d/2) true) (List.replicate (2*d) false)
    (List.replicate n true) []
  let q4 := cfg (some .install) none (List.replicate d true)
    (List.replicate n true) [] [] (List.replicate d false) []
    (List.replicate (d-1) true) (List.replicate (d/2) true)
    (List.replicate (2*d) false) (List.replicate n true) []
  have h1 : run n q0 = q1 := by
    simpa only [q0, q1, degreeReady, List.append_nil] using
      scanN_run n none (List.replicate d true) [] []
        (List.replicate d false) [] (List.replicate (d-1) true)
        (List.replicate (d/2) true) (List.replicate (2*d) false) [] []
  have h2 : run 1 q1 = q2 := by
    exact run_one (step_scanN_nil (List.replicate d true) []
      (List.replicate n true) (List.replicate d false) []
      (List.replicate (d-1) true) (List.replicate (d/2) true)
      (List.replicate (2*d) false) (List.replicate n true) []
      (if n = 0 then none else some true))
  have h3 : run n q2 = q3 := by
    simpa only [q2, q3, List.append_nil] using
      restoreN_run n none (List.replicate d true) [] []
        (List.replicate d false) [] (List.replicate (d-1) true)
        (List.replicate (d/2) true) (List.replicate (2*d) false)
        (List.replicate n true) []
  have h4 : run 1 q3 = q4 := by
    exact run_one (step_restoreN_nil (List.replicate d true)
      (List.replicate n true) [] (List.replicate d false) []
      (List.replicate (d-1) true) (List.replicate (d/2) true)
      (List.replicate (2*d) false) (List.replicate n true) []
      (if n = 0 then none else some true))
  have h5 : run 1 q4 = prepared d n := by
    exact run_one (step_install (List.replicate d true)
      (List.replicate n true) [] [] (List.replicate d false) []
      (List.replicate (d-1) true) (List.replicate (d/2) true)
      (List.replicate (2*d) false) (List.replicate n true) [] none)
  have ht : 2*n+3 = n+1+n+1+1 := by omega
  have hchain : run (n+1+n+1+1) q0 =
      run 1 (run 1 (run n (run 1 (run n q0)))) := by
    rw [run_add (n+1+n+1) 1, run_add (n+1+n) 1,
      run_add (n+1) n, run_add n 1]
  change run (2*n+3) q0 = prepared d n
  rw [ht, hchain, h1, h2, h3, h4, h5]

theorem run_prepare (d n : Nat) (hd : 0 < d) :
    run (2*d+d/2+2*n+7) (initial d n) = prepared d n := by
  have htime : 2*d+d/2+2*n+7 = (2*d+d/2+4)+(2*n+3) := by omega
  rw [htime, run_add, run_degree_stage d n hd, run_length_stage]

#print axioms run_prepare

end CurrentAdditive.FieldSearchCompletion.FieldUnaryBankPrep
