import Paper2.SuccessCodec

/-! Segment 2, item (2) prerequisite: every carrier value is a produced word
of its recursive code.

The request descent physically skips and captures label words with the
code-driven skipper (`FetchLabel.skipN_run` / `capture_run`), whose premise
is that each skipped word is `Produces (meaning code)`. Below level `k` the
labels are requested values (fixed tails, diagonal tails, source columns),
not sampled ones, so "produced by the sampler" is not available. This file
proves the needed semantic fact without any choice of values: every branch
of the actual finite-choice programs (`Program.uniform`, `iid`, `prod`, the
`tagged` 256-draw and the `rows` 512-draw) is a legal `Produces` path, hence
each actual program produces every value of its carrier; with the admitted
code/program identities (`seedRecursiveCodes_exact`, `ticketProd_exact`,
`tagged_exact`, `raw_exact`, `outer_exact`, `fixedTail_exact`,
`graphRows_canonical_exact`) every codec word is produced by its code.
This is a statement about reachable syntax only (no probabilities). -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace Paper2.FullSupport

open RecursiveSamplingProgram RecursiveSamplingLaws RecursiveRequestCodeShape
open GeneratorCode GeneratorSource RecursiveLabelCodecScratch
open RecursiveEntries

/-- Every value of the carrier is a possible terminal value. -/
def Full {A : Type*} (p : Program A) : Prop := ∀ a, Produces p a

theorem full_uniform (n : ℕ) (hn : 0 < n) : Full (Program.uniform n hn) :=
  fun i => .draw i (.pure i)

theorem full_map {A B : Type*} (f : A → B) (hf : Function.Surjective f)
    {p : Program A} (hp : Full p) : Full (Program.map f p) := by
  intro b
  obtain ⟨a, rfl⟩ := hf b
  exact (produces_map f p).mpr ⟨a, hp a, rfl⟩

theorem full_prod {A B : Type*} {p : Program A} {q : Program B}
    (hp : Full p) (hq : Full q) : Full (prod p q) := by
  rintro ⟨a, b⟩
  unfold prod
  exact (produces_bind p _).mpr ⟨a, hp a, (produces_map _ q).mpr ⟨b, hq b, rfl⟩⟩

theorem full_iid {A : Type*} {p : Program A} (hp : Full p) : ∀ n, Full (iid p n)
  | 0 => fun f => by
      have hf : f = finZeroElim := funext fun i => i.elim0
      rw [hf]
      exact .pure _
  | n + 1 => fun f => by
      change Produces (Program.bind p (fun a => Program.map (Fin.cons a) (iid p n))) f
      exact (produces_bind p _).mpr ⟨f 0, hp _,
        (produces_map _ _).mpr ⟨Fin.tail f, full_iid hp n _, Fin.cons_self_tail f⟩⟩

section Source

variable {X Y V A : Type*} {q₁ q₂ s : ℕ}

theorem full_uniform' (n : ℕ) [NeZero n] : Full (RecursiveSampling.uniform n) :=
  full_uniform _ _

theorem full_outer [NeZero q₂] {p : Program Y} (hp : Full p) :
    Full (RecursiveSampling.outer (q₁ := q₁) (q₂ := q₂) (s := s) p) :=
  full_prod (full_uniform' q₂) (full_iid hp _)

theorem full_raw [NeZero q₂] {p : Program Y} (hp : Full p) :
    Full (RecursiveSampling.raw (q₁ := q₁) (q₂ := q₂) (s := s) p) :=
  full_prod (full_iid hp _) (full_iid (full_outer hp) _)

theorem full_fixedTail [NeZero q₂] {p : Program Y} (hp : Full p) :
    Full (RecursiveSampling.fixedTail (q₁ := q₁) (q₂ := q₂) (s := s) p) :=
  full_iid (full_outer hp) _

theorem full_tagged [NeZero q₂] {p : Program Y} (hp : Full p) :
    Full (RecursiveSampling.tagged (q₁ := q₁) (q₂ := q₂) (s := s) p) := by
  intro z
  unfold RecursiveSampling.tagged
  cases z with
  | unrestricted Z =>
      refine .draw ⟨0, by decide⟩ ?_
      simpa using (produces_map _ _).mpr ⟨Z, full_raw hp Z, rfl⟩
  | fixedTail js =>
      refine .draw ⟨254, by decide⟩ ?_
      simpa using (produces_map _ _).mpr ⟨js, full_fixedTail hp js, rfl⟩
  | diagonal j =>
      refine .draw ⟨255, by decide⟩ ?_
      simpa using (produces_map _ _).mpr ⟨j, full_outer hp j, rfl⟩

theorem full_templateRow [NeZero q₁] [NeZero s] {p : Program X} (hp : Full p) :
    Full (RecursiveSampling.templateRow (q₁ := q₁) (q₂ := q₂) (s := s) p) :=
  full_prod (full_uniform' s) (full_iid (full_prod (full_uniform' q₁) hp) _)

theorem full_rows [NeZero q₁] [NeZero s] {vs : Program V} {as : Program A}
    {p : Program X} (hv : Full vs) (ha : Full as) (hp : Full p) :
    Full (RecursiveSampling.rows (q₁ := q₁) (q₂ := q₂) (s := s) vs as p) := by
  intro r
  unfold RecursiveSampling.rows
  rcases r with z | ⟨va, x⟩
  · refine .draw ⟨0, by decide⟩ ?_
    simpa using (produces_map _ _).mpr ⟨z, full_templateRow hp z, rfl⟩
  · rcases va with v | a
    · refine .draw ⟨510, by decide⟩ ?_
      simpa using (produces_map (fun k => (Sum.inr (Sum.inl k.1, k.2) :
        SourceMatrix.RawRow q₁ q₂ s X (V ⊕ A))) _).mpr
        ⟨(v, x), full_prod hv hp (v, x), rfl⟩
    · refine .draw ⟨511, by decide⟩ ?_
      simpa using (produces_map (fun k => (Sum.inr (Sum.inr k.1, k.2) :
        SourceMatrix.RawRow q₁ q₂ s X (V ⊕ A))) _).mpr
        ⟨(a, x), full_prod ha hp (a, x), rfl⟩

theorem full_graphRows [Fintype V] [Nonempty V] [NeZero q₁]
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s) {p : Program X} (hp : Full p) :
    Full (RecursiveSampling.graphRows (q₁ := q₁) (q₂ := q₂) order hs p) := by
  letI : NeZero s := ⟨by omega⟩
  unfold RecursiveSampling.graphRows
  apply full_map _ (SourceLawBinding.rawRowEquiv q₁ q₂ s X V).surjective
  apply full_rows
  · exact full_prod (full_uniform _ _)
      (full_map order order.surjective (full_uniform _ _))
  · exact full_prod (full_uniform _ _) (full_uniform _ _)
  · exact hp

end Source

theorem full_programs {X₀ Y₀ V : Type} [Fintype V] [Nonempty V]
    {s q₁ q₂ w Q : ℕ} [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]
    (order : Fin (Fintype.card V) ≃ V) (hs : 4 ≤ s)
    {row₀ : Program X₀} {col₀ : Program Y₀} (hr : Full row₀) (hc : Full col₀) :
    ∀ k, Full (RecursiveSampling.programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        order hs row₀ col₀ k).1 ∧
      Full (RecursiveSampling.programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        order hs row₀ col₀ k).2
  | 0 => ⟨hr, hc⟩
  | k + 1 =>
      have ih := full_programs order hs hr hc k
      ⟨full_iid (full_prod (full_uniform' w) (full_tagged ih.2)) Q,
        full_prod (full_uniform' Q) (full_iid (full_graphRows order hs ih.1) w)⟩

theorem full_seedRow (p : ℕ) : Full (RecursiveSamplingSeed.seedRow p) :=
  full_iid (full_map _ RecursiveSamplingSeed.bitEquiv.surjective (full_uniform _ _)) p

theorem full_seedColumn (p : ℕ) (hp : 0 < p) : Full (RecursiveSamplingSeed.seedColumn p hp) :=
  full_uniform p hp

/-! ### Every codec word is produced by its code -/

theorem code_full {A : Type} {c : Code} {ca : PrefixCodec A} {p : Program A}
    (hc : meaning c = Program.map ca.encode p) (hp : Full p) (a : A) :
    Produces (meaning c) (ca.encode a) := by
  rw [hc]
  exact (produces_map _ _).mpr ⟨a, hp a, rfl⟩

section Seed

variable {n p s q₁ q₂ w Q : ℕ} [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

theorem seed_programs_full (hp : 0 < p) (hs : 4 ≤ s) (k : ℕ) :
    Full (RecursiveSampling.programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        (finCongr (Fintype.card_fin n)) hs
        (RecursiveSamplingSeed.seedRow p) (RecursiveSamplingSeed.seedColumn p hp) k).1 ∧
    Full (RecursiveSampling.programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        (finCongr (Fintype.card_fin n)) hs
        (RecursiveSamplingSeed.seedRow p) (RecursiveSamplingSeed.seedColumn p hp) k).2 :=
  full_programs _ hs (full_seedRow p) (full_seedColumn p hp) k

/-- Level-`k` row and column words: every encoded carrier value is produced by
the actual level-`k` code. -/
theorem codes_full (hp : 0 < p) (hs : 4 ≤ s) (k : ℕ) :
    (∀ x, Produces (meaning (seedRecursiveCodes n p s q₁ q₂ w Q k).1)
      ((defaultCarrierCodecs n p s q₁ q₂ w Q k).1.encode x)) ∧
    (∀ y, Produces (meaning (seedRecursiveCodes n p s q₁ q₂ w Q k).2)
      ((defaultCarrierCodecs n p s q₁ q₂ w Q k).2.encode y)) := by
  obtain ⟨hr, hc⟩ := seedRecursiveCodes_exact (n := n) (p := p) (s := s) (q₁ := q₁)
    (q₂ := q₂) (w := w) (Q := Q) hp hs k
  obtain ⟨fr, fc⟩ := seed_programs_full (n := n) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    hp hs k
  exact ⟨code_full hr fr, code_full hc fc⟩

/-- The level-`k` column meaning, for the sub-code lemmas below. -/
theorem col_exact (hp : 0 < p) (hs : 4 ≤ s) (k : ℕ) :
    meaning (seedRecursiveCodes n p s q₁ q₂ w Q k).2 =
      Program.map (defaultCarrierCodecs n p s q₁ q₂ w Q k).2.encode
        (RecursiveSampling.programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
          (finCongr (Fintype.card_fin n)) hs
          (RecursiveSamplingSeed.seedRow p) (RecursiveSamplingSeed.seedColumn p hp) k).2 :=
  (seedRecursiveCodes_exact (n := n) (p := p) (s := s) (q₁ := q₁)
    (q₂ := q₂) (w := w) (Q := Q) hp hs k).2

theorem row_exact (hp : 0 < p) (hs : 4 ≤ s) (k : ℕ) :
    meaning (seedRecursiveCodes n p s q₁ q₂ w Q k).1 =
      Program.map (defaultCarrierCodecs n p s q₁ q₂ w Q k).1.encode
        (RecursiveSampling.programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
          (finCongr (Fintype.card_fin n)) hs
          (RecursiveSamplingSeed.seedRow p) (RecursiveSamplingSeed.seedColumn p hp) k).1 :=
  (seedRecursiveCodes_exact (n := n) (p := p) (s := s) (q₁ := q₁)
    (q₂ := q₂) (w := w) (Q := Q) hp hs k).1

/-- Sub-codes on the one-level request path from level `k+1` to `k`: the
row entry `E_k = append (ticket w) (taggedCode col_k)`, the tagged column,
the raw column, the outer column, the fixed-tail tuple and the raw row
(`graphRowsCode row_k`). Each produces every encoded value. -/
theorem subcodes_full (hp : 0 < p) (hs : 4 ≤ s) (k : ℕ) :
    let C := defaultCarrierCodecs n p s q₁ q₂ w Q k
    let c := seedRecursiveCodes n p s q₁ q₂ w Q k
    (∀ e, Produces (meaning (.append (.ticket w) (taggedCode q₁ q₂ s c.2)))
      ((prodCodec (finCodec w) (taggedColumnCodec q₁ q₂ s C.2)).encode e)) ∧
    (∀ z, Produces (meaning (taggedCode q₁ q₂ s c.2))
      ((taggedColumnCodec q₁ q₂ s C.2).encode z)) ∧
    (∀ z, Produces (meaning (rawCode q₁ q₂ s c.2))
      ((rawColumnCodec q₁ q₂ s C.2).encode z)) ∧
    (∀ o, Produces (meaning (outerCode q₁ q₂ s c.2))
      ((outerColumnCodec q₁ q₂ s C.2).encode o)) ∧
    (∀ js, Produces (meaning (fixedTailCode q₁ q₂ s c.2))
      ((piCodec (outerColumnCodec q₁ q₂ s C.2) s).encode js)) ∧
    (∀ r, Produces (meaning (graphRowsCode (V := Fin n) q₁ q₂ s c.1))
      ((rawRowCodec q₁ q₂ s C.1 (defaultItemCodec n s)).encode r)) := by
  intro C c
  have hc := col_exact (n := n) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    hp hs k
  have hr := row_exact (n := n) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    hp hs k
  obtain ⟨fr, fc⟩ := seed_programs_full (n := n) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    hp hs k
  have htag := tagged_exact (q₁ := q₁) (q₂ := q₂) (s := s) _ _ _ hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact code_full (ticketProd_exact w _ _ _ htag)
      (full_prod (full_uniform' w) (full_tagged fc))
  · exact code_full htag (full_tagged fc)
  · exact code_full (raw_exact (q₁ := q₁) (q₂ := q₂) (s := s) _ _ _ hc) (full_raw fc)
  · exact code_full (outer_exact (q₁ := q₁) (q₂ := q₂) (s := s) _ _ _ hc) (full_outer fc)
  · exact code_full (fixedTail_exact (q₁ := q₁) (q₂ := q₂) (s := s) _ _ _ hc)
      (full_fixedTail fc)
  · exact code_full (graphRows_canonical_exact (n := n) (q₁ := q₁) (q₂ := q₂) hs _ _ _ hr)
      (full_graphRows _ hs fr)

end Seed

#print axioms full_iid
#print axioms full_tagged
#print axioms full_rows
#print axioms full_graphRows
#print axioms full_programs
#print axioms codes_full
#print axioms subcodes_full

end Paper2.FullSupport
