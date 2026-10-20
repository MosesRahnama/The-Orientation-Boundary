import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import OperatorKO7.Meta.Rewriting.Match
import OperatorKO7.Meta.UniqueNormalization.Coalgebra

/-!
# Finite saturation of the relativized consistency relation

The iteration uses the clauses of `DownStepOn`, without adding transitivity.
There are at most `A.toFinset.card ^ 2` possible pairs, so that many inflationary
iterations suffice. Simultaneous matching of both sides of each rule computes
the root-step table, including rules with new right-hand-side variables.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v w

namespace FiniteSaturation

variable {alpha : Type w} [DecidableEq alpha]

/-- Retain earlier pairs and add one application of the specified operator. -/
def stage (f : Finset alpha → Finset alpha) : Nat → Finset alpha
  | 0 => ∅
  | n + 1 => stage f n ∪ f (stage f n)

theorem stage_subset_succ (f : Finset alpha → Finset alpha) (n : Nat) :
    stage f n ⊆ stage f (n + 1) := Finset.subset_union_left

theorem stage_subset_bound
    (f : Finset alpha → Finset alpha) (B : Finset alpha)
    (hbound : ∀ S, S ⊆ B → f S ⊆ B) (n : Nat) : stage f n ⊆ B := by
  induction n with
  | zero => exact Finset.empty_subset B
  | succ n ih => exact Finset.union_subset ih (hbound _ ih)

/-- Once an iteration adds nothing, every later iteration has the same value. -/
theorem stage_add_eq_of_stable
    {f : Finset alpha → Finset alpha} {n : Nat}
    (h : stage f (n + 1) = stage f n) (k : Nat) :
    stage f (n + k) = stage f n := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, stage, ih]
      exact h

/-- Before stabilization, each iteration increases cardinality. -/
theorem card_stage_ge_of_no_stable
    (f : Finset alpha → Finset alpha) (n : Nat)
    (h : ∀ k, k < n → stage f (k + 1) ≠ stage f k) :
    n ≤ (stage f n).card := by
  revert h
  induction n with
  | zero => intro _; exact Nat.zero_le _
  | succ n ih =>
      intro h
      have hn := ih (fun k hk => h k (by omega))
      have hlt : (stage f n).card < (stage f (n + 1)).card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨stage_subset_succ f n, fun heq => h n (by omega) heq.symm⟩)
      omega

/-- An iteration confined to B stabilizes by iteration `B.card`. No
monotonicity assumption on f is needed for this inflationary iteration. -/
theorem exists_stable_le_card
    (f : Finset alpha → Finset alpha) (B : Finset alpha)
    (hbound : ∀ S, S ⊆ B → f S ⊆ B) :
    ∃ n, n ≤ B.card ∧ stage f (n + 1) = stage f n := by
  classical
  by_contra hnone
  have hstrict : ∀ k, k < B.card + 1 → stage f (k + 1) ≠ stage f k := by
    intro k hk heq
    exact hnone ⟨k, by omega, heq⟩
  have hlarge := card_stage_ge_of_no_stable f (B.card + 1) hstrict
  have hsmall := Finset.card_le_card (stage_subset_bound f B hbound (B.card + 1))
  omega

theorem stable_at_card
    (f : Finset alpha → Finset alpha) (B : Finset alpha)
    (hbound : ∀ S, S ⊆ B → f S ⊆ B) :
    stage f (B.card + 1) = stage f B.card := by
  obtain ⟨n, hn, hstable⟩ := exists_stable_le_card f B hbound
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  rw [hk]
  have hnext : stage f (n + k + 1) = stage f n := by
    simpa [Nat.add_assoc] using stage_add_eq_of_stable hstable (k + 1)
  exact hnext.trans (stage_add_eq_of_stable hstable k).symm

end FiniteSaturation

variable {sigma : Type u} {nu : Type v}

namespace FiniteMatching

/-- Every stored binding agrees with the supplied substitution. -/
def Agrees [DecidableEq nu] (s : Subst sigma nu) (m : PartialMap sigma nu) : Prop :=
  ∀ x t, PartialMap.find? m x = some t → s x = t

theorem matchList_complete_core [DecidableEq sigma] [DecidableEq nu]
    (s : Subst sigma nu) {ls : List (Term sigma nu)}
    (ih : ∀ a ∈ ls, ∀ m, Agrees s m →
      ∃ m', matchAux a (Subst.apply s a) m = some m' ∧ Agrees s m') :
    ∀ m, Agrees s m →
      ∃ m', matchAuxList ls (ls.map (Subst.apply s)) m = some m' ∧ Agrees s m' := by
  induction ls with
  | nil => intro m hm; exact ⟨m, rfl, hm⟩
  | cons a as ihas =>
      intro m hm
      obtain ⟨m1, h1, hm1⟩ := ih a (by simp) m hm
      obtain ⟨m2, h2, hm2⟩ :=
        ihas (fun b hb => ih b (by simp [hb])) m1 hm1
      refine ⟨m2, ?_, hm2⟩
      simp only [List.map_cons, matchAuxList, h1]
      exact h2

/-- Matching succeeds on every actual substitution instance and preserves
agreement with the witness substitution. -/
theorem match_complete_core [DecidableEq sigma] [DecidableEq nu]
    (s : Subst sigma nu) (l : Term sigma nu) :
    ∀ m, Agrees s m →
      ∃ m', matchAux l (Subst.apply s l) m = some m' ∧ Agrees s m' := by
  induction l using Term.rec' with
  | hvar x =>
      intro m hm
      cases hx : PartialMap.find? m x with
      | some t =>
          have ht : t = s x := (hm x t hx).symm
          exact ⟨m, by simp [Subst.apply_var, matchAux, hx, ht], hm⟩
      | none =>
          refine ⟨(x, s x) :: m, by simp [Subst.apply_var, matchAux, hx], ?_⟩
          intro y b hy
          by_cases hxy : x = y
          · subst y
            simpa [PartialMap.find?_cons] using hy
          · exact hm y b (by simpa [PartialMap.find?_cons, hxy] using hy)
  | happ f ls ih =>
      intro m hm
      obtain ⟨m', hmatch, hm'⟩ := matchList_complete_core s ih m hm
      refine ⟨m', ?_, hm'⟩
      simpa only [Subst.apply_app, Subst.applyList_eq_map, matchAux, if_true]
        using hmatch

theorem matchList_complete [DecidableEq sigma] [DecidableEq nu]
    (s : Subst sigma nu) (ls : List (Term sigma nu)) :
    ∃ m, matchAuxList ls (ls.map (Subst.apply s)) [] = some m := by
  obtain ⟨m, hm, _⟩ := matchList_complete_core s
    (fun a _ => match_complete_core s a) []
    (by intro x t h; simp at h)
  exact ⟨m, hm⟩

/-- A shared accumulator enforces one substitution for all patterns. -/
theorem matchList_iff [DecidableEq sigma] [DecidableEq nu]
    (ls ts : List (Term sigma nu)) :
    (∃ m, matchAuxList ls ts [] = some m) ↔
      ∃ s : Subst sigma nu, ls.map (Subst.apply s) = ts := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨PartialMap.toSubst m,
      matchAuxList_sound_core (fun a _ => matchAux_sound_core a) ts [] m hm⟩
  · rintro ⟨s, rfl⟩
    exact matchList_complete s ls

/-- Both rule sides are matched against fixed endpoints using one accumulator. -/
def ruleMatches [DecidableEq sigma] [DecidableEq nu]
    (rule : Rule sigma nu) (a b : Term sigma nu) : Bool :=
  (matchAuxList [rule.lhs, rule.rhs] [a, b] []).isSome

theorem ruleMatches_iff [DecidableEq sigma] [DecidableEq nu]
    (rule : Rule sigma nu) (a b : Term sigma nu) :
    ruleMatches rule a b = true ↔
      ∃ s : Subst sigma nu, a = Subst.apply s rule.lhs ∧
        b = Subst.apply s rule.rhs := by
  have hsome : ruleMatches rule a b = true ↔
      ∃ m, matchAuxList [rule.lhs, rule.rhs] [a, b] [] = some m := by
    unfold ruleMatches
    cases matchAuxList [rule.lhs, rule.rhs] [a, b] [] <;> simp
  rw [hsome, matchList_iff]
  constructor
  · rintro ⟨s, hs⟩
    have hp : Subst.apply s rule.lhs = a ∧ Subst.apply s rule.rhs = b := by
      simpa using hs
    exact ⟨s, hp.1.symm, hp.2.symm⟩
  · rintro ⟨s, ha, hb⟩
    exact ⟨s, by simp [ha, hb]⟩

def rootMatches [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) (a b : Term sigma nu) : Bool :=
  R.any (fun rule => ruleMatches rule a b)

/-- No right-variable containment condition is required. -/
theorem rootMatches_iff [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) (a b : Term sigma nu) :
    rootMatches R a b = true ↔ rootStep R a b := by
  simp only [rootMatches, List.any_eq_true, ruleMatches_iff, rootStep]

def decidableRootStep [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) (a b : Term sigma nu) : Decidable (rootStep R a b) :=
  decidable_of_iff (rootMatches R a b = true) (rootMatches_iff R a b)

end FiniteMatching

namespace FiniteDown

abbrev Pair (sigma : Type u) (nu : Type v) :=
  Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu

/-- Pairs of distinct-list members, with duplicate terms removed. -/
def pairUniverse [DecidableEq sigma] [DecidableEq nu]
    (A : List (Term (sigma ⊕ sigma) nu)) : Finset (Pair sigma nu) :=
  A.toFinset.product A.toFinset

theorem mem_pairUniverse [DecidableEq sigma] [DecidableEq nu]
    {A : List (Term (sigma ⊕ sigma) nu)} {a b : Term (sigma ⊕ sigma) nu} :
    (a, b) ∈ pairUniverse A ↔ a ∈ A ∧ b ∈ A := by
  simp [pairUniverse]

theorem card_pairUniverse [DecidableEq sigma] [DecidableEq nu]
    (A : List (Term (sigma ⊕ sigma) nu)) :
    (pairUniverse A).card = A.toFinset.card ^ 2 := by
  simp [pairUniverse, pow_two]

/-- A semantic iteration layer; the executable version appears below. -/
noncomputable def layer [DecidableEq sigma] [DecidableEq nu]
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (S : Finset (Pair sigma nu)) : Finset (Pair sigma nu) := by
  classical
  exact (pairUniverse A).filter (fun e => DownStepOn A R (fun x y => (x, y) ∈ S) e.1 e.2)

theorem mem_layer [DecidableEq sigma] [DecidableEq nu]
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {S : Finset (Pair sigma nu)} {a b : Term (sigma ⊕ sigma) nu} :
    (a, b) ∈ layer A R S ↔ DownStepOn A R (fun x y => (x, y) ∈ S) a b := by
  classical
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨mem_pairUniverse.mpr ⟨h.1, h.2.1⟩, h⟩

theorem layer_subset [DecidableEq sigma] [DecidableEq nu]
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (S : Finset (Pair sigma nu)) : layer A R S ⊆ pairUniverse A := by
  classical
  exact Finset.filter_subset _ _

/-- Every generated pair is justified by the actual relativized relation. -/
theorem stage_sound [DecidableEq sigma] [DecidableEq nu]
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (n : Nat) {a b : Term (sigma ⊕ sigma) nu}
    (h : (a, b) ∈ FiniteSaturation.stage (layer A R) n) : DownOn A R a b := by
  induction n generalizing a b with
  | zero => exact (Finset.notMem_empty _ h).elim
  | succ n ih =>
      rcases Finset.mem_union.mp h with hold | hnew
      · exact ih hold
      · exact DownOn.closed a b
          (DownStepOn_mono (fun x y hxy => ih hxy) (mem_layer.mp hnew))

/-- The bounded iteration computes all pairs of DownOn. Neither constructor
rules, non-overlap, nor transitivity is assumed. -/
theorem mem_bounded_stage_iff [DecidableEq sigma] [DecidableEq nu]
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (a b : Term (sigma ⊕ sigma) nu) :
    (a, b) ∈ FiniteSaturation.stage (layer A R) (A.toFinset.card ^ 2) ↔
      DownOn A R a b := by
  constructor
  · exact stage_sound _
  · intro hdown
    have hstable :
        FiniteSaturation.stage (layer A R) (A.toFinset.card ^ 2 + 1) =
          FiniteSaturation.stage (layer A R) (A.toFinset.card ^ 2) := by
      simpa only [card_pairUniverse] using
        FiniteSaturation.stable_at_card (layer A R) (pairUniverse A)
          (fun S _ => layer_subset A R S)
    apply DownOn.least (E := fun x y =>
      (x, y) ∈ FiniteSaturation.stage (layer A R) (A.toFinset.card ^ 2)) ?_ hdown
    intro x y hxy
    have hnext : (x, y) ∈
        FiniteSaturation.stage (layer A R) (A.toFinset.card ^ 2 + 1) :=
      Finset.mem_union_right _ (mem_layer.mpr hxy)
    exact hstable ▸ hnext

/-- Decidable equality is unnecessary for the mathematical bound. -/
theorem bounded_saturation
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu) :
    letI := Classical.decEq sigma
    letI := Classical.decEq nu
    ∀ a b, DownOn A R a b ↔
      (a, b) ∈ FiniteSaturation.stage (layer A R) (A.toFinset.card ^ 2) := by
  classical
  intro a b
  exact (mem_bounded_stage_iff A R a b).symm

/-! ## Executable layers from an actual finite root-step table -/

/-- Paired argument membership, evaluated without quantifying over terms. -/
def argsRelated [DecidableEq sigma] [DecidableEq nu]
    (S : Finset (Pair sigma nu)) :
    List (Term (sigma ⊕ sigma) nu) → List (Term (sigma ⊕ sigma) nu) → Bool
  | [], [] => true
  | x :: xs, y :: ys => decide ((x, y) ∈ S) && argsRelated S xs ys
  | _, _ => false

theorem argsRelated_iff [DecidableEq sigma] [DecidableEq nu]
    (S : Finset (Pair sigma nu)) (xs ys : List (Term (sigma ⊕ sigma) nu)) :
    argsRelated S xs ys = true ↔ List.Forall₂ (fun x y => (x, y) ∈ S) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [argsRelated]
  | cons x xs ih => cases ys <;> simp [argsRelated, ih]

/-- One congruence layer over all symbols; variables are handled by reflexivity. -/
def termRelated [DecidableEq sigma] [DecidableEq nu]
    (S : Finset (Pair sigma nu)) :
    Term (sigma ⊕ sigma) nu → Term (sigma ⊕ sigma) nu → Bool
  | .app f xs, .app g ys => decide (f = g) && argsRelated S xs ys
  | _, _ => false

theorem termRelated_iff [DecidableEq sigma] [DecidableEq nu]
    (S : Finset (Pair sigma nu)) (a b : Term (sigma ⊕ sigma) nu) :
    termRelated S a b = true ↔ tildeAll (fun x y => (x, y) ∈ S) a b := by
  cases a <;> cases b <;>
    simp [termRelated, argsRelated_iff, tildeAll, tildeOn]
  all_goals
    intro _
    exact eq_comm

/-- Destructor congruence is the composition clause's restricted first step. -/
def barRelated [DecidableEq sigma] [DecidableEq nu]
    (S : Finset (Pair sigma nu)) (a b : Term (sigma ⊕ sigma) nu) : Bool :=
  match a with
  | .app (.inr _) _ => termRelated S a b
  | _ => false

theorem barRelated_iff [DecidableEq sigma] [DecidableEq nu]
    (S : Finset (Pair sigma nu)) (a b : Term (sigma ⊕ sigma) nu) :
    barRelated S a b = true ↔ barRel (fun x y => (x, y) ∈ S) a b := by
  cases a with
  | var x => simp [barRelated, barRel, tildeOn]
  | app f xs =>
      cases f <;> cases b <;>
        simp [barRelated, termRelated, argsRelated_iff, barRel, tildeOn]
      all_goals
        intro _
        exact eq_comm

/-- The root table must describe the original rewrite relation at every
ordered pair of carrier members. Entries outside A are irrelevant. -/
def RootTableExact [DecidableEq sigma] [DecidableEq nu]
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (roots : Finset (Pair sigma nu)) : Prop :=
  ∀ a b, a ∈ A → b ∈ A → ((a, b) ∈ roots ↔ rootStep R a b)

/-- A finite evaluation of the operator body, without endpoint membership. -/
def oneStep [DecidableEq sigma] [DecidableEq nu]
    (A : List (Term (sigma ⊕ sigma) nu)) (roots S : Finset (Pair sigma nu))
    (a b : Term (sigma ⊕ sigma) nu) : Bool :=
  decide (a = b) || (decide ((b, a) ∈ S) ||
    (A.any (fun c => decide ((a, c) ∈ roots) && decide ((c, b) ∈ S)) ||
    (A.any (fun c => barRelated S a c && decide ((c, b) ∈ S)) ||
    termRelated S a b)))

theorem oneStep_iff [DecidableEq sigma] [DecidableEq nu]
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {roots : Finset (Pair sigma nu)} (hroots : RootTableExact A R roots)
    (S : Finset (Pair sigma nu)) {a b : Term (sigma ⊕ sigma) nu}
    (ha : a ∈ A) (hb : b ∈ A) :
    oneStep A roots S a b = true ↔
      DownStepOn A R (fun x y => (x, y) ∈ S) a b := by
  have hlogic : oneStep A roots S a b = true ↔
      (a = b ∨ (b, a) ∈ S ∨
        (∃ c ∈ A, (a, c) ∈ roots ∧ (c, b) ∈ S) ∨
        (∃ c ∈ A, barRel (fun x y => (x, y) ∈ S) a c ∧ (c, b) ∈ S) ∨
        tildeAll (fun x y => (x, y) ∈ S) a b) := by
    simp only [oneStep, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, List.any_eq_true, barRelated_iff, termRelated_iff]
  rw [hlogic]
  constructor
  · intro h
    refine ⟨ha, hb, ?_⟩
    rcases h with heq | hinv | ⟨c, hc, hr, htail⟩ | ⟨c, hc, hbar, htail⟩ | htilde
    · exact Or.inl heq
    · exact Or.inr (Or.inl hinv)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, (hroots a c ha hc).mp hr, htail⟩))
    · obtain ⟨f, xs, ys, ⟨d, hfd⟩, hax, hcy, hargs⟩ := hbar
      subst f
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨d, xs, ys, hax, hargs, hcy ▸ hc, hcy ▸ htail⟩)))
    · obtain ⟨f, xs, ys, _, hax, hby, hargs⟩ := htilde
      cases f with
      | inl c => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨.inl c, xs, ys, ⟨c, rfl⟩, hax, hby, hargs⟩))))
      | inr d => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨.inr d, xs, ys, ⟨d, rfl⟩, hax, hby, hargs⟩))))
  · rintro ⟨_, _, h⟩
    rcases h with heq | hinv | ⟨c, hc, hr, htail⟩ |
        ⟨d, xs, ys, hax, hargs, hc, htail⟩ | hhat | hbar
    · exact Or.inl heq
    · exact Or.inr (Or.inl hinv)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, (hroots a c ha hc).mpr hr, htail⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨.app (.inr d) ys, hc,
          ⟨.inr d, xs, ys, ⟨d, rfl⟩, hax, rfl, hargs⟩, htail⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (tildeOn_mono_pred (fun _ _ => True.intro) hhat))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (tildeOn_mono_pred (fun _ _ => True.intro) hbar))))

/-- Executable one-layer table; every output pair belongs to A. -/
def tableLayer [DecidableEq sigma] [DecidableEq nu]
    (A : List (Term (sigma ⊕ sigma) nu)) (roots S : Finset (Pair sigma nu)) :
    Finset (Pair sigma nu) :=
  (pairUniverse A).filter (fun e => oneStep A roots S e.1 e.2 = true)

theorem tableLayer_eq_layer [DecidableEq sigma] [DecidableEq nu]
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {roots : Finset (Pair sigma nu)} (hroots : RootTableExact A R roots)
    (S : Finset (Pair sigma nu)) : tableLayer A roots S = layer A R S := by
  classical
  apply Finset.ext
  rintro ⟨a, b⟩
  rw [mem_layer]
  constructor
  · intro h
    obtain ⟨hmem, hstep⟩ := Finset.mem_filter.mp h
    obtain ⟨ha, hb⟩ := mem_pairUniverse.mp hmem
    exact (oneStep_iff hroots S ha hb).mp hstep
  · intro h
    exact Finset.mem_filter.mpr ⟨mem_pairUniverse.mpr ⟨h.1, h.2.1⟩,
      (oneStep_iff hroots S h.1 h.2.1).mpr h⟩

/-- Execute the fixed number of iterations; there is no search termination
premise and no transitive-closure operation. -/
def compute [DecidableEq sigma] [DecidableEq nu]
    (A : List (Term (sigma ⊕ sigma) nu)) (roots : Finset (Pair sigma nu)) :
    Finset (Pair sigma nu) :=
  FiniteSaturation.stage (tableLayer A roots) (A.toFinset.card ^ 2)

theorem mem_compute_iff [DecidableEq sigma] [DecidableEq nu]
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {roots : Finset (Pair sigma nu)} (hroots : RootTableExact A R roots)
    (a b : Term (sigma ⊕ sigma) nu) :
    (a, b) ∈ compute A roots ↔ DownOn A R a b := by
  have hf : tableLayer A roots = layer A R :=
    funext (tableLayer_eq_layer hroots)
  unfold compute
  rw [hf]
  exact mem_bounded_stage_iff A R a b

/-- Decidability is obtained from the computed table, not classical choice. -/
def decidableDownOn [DecidableEq sigma] [DecidableEq nu]
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {roots : Finset (Pair sigma nu)} (hroots : RootTableExact A R roots)
    (a b : Term (sigma ⊕ sigma) nu) : Decidable (DownOn A R a b) :=
  decidable_of_iff ((a, b) ∈ compute A roots) (mem_compute_iff hroots a b)

/-- Compute the exact root table from the actual finite rewrite system. -/
def rootTable [DecidableEq sigma] [DecidableEq nu]
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu) :
    Finset (Pair sigma nu) :=
  (pairUniverse A).filter (fun e => FiniteMatching.rootMatches R e.1 e.2 = true)

theorem rootTable_exact [DecidableEq sigma] [DecidableEq nu]
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu) :
    RootTableExact A R (rootTable A R) := by
  intro a b ha hb
  simp [rootTable, mem_pairUniverse, ha, hb, FiniteMatching.rootMatches_iff]

/-- Compute DownOn directly from the carrier and rules; no table certificate
is an input. -/
def computeTRS [DecidableEq sigma] [DecidableEq nu]
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu) :
    Finset (Pair sigma nu) := compute A (rootTable A R)

theorem mem_computeTRS_iff [DecidableEq sigma] [DecidableEq nu]
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (a b : Term (sigma ⊕ sigma) nu) :
    (a, b) ∈ computeTRS A R ↔ DownOn A R a b :=
  mem_compute_iff (rootTable_exact A R) a b

/-- Finite-carrier Down membership is decidable for every finite rewrite system. -/
def decidableDownOnTRS [DecidableEq sigma] [DecidableEq nu]
    (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu)
    (a b : Term (sigma ⊕ sigma) nu) : Decidable (DownOn A R a b) :=
  decidable_of_iff ((a, b) ∈ computeTRS A R) (mem_computeTRS_iff A R a b)

end FiniteDown

end OperatorKO7.Meta.UniqueNormalization
