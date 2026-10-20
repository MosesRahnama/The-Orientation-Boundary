import OperatorKO7.Meta.Methods.OrientationClosure.DependencyPairSoundness
import Mathlib.Logic.Hydra
import Mathlib.Tactic

/-!
# Sorted and context-sensitive method rows

Four rows of the method universe, each stated in the method's own language for the free recursor
`freeRecursorTRS`.

Section 1 is a generic core: rewriting restricted to admitted substitutions and to active argument
positions, its minimal dependency chains, the chain soundness theorem, and the subterm criterion.
Context-sensitive rewriting (Section 2) and order-sorted rewriting (Section 5) are instances.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness

universe u v w

/-! ## 1. Restricted rewriting and its minimal chains -/

section ListSteps

variable {α : Type w}

/-- One `r`-step at one position of a list whose index satisfies `P`. -/
def PStep (r : α → α → Prop) (P : Nat → Prop) (xs ys : List α) : Prop :=
  ∃ pre post : List α, ∃ a b : α,
    xs = pre ++ a :: post ∧ ys = pre ++ b :: post ∧ P pre.length ∧ r a b

theorem not_pstep_nil (r : α → α → Prop) (P : Nat → Prop) (ys : List α) : ¬ PStep r P [] ys := by
  rintro ⟨pre, post, a, b, h, -, -, -⟩
  cases pre <;> simp at h

theorem pstep_cons_iff (r : α → α → Prop) (P : Nat → Prop) (a : α) (rest ys : List α) :
    PStep r P (a :: rest) ys ↔
      (P 0 ∧ ∃ b, r a b ∧ ys = b :: rest) ∨
        (∃ rest', PStep r (fun i => P (i + 1)) rest rest' ∧ ys = a :: rest') := by
  constructor
  · rintro ⟨pre, post, x, y, hxs, hys, hP, hr⟩
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hxs hys
      obtain ⟨rfl, rfl⟩ := hxs
      exact Or.inl ⟨hP, y, hr, hys⟩
    | cons p pre' =>
      simp only [List.cons_append, List.cons.injEq] at hxs hys
      obtain ⟨rfl, rfl⟩ := hxs
      exact Or.inr ⟨pre' ++ y :: post, ⟨pre', post, x, y, rfl, rfl, hP, hr⟩, hys⟩
  · rintro (⟨hP, b, hab, rfl⟩ | ⟨rest', ⟨pre, post, x, y, rfl, rfl, hP, hr⟩, rfl⟩)
    · exact ⟨[], rest, a, b, rfl, rfl, hP, hab⟩
    · exact ⟨a :: pre, post, x, y, rfl, rfl, hP, hr⟩

theorem acc_pstep_cons {r : α → α → Prop} (P : Nat → Prop) (a : α)
    (ha : P 0 → Acc (fun y x => r x y) a) :
    ∀ rest : List α, Acc (fun ys xs => PStep r (fun i => P (i + 1)) xs ys) rest →
      Acc (fun ys xs => PStep r P xs ys) (a :: rest) := by
  by_cases hP : P 0
  · have hacc := ha hP
    clear ha
    induction hacc with
    | intro a _ iha =>
      intro rest hr
      induction hr with
      | intro rest hr' ihr =>
        refine Acc.intro _ fun ys hys => ?_
        rcases (pstep_cons_iff r P a rest ys).1 hys with ⟨-, b, hab, rfl⟩ | ⟨rest', hrr, rfl⟩
        · exact iha b hab rest (Acc.intro rest hr')
        · exact ihr rest' hrr
  · intro rest hr
    induction hr with
    | intro rest _ ihr =>
      refine Acc.intro _ fun ys hys => ?_
      rcases (pstep_cons_iff r P a rest ys).1 hys with ⟨hP0, -⟩ | ⟨rest', hrr, rfl⟩
      · exact absurd hP0 hP
      · exact ihr rest' hrr

/-- Strongly normalizing elements at the admitted positions make list steps well founded. -/
theorem acc_pstep {r : α → α → Prop} :
    ∀ (xs : List α) (P : Nat → Prop), (∀ i a, xs[i]? = some a → P i → Acc (fun y x => r x y) a) →
      Acc (fun ys xs => PStep r P xs ys) xs
  | [], _, _ => Acc.intro _ fun ys h => absurd h (not_pstep_nil r _ ys)
  | a :: rest, P, h =>
    acc_pstep_cons P a (fun hP => h 0 a (by simp) hP) rest
      (acc_pstep rest (fun i => P (i + 1)) fun i b hb hP =>
        h (i + 1) b (by rw [List.getElem?_cons_succ]; exact hb) hP)

theorem getElem?_mid (pre post : List α) (a : α) : (pre ++ a :: post)[pre.length]? = some a := by
  rw [List.getElem?_append_right (le_refl _), Nat.sub_self, List.getElem?_cons_zero]

theorem getElem?_mid_ne (pre post : List α) (a b : α) {i : Nat} (hi : i ≠ pre.length) :
    (pre ++ b :: post)[i]? = (pre ++ a :: post)[i]? := by
  rcases lt_or_gt_of_ne hi with hi | hi
  · rw [List.getElem?_append_left hi, List.getElem?_append_left hi]
  · rw [List.getElem?_append_right hi.le, List.getElem?_append_right hi.le]
    obtain ⟨k, hk⟩ : ∃ k, i - pre.length = k + 1 := ⟨i - pre.length - 1, by omega⟩
    rw [hk, List.getElem?_cons_succ, List.getElem?_cons_succ]

theorem split_of_getElem? {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    ∃ pre post, l = pre ++ a :: post ∧ pre.length = i := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨[], xs, rfl, rfl⟩
    | succ k =>
      rw [List.getElem?_cons_succ] at h
      obtain ⟨pre, post, rfl, hk⟩ := ih h
      exact ⟨x :: pre, post, rfl, by simp [hk]⟩

/-- A list step keeps a positionwise property that the element steps keep. -/
theorem pstep_preserve {r : α → α → Prop} {P : Nat → Prop} {Q : Nat → α → Prop}
    (hQ : ∀ i a b, P i → Q i a → r a b → Q i b) {xs ys : List α} (h : PStep r P xs ys)
    (hxs : ∀ i a, xs[i]? = some a → Q i a) : ∀ i a, ys[i]? = some a → Q i a := by
  obtain ⟨pre, post, a0, b0, rfl, rfl, hP, hr⟩ := h
  intro i c hc
  by_cases hi : i = pre.length
  · subst hi
    rw [getElem?_mid] at hc
    cases hc
    exact hQ _ a0 _ hP (hxs _ a0 (getElem?_mid pre post a0)) hr
  · rw [getElem?_mid_ne pre post a0 b0 hi] at hc
    exact hxs i c hc

/-- Position `i` after a list step comes from position `i` before it by at most one step. -/
theorem pstep_getElem? {r : α → α → Prop} {P : Nat → Prop} {xs ys : List α}
    (h : PStep r P xs ys) (i : Nat) (y : α) (hy : ys[i]? = some y) :
    ∃ x, xs[i]? = some x ∧ Relation.ReflTransGen r x y := by
  obtain ⟨pre, post, a, b, rfl, rfl, -, hab⟩ := h
  by_cases hi : i = pre.length
  · subst hi
    rw [getElem?_mid] at hy
    cases hy
    exact ⟨a, getElem?_mid pre post a, .single hab⟩
  · rw [getElem?_mid_ne pre post a b hi] at hy
    exact ⟨y, hy, .refl⟩

theorem psteps_getElem? {r : α → α → Prop} {P : Nat → Prop} {xs ys : List α}
    (h : Relation.ReflTransGen (PStep r P) xs ys) (i : Nat) :
    ∀ y, ys[i]? = some y → ∃ x, xs[i]? = some x ∧ Relation.ReflTransGen r x y := by
  induction h with
  | refl => exact fun y hy => ⟨y, hy, .refl⟩
  | tail _ hstep ih =>
    intro y hy
    obtain ⟨m, hm, hmy⟩ := pstep_getElem? hstep i y hy
    obtain ⟨x, hx, hxm⟩ := ih m hm
    exact ⟨x, hx, hxm.trans hmy⟩

end ListSteps

section Restricted

variable {sigma : Type u} {nu : Type v}

/-- A root step of `R` whose matching substitution is admitted by `ok`. -/
def RRoot (R : TRS sigma nu) (ok : Subst sigma nu → Prop) (s t : Term sigma nu) : Prop :=
  ∃ rule ∈ R, ∃ σ : Subst sigma nu, ok σ ∧ s = Subst.apply σ rule.lhs ∧
    t = Subst.apply σ rule.rhs

/-- Rewriting with admitted substitutions, below the root only at active argument positions. -/
inductive RStep (R : TRS sigma nu) (ok : Subst sigma nu → Prop) (act : sigma → Nat → Prop) :
    Term sigma nu → Term sigma nu → Prop
  | root {s t : Term sigma nu} (h : RRoot R ok s t) : RStep R ok act s t
  | arg (f : sigma) (pre post : List (Term sigma nu)) {a b : Term sigma nu}
      (hact : act f pre.length) (h : RStep R ok act a b) :
      RStep R ok act (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post))

/-- Strong normalization for the restricted relation. -/
abbrev RSN (R : TRS sigma nu) (ok : Subst sigma nu → Prop) (act : sigma → Nat → Prop)
    (t : Term sigma nu) : Prop :=
  Acc (fun u t => RStep R ok act t u) t

/-- Restricted steps in the active argument positions of `f`. -/
abbrev RArgStep (R : TRS sigma nu) (ok : Subst sigma nu → Prop) (act : sigma → Nat → Prop)
    (f : sigma) : List (Term sigma nu) → List (Term sigma nu) → Prop :=
  PStep (RStep R ok act) (act f)

/-- The active arguments of `f` in `xs` are strongly normalizing. -/
def ActArgsSN (R : TRS sigma nu) (ok : Subst sigma nu → Prop) (act : sigma → Nat → Prop)
    (f : sigma) (xs : List (Term sigma nu)) : Prop :=
  ∀ i a, xs[i]? = some a → act f i → RSN R ok act a

/-- `w` occurs in `t` at a position reached through active argument positions only. -/
inductive ActSub (act : sigma → Nat → Prop) : Term sigma nu → Term sigma nu → Prop
  | refl (t : Term sigma nu) : ActSub act t t
  | arg {w a : Term sigma nu} (f : sigma) (args : List (Term sigma nu)) (i : Nat)
      (hi : args[i]? = some a) (hact : act f i) (h : ActSub act w a) : ActSub act w (.app f args)

/-- `w` occurs strictly below the root of `t` through active positions. -/
def ProperActSub (act : sigma → Nat → Prop) (w t : Term sigma nu) : Prop :=
  ∃ f args i a, t = .app f args ∧ args[i]? = some a ∧ act f i ∧ ActSub act w a

/-- No variable moves from an inactive left-hand-side position to an active right-hand-side
position. -/
def Conservative (R : TRS sigma nu) (act : sigma → Nat → Prop) : Prop :=
  ∀ rule ∈ R, ∀ x : nu, ActSub act (.var x) rule.rhs → ActSub act (.var x) rule.lhs

/-- A minimal chain step between calls; `W` admits calls. -/
def RChainStep (R : TRS sigma nu) (ok : Subst sigma nu → Prop) (act : sigma → Nat → Prop)
    (W : sigma × List (Term sigma nu) → Prop) (c d : sigma × List (Term sigma nu)) : Prop :=
  W c ∧ ActArgsSN R ok act c.1 c.2 ∧ W d ∧ ActArgsSN R ok act d.1 d.2 ∧
    ∃ args', Relation.ReflTransGen (RArgStep R ok act c.1) c.2 args' ∧
      ∃ rule ∈ R, ∃ σ : Subst sigma nu, ok σ ∧ Term.app c.1 args' = Subst.apply σ rule.lhs ∧
        ∃ targs, ActSub act (Term.app d.1 targs) rule.rhs ∧ IsDefined R d.1 ∧
          d.2 = Subst.applyList σ targs

/-- `u` is an active argument of `t`, or a restricted reduct of `t`. -/
def RStepOrSub (R : TRS sigma nu) (ok : Subst sigma nu → Prop) (act : sigma → Nat → Prop)
    (u t : Term sigma nu) : Prop :=
  RStep R ok act t u ∨ ∃ f args i, t = .app f args ∧ args[i]? = some u ∧ act f i

/-- A pair instance between admitted calls. -/
def RPairInst (R : TRS sigma nu) (ok : Subst sigma nu → Prop) (act : sigma → Nat → Prop)
    (W : sigma × List (Term sigma nu) → Prop) (c d : sigma × List (Term sigma nu)) : Prop :=
  W c ∧ W d ∧ ∃ rule ∈ R, ∃ σ : Subst sigma nu, ok σ ∧ ∃ largs, rule.lhs = .app c.1 largs ∧
    c.2 = Subst.applyList σ largs ∧ ∃ targs, ActSub act (.app d.1 targs) rule.rhs ∧
      IsDefined R d.1 ∧ d.2 = Subst.applyList σ targs

/-- The subterm criterion with a projection to active positions: the projected argument of every
admitted pair instance strictly decreases in the active subterm order. -/
def RSubtermCriterion (R : TRS sigma nu) (ok : Subst sigma nu → Prop) (act : sigma → Nat → Prop)
    (W : sigma × List (Term sigma nu) → Prop) (proj : sigma → Nat) : Prop :=
  (∀ f, IsDefined R f → act f (proj f)) ∧
    ∀ c d, RPairInst R ok act W c d →
      ∃ x y, c.2[proj c.1]? = some x ∧ d.2[proj d.1]? = some y ∧ ProperActSub act y x

variable {R : TRS sigma nu} {ok : Subst sigma nu → Prop} {act : sigma → Nat → Prop}

theorem rstep_app_iff (f : sigma) (args : List (Term sigma nu)) (u : Term sigma nu) :
    RStep R ok act (.app f args) u ↔
      RRoot R ok (.app f args) u ∨ ∃ args', RArgStep R ok act f args args' ∧ u = .app f args' := by
  constructor
  · intro h
    cases h with
    | root h => exact Or.inl h
    | arg g pre post hact hab => exact Or.inr ⟨_, ⟨pre, post, _, _, rfl, rfl, hact, hab⟩, rfl⟩
  · rintro (h | ⟨args', ⟨pre, post, a, b, rfl, rfl, hact, hab⟩, rfl⟩)
    · exact RStep.root h
    · exact RStep.arg f pre post hact hab

theorem not_rstep_var (x : nu) (u : Term sigma nu) : ¬ RStep R ok act (.var x) u := by
  intro h
  cases h with
  | root h =>
    obtain ⟨rule, -, σ, -, hl, -⟩ := h
    obtain ⟨g, largs, hg⟩ := lhs_eq_app rule
    rw [hg, Subst.apply_app] at hl
    exact Term.noConfusion hl

theorem not_rroot_of_not_defined {f : sigma} (hf : ¬ IsDefined R f) (args : List (Term sigma nu))
    (u : Term sigma nu) : ¬ RRoot R ok (.app f args) u := by
  rintro ⟨rule, hrule, σ, -, hl, -⟩
  obtain ⟨g, largs, hg⟩ := lhs_eq_app rule
  rw [hg, Subst.apply_app] at hl
  simp only [Term.app.injEq] at hl
  exact hf ⟨rule, hrule, largs, by rw [hg, hl.1]⟩

theorem actArgsSN_step {f : sigma} {xs ys : List (Term sigma nu)}
    (hxs : ActArgsSN R ok act f xs) (h : RArgStep R ok act f xs ys) : ActArgsSN R ok act f ys :=
  pstep_preserve (Q := fun i a => act f i → RSN R ok act a)
    (fun _ _ _ _ hQ hr hi => (hQ hi).inv hr) h hxs

/-- An application with an undefined root and strongly normalizing active arguments is strongly
normalizing. -/
theorem rsn_app_of_not_defined {f : sigma} (hf : ¬ IsDefined R f) :
    ∀ args, ActArgsSN R ok act f args → RSN R ok act (.app f args) := by
  intro args hargs
  have hacc : Acc (fun ys xs => RArgStep R ok act f xs ys) args :=
    acc_pstep args (act f) (fun i a hi hact => hargs i a hi hact)
  induction hacc with
  | intro xs _ ih =>
    refine Acc.intro _ fun u hu => ?_
    rcases (rstep_app_iff f xs u).1 hu with hroot | ⟨ys, hys, rfl⟩
    · exact absurd hroot (not_rroot_of_not_defined hf xs u)
    · exact ih ys hys (actArgsSN_step hargs hys)

theorem actSub_lift {w t : Term sigma nu} (h : ActSub act w t) :
    ∀ {w'}, RStep R ok act w w' → ∃ t', RStep R ok act t t' ∧ ActSub act w' t' := by
  induction h with
  | refl => intro w' hw; exact ⟨w', hw, .refl w'⟩
  | arg f args i hi hact _ ih =>
    intro w' hw
    obtain ⟨a', ha', hsub⟩ := ih hw
    obtain ⟨pre, post, rfl, rfl⟩ := split_of_getElem? hi
    exact ⟨.app f (pre ++ a' :: post), RStep.arg f pre post hact ha',
      .arg f _ pre.length (getElem?_mid pre post a') hact hsub⟩

/-- Active subterms of strongly normalizing terms are strongly normalizing. -/
theorem rsn_of_actSub {w t : Term sigma nu} (h : ActSub act w t) (ht : RSN R ok act t) :
    RSN R ok act w := by
  induction ht generalizing w with
  | intro t _ ih =>
    exact Acc.intro w fun w' hw' => by
      obtain ⟨t', ht', hs⟩ := actSub_lift (R := R) (ok := ok) h hw'
      exact ih t' ht' hs

theorem ActSub.trans {w a t : Term sigma nu} (h1 : ActSub act w a) (h2 : ActSub act a t) :
    ActSub act w t := by
  induction h2 with
  | refl => exact h1
  | arg f args i hi hact _ ih => exact .arg f args i hi hact ih

theorem actSub_var_iff {w : Term sigma nu} {x : nu} : ActSub act w (.var x) ↔ w = .var x := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .refl _

theorem actSub_app_iff {w : Term sigma nu} {f : sigma} {args : List (Term sigma nu)} :
    ActSub act w (.app f args) ↔
      w = .app f args ∨ ∃ i a, args[i]? = some a ∧ act f i ∧ ActSub act w a := by
  constructor
  · intro h
    cases h with
    | refl => exact Or.inl rfl
    | arg f args i hi hact h => exact Or.inr ⟨i, _, hi, hact, h⟩
  · rintro (rfl | ⟨i, a, hi, hact, h⟩)
    · exact .refl _
    · exact .arg f args i hi hact h

theorem not_rstep_const {f : sigma} (hf : ¬ IsDefined R f) (u : Term sigma nu) :
    ¬ RStep R ok act (.app f []) u := by
  intro h
  rcases (rstep_app_iff f [] u).1 h with hroot | ⟨ys, hys, -⟩
  · exact not_rroot_of_not_defined hf [] u hroot
  · exact not_pstep_nil _ _ ys hys

theorem not_acc_of_cycle {α : Type w} {r : α → α → Prop} {x y : α} (h1 : r y x) (h2 : r x y) :
    ¬ Acc r x := by
  intro hx
  induction hx generalizing y with
  | intro x _ ih => exact ih y h1 h2 h1

theorem ActSub.subst (σ : Subst sigma nu) {w t : Term sigma nu} (h : ActSub act w t) :
    ActSub act (Subst.apply σ w) (Subst.apply σ t) := by
  induction h with
  | refl => exact .refl _
  | arg f args i hi hact _ ih =>
    rw [Subst.apply_app]
    exact .arg f _ i (by rw [Subst.applyList_eq_map, List.getElem?_map, hi]; rfl) hact ih

theorem ActSub.of_app {w : Term sigma nu} {g : sigma} {largs : List (Term sigma nu)}
    (h : ActSub act w (.app g largs)) (hw : w ≠ .app g largs) :
    ∃ i a, largs[i]? = some a ∧ act g i ∧ ActSub act w a := by
  cases h with
  | refl => exact absurd rfl hw
  | arg f args i hi hact h => exact ⟨i, _, hi, hact, h⟩

/-- The chain theorem for restricted rewriting: a call accessible for the minimal chain relation,
with strongly normalizing active arguments, gives strongly normalizing applications after any
active argument rewriting. -/
theorem rsn_of_rchain_acc {W : sigma × List (Term sigma nu) → Prop}
    (hcons : Conservative R act)
    (hW : ∀ rule ∈ R, ∀ σ : Subst sigma nu, ok σ → ∀ (g : sigma) (targs : List (Term sigma nu)),
      ActSub act (.app g targs) rule.rhs → IsDefined R g → W (g, Subst.applyList σ targs)) :
    ∀ c : sigma × List (Term sigma nu), Acc (fun d c => RChainStep R ok act W c d) c → W c →
      ActArgsSN R ok act c.1 c.2 → ∀ xs, Relation.ReflTransGen (RArgStep R ok act c.1) c.2 xs →
        ActArgsSN R ok act c.1 xs → RSN R ok act (.app c.1 xs) := by
  intro c hc
  induction hc with
  | intro c _ ihc =>
    intro hWc hcSN xs hreach hxs
    have hacc : Acc (fun ys xs => RArgStep R ok act c.1 xs ys) xs :=
      acc_pstep xs (act c.1) (fun i a hi hact => hxs i a hi hact)
    induction hacc with
    | intro xs _ ihx =>
      refine Acc.intro _ fun u hu => ?_
      rcases (rstep_app_iff c.1 xs u).1 hu with hroot | ⟨ys, hys, rfl⟩
      · obtain ⟨rule, hrule, σ, hσ, hl, rfl⟩ := hroot
        obtain ⟨g0, largs, hg0⟩ := lhs_eq_app rule
        have hl' := hl
        rw [hg0, Subst.apply_app] at hl'
        simp only [Term.app.injEq] at hl'
        obtain ⟨hc1, hxsEq⟩ := hl'
        have hvar : ∀ x : nu, ActSub act (.var x) rule.rhs → RSN R ok act (σ x) := by
          intro x hx
          have hxl := hcons rule hrule x hx
          rw [hg0] at hxl
          obtain ⟨i, a, ha, hact, hsub⟩ := hxl.of_app (fun h => Term.noConfusion h)
          have hxi : xs[i]? = some (Subst.apply σ a) := by
            rw [hxsEq, Subst.applyList_eq_map, List.getElem?_map, ha]; rfl
          have hsn := hxs i _ hxi (by rw [hc1]; exact hact)
          have := rsn_of_actSub (hsub.subst σ) hsn
          simpa using this
        have key : ∀ w, ActSub act w rule.rhs → RSN R ok act (Subst.apply σ w) := by
          intro w
          induction w using Term.rec' with
          | hvar x => intro hw; simpa using hvar x hw
          | happ g targs ih =>
            intro hw
            have hargs : ActArgsSN R ok act g (Subst.applyList σ targs) := by
              intro i a hi hact
              rw [Subst.applyList_eq_map, List.getElem?_map, Option.map_eq_some_iff] at hi
              obtain ⟨t, ht, rfl⟩ := hi
              exact ih t (List.mem_of_getElem? ht)
                (ActSub.trans (.arg g targs i ht hact (.refl t)) hw)
            rw [Subst.apply_app]
            by_cases hg : IsDefined R g
            · have hWd := hW rule hrule σ hσ g targs hw hg
              have hstep : RChainStep R ok act W c (g, Subst.applyList σ targs) :=
                ⟨hWc, hcSN, hWd, hargs, xs, hreach, rule, hrule, σ, hσ, hl, targs, hw, hg, rfl⟩
              exact ihc _ hstep hWd hargs _ Relation.ReflTransGen.refl hargs
            · exact rsn_app_of_not_defined hg _ hargs
        exact key rule.rhs (.refl _)
      · exact ihx ys hys (hreach.tail hys) (actArgsSN_step hxs hys)

/-- Chain soundness: a well-founded minimal chain relation gives strong normalization of every
admitted term. -/
theorem rsn_of_rchain_wf {W : sigma × List (Term sigma nu) → Prop}
    (hcons : Conservative R act)
    (hW : ∀ rule ∈ R, ∀ σ : Subst sigma nu, ok σ → ∀ (g : sigma) (targs : List (Term sigma nu)),
      ActSub act (.app g targs) rule.rhs → IsDefined R g → W (g, Subst.applyList σ targs))
    (Tok : Term sigma nu → Prop)
    (hTok : ∀ f args, Tok (.app f args) → W (f, args) ∧ ∀ a ∈ args, Tok a)
    (hwf : WellFounded (fun d c => RChainStep R ok act W c d)) :
    ∀ t, Tok t → RSN R ok act t := by
  intro t
  induction t using Term.rec' with
  | hvar x => intro _; exact Acc.intro _ fun u h => absurd h (not_rstep_var x u)
  | happ f args ih =>
    intro ht
    obtain ⟨hWt, hargs⟩ := hTok f args ht
    have hsn : ActArgsSN R ok act f args := fun i a hi _ =>
      ih a (List.mem_of_getElem? hi) (hargs a (List.mem_of_getElem? hi))
    exact rsn_of_rchain_acc hcons hW (f, args) (hwf.apply _) hWt hsn args
      Relation.ReflTransGen.refl hsn

theorem acc_rStepOrSub_of_actSub :
    ∀ t : Term sigma nu, RSN R ok act t → ∀ u, ActSub act u t → Acc (RStepOrSub R ok act) u := by
  intro t ht
  induction ht with
  | intro t _ iht =>
    suffices key : ∀ n, ∀ u, Term.size u ≤ n → ActSub act u t → Acc (RStepOrSub R ok act) u from
      fun u hu => key _ u le_rfl hu
    intro n
    induction n with
    | zero => intro u hsz; exact absurd hsz (by have := Term.one_le_size u; omega)
    | succ n ihn =>
      intro u hsz hu
      refine Acc.intro _ fun v hv => ?_
      rcases hv with hstep | ⟨f, args, i, rfl, hi, hact⟩
      · obtain ⟨t', htt', hsub⟩ := actSub_lift hu hstep
        exact iht t' htt' v hsub
      · have hlt := Term.size_lt_of_mem (f := f) (List.mem_of_getElem? hi)
        exact ihn v (by omega) (ActSub.trans (.arg f args i hi hact (.refl v)) hu)

theorem ActSub.reflTransGen {w t : Term sigma nu} (h : ActSub act w t) :
    Relation.ReflTransGen (RStepOrSub R ok act) w t := by
  induction h with
  | refl => exact .refl
  | arg f args i hi hact _ ih => exact ih.tail (Or.inr ⟨f, args, i, rfl, hi, hact⟩)

theorem ProperActSub.transGen {w t : Term sigma nu} (h : ProperActSub act w t) :
    Relation.TransGen (RStepOrSub R ok act) w t := by
  obtain ⟨f, args, i, a, rfl, hi, hact, hsub⟩ := h
  exact Relation.TransGen.tail' (ActSub.reflTransGen hsub) (Or.inr ⟨f, args, i, rfl, hi, hact⟩)

theorem ProperActSub.subst (σ : Subst sigma nu) {w t : Term sigma nu} (h : ProperActSub act w t) :
    ProperActSub act (Subst.apply σ w) (Subst.apply σ t) := by
  obtain ⟨f, args, i, a, rfl, hi, hact, hsub⟩ := h
  refine ⟨f, Subst.applyList σ args, i, Subst.apply σ a, by rw [Subst.apply_app], ?_, hact,
    hsub.subst σ⟩
  rw [Subst.applyList_eq_map, List.getElem?_map, hi]; rfl

theorem rsteps_reflTransGen {x y : Term sigma nu}
    (h : Relation.ReflTransGen (RStep R ok act) x y) :
    Relation.ReflTransGen (RStepOrSub R ok act) y x := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact Relation.ReflTransGen.head (Or.inl hst) ih

theorem rchainStep_proj {W : sigma × List (Term sigma nu) → Prop}
    (hWred : ∀ c xs, W c → Relation.ReflTransGen (RArgStep R ok act c.1) c.2 xs → W (c.1, xs))
    {proj : sigma → Nat} (hsc : RSubtermCriterion R ok act W proj)
    {c d : sigma × List (Term sigma nu)} (h : RChainStep R ok act W c d) :
    ∃ x y, c.2[proj c.1]? = some x ∧ d.2[proj d.1]? = some y ∧
      Relation.TransGen (RStepOrSub R ok act) y x := by
  obtain ⟨hWc, -, hWd, -, xs, hreach, rule, hrule, σ, hσ, hl, targs, hsub, hdef, hd⟩ := h
  obtain ⟨g0, largs, hg0⟩ := lhs_eq_app rule
  have hl' := hl
  rw [hg0, Subst.apply_app] at hl'
  simp only [Term.app.injEq] at hl'
  obtain ⟨hf, hxsEq⟩ := hl'
  have hlhs : rule.lhs = .app c.1 largs := by rw [hg0, hf]
  have hinst : RPairInst R ok act W (c.1, xs) d :=
    ⟨hWred c xs hWc hreach, hWd, rule, hrule, σ, hσ, largs, hlhs, hxsEq, targs, hsub, hdef, hd⟩
  obtain ⟨x', y, hx', hy, hprop⟩ := hsc.2 _ _ hinst
  obtain ⟨x, hx, hxx⟩ := psteps_getElem? hreach (proj c.1) x' hx'
  exact ⟨x, y, hx, hy, Relation.TransGen.trans_left hprop.transGen (rsteps_reflTransGen hxx)⟩

/-- The subterm criterion makes the minimal chain relation well founded. -/
theorem rchain_wf_of_criterion {W : sigma × List (Term sigma nu) → Prop}
    (hWred : ∀ c xs, W c → Relation.ReflTransGen (RArgStep R ok act c.1) c.2 xs → W (c.1, xs))
    {proj : sigma → Nat} (hsc : RSubtermCriterion R ok act W proj) :
    WellFounded (fun d c => RChainStep R ok act W c d) := by
  have key : ∀ x, Acc (Relation.TransGen (RStepOrSub R ok act)) x →
      ∀ c : sigma × List (Term sigma nu), c.2[proj c.1]? = some x →
        Acc (fun d c => RChainStep R ok act W c d) c := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      intro c hc
      refine Acc.intro _ fun d hd => ?_
      obtain ⟨x', y, hx', hy, hyx⟩ := rchainStep_proj hWred hsc hd
      rw [hc] at hx'
      cases hx'
      exact ih y hyx d hy
  constructor
  intro c
  refine Acc.intro _ fun d hd => ?_
  obtain ⟨-, y, -, hy, -⟩ := rchainStep_proj hWred hsc hd
  have hdef : IsDefined R d.1 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hdef, -⟩ := hd
    exact hdef
  have hysn : RSN R ok act y := hd.2.2.2.1 (proj d.1) y hy (hsc.1 _ hdef)
  exact key y ((acc_rStepOrSub_of_actSub y hysn y (.refl y)).transGen) d hy

/-- Termination by the subterm criterion, through the chain theorem. -/
theorem rsn_of_criterion {W : sigma × List (Term sigma nu) → Prop}
    (hcons : Conservative R act)
    (hW : ∀ rule ∈ R, ∀ σ : Subst sigma nu, ok σ → ∀ (g : sigma) (targs : List (Term sigma nu)),
      ActSub act (.app g targs) rule.rhs → IsDefined R g → W (g, Subst.applyList σ targs))
    (hWred : ∀ c xs, W c → Relation.ReflTransGen (RArgStep R ok act c.1) c.2 xs → W (c.1, xs))
    (Tok : Term sigma nu → Prop)
    (hTok : ∀ f args, Tok (.app f args) → W (f, args) ∧ ∀ a ∈ args, Tok a)
    {proj : sigma → Nat} (hsc : RSubtermCriterion R ok act W proj) :
    ∀ t, Tok t → RSN R ok act t :=
  rsn_of_rchain_wf hcons hW Tok hTok (rchain_wf_of_criterion hWred hsc)

end Restricted

theorem exists_getElem?_cons {α : Type w} {P : Nat → α → Prop} (b : α) (l : List α) :
    (∃ i a, (b :: l)[i]? = some a ∧ P i a) ↔ P 0 b ∨ ∃ i a, l[i]? = some a ∧ P (i + 1) a := by
  constructor
  · rintro ⟨i, a, hi, hP⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      exact Or.inl hP
    | succ k =>
      rw [List.getElem?_cons_succ] at hi
      exact Or.inr ⟨k, a, hi, hP⟩
  · rintro (hP | ⟨i, a, hi, hP⟩)
    · exact ⟨0, b, by simp, hP⟩
    · exact ⟨i + 1, a, by rw [List.getElem?_cons_succ]; exact hi, hP⟩

theorem not_exists_getElem?_nil {α : Type w} {P : Nat → α → Prop} :
    ¬ ∃ i a, ([] : List α)[i]? = some a ∧ P i a := by
  rintro ⟨i, a, h, -⟩
  simp at h

/-! ## 2. Row: contextSensitiveDP -/

section ContextSensitive

variable {sigma : Type u} {nu : Type v}

/-- Context-sensitive rewriting under a replacement map `μ` (Lucas 1998; Alarcón, Gutiérrez and
Lucas, Information and Computation 208, 2010, Section 2.5): a rule instance is contracted at a
`μ`-replacing position, that is at the root or inside an argument whose position is active. -/
abbrev MuStep (R : TRS sigma nu) (μ : sigma → Nat → Bool) :
    Term sigma nu → Term sigma nu → Prop :=
  RStep R (fun _ => True) (fun f i => μ f i = true)

/-- `μ`-termination of a term. -/
abbrev MuSN (R : TRS sigma nu) (μ : sigma → Nat → Bool) (t : Term sigma nu) : Prop :=
  RSN R (fun _ => True) (fun f i => μ f i = true) t

/-- The `μ`-replacing subterm relation. -/
abbrev MuSub (μ : sigma → Nat → Bool) : Term sigma nu → Term sigma nu → Prop :=
  ActSub (fun f i => μ f i = true)

/-- `R` is `μ`-conservative: every `μ`-replacing variable of a right-hand side is `μ`-replacing in
its left-hand side, so no rule has a migrating variable (AGL 2010, Section 6, before
Proposition 6). -/
def MuConservative (R : TRS sigma nu) (μ : sigma → Nat → Bool) : Prop :=
  Conservative R (fun f i => μ f i = true)

/-- Context-sensitive dependency pairs (AGL 2010, Definition 3, the part `DP_F`; for a
`μ`-conservative system it is all of `DP(R, μ)` by Proposition 6): from a left-hand side to a
defined-rooted `μ`-replacing subterm of the right-hand side. The two filtering conditions of
Definition 3 are dropped, which only adds pairs. -/
def MuPair (R : TRS sigma nu) (μ : sigma → Nat → Bool)
    (c d : sigma × List (Term sigma nu)) : Prop :=
  ∃ rule ∈ R, rule.lhs = .app c.1 c.2 ∧ MuSub μ (.app d.1 d.2) rule.rhs ∧ IsDefined R d.1

/-- The `μ`-subterm criterion (AGL 2010, Theorem 10, noncollapsing pairs, with a projection to
`μ`-replacing positions): every pair strictly decreases the projected argument in the
`μ`-replacing subterm order. -/
def MuSubtermCriterion (R : TRS sigma nu) (μ : sigma → Nat → Bool) (proj : sigma → Nat) : Prop :=
  (∀ f, IsDefined R f → μ f (proj f) = true) ∧
    ∀ c d, MuPair R μ c d → ∃ x y, c.2[proj c.1]? = some x ∧ d.2[proj d.1]? = some y ∧
      ProperActSub (fun f i => μ f i = true) y x

theorem muCriterion_inst {R : TRS sigma nu} {μ : sigma → Nat → Bool} {proj : sigma → Nat}
    (hsc : MuSubtermCriterion R μ proj) :
    RSubtermCriterion R (fun _ => True) (fun f i => μ f i = true) (fun _ => True) proj := by
  refine ⟨hsc.1, ?_⟩
  rintro ⟨f, cargs⟩ ⟨g, dargs⟩ ⟨-, -, rule, hrule, σ, -, largs, hl, hc, targs, hsub, hdef, hd⟩
  obtain ⟨x0, y0, hx0, hy0, hprop⟩ := hsc.2 (f, largs) (g, targs) ⟨rule, hrule, hl, hsub, hdef⟩
  have hx0' : largs[proj f]? = some x0 := hx0
  have hy0' : targs[proj g]? = some y0 := hy0
  have hc' : cargs = Subst.applyList σ largs := hc
  have hd' : dargs = Subst.applyList σ targs := hd
  refine ⟨Subst.apply σ x0, Subst.apply σ y0, ?_, ?_, hprop.subst σ⟩
  · show cargs[proj f]? = some (Subst.apply σ x0)
    rw [hc', Subst.applyList_eq_map, List.getElem?_map, hx0']
    rfl
  · show dargs[proj g]? = some (Subst.apply σ y0)
    rw [hd', Subst.applyList_eq_map, List.getElem?_map, hy0']
    rfl

/-- Soundness of the `μ`-subterm criterion for every `μ`-conservative system, through the
context-sensitive chain theorem `rsn_of_rchain_wf` (AGL 2010, Theorem 2 with Theorem 10). -/
theorem muTerminating_of_criterion (R : TRS sigma nu) (μ : sigma → Nat → Bool)
    (hcons : MuConservative R μ) {proj : sigma → Nat} (hsc : MuSubtermCriterion R μ proj) :
    ∀ t : Term sigma nu, MuSN R μ t :=
  fun t => rsn_of_criterion (W := fun _ => True) hcons (fun _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial) (fun _ => True) (fun _ _ _ => ⟨trivial, fun _ _ => trivial⟩)
    (muCriterion_inst hsc) t trivial

end ContextSensitive

/-- Arities of the free symbols. -/
def fArity : FreeSym → Nat
  | .zero => 0
  | .succ => 1
  | .wrap => 2
  | .recur => 3

/-- First-order terms over the free symbols. -/
abbrev FTerm : Type := Term FreeSym Nat

/-- Native data: a replacement map, the active argument positions of every symbol. -/
abbrev contextSensitiveDPData : Type := FreeSym → Nat → Bool

/-- Alarcón, Gutiérrez and Lucas (Context-sensitive dependency pairs, Information and Computation
208(8), 2010), Section 2.5 and Section 6: `μ` is a replacement map (active positions lie below the
arity) and the free recursor is `μ`-conservative. -/
def contextSensitiveDPLaws (μ : contextSensitiveDPData) : Prop :=
  (∀ f i, μ f i = true → i < fArity f) ∧ MuConservative freeRecursorTRS μ

/-- Acceptance: the `μ`-subterm criterion of Theorem 10 with a projection to active positions. -/
def contextSensitiveDPAccepts (μ : contextSensitiveDPData) : Prop :=
  ∃ proj : FreeSym → Nat, MuSubtermCriterion freeRecursorTRS μ proj

/-- Verdict: escape. -/
def contextSensitiveDPResult (μ : contextSensitiveDPData) : Prop :=
  contextSensitiveDPAccepts μ ∧ ∀ t : FTerm, MuSN freeRecursorTRS μ t

theorem contextSensitiveDP_sound :
    ∀ μ, contextSensitiveDPLaws μ → contextSensitiveDPAccepts μ →
      ∀ t : FTerm, MuSN freeRecursorTRS μ t := by
  rintro μ hL ⟨proj, hsc⟩
  exact muTerminating_of_criterion freeRecursorTRS μ hL.2 hsc

/-- The witness map: `recur` active in all three arguments, `succ` in its argument, `wrap` only in
its recursive argument; the payload position of `wrap` is blocked. -/
def contextSensitiveDPWitness : contextSensitiveDPData
  | .recur, i => decide (i < 3)
  | .succ, i => decide (i = 0)
  | .wrap, i => decide (i = 1)
  | .zero, _ => false

/-- The counter projection. -/
def muProj : FreeSym → Nat
  | .recur => 2
  | _ => 0

theorem contextSensitiveDPWitness_laws : contextSensitiveDPLaws contextSensitiveDPWitness := by
  refine ⟨?_, ?_⟩
  · intro f i h
    cases f <;> simp [contextSensitiveDPWitness, fArity] at h ⊢ <;> omega
  · intro rule hrule x hx
    simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
    rcases hrule with rfl | rfl
    · simp only [zeroRule, actSub_var_iff, Term.var.injEq] at hx
      subst hx
      simp [zeroRule, actSub_app_iff, actSub_var_iff, exists_getElem?_cons,
        contextSensitiveDPWitness]
    · simp [succRule, actSub_app_iff, actSub_var_iff, exists_getElem?_cons,
        contextSensitiveDPWitness] at hx ⊢
      omega

theorem contextSensitiveDPWitness_accepts :
    MuSubtermCriterion freeRecursorTRS contextSensitiveDPWitness muProj := by
  refine ⟨?_, ?_⟩
  · intro f hf
    rw [freeRecursorTRS_defined_iff] at hf
    subst hf
    rfl
  · rintro ⟨f, cargs⟩ ⟨g, dargs⟩ ⟨rule, hrule, hl, hsub, hdef⟩
    simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
    rcases hrule with rfl | rfl
    · simp [zeroRule, actSub_var_iff] at hsub
    · simp only [succRule, Term.app.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      rw [freeRecursorTRS_defined_iff] at hdef
      simp only at hdef
      subst hdef
      simp [succRule, actSub_app_iff, actSub_var_iff, exists_getElem?_cons,
        contextSensitiveDPWitness] at hsub
      subst hsub
      refine ⟨.app .succ [.var 2], .var 2, rfl, rfl, .succ, [.var 2], 0, .var 2, rfl, rfl, rfl,
        .refl _⟩

theorem contextSensitiveDPWitness_result : contextSensitiveDPResult contextSensitiveDPWitness :=
  ⟨⟨muProj, contextSensitiveDPWitness_accepts⟩,
    contextSensitiveDP_sound _ contextSensitiveDPWitness_laws
      ⟨muProj, contextSensitiveDPWitness_accepts⟩⟩

/-- A payload redex under `wrap`. -/
def blockedTerm : FTerm :=
  .app .wrap [.app .recur [.app .zero [], .app .zero [], .app .zero []], .app .zero []]

/-- The witness map with the recursive call's position under `wrap` blocked as well. -/
def callBlockedMap : contextSensitiveDPData := fun f i =>
  if f = .wrap then false else contextSensitiveDPWitness f i

/-- The two-symbol system of AGL 2010, Example 4: `a → c(f(a))`, `f(c(x)) → x`. -/
inductive Ex4Sym
  | a
  | c
  | f
  deriving DecidableEq

def ex4RuleA : Rule Ex4Sym Nat :=
  ⟨.app .a [], .app .c [.app .f [.app .a []]], rfl⟩

def ex4RuleF : Rule Ex4Sym Nat :=
  ⟨.app .f [.app .c [.var 0]], .var 0, rfl⟩

def ex4TRS : TRS Ex4Sym Nat := [ex4RuleA, ex4RuleF]

/-- `μ(f) = {1}`, `μ(c) = ∅` (AGL 2010, Example 4). -/
def ex4Map : Ex4Sym → Nat → Bool
  | .f, i => decide (i = 0)
  | _, _ => false

def ex4Start : Term Ex4Sym Nat := .app .f [.app .a []]

theorem ex4_loop :
    MuStep ex4TRS ex4Map ex4Start (.app .f [.app .c [.app .f [.app .a []]]]) ∧
      MuStep ex4TRS ex4Map (.app .f [.app .c [.app .f [.app .a []]]]) ex4Start := by
  refine ⟨?_, ?_⟩
  · exact RStep.arg Ex4Sym.f [] [] rfl
      (RStep.root ⟨ex4RuleA, by simp [ex4TRS], Subst.id, trivial, rfl, rfl⟩)
  · exact RStep.root ⟨ex4RuleF, by simp [ex4TRS], fun _ => .app .f [.app .a []], trivial, rfl, rfl⟩

/-- Blocked versus active positions, and the map mismatch of AGL 2010, Example 4: under the witness
the payload redex of `blockedTerm` rewrites by ordinary rewriting and not by `μ`-rewriting; with the
recursive call blocked there is no pair at all; and a system with a migrating variable has no pair,
fails `μ`-conservativeness, and is not `μ`-terminating, so the conservativeness law is
load-bearing. -/
theorem contextSensitiveDPWitness_feature :
    (Step freeRecursorTRS blockedTerm (.app .wrap [.app .zero [], .app .zero []]) ∧
      ∀ u, ¬ MuStep freeRecursorTRS contextSensitiveDPWitness blockedTerm u) ∧
    (∀ c d, ¬ MuPair freeRecursorTRS callBlockedMap c d) ∧
    (¬ MuConservative ex4TRS ex4Map ∧ (∀ c d, ¬ MuPair ex4TRS ex4Map c d) ∧
      ¬ MuSN ex4TRS ex4Map ex4Start) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact Step.arg FreeSym.wrap [] [.app .zero []]
      (Step.root ⟨zeroRule, by simp [freeRecursorTRS], fun _ => .app .zero [], rfl, rfl⟩)
  · intro u h
    rcases (rstep_app_iff _ _ u).1 h with hroot | ⟨ys, hys, -⟩
    · exact not_rroot_of_not_defined freeRecursorTRS_wrap_not_defined _ u hroot
    · rcases (pstep_cons_iff _ _ _ _ ys).1 hys with ⟨h0, -⟩ | ⟨rest', hrest, -⟩
      · exact absurd h0 (by decide)
      · rcases (pstep_cons_iff _ _ _ _ rest').1 hrest with ⟨-, b, hb, -⟩ | ⟨rest'', hnil, -⟩
        · exact not_rstep_const (by rw [freeRecursorTRS_defined_iff]; exact fun h => by cases h) b hb
        · exact not_pstep_nil _ _ rest'' hnil
  · rintro ⟨f, cargs⟩ ⟨g, dargs⟩ ⟨rule, hrule, -, hsub, hdef⟩
    simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
    rcases hrule with rfl | rfl
    · simp [zeroRule, actSub_var_iff] at hsub
    · rw [freeRecursorTRS_defined_iff] at hdef
      simp only at hdef
      subst hdef
      simp [succRule, actSub_app_iff, callBlockedMap] at hsub
  · intro h
    have := h ex4RuleF (by simp [ex4TRS]) 0 (.refl _)
    simp [ex4RuleF, actSub_app_iff, exists_getElem?_cons, ex4Map] at this
  · rintro ⟨f0, cargs⟩ ⟨g0, dargs⟩ ⟨rule, hrule, -, hsub, hdef⟩
    simp only [ex4TRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
    rcases hrule with rfl | rfl
    · simp [ex4RuleA, actSub_app_iff, ex4Map] at hsub
      obtain ⟨rfl, rfl⟩ := hsub
      obtain ⟨rule, hrule, largs, hl⟩ := hdef
      simp only [ex4TRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
      rcases hrule with rfl | rfl <;> simp [ex4RuleA, ex4RuleF] at hl
    · simp [ex4RuleF, actSub_var_iff] at hsub
  · exact not_acc_of_cycle ex4_loop.1 ex4_loop.2

/-- The counter position of `recur` blocked, everything else as in the witness. -/
def contextSensitiveDPMutant : contextSensitiveDPData := fun f i =>
  if f = .recur ∧ i = 2 then false else contextSensitiveDPWitness f i

/-- Blocking the counter keeps the laws and loses the criterion: no projection to an active
position of `recur` decreases along the pair. -/
theorem contextSensitiveDP_mutation :
    contextSensitiveDPLaws contextSensitiveDPMutant ∧
      ¬ contextSensitiveDPAccepts contextSensitiveDPMutant := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro f i h
    cases f <;> simp [contextSensitiveDPMutant, contextSensitiveDPWitness, fArity] at h ⊢ <;>
      omega
  · intro rule hrule x hx
    simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
    rcases hrule with rfl | rfl
    · simp only [zeroRule, actSub_var_iff, Term.var.injEq] at hx
      subst hx
      simp [zeroRule, actSub_app_iff, actSub_var_iff, exists_getElem?_cons,
        contextSensitiveDPMutant, contextSensitiveDPWitness]
    · simp [succRule, actSub_app_iff, actSub_var_iff, exists_getElem?_cons,
        contextSensitiveDPMutant, contextSensitiveDPWitness] at hx ⊢
      omega
  · rintro ⟨proj, hact, hdec⟩
    have hpair : MuPair freeRecursorTRS contextSensitiveDPMutant
        (.recur, [.var 0, .var 1, .app .succ [.var 2]]) (.recur, [.var 0, .var 1, .var 2]) := by
      refine ⟨succRule, by simp [freeRecursorTRS], rfl, ?_, (freeRecursorTRS_defined_iff _).2 rfl⟩
      exact .arg FreeSym.wrap _ 1 rfl rfl (.refl _)
    have hp := hact FreeSym.recur ((freeRecursorTRS_defined_iff _).2 rfl)
    obtain ⟨x, y, hx, hy, f, args, i, a, hxa, -, -, -⟩ := hdec _ _ hpair
    have hlt : proj FreeSym.recur < 2 := by
      by_contra hge
      have : proj FreeSym.recur = 2 ∨ 3 ≤ proj FreeSym.recur := by omega
      rcases this with h2 | h3
      · simp [contextSensitiveDPMutant, h2] at hp
      · simp [contextSensitiveDPMutant, contextSensitiveDPWitness] at hp
        omega
    interval_cases h : proj FreeSym.recur <;> simp_all

/-! ## 3. Many-sorted systems and the row typeIntroduction -/

/-- A sort attachment (Aoto and Toyama 1997, as recalled by Iwami 2004, Section 2.2): argument
sorts and result sort of every symbol, and a sort for every variable. -/
structure SortAttach (sigma : Type u) (S : Type) where
  arg : sigma → Nat → S
  res : sigma → S
  var : Nat → S

section ManySorted

variable {sigma : Type u} {S : Type}

/-- Well-sorted terms of a sort under an attachment; applications carry the declared arity. -/
inductive HasSort (ar : sigma → Nat) (A : SortAttach sigma S) : Term sigma Nat → S → Prop
  | var (x : Nat) : HasSort ar A (.var x) (A.var x)
  | app (f : sigma) (args : List (Term sigma Nat)) (hlen : args.length = ar f)
      (hargs : ∀ i a, args[i]? = some a → HasSort ar A a (A.arg f i)) :
      HasSort ar A (.app f args) (A.res f)

/-- Arguments of `f` well sorted from position `k` on. -/
def ArgsSorted (ar : sigma → Nat) (A : SortAttach sigma S) (f : sigma) :
    Nat → List (Term sigma Nat) → Prop
  | _, [] => True
  | k, a :: as => HasSort ar A a (A.arg f k) ∧ ArgsSorted ar A f (k + 1) as

/-- The rewrite relation of the sorted system: rewriting of well-sorted terms. -/
def SortedStep (ar : sigma → Nat) (A : SortAttach sigma S) (R : TRS sigma Nat)
    (t u : Term sigma Nat) : Prop :=
  (∃ s, HasSort ar A t s) ∧ Step R t u

/-- Termination of the sorted system: no well-sorted term starts an infinite sorted rewrite
sequence. -/
def SortedTerminates (ar : sigma → Nat) (A : SortAttach sigma S) (R : TRS sigma Nat) : Prop :=
  ∀ t s, HasSort ar A t s → Acc (fun u t => SortedStep ar A R t u) t

variable {ar : sigma → Nat} {A : SortAttach sigma S}

theorem hasSort_var_iff {x : Nat} {s : S} : HasSort ar A (.var x) s ↔ s = A.var x := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .var x

theorem hasSort_app_iff {f : sigma} {args : List (Term sigma Nat)} {s : S} :
    HasSort ar A (.app f args) s ↔
      s = A.res f ∧ args.length = ar f ∧ ∀ i a, args[i]? = some a → HasSort ar A a (A.arg f i) := by
  constructor
  · intro h
    cases h with
    | app _ _ hlen hargs => exact ⟨rfl, hlen, hargs⟩
  · rintro ⟨rfl, hlen, hargs⟩
    exact .app f args hlen hargs

theorem argsSorted_getElem? {f : sigma} :
    ∀ (k : Nat) (args : List (Term sigma Nat)), ArgsSorted ar A f k args →
      ∀ i a, args[i]? = some a → HasSort ar A a (A.arg f (k + i))
  | _, [], _, _, _, h => by simp at h
  | k, b :: bs, h, 0, a, hi => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simpa using h.1
  | k, b :: bs, h, i + 1, a, hi => by
      rw [List.getElem?_cons_succ] at hi
      have := argsSorted_getElem? (k + 1) bs h.2 i a hi
      rwa [show k + 1 + i = k + (i + 1) by omega] at this

theorem hasSort_mk {f : sigma} {args : List (Term sigma Nat)} (hlen : args.length = ar f)
    (h : ArgsSorted ar A f 0 args) : HasSort ar A (.app f args) (A.res f) :=
  .app f args hlen fun i a hi => by simpa using argsSorted_getElem? 0 args h i a hi

theorem hasSort_arg_mid {f : sigma} {pre post : List (Term sigma Nat)} {a : Term sigma Nat}
    {s : S} (h : HasSort ar A (.app f (pre ++ a :: post)) s) :
    HasSort ar A a (A.arg f pre.length) :=
  (hasSort_app_iff.1 h).2.2 _ a (getElem?_mid pre post a)

theorem hasSort_replace {f : sigma} {pre post : List (Term sigma Nat)} {a b : Term sigma Nat}
    {s : S} (h : HasSort ar A (.app f (pre ++ a :: post)) s)
    (hb : HasSort ar A b (A.arg f pre.length)) : HasSort ar A (.app f (pre ++ b :: post)) s := by
  obtain ⟨rfl, hlen, hargs⟩ := hasSort_app_iff.1 h
  refine .app f _ (by simpa using hlen) fun i c hc => ?_
  by_cases hi : i = pre.length
  · subst hi
    rw [getElem?_mid] at hc
    cases hc
    exact hb
  · rw [getElem?_mid_ne pre post a b hi] at hc
    exact hargs i c hc

end ManySorted

section Occurrences

variable {sigma : Type u}

mutual
/-- Occurrences of the variable `x` in a term. -/
def occ (x : Nat) : Term sigma Nat → Nat
  | .var y => if y = x then 1 else 0
  | .app _ args => occList x args
/-- Occurrences of `x` in an argument list. -/
def occList (x : Nat) : List (Term sigma Nat) → Nat
  | [] => 0
  | a :: as => occ x a + occList x as
end

/-- A collapsing rule: its right-hand side is a variable (Aoto 2001, Section 2). -/
def IsCollapsing (rule : Rule sigma Nat) : Prop := ∃ x, rule.rhs = .var x

/-- A duplicating rule: some variable occurs more often on the right than on the left (Aoto 2001,
Section 2). -/
def IsDuplicating (rule : Rule sigma Nat) : Prop := ∃ x, occ x rule.lhs < occ x rule.rhs

/-- The side condition of Zantema's type elimination theorem: the system has no collapsing rule or
no duplicating rule. -/
def ZantemaCondition (R : TRS sigma Nat) : Prop :=
  (∀ rule ∈ R, ¬ IsCollapsing rule) ∨ (∀ rule ∈ R, ¬ IsDuplicating rule)

end Occurrences

theorem sizeList_append {sigma : Type u} {nu : Type v} (l1 l2 : List (Term sigma nu)) :
    Term.sizeList (l1 ++ l2) = Term.sizeList l1 + Term.sizeList l2 := by
  induction l1 with
  | nil => simp
  | cons a as ih =>
    simp only [List.cons_append, Term.sizeList_cons, ih]
    omega

theorem not_acc_of_transGen_self {α : Type w} {r : α → α → Prop} {x : α}
    (h : Relation.TransGen r x x) : ¬ Acc r x := by
  intro hx
  have h2 := hx.transGen
  clear hx
  induction h2 with
  | intro x _ ih => exact ih x h h

/-- Native data: a sort attachment for the four free symbols and the variables, sorts coded by
naturals. -/
abbrev typeIntroductionData : Type := SortAttach FreeSym Nat

/-- Zantema (Termination of term rewriting: interpretation and type elimination, Journal of
Symbolic Computation 17, 1994, 23-50), in the attachment formulation of Iwami 2004, Section 2.2:
both rules are well sorted with the same sort on both sides. -/
def typeIntroductionLaws (A : typeIntroductionData) : Prop :=
  ∀ rule ∈ freeRecursorTRS, ∃ s, HasSort fArity A rule.lhs s ∧ HasSort fArity A rule.rhs s

/-- Acceptance by type introduction: the side condition of Zantema's type elimination theorem
(termination is persistent for systems without collapsing or without duplicating rules, as
restated by Aoto 2001, Section 1, and Iwami 2004, Section 1) together with termination of the
sorted system. -/
def typeIntroductionAccepts (A : typeIntroductionData) : Prop :=
  ZantemaCondition freeRecursorTRS ∧ SortedTerminates fArity A freeRecursorTRS

/-- Verdict: barrier. -/
def typeIntroductionResult (A : typeIntroductionData) : Prop := ¬ typeIntroductionAccepts A

/-- The zero rule collapses and the successor rule duplicates the step argument, under every
attachment. -/
theorem freeRecursor_not_zantema : ¬ ZantemaCondition freeRecursorTRS := by
  rintro (h | h)
  · exact h zeroRule (by simp [freeRecursorTRS]) ⟨0, rfl⟩
  · exact h succRule (by simp [freeRecursorTRS]) ⟨1, by decide⟩

theorem typeIntroduction_universal :
    ∀ A, typeIntroductionLaws A → typeIntroductionResult A :=
  fun _ _ hacc => freeRecursor_not_zantema hacc.1

/-- The natural attachment: counters of sort `0`, values of sort `1`. -/
def typeIntroductionWitness : typeIntroductionData where
  arg := fun f i => match f, i with
    | .recur, 2 => 0
    | .succ, _ => 0
    | _, _ => 1
  res := fun
    | .zero => 0
    | .succ => 0
    | _ => 1
  var := fun
    | 2 => 0
    | _ => 1

theorem typeIntroductionWitness_laws : typeIntroductionLaws typeIntroductionWitness := by
  intro rule hrule
  simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
  rcases hrule with rfl | rfl
  · exact ⟨1, hasSort_mk rfl ⟨.var 0, .var 1, hasSort_mk rfl trivial, trivial⟩, .var 0⟩
  · exact ⟨1, hasSort_mk rfl ⟨.var 0, .var 1, hasSort_mk rfl ⟨.var 2, trivial⟩, trivial⟩,
      hasSort_mk rfl ⟨.var 1, hasSort_mk rfl ⟨.var 0, .var 1, .var 2, trivial⟩, trivial⟩⟩

theorem typeIntroductionWitness_result : typeIntroductionResult typeIntroductionWitness :=
  typeIntroduction_universal _ typeIntroductionWitness_laws

/-- Toyama's symbols (Toyama, Counterexamples to termination for the direct sum of term rewriting
systems, Information Processing Letters 25, 1987), with the sorts of Aoto 2001, Section 3. -/
inductive ToySym
  | f
  | g
  | a
  | b
  deriving DecidableEq

def toyArity : ToySym → Nat
  | .f => 3
  | .g => 2
  | .a => 0
  | .b => 0

/-- `f(a, b, x) → f(x, x, x)`. -/
def toyRuleF : Rule ToySym Nat :=
  ⟨.app .f [.app .a [], .app .b [], .var 0], .app .f [.var 0, .var 0, .var 0], rfl⟩

/-- `g(y, z) → y`. -/
def toyRuleG1 : Rule ToySym Nat := ⟨.app .g [.var 1, .var 2], .var 1, rfl⟩

/-- `g(y, z) → z`. -/
def toyRuleG2 : Rule ToySym Nat := ⟨.app .g [.var 1, .var 2], .var 2, rfl⟩

def toyTRS : TRS ToySym Nat := [toyRuleF, toyRuleG1, toyRuleG2]

/-- `f : 1 × 1 × 1 → 1`, `g : 0 × 0 → 0`, `a, b : 1`, the variable of the `f`-rule of sort `1` and
the other variables of sort `0`. -/
def toyAttach : SortAttach ToySym Nat where
  arg := fun s _ => match s with
    | .f => 1
    | _ => 0
  res := fun
    | .g => 0
    | _ => 1
  var := fun
    | 0 => 1
    | _ => 0

def toyGab : Term ToySym Nat := .app .g [.app .a [], .app .b []]

def toyLoop : Term ToySym Nat := .app .f [toyGab, toyGab, toyGab]

theorem toyAttach_consistent :
    ∀ rule ∈ toyTRS, ∃ s, HasSort toyArity toyAttach rule.lhs s ∧
      HasSort toyArity toyAttach rule.rhs s := by
  intro rule hrule
  simp only [toyTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
  rcases hrule with rfl | rfl | rfl
  · exact ⟨1, hasSort_mk rfl ⟨hasSort_mk rfl trivial, hasSort_mk rfl trivial, .var 0, trivial⟩,
      hasSort_mk rfl ⟨.var 0, .var 0, .var 0, trivial⟩⟩
  · exact ⟨0, hasSort_mk rfl ⟨.var 1, .var 2, trivial⟩, .var 1⟩
  · exact ⟨0, hasSort_mk rfl ⟨.var 1, .var 2, trivial⟩, .var 2⟩

theorem toy_cycle : Relation.TransGen (fun u t => Step toyTRS t u) toyLoop toyLoop := by
  have s1 : Step toyTRS toyLoop (.app .f [.app .a [], toyGab, toyGab]) :=
    Step.arg ToySym.f [] [toyGab, toyGab]
      (Step.root ⟨toyRuleG1, by simp [toyTRS], fun | 1 => .app .a [] | _ => .app .b [], rfl, rfl⟩)
  have s2 : Step toyTRS (.app .f [.app .a [], toyGab, toyGab])
      (.app .f [.app .a [], .app .b [], toyGab]) :=
    Step.arg ToySym.f [.app .a []] [toyGab]
      (Step.root ⟨toyRuleG2, by simp [toyTRS], fun | 1 => .app .a [] | _ => .app .b [], rfl, rfl⟩)
  have s3 : Step toyTRS (.app .f [.app .a [], .app .b [], toyGab]) toyLoop :=
    Step.root ⟨toyRuleF, by simp [toyTRS], fun _ => toyGab, rfl, rfl⟩
  exact Relation.TransGen.head s3 (Relation.TransGen.head s2 (Relation.TransGen.single s1))

theorem toy_not_zantema : ¬ ZantemaCondition toyTRS := by
  rintro (h | h)
  · exact h toyRuleG1 (by simp [toyTRS]) ⟨1, rfl⟩
  · exact h toyRuleF (by simp [toyTRS]) ⟨0, by decide⟩

theorem toy_not_defined_g_a : ¬ IsDefined toyTRS ToySym.a ∧ ¬ IsDefined toyTRS ToySym.b := by
  constructor <;>
  · rintro ⟨rule, hrule, largs, hl⟩
    simp only [toyTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
    rcases hrule with rfl | rfl | rfl <;> simp [toyRuleF, toyRuleG1, toyRuleG2] at hl

/-- Steps from sort-`0` terms shrink the term and stay of sort `0`. -/
theorem toy_step0 {t u : Term ToySym Nat} (h : Step toyTRS t u)
    (ht : HasSort toyArity toyAttach t 0) :
    Term.size u < Term.size t ∧ HasSort toyArity toyAttach u 0 := by
  induction h with
  | root h =>
    obtain ⟨rule, hrule, σ, rfl, rfl⟩ := h
    simp only [toyTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
    rcases hrule with rfl | rfl | rfl
    · simp [toyRuleF, hasSort_app_iff, toyAttach] at ht
    · simp only [toyRuleG1, Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
        Subst.apply_var] at ht ⊢
      refine ⟨by simp; omega, (hasSort_app_iff.1 ht).2.2 0 _ rfl⟩
    · simp only [toyRuleG2, Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
        Subst.apply_var] at ht ⊢
      refine ⟨by simp; omega, (hasSort_app_iff.1 ht).2.2 1 _ rfl⟩
  | arg sym pre post hab ih =>
    have hs := (hasSort_app_iff.1 ht).1
    have ha := hasSort_arg_mid ht
    have hf : sym = .g := by
      cases sym
      · exact absurd hs (by decide)
      · rfl
      · exact absurd hs (by decide)
      · exact absurd hs (by decide)
    subst hf
    obtain ⟨hlt, hb⟩ := ih ha
    refine ⟨?_, hasSort_replace ht hb⟩
    simp only [Term.size_app, sizeList_append, Term.sizeList_cons]
    omega

theorem toy_sn0 : ∀ n (t : Term ToySym Nat), Term.size t ≤ n →
    HasSort toyArity toyAttach t 0 → SN toyTRS t := by
  intro n
  induction n with
  | zero => intro t hsz; exact absurd hsz (by have := Term.one_le_size t; omega)
  | succ n ih =>
    intro t hsz ht
    refine Acc.intro _ fun u hu => ?_
    obtain ⟨hlt, hu0⟩ := toy_step0 hu ht
    exact ih u (by omega) hu0

/-- Steps from sort-`1` terms stay of sort `1` and produce `f`-rooted terms. -/
theorem toy_step1 {t u : Term ToySym Nat} (h : Step toyTRS t u)
    (ht : HasSort toyArity toyAttach t 1) :
    HasSort toyArity toyAttach u 1 ∧ ∃ us, u = .app .f us := by
  induction h with
  | root h =>
    obtain ⟨rule, hrule, σ, rfl, rfl⟩ := h
    simp only [toyTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
    rcases hrule with rfl | rfl | rfl
    · simp only [toyRuleF, Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
        Subst.apply_var] at ht ⊢
      have h0 : HasSort toyArity toyAttach (σ 0) 1 := (hasSort_app_iff.1 ht).2.2 2 _ rfl
      exact ⟨hasSort_mk rfl ⟨h0, h0, h0, trivial⟩, _, rfl⟩
    · simp [toyRuleG1, hasSort_app_iff, toyAttach] at ht
    · simp [toyRuleG2, hasSort_app_iff, toyAttach] at ht
  | arg sym pre post hab ih =>
    have hs := hasSort_app_iff.1 ht
    have ha := hasSort_arg_mid ht
    have hf : sym = .f := by
      cases sym
      · rfl
      · simp [toyAttach] at hs
      · simp [toyArity] at hs
      · simp [toyArity] at hs
    subst hf
    exact ⟨hasSort_replace ht (ih ha).1, _, rfl⟩

theorem toy_steps1 {t u : Term ToySym Nat}
    (h : Relation.ReflTransGen (Step toyTRS) t u) (ht : HasSort toyArity toyAttach t 1) :
    HasSort toyArity toyAttach u 1 ∧ (u = t ∨ ∃ us, u = .app .f us) := by
  induction h with
  | refl => exact ⟨ht, Or.inl rfl⟩
  | tail _ hstep ih =>
    obtain ⟨hs, -⟩ := ih
    obtain ⟨hs', us, rfl⟩ := toy_step1 hstep hs
    exact ⟨hs', Or.inr ⟨us, rfl⟩⟩

/-- An `f`-node whose first two arguments are not `a` and `b` never becomes a redex. -/
theorem toy_sn_f_blocked : ∀ ys : List (Term ToySym Nat),
    (∀ y ∈ ys, HasSort toyArity toyAttach y 1 ∧ SN toyTRS y) →
    ¬ (ys[0]? = some (.app .a []) ∧ ys[1]? = some (.app .b [])) →
      SN toyTRS (.app .f ys) := by
  intro ys hys hblock
  have hacc := accArgs ys fun y hy => (hys y hy).2
  induction hacc with
  | intro ys _ ih =>
    refine Acc.intro _ fun u hu => ?_
    rcases (step_app_iff toyTRS _ ys u).1 hu with hroot | ⟨zs, hzs, rfl⟩
    · obtain ⟨rule, hrule, σ, hl, -⟩ := hroot
      simp only [toyTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
      rcases hrule with rfl | rfl | rfl
      · simp only [toyRuleF, Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
          Subst.apply_var, Term.app.injEq, true_and] at hl
        subst hl
        exact absurd ⟨rfl, rfl⟩ hblock
      · simp [toyRuleG1] at hl
      · simp [toyRuleG2] at hl
    · have hzs' : ∀ z ∈ zs, HasSort toyArity toyAttach z 1 ∧ SN toyTRS z := by
        obtain ⟨pre, post, x, y, rfl, rfl, hxy⟩ := hzs
        intro z hz
        simp only [List.mem_append, List.mem_cons] at hz
        rcases hz with hz | rfl | hz
        · exact hys z (by simp [hz])
        · have hx := hys x (by simp)
          exact ⟨(toy_step1 hxy hx.1).1, hx.2.inv hxy⟩
        · exact hys z (by simp [hz])
      refine ih zs hzs hzs' fun ⟨h0, h1⟩ => hblock ⟨?_, ?_⟩
      · obtain ⟨x, hx, hxz⟩ := argStep_getElem? hzs 0 _ h0
        have hxs := hys x (List.mem_of_getElem? hx)
        rcases (toy_steps1 hxz hxs.1).2 with heq | ⟨us, heq⟩
        · rw [heq]; exact hx
        · exact absurd heq (by simp)
      · obtain ⟨x, hx, hxz⟩ := argStep_getElem? hzs 1 _ h1
        have hxs := hys x (List.mem_of_getElem? hx)
        rcases (toy_steps1 hxz hxs.1).2 with heq | ⟨us, heq⟩
        · rw [heq]; exact hx
        · exact absurd heq (by simp)

theorem toy_sn_f : ∀ ys : List (Term ToySym Nat),
    (∀ y ∈ ys, HasSort toyArity toyAttach y 1 ∧ SN toyTRS y) → SN toyTRS (.app .f ys) := by
  intro ys hys
  have hacc := accArgs ys fun y hy => (hys y hy).2
  induction hacc with
  | intro ys _ ih =>
    refine Acc.intro _ fun u hu => ?_
    rcases (step_app_iff toyTRS _ ys u).1 hu with hroot | ⟨zs, hzs, rfl⟩
    · obtain ⟨rule, hrule, σ, hl, rfl⟩ := hroot
      simp only [toyTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
      rcases hrule with rfl | rfl | rfl
      · simp only [toyRuleF, Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
          Subst.apply_var, Term.app.injEq, true_and] at hl ⊢
        subst hl
        have h0 := hys (σ 0) (by simp)
        refine toy_sn_f_blocked [σ 0, σ 0, σ 0] (by simp [h0]) ?_
        rintro ⟨h1, h2⟩
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h1 h2
        rw [h1] at h2
        simp at h2
      · simp [toyRuleG1] at hl
      · simp [toyRuleG2] at hl
    · have hzs' : ∀ z ∈ zs, HasSort toyArity toyAttach z 1 ∧ SN toyTRS z := by
        obtain ⟨pre, post, x, y, rfl, rfl, hxy⟩ := hzs
        intro z hz
        simp only [List.mem_append, List.mem_cons] at hz
        rcases hz with hz | rfl | hz
        · exact hys z (by simp [hz])
        · have hx := hys x (by simp)
          exact ⟨(toy_step1 hxy hx.1).1, hx.2.inv hxy⟩
        · exact hys z (by simp [hz])
      exact ih zs hzs hzs'

theorem toy_sn1 : ∀ t : Term ToySym Nat, HasSort toyArity toyAttach t 1 → SN toyTRS t := by
  intro t
  induction t using Term.rec' with
  | hvar x => intro _; exact Acc.intro _ fun u h => absurd h (not_step_var toyTRS x u)
  | happ s args ih =>
    intro ht
    obtain ⟨hres, hlen, hargs⟩ := hasSort_app_iff.1 ht
    cases s with
    | f =>
      refine toy_sn_f args fun y hy => ?_
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hy
      have hy1 : HasSort toyArity toyAttach y 1 := hargs i y hi
      exact ⟨hy1, ih y hy hy1⟩
    | g => simp [toyAttach] at hres
    | a =>
      have : args = [] := List.eq_nil_of_length_eq_zero hlen
      subst this
      exact sn_app_of_not_defined toy_not_defined_g_a.1 [] (by simp)
    | b =>
      have : args = [] := List.eq_nil_of_length_eq_zero hlen
      subst this
      exact sn_app_of_not_defined toy_not_defined_g_a.2 [] (by simp)

/-- The sorted Toyama system terminates. -/
theorem toy_sortedTerminates : SortedTerminates toyArity toyAttach toyTRS := by
  intro t s ht
  have hsn : SN toyTRS t := by
    have hs : s = 0 ∨ s = 1 := by
      cases ht with
      | var x => cases x <;> simp [toyAttach]
      | app sym args _ _ => cases sym <;> simp [toyAttach]
    rcases hs with rfl | rfl
    · exact toy_sn0 _ t le_rfl ht
    · exact toy_sn1 t ht
  exact Subrelation.accessible (fun h => h.2) hsn

/-- The counter sort given the value sort, everything else as in the witness: the successor
rule is ill sorted. -/
def typeIntroductionMutant : typeIntroductionData :=
  { typeIntroductionWitness with
    res := fun
      | .zero => 0
      | _ => 1 }

theorem typeIntroduction_mutation : ¬ typeIntroductionLaws typeIntroductionMutant := by
  intro h
  obtain ⟨s, hl, -⟩ := h succRule (by simp [freeRecursorTRS])
  have h2 := (hasSort_app_iff.1 hl).2.2 2 _ rfl
  have h3 := (hasSort_app_iff.1 h2).1
  exact absurd h3 (by decide)

/-- Toyama's system: the sorted system terminates, the unsorted system loops, and the system
violates Zantema's side condition, so the side condition is necessary for type elimination. -/
theorem typeIntroductionWitness_feature :
    SortedTerminates toyArity toyAttach toyTRS ∧ ¬ SN toyTRS toyLoop ∧
      ¬ ZantemaCondition toyTRS :=
  ⟨toy_sortedTerminates, not_acc_of_transGen_self toy_cycle, toy_not_zantema⟩

/-! ## 4. Order-sorted rewriting and the row orderSortedDP -/

/-- Native data: an order-sorted signature over the sort codes `Fin 4`: a subsort order, one rank
declaration per symbol, and a sort for every variable. -/
structure orderSortedDPData where
  le : Fin 4 → Fin 4 → Bool
  arg : FreeSym → Nat → Fin 4
  res : FreeSym → Fin 4
  var : Nat → Fin 4

/-- The least sort of a term: with one rank declaration per symbol it is the declared result sort,
or the sort of the variable. -/
def lsort (M : orderSortedDPData) : FTerm → Fin 4
  | .var x => M.var x
  | .app f _ => M.res f

/-- Well-formed order-sorted terms (Lucas and Meseguer, Strong and weak operational termination of
order-sorted rewrite theories, WRLA 2014, LNCS 8663, Section 2: an argument of sort `s'` fills a
position of sort `s` when `s' ≤ s`). -/
inductive OSWF (M : orderSortedDPData) : FTerm → Prop
  | var (x : Nat) : OSWF M (.var x)
  | app (f : FreeSym) (args : List FTerm) (hlen : args.length = fArity f)
      (hwf : ∀ (i : Nat) (a : FTerm), args[i]? = some a → OSWF M a)
      (hle : ∀ (i : Nat) (a : FTerm), args[i]? = some a → M.le (lsort M a) (M.arg f i) = true) :
      OSWF M (.app f args)

/-- `t` is a term of sort `s`. -/
def OSHasSort (M : orderSortedDPData) (t : FTerm) (s : Fin 4) : Prop :=
  OSWF M t ∧ M.le (lsort M t) s = true

/-- An order-sorted substitution: every variable is mapped to a term of the variable's sort. -/
def OSSubst (M : orderSortedDPData) (σ : Subst FreeSym Nat) : Prop :=
  ∀ x, OSHasSort M (σ x) (M.var x)

/-- Order-sorted rewriting (WRLA 2014, Figure 1, rules Cong and Repl without conditions and without
axioms): rule instances under order-sorted substitutions, closed under contexts. -/
abbrev OSStep (M : orderSortedDPData) (R : TRS FreeSym Nat) : FTerm → FTerm → Prop :=
  RStep R (OSSubst M) (fun _ _ => True)

/-- Order-sorted strong normalization. -/
abbrev OSSN (M : orderSortedDPData) (R : TRS FreeSym Nat) (t : FTerm) : Prop :=
  RSN R (OSSubst M) (fun _ _ => True) t

/-- Well-sorted calls: the declared arity and argument sorts. -/
def OSCall (M : orderSortedDPData) (c : FreeSym × List FTerm) : Prop :=
  c.2.length = fArity c.1 ∧ ∀ i a, c.2[i]? = some a → OSHasSort M a (M.arg c.1 i)

/-- The subsort relation is a partial order (WRLA 2014, Section 2). -/
def OSOrderLaws (M : orderSortedDPData) : Prop :=
  (∀ s, M.le s s = true) ∧ (∀ s t u, M.le s t = true → M.le t u = true → M.le s u = true) ∧
    ∀ s t, M.le s t = true → M.le t s = true → s = t

/-- Rules are well formed and sort-decreasing (WRLA 2014, Section 2). -/
def OSRuleLaws (M : orderSortedDPData) (R : TRS FreeSym Nat) : Prop :=
  ∀ rule ∈ R, OSWF M rule.lhs ∧ OSWF M rule.rhs ∧
    M.le (lsort M rule.rhs) (lsort M rule.lhs) = true

/-- Arguments of `f` well formed with admissible sorts from position `k` on. -/
def OSArgsOK (M : orderSortedDPData) (f : FreeSym) : Nat → List FTerm → Prop
  | _, [] => True
  | k, a :: as => OSWF M a ∧ M.le (lsort M a) (M.arg f k) = true ∧ OSArgsOK M f (k + 1) as

theorem oswf_app_iff {M : orderSortedDPData} {f : FreeSym} {args : List FTerm} :
    OSWF M (.app f args) ↔ args.length = fArity f ∧
      (∀ (i : Nat) (a : FTerm), args[i]? = some a → OSWF M a) ∧
      ∀ (i : Nat) (a : FTerm), args[i]? = some a → M.le (lsort M a) (M.arg f i) = true := by
  constructor
  · intro h
    cases h with
    | app _ _ hlen hwf hle => exact ⟨hlen, hwf, hle⟩
  · rintro ⟨hlen, hwf, hle⟩
    exact .app f args hlen hwf hle

theorem osArgsOK_getElem? {M : orderSortedDPData} {f : FreeSym} :
    ∀ (k : Nat) (args : List FTerm), OSArgsOK M f k args →
      ∀ (i : Nat) (a : FTerm), args[i]? = some a →
        OSWF M a ∧ M.le (lsort M a) (M.arg f (k + i)) = true
  | _, [], _, _, _, h => by simp at h
  | k, b :: bs, h, 0, a, hi => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi
      simpa using ⟨h.1, h.2.1⟩
  | k, b :: bs, h, i + 1, a, hi => by
      rw [List.getElem?_cons_succ] at hi
      have := osArgsOK_getElem? (k + 1) bs h.2.2 i a hi
      rwa [show k + 1 + i = k + (i + 1) by omega] at this

theorem oswf_mk {M : orderSortedDPData} {f : FreeSym} {args : List FTerm}
    (hlen : args.length = fArity f) (h : OSArgsOK M f 0 args) : OSWF M (.app f args) :=
  .app f args hlen (fun i a hi => (osArgsOK_getElem? 0 args h i a hi).1)
    (fun i a hi => by simpa using (osArgsOK_getElem? 0 args h i a hi).2)

theorem oswf_of_actSub {M : orderSortedDPData} {act : FreeSym → Nat → Prop} {w t : FTerm}
    (h : ActSub act w t) (ht : OSWF M t) : OSWF M w := by
  induction h with
  | refl => exact ht
  | arg f args i hi _ _ ih => exact ih ((oswf_app_iff.1 ht).2.1 i _ hi)

/-- Substitution lemma: an order-sorted substitution keeps well-formedness and does not raise the
least sort. -/
theorem os_subst {M : orderSortedDPData} (hM : OSOrderLaws M) {σ : Subst FreeSym Nat}
    (hσ : OSSubst M σ) : ∀ t : FTerm, OSWF M t →
      OSWF M (Subst.apply σ t) ∧ M.le (lsort M (Subst.apply σ t)) (lsort M t) = true := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
    intro _
    simp only [Subst.apply_var, lsort]
    exact hσ x
  | happ f args ih =>
    intro ht
    obtain ⟨hlen, hwf, hle⟩ := oswf_app_iff.1 ht
    rw [Subst.apply_app]
    refine ⟨.app f _ (by rw [Subst.applyList_eq_map, List.length_map]; exact hlen) ?_ ?_,
      hM.1 _⟩
    · intro i a' hi
      rw [Subst.applyList_eq_map, List.getElem?_map, Option.map_eq_some_iff] at hi
      obtain ⟨a, ha, rfl⟩ := hi
      exact (ih a (List.mem_of_getElem? ha) (hwf i a ha)).1
    · intro i a' hi
      rw [Subst.applyList_eq_map, List.getElem?_map, Option.map_eq_some_iff] at hi
      obtain ⟨a, ha, rfl⟩ := hi
      exact hM.2.1 _ _ _ (ih a (List.mem_of_getElem? ha) (hwf i a ha)).2 (hle i a ha)

/-- Subject reduction: order-sorted rewriting keeps every sort of a well-formed term. -/
theorem os_subject_reduction {M : orderSortedDPData} {R : TRS FreeSym Nat} (hM : OSOrderLaws M)
    (hR : OSRuleLaws M R) {t u : FTerm} (h : OSStep M R t u) :
    ∀ s, OSHasSort M t s → OSHasSort M u s := by
  induction h with
  | root h =>
    obtain ⟨rule, hrule, σ, hσ, rfl, rfl⟩ := h
    rintro s ⟨-, hls⟩
    obtain ⟨-, hwr, hdec⟩ := hR rule hrule
    obtain ⟨g, largs, hg⟩ := lhs_eq_app rule
    obtain ⟨hwr', hler⟩ := os_subst hM hσ _ hwr
    refine ⟨hwr', ?_⟩
    have hlsl : lsort M (Subst.apply σ rule.lhs) = lsort M rule.lhs := by
      rw [hg, Subst.apply_app]
      rfl
    rw [hlsl] at hls
    exact hM.2.1 _ _ _ hler (hM.2.1 _ _ _ hdec hls)
  | arg f pre post _ _ ih =>
    rintro s ⟨hwt, hls⟩
    obtain ⟨hlen, hwf, hle⟩ := oswf_app_iff.1 hwt
    obtain ⟨hwb, hleb⟩ := ih _ ⟨hwf _ _ (getElem?_mid pre post _), hle _ _ (getElem?_mid pre post _)⟩
    refine ⟨.app f _ (by simpa using hlen) ?_ ?_, hls⟩
    · intro i c hc
      by_cases hi : i = pre.length
      · subst hi
        rw [getElem?_mid] at hc
        cases hc
        exact hwb
      · rw [getElem?_mid_ne pre post _ _ hi] at hc
        exact hwf i c hc
    · intro i c hc
      by_cases hi : i = pre.length
      · subst hi
        rw [getElem?_mid] at hc
        cases hc
        exact hleb
      · rw [getElem?_mid_ne pre post _ _ hi] at hc
        exact hle i c hc

theorem oscall_step {M : orderSortedDPData} {R : TRS FreeSym Nat} (hM : OSOrderLaws M)
    (hR : OSRuleLaws M R) {f : FreeSym} {xs ys : List FTerm} (hc : OSCall M (f, xs))
    (h : RArgStep R (OSSubst M) (fun _ _ => True) f xs ys) : OSCall M (f, ys) := by
  refine ⟨?_, pstep_preserve (Q := fun i a => OSHasSort M a (M.arg f i))
    (fun _ _ _ _ hQ hr => os_subject_reduction hM hR hr _ hQ) h hc.2⟩
  obtain ⟨pre, post, a, b, rfl, rfl, -, -⟩ := h
  have h1 : (pre ++ a :: post).length = fArity f := hc.1
  show (pre ++ b :: post).length = fArity f
  simpa using h1

theorem oscall_steps {M : orderSortedDPData} {R : TRS FreeSym Nat} (hM : OSOrderLaws M)
    (hR : OSRuleLaws M R) : ∀ (c : FreeSym × List FTerm) (xs : List FTerm), OSCall M c →
      Relation.ReflTransGen (RArgStep R (OSSubst M) (fun _ _ => True) c.1) c.2 xs →
        OSCall M (c.1, xs) := by
  rintro ⟨f, cargs⟩ xs hc hreach
  induction hreach with
  | refl => exact hc
  | tail _ hstep ih => exact oscall_step hM hR ih hstep

theorem os_calls_of_rhs {M : orderSortedDPData} {R : TRS FreeSym Nat} (hM : OSOrderLaws M)
    (hR : OSRuleLaws M R) :
    ∀ rule ∈ R, ∀ σ : Subst FreeSym Nat, OSSubst M σ → ∀ (g : FreeSym) (targs : List FTerm),
      ActSub (fun _ _ => True) (.app g targs) rule.rhs → IsDefined R g →
        OSCall M (g, Subst.applyList σ targs) := by
  intro rule hrule σ hσ g targs hsub _
  obtain ⟨hlen, hwf, hle⟩ := oswf_app_iff.1 (oswf_of_actSub hsub (hR rule hrule).2.1)
  refine ⟨?_, ?_⟩
  · show (Subst.applyList σ targs).length = fArity g
    rw [Subst.applyList_eq_map, List.length_map]
    exact hlen
  · intro i a' hi
    change (Subst.applyList σ targs)[i]? = some a' at hi
    rw [Subst.applyList_eq_map, List.getElem?_map, Option.map_eq_some_iff] at hi
    obtain ⟨a, ha, rfl⟩ := hi
    obtain ⟨hwa, hlea⟩ := os_subst hM hσ a (hwf i a ha)
    exact ⟨hwa, hM.2.1 _ _ _ hlea (hle i a ha)⟩

theorem os_calls_of_term {M : orderSortedDPData} :
    ∀ (f : FreeSym) (args : List FTerm), OSWF M (.app f args) →
      OSCall M (f, args) ∧ ∀ a ∈ args, OSWF M a := by
  intro f args h
  obtain ⟨hlen, hwf, hle⟩ := oswf_app_iff.1 h
  refine ⟨⟨hlen, fun i a hi => ⟨hwf i a hi, hle i a hi⟩⟩, fun a ha => ?_⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ha
  exact hwf i a hi

/-- Order-sorted chain soundness with the subterm criterion on well-sorted calls, for every
well-formed sort-decreasing system over the free symbols: every well-formed term is
order-sorted terminating. -/
theorem osTerminating_of_criterion {M : orderSortedDPData} {R : TRS FreeSym Nat}
    (hM : OSOrderLaws M) (hR : OSRuleLaws M R) (hcons : Conservative R (fun _ _ => True))
    {proj : FreeSym → Nat}
    (hsc : RSubtermCriterion R (OSSubst M) (fun _ _ => True) (OSCall M) proj) :
    ∀ t, OSWF M t → OSSN M R t :=
  rsn_of_criterion hcons (os_calls_of_rhs hM hR) (oscall_steps hM hR) (OSWF M) os_calls_of_term
    hsc

theorem free_conservative_all : Conservative freeRecursorTRS (fun _ _ => True) := by
  intro rule hrule x hx
  simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
  rcases hrule with rfl | rfl
  · simp only [zeroRule, actSub_var_iff, Term.var.injEq] at hx
    subst hx
    simp [zeroRule, actSub_app_iff, actSub_var_iff, exists_getElem?_cons]
  · simp [succRule, actSub_app_iff, actSub_var_iff, exists_getElem?_cons] at hx ⊢
    omega

/-- Lucas and Meseguer (Order-sorted dependency pairs, PPDP 2008, 108-119): the subsort order is a
partial order and both rules are well formed and sort-decreasing. -/
def orderSortedDPLaws (M : orderSortedDPData) : Prop :=
  OSOrderLaws M ∧ OSRuleLaws M freeRecursorTRS

/-- Acceptance: the subterm criterion on every order-sorted pair instance between well-sorted
calls. -/
def orderSortedDPAccepts (M : orderSortedDPData) : Prop :=
  ∃ proj : FreeSym → Nat,
    RSubtermCriterion freeRecursorTRS (OSSubst M) (fun _ _ => True) (OSCall M) proj

/-- Verdict: escape. -/
def orderSortedDPResult (M : orderSortedDPData) : Prop :=
  orderSortedDPAccepts M ∧ ∀ t, OSWF M t → OSSN M freeRecursorTRS t

theorem orderSortedDP_sound :
    ∀ M, orderSortedDPLaws M → orderSortedDPAccepts M →
      ∀ t, OSWF M t → OSSN M freeRecursorTRS t := by
  rintro M ⟨hM, hR⟩ ⟨proj, hsc⟩
  exact osTerminating_of_criterion hM hR free_conservative_all hsc

/-- The counter projection satisfies the criterion on the order-sorted pair instances. -/
theorem free_os_criterion (M : orderSortedDPData) :
    RSubtermCriterion freeRecursorTRS (OSSubst M) (fun _ _ => True) (OSCall M) muProj := by
  refine ⟨fun _ _ => trivial, ?_⟩
  rintro ⟨f, cargs⟩ ⟨g, dargs⟩ ⟨-, -, rule, hrule, σ, -, largs, hl, hc, targs, hsub, hdef, hd⟩
  simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
  rcases hrule with rfl | rfl
  · simp [zeroRule, actSub_var_iff] at hsub
  · rw [freeRecursorTRS_defined_iff] at hdef
    simp only at hdef
    subst hdef
    simp [succRule, actSub_app_iff, actSub_var_iff, exists_getElem?_cons] at hsub
    subst hsub
    simp only [succRule, Term.app.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    have hc' : cargs = [σ 0, σ 1, .app .succ [σ 2]] := by simpa using hc
    have hd' : dargs = [σ 0, σ 1, σ 2] := by simpa using hd
    subst hc' hd'
    exact ⟨.app .succ [σ 2], σ 2, rfl, rfl, .succ, [σ 2], 0, σ 2, rfl, rfl, trivial, .refl _⟩

/-- Sorts `0 = Zero`, `1 = NzNat`, `2 = Nat`, `3` for values; `Zero < Nat`, `NzNat < Nat`;
`zero : Zero`, `succ : Nat → NzNat`, `recur : 3 × 3 × Nat → 3`, `wrap : 3 × 3 → 3`. -/
def orderSortedDPWitness : orderSortedDPData where
  le := fun s t => decide (s = t ∨ (s = 0 ∧ t = 2) ∨ (s = 1 ∧ t = 2))
  arg := fun f i => match f, i with
    | .recur, 2 => 2
    | .succ, _ => 2
    | _, _ => 3
  res := fun
    | .zero => 0
    | .succ => 1
    | _ => 3
  var := fun
    | 2 => 2
    | _ => 3

theorem orderSortedDPWitness_laws : orderSortedDPLaws orderSortedDPWitness := by
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  intro rule hrule
  simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
  rcases hrule with rfl | rfl
  · exact ⟨oswf_mk rfl ⟨.var 0, rfl, .var 1, rfl, oswf_mk rfl trivial, rfl, trivial⟩, .var 0, rfl⟩
  · exact ⟨oswf_mk rfl ⟨.var 0, rfl, .var 1, rfl, oswf_mk rfl ⟨.var 2, rfl, trivial⟩, rfl, trivial⟩,
      oswf_mk rfl ⟨.var 1, rfl, oswf_mk rfl ⟨.var 0, rfl, .var 1, rfl, .var 2, rfl, trivial⟩, rfl,
        trivial⟩, rfl⟩

theorem orderSortedDPWitness_result : orderSortedDPResult orderSortedDPWitness :=
  ⟨⟨muProj, free_os_criterion _⟩,
    orderSortedDP_sound _ orderSortedDPWitness_laws ⟨muProj, free_os_criterion _⟩⟩

/-- The ill-sorted call `recur(b, s, wrap(x, y))`. -/
def illSortedRecur : FTerm := .app .recur [.var 0, .var 1, .app .wrap [.var 3, .var 4]]

/-- The zero rule uses the subsort `Zero < Nat` and the successor rule `NzNat < Nat`; the call
`recur(b, s, wrap(x, y))` and the zero-arity call `recur()` are not well sorted; the constant
`zero` has least sort `Zero`. -/
theorem orderSortedDPWitness_feature :
    (orderSortedDPWitness.res .zero ≠ orderSortedDPWitness.arg .recur 2 ∧
      orderSortedDPWitness.le (orderSortedDPWitness.res .zero)
        (orderSortedDPWitness.arg .recur 2) = true ∧
      orderSortedDPWitness.res .succ ≠ orderSortedDPWitness.arg .recur 2 ∧
      orderSortedDPWitness.le (orderSortedDPWitness.res .succ)
        (orderSortedDPWitness.arg .recur 2) = true) ∧
    ¬ OSWF orderSortedDPWitness illSortedRecur ∧
    ¬ OSCall orderSortedDPWitness (.recur, [.var 0, .var 1, .app .wrap [.var 3, .var 4]]) ∧
    ¬ OSCall orderSortedDPWitness (.recur, []) ∧
    OSHasSort orderSortedDPWitness (.app .zero []) 0 := by
  refine ⟨by decide, ?_, ?_, ?_, ⟨oswf_mk rfl trivial, rfl⟩⟩
  · intro h
    have := (oswf_app_iff.1 h).2.2 2 _ rfl
    exact absurd this (by decide)
  · intro h
    have := (h.2 2 _ rfl).2
    exact absurd this (by decide)
  · intro h
    exact absurd h.1 (by decide)

/-- The subsort `Zero < Nat` removed, everything else as in the witness. -/
def orderSortedDPMutant : orderSortedDPData :=
  { orderSortedDPWitness with le := fun s t => decide (s = t ∨ (s = 1 ∧ t = 2)) }

/-- Without `Zero < Nat` the zero rule is not well formed. -/
theorem orderSortedDP_mutation : ¬ orderSortedDPLaws orderSortedDPMutant := by
  rintro ⟨-, hR⟩
  have h := (hR zeroRule (by simp [freeRecursorTRS])).1
  have := (oswf_app_iff.1 h).2.2 2 _ rfl
  exact absurd this (by decide)

/-! ## 5. Persistence of termination and the row manySortedPersistence -/

/-! ### Local confluence and normal forms of the free recursor -/

/-- A normal form of the free recursor. -/
def FNF (t : FTerm) : Prop := ∀ u, ¬ Step freeRecursorTRS t u

/-- A chosen normal form reachable from `t`, when one exists. -/
noncomputable def fnf (t : FTerm) : FTerm := by
  classical
  exact if h : ∃ u, StepStar freeRecursorTRS t u ∧ FNF u then h.choose else t

theorem free_not_defined_zero : ¬ IsDefined freeRecursorTRS FreeSym.zero := by
  rw [freeRecursorTRS_defined_iff]
  decide

theorem free_not_defined_succ : ¬ IsDefined freeRecursorTRS FreeSym.succ := by
  rw [freeRecursorTRS_defined_iff]
  decide

theorem free_no_step_zero (u : FTerm) : ¬ Step freeRecursorTRS (.app .zero []) u := by
  intro h
  rcases (step_app_iff _ _ _ u).1 h with hr | ⟨ys, hys, -⟩
  · exact not_rootStep_of_not_defined free_not_defined_zero _ _ hr
  · exact not_argStep_nil _ ys hys

theorem free_step_succ {c u : FTerm} (h : Step freeRecursorTRS (.app .succ [c]) u) :
    ∃ c', Step freeRecursorTRS c c' ∧ u = .app .succ [c'] := by
  rcases (step_app_iff _ _ _ u).1 h with hr | ⟨ys, hys, rfl⟩
  · exact absurd hr (not_rootStep_of_not_defined free_not_defined_succ _ _)
  · rcases (argStep_cons_iff _ _ _ _).1 hys with ⟨c', hc, rfl⟩ | ⟨rest', hr, -⟩
    · exact ⟨c', hc, rfl⟩
    · exact absurd hr (not_argStep_nil _ _)

theorem free_root_shape {t u : FTerm} (h : rootStep freeRecursorTRS t u) :
    (∃ b s, t = .app .recur [b, s, .app .zero []] ∧ u = b) ∨
      (∃ b s n, t = .app .recur [b, s, .app .succ [n]] ∧
        u = .app .wrap [s, .app .recur [b, s, n]]) := by
  obtain ⟨rule, hrule, σ, rfl, rfl⟩ := h
  simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
  rcases hrule with rfl | rfl
  · exact Or.inl ⟨σ 0, σ 1, rfl, rfl⟩
  · exact Or.inr ⟨σ 0, σ 1, σ 2, rfl, rfl⟩

theorem free_root_zero (b s : FTerm) :
    rootStep freeRecursorTRS (.app .recur [b, s, .app .zero []]) b :=
  ⟨zeroRule, by simp [freeRecursorTRS], fun x => match x with | 0 => b | _ => s, rfl, rfl⟩

theorem free_root_succ (b s n : FTerm) :
    rootStep freeRecursorTRS (.app .recur [b, s, .app .succ [n]])
      (.app .wrap [s, .app .recur [b, s, n]]) :=
  ⟨succRule, by simp [freeRecursorTRS], fun x => match x with | 0 => b | 1 => s | _ => n,
    rfl, rfl⟩

theorem free_root_det {t u1 u2 : FTerm} (h1 : rootStep freeRecursorTRS t u1)
    (h2 : rootStep freeRecursorTRS t u2) : u1 = u2 := by
  rcases free_root_shape h1 with ⟨b, s, rfl, rfl⟩ | ⟨b, s, n, rfl, rfl⟩ <;>
    rcases free_root_shape h2 with ⟨b', s', h, rfl⟩ | ⟨b', s', n', h, rfl⟩ <;>
    simp_all

theorem set_mid {α : Type w} (pre post : List α) (a b : α) :
    (pre ++ a :: post).set pre.length b = pre ++ b :: post := by
  induction pre with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem argStep_iff_set {R : TRS FreeSym Nat} {args ys : List FTerm} :
    ArgStep R args ys ↔ ∃ i a b, args[i]? = some a ∧ Step R a b ∧ ys = args.set i b := by
  constructor
  · rintro ⟨pre, post, a, b, rfl, rfl, hab⟩
    exact ⟨pre.length, a, b, getElem?_mid pre post a, hab, (set_mid pre post a b).symm⟩
  · rintro ⟨i, a, b, hi, hab, rfl⟩
    obtain ⟨pre, post, rfl, rfl⟩ := split_of_getElem? hi
    exact ⟨pre, post, a, b, rfl, set_mid pre post a b, hab⟩

theorem free_join_root_arg {f : FreeSym} {args ys : List FTerm} {u1 : FTerm}
    (hr : rootStep freeRecursorTRS (.app f args) u1) (ha : ArgStep freeRecursorTRS args ys) :
    ∃ w, StepStar freeRecursorTRS u1 w ∧ StepStar freeRecursorTRS (.app f ys) w := by
  rcases free_root_shape hr with ⟨b, s, h, hu⟩ | ⟨b, s, n, h, hu⟩
  · subst u1
    simp only [Term.app.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases (argStep_cons_iff _ _ _ _).1 ha with ⟨b', hb, rfl⟩ | ⟨r1, h1, rfl⟩
    · exact ⟨b', .single hb, .single (Step.root (free_root_zero b' s))⟩
    · rcases (argStep_cons_iff _ _ _ _).1 h1 with ⟨s', -, rfl⟩ | ⟨r2, h2, rfl⟩
      · exact ⟨b, StepStar.refl _ _, .single (Step.root (free_root_zero b s'))⟩
      · rcases (argStep_cons_iff _ _ _ _).1 h2 with ⟨z, hz, -⟩ | ⟨r3, h3, -⟩
        · exact absurd hz (free_no_step_zero z)
        · exact absurd h3 (not_argStep_nil _ _)
  · subst u1
    simp only [Term.app.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases (argStep_cons_iff _ _ _ _).1 ha with ⟨b', hb, rfl⟩ | ⟨r1, h1, rfl⟩
    · exact ⟨.app .wrap [s, .app .recur [b', s, n]],
        .single (Step.arg .wrap [s] [] (Step.arg .recur [] [s, n] hb)),
        .single (Step.root (free_root_succ b' s n))⟩
    · rcases (argStep_cons_iff _ _ _ _).1 h1 with ⟨s', hs, rfl⟩ | ⟨r2, h2, rfl⟩
      · exact ⟨.app .wrap [s', .app .recur [b, s', n]],
          Relation.ReflTransGen.head (Step.arg .wrap [] [.app .recur [b, s, n]] hs)
            (.single (Step.arg .wrap [s'] [] (Step.arg .recur [b] [n] hs))),
          .single (Step.root (free_root_succ b s' n))⟩
      · rcases (argStep_cons_iff _ _ _ _).1 h2 with ⟨c', hc, rfl⟩ | ⟨r3, h3, -⟩
        · obtain ⟨n', hn, rfl⟩ := free_step_succ hc
          exact ⟨.app .wrap [s, .app .recur [b, s, n']],
            .single (Step.arg .wrap [s] [] (Step.arg .recur [b, s] [] hn)),
            .single (Step.root (free_root_succ b s n'))⟩
        · exact absurd h3 (not_argStep_nil _ _)

theorem free_join_arg_arg {f : FreeSym} {args ys1 ys2 : List FTerm}
    (ih : ∀ a ∈ args, ∀ t1 t2, Step freeRecursorTRS a t1 → Step freeRecursorTRS a t2 →
      ∃ w, StepStar freeRecursorTRS t1 w ∧ StepStar freeRecursorTRS t2 w)
    (h1 : ArgStep freeRecursorTRS args ys1) (h2 : ArgStep freeRecursorTRS args ys2) :
    ∃ w, StepStar freeRecursorTRS (.app f ys1) w ∧ StepStar freeRecursorTRS (.app f ys2) w := by
  obtain ⟨i, a1, b1, hi, hab1, rfl⟩ := argStep_iff_set.1 h1
  obtain ⟨j, a2, b2, hj, hab2, rfl⟩ := argStep_iff_set.1 h2
  by_cases hij : i = j
  · subst hij
    rw [hi] at hj
    cases hj
    obtain ⟨w0, hw1, hw2⟩ := ih a1 (List.mem_of_getElem? hi) b1 b2 hab1 hab2
    obtain ⟨pre, post, rfl, rfl⟩ := split_of_getElem? hi
    refine ⟨.app f (pre ++ w0 :: post), ?_, ?_⟩
    · rw [set_mid]
      exact StepStar.arg_congr _ f pre post hw1
    · rw [set_mid]
      exact StepStar.arg_congr _ f pre post hw2
  · refine ⟨.app f ((args.set i b1).set j b2), .single ?_, ?_⟩
    · exact (step_app_iff _ _ _ _).2 (Or.inr ⟨_, argStep_iff_set.2
        ⟨j, a2, b2, by rw [List.getElem?_set_ne hij]; exact hj, hab2, rfl⟩, rfl⟩)
    · rw [List.set_comm b1 b2 hij]
      exact .single ((step_app_iff _ _ _ _).2 (Or.inr ⟨_, argStep_iff_set.2
        ⟨i, a1, b1, by rw [List.getElem?_set_ne (Ne.symm hij)]; exact hi, hab1, rfl⟩, rfl⟩))

/-- Local confluence of the free recursor on all first-order terms: its two rules do not
overlap. -/
theorem free_localConfluent : ∀ t t1 t2 : FTerm, Step freeRecursorTRS t t1 →
    Step freeRecursorTRS t t2 → ∃ w, StepStar freeRecursorTRS t1 w ∧ StepStar freeRecursorTRS t2 w := by
  intro t
  induction t using Term.rec' with
  | hvar x => intro t1 t2 h; exact absurd h (not_step_var _ x t1)
  | happ f args ih =>
    intro t1 t2 h1 h2
    rcases (step_app_iff _ _ _ _).1 h1 with hr1 | ⟨ys1, hys1, rfl⟩ <;>
      rcases (step_app_iff _ _ _ _).1 h2 with hr2 | ⟨ys2, hys2, rfl⟩
    · obtain rfl := free_root_det hr1 hr2
      exact ⟨t1, StepStar.refl _ _, StepStar.refl _ _⟩
    · exact free_join_root_arg hr1 hys2
    · obtain ⟨w, hw2, hw1⟩ := free_join_root_arg hr2 hys1
      exact ⟨w, hw1, hw2⟩
    · exact free_join_arg_arg ih hys1 hys2

/-- Newman's lemma on one strongly normalizing term. -/
theorem free_confluent_of_sn {t : FTerm} (ht : SN freeRecursorTRS t) :
    ∀ u1 u2, StepStar freeRecursorTRS t u1 → StepStar freeRecursorTRS t u2 →
      ∃ w, StepStar freeRecursorTRS u1 w ∧ StepStar freeRecursorTRS u2 w := by
  induction ht with
  | intro t _ ih =>
    intro u1 u2 h1 h2
    rcases Relation.ReflTransGen.cases_head h1 with rfl | ⟨t1, ht1, h1'⟩
    · exact ⟨u2, h2, StepStar.refl _ _⟩
    rcases Relation.ReflTransGen.cases_head h2 with rfl | ⟨t2, ht2, h2'⟩
    · exact ⟨u1, StepStar.refl _ _, h1⟩
    obtain ⟨w, hw1, hw2⟩ := free_localConfluent t t1 t2 ht1 ht2
    obtain ⟨w1, hu1, hww1⟩ := ih t1 ht1 u1 w h1' hw1
    obtain ⟨w2, hu2, hw12⟩ := ih t2 ht2 u2 w1 h2' (hw2.trans hww1)
    exact ⟨w2, hu1.trans hw12, hu2⟩

theorem exists_fnf {t : FTerm} (ht : SN freeRecursorTRS t) :
    ∃ u, StepStar freeRecursorTRS t u ∧ FNF u := by
  induction ht with
  | intro t _ ih =>
    by_cases hnf : FNF t
    · exact ⟨t, StepStar.refl _ _, hnf⟩
    · simp only [FNF, not_forall, not_not] at hnf
      obtain ⟨u, hu⟩ := hnf
      obtain ⟨w, huw, hw⟩ := ih u hu
      exact ⟨w, Relation.ReflTransGen.head hu huw, hw⟩

theorem fnf_spec {t : FTerm} (ht : SN freeRecursorTRS t) :
    StepStar freeRecursorTRS t (fnf t) ∧ FNF (fnf t) := by
  have he := exists_fnf ht
  unfold fnf
  rw [dif_pos he]
  exact he.choose_spec

theorem fnf_self_steps {u w : FTerm} (hu : FNF u) (h : StepStar freeRecursorTRS u w) : w = u := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hc, -⟩
  · rfl
  · exact absurd hc (hu c)

/-- Normal forms reachable from a strongly normalizing term are unique. -/
theorem fnf_unique {t u : FTerm} (ht : SN freeRecursorTRS t)
    (htu : StepStar freeRecursorTRS t u) (hu : FNF u) : u = fnf t := by
  obtain ⟨h1, h2⟩ := fnf_spec ht
  obtain ⟨w, hw1, hw2⟩ := free_confluent_of_sn ht u (fnf t) htu h1
  exact (fnf_self_steps hu hw1).symm.trans (fnf_self_steps h2 hw2)

theorem fnf_step {t t' : FTerm} (ht : SN freeRecursorTRS t) (h : Step freeRecursorTRS t t') :
    fnf t' = fnf t := by
  obtain ⟨h1, h2⟩ := fnf_spec (ht.inv h)
  exact fnf_unique ht (Relation.ReflTransGen.head h h1) h2

theorem fnf_var (x : Nat) : fnf (.var x) = .var x := by
  have hnf : FNF (.var x) := fun u h => not_step_var _ x u h
  exact (fnf_unique (Acc.intro _ fun u h => absurd h (not_step_var _ x u)) (StepStar.refl _ _)
    hnf).symm

theorem fnf_zero : fnf (.app .zero []) = .app .zero [] := by
  have hnf : FNF (.app .zero []) := free_no_step_zero
  exact (fnf_unique (Acc.intro _ fun u h => absurd h (free_no_step_zero u)) (StepStar.refl _ _)
    hnf).symm

theorem sn_succ {c : FTerm} (hc : SN freeRecursorTRS c) : SN freeRecursorTRS (.app .succ [c]) :=
  sn_app_of_not_defined free_not_defined_succ [c] (by simpa using hc)

theorem fnf_succ {c : FTerm} (hc : SN freeRecursorTRS c) :
    fnf (.app .succ [c]) = .app .succ [fnf c] := by
  obtain ⟨h1, h2⟩ := fnf_spec hc
  have hnf : FNF (.app .succ [fnf c]) := by
    intro u hu
    obtain ⟨c', hc', -⟩ := free_step_succ hu
    exact h2 c' hc'
  exact (fnf_unique (sn_succ hc) (StepStar.arg_congr _ .succ [] [] h1) hnf).symm

/-! ### Layers, projections and principal subterms -/

section Persistence

variable {S : Type} [DecidableEq S] (A : SortAttach FreeSym S) (inh : S → Nat)

/-- `t` fits a position of sort `s`: its root symbol or variable has sort `s`, and an application
has the declared arity. A term that does not fit its position is a principal subterm (Iwami 2004,
Definition 3.2; Aoto 2001, Definition 3.2). -/
def Fits (s : S) : FTerm → Prop
  | .var x => A.var x = s
  | .app f args => A.res f = s ∧ args.length = fArity f

mutual
/-- The top layer at sort `s`, every principal subterm replaced by the inhabitant variable of the
sort of its position. -/
def proj0 (s : S) : FTerm → FTerm
  | .var x => if A.var x = s then .var x else .var (inh s)
  | .app f args =>
      if A.res f = s ∧ args.length = fArity f then .app f (proj0List f 0 args) else .var (inh s)
/-- `proj0` on the arguments of `f` from position `k` on. -/
def proj0List (f : FreeSym) : Nat → List FTerm → List FTerm
  | _, [] => []
  | k, a :: as => proj0 (A.arg f k) a :: proj0List f (k + 1) as
end

mutual
/-- The top layer at sort `s`, every principal subterm replaced by the `proj0`-layer of its
normal form. -/
noncomputable def proj (s : S) : FTerm → FTerm
  | .var x => if A.var x = s then .var x else .var (inh s)
  | .app f args =>
      if A.res f = s ∧ args.length = fArity f then .app f (projList f 0 args)
      else proj0 A inh s (fnf (.app f args))
/-- `proj` on the arguments of `f` from position `k` on. -/
noncomputable def projList (f : FreeSym) : Nat → List FTerm → List FTerm
  | _, [] => []
  | k, a :: as => proj (A.arg f k) a :: projList f (k + 1) as
end

mutual
/-- The principal subterms of `t` at sort `s`. -/
def aliens (s : S) : FTerm → List FTerm
  | .var x => if A.var x = s then [] else [.var x]
  | .app f args =>
      if A.res f = s ∧ args.length = fArity f then aliensList f 0 args else [.app f args]
/-- The principal subterms of the arguments of `f` from position `k` on. -/
def aliensList (f : FreeSym) : Nat → List FTerm → List FTerm
  | _, [] => []
  | k, a :: as => aliens (A.arg f k) a ++ aliensList f (k + 1) as
end

variable {A inh}

theorem proj0List_length (f : FreeSym) :
    ∀ (k : Nat) (args : List FTerm), (proj0List A inh f k args).length = args.length
  | _, [] => by simp [proj0List]
  | k, _ :: as => by simp [proj0List, proj0List_length f (k + 1) as]

theorem proj0List_getElem? (f : FreeSym) :
    ∀ (k : Nat) (args : List FTerm) (i : Nat),
      (proj0List A inh f k args)[i]? = (args[i]?).map (proj0 A inh (A.arg f (k + i)))
  | _, [], _ => by simp [proj0List]
  | k, a :: as, 0 => by simp [proj0List]
  | k, a :: as, i + 1 => by
      rw [proj0List, List.getElem?_cons_succ, List.getElem?_cons_succ,
        proj0List_getElem? f (k + 1) as i, show k + 1 + i = k + (i + 1) by omega]

theorem projList_length (f : FreeSym) :
    ∀ (k : Nat) (args : List FTerm), (projList A inh f k args).length = args.length
  | _, [] => by simp [projList]
  | k, _ :: as => by simp [projList, projList_length f (k + 1) as]

theorem projList_getElem? (f : FreeSym) :
    ∀ (k : Nat) (args : List FTerm) (i : Nat),
      (projList A inh f k args)[i]? = (args[i]?).map (proj A inh (A.arg f (k + i)))
  | _, [], _ => by simp [projList]
  | k, a :: as, 0 => by simp [projList]
  | k, a :: as, i + 1 => by
      rw [projList, List.getElem?_cons_succ, List.getElem?_cons_succ,
        projList_getElem? f (k + 1) as i, show k + 1 + i = k + (i + 1) by omega]

omit [DecidableEq S] in
theorem hasSort_inh (hinh : ∀ s, A.var (inh s) = s) (s : S) :
    HasSort fArity A (.var (inh s)) s := by
  have := HasSort.var (ar := fArity) (A := A) (inh s)
  rwa [hinh s] at this

/-- Every `proj0`-layer is well sorted of its sort. -/
theorem hasSort_proj0 (hinh : ∀ s, A.var (inh s) = s) :
    ∀ (t : FTerm) (s : S), HasSort fArity A (proj0 A inh s t) s := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
    intro s
    simp only [proj0]
    split_ifs with h
    · rw [← h]
      exact .var x
    · exact hasSort_inh hinh s
  | happ f args ih =>
    intro s
    simp only [proj0]
    split_ifs with h
    · obtain ⟨rfl, hlen⟩ := h
      refine .app f _ (by rw [proj0List_length]; exact hlen) fun i a hi => ?_
      rw [proj0List_getElem?, Option.map_eq_some_iff] at hi
      obtain ⟨b, hb, rfl⟩ := hi
      have := ih b (List.mem_of_getElem? hb) (A.arg f (0 + i))
      simpa using this
    · exact hasSort_inh hinh s

/-- Every `proj`-layer is well sorted of its sort. -/
theorem hasSort_proj (hinh : ∀ s, A.var (inh s) = s) :
    ∀ (t : FTerm) (s : S), HasSort fArity A (proj A inh s t) s := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
    intro s
    simp only [proj]
    split_ifs with h
    · rw [← h]
      exact .var x
    · exact hasSort_inh hinh s
  | happ f args ih =>
    intro s
    simp only [proj]
    split_ifs with h
    · obtain ⟨rfl, hlen⟩ := h
      refine .app f _ (by rw [projList_length]; exact hlen) fun i a hi => ?_
      rw [projList_getElem?, Option.map_eq_some_iff] at hi
      obtain ⟨b, hb, rfl⟩ := hi
      have := ih b (List.mem_of_getElem? hb) (A.arg f (0 + i))
      simpa using this
    · exact hasSort_proj0 hinh _ s

end Persistence

/-- The sort equalities that consistency of an attachment with both rules forces: counters, values
and step arguments each occupy one sort. -/
structure Consistent {S : Type} (A : SortAttach FreeSym S) : Prop where
  e1 : A.arg .recur 0 = A.res .recur
  e2 : A.res .wrap = A.res .recur
  e3 : A.arg .wrap 1 = A.res .recur
  e4 : A.arg .wrap 0 = A.arg .recur 1
  e5 : A.res .zero = A.arg .recur 2
  e6 : A.res .succ = A.arg .recur 2
  e7 : A.arg .succ 0 = A.arg .recur 2

theorem consistent_of_rules {S : Type} {A : SortAttach FreeSym S}
    (h : ∀ rule ∈ freeRecursorTRS, ∃ s, HasSort fArity A rule.lhs s ∧
      HasSort fArity A rule.rhs s) : Consistent A := by
  obtain ⟨s0, hl0, hr0⟩ := h zeroRule (by simp [freeRecursorTRS])
  obtain ⟨s1, hl1, hr1⟩ := h succRule (by simp [freeRecursorTRS])
  simp only [zeroRule, succRule] at hl0 hr0 hl1 hr1
  obtain ⟨hs0, -, hargs0⟩ := hasSort_app_iff.1 hl0
  have hr0' := hasSort_var_iff.1 hr0
  have h00 := hasSort_var_iff.1 (hargs0 0 _ rfl)
  have h02 := (hasSort_app_iff.1 (hargs0 2 _ rfl)).1
  obtain ⟨hs1, -, hargs1⟩ := hasSort_app_iff.1 hl1
  have h11 := hasSort_var_iff.1 (hargs1 1 _ rfl)
  obtain ⟨h12, -, hsucc⟩ := hasSort_app_iff.1 (hargs1 2 _ rfl)
  have hsv := hasSort_var_iff.1 (hsucc 0 _ rfl)
  obtain ⟨hw, -, hwargs⟩ := hasSort_app_iff.1 hr1
  have hw0 := hasSort_var_iff.1 (hwargs 0 _ rfl)
  obtain ⟨hw1, -, hrargs⟩ := hasSort_app_iff.1 (hwargs 1 _ rfl)
  have hr2 := hasSort_var_iff.1 (hrargs 2 _ rfl)
  exact ⟨by rw [h00, ← hr0', hs0], by rw [← hw, hs1], hw1, by rw [hw0, h11], h02.symm, h12.symm,
    by rw [hsv, hr2]⟩

/-- The order on principal subterms: `a'` lies below the strongly normalizing term `a` through
rewrite steps and passages to arguments. -/
def AlienLt (a' a : FTerm) : Prop :=
  SN freeRecursorTRS a ∧ Relation.TransGen (StepOrSub freeRecursorTRS) a' a

theorem alienLt_wf : WellFounded AlienLt := by
  constructor
  intro a
  by_cases ha : SN freeRecursorTRS a
  · exact Subrelation.accessible (fun h => h.2) (acc_stepOrSub_of_sn ha).transGen
  · exact Acc.intro a fun a' h => absurd h.1 ha

theorem sn_of_isSubterm {w t : FTerm} (h : IsSubterm w t) (ht : SN freeRecursorTRS t) :
    SN freeRecursorTRS w := by
  induction ht generalizing w with
  | intro t _ ih =>
    exact Acc.intro w fun w' hw' => by
      obtain ⟨t', ht', hs⟩ := step_lift_subterm h hw'
      exact ih t' ht' hs

theorem fits_change {S : Type} {A : SortAttach FreeSym S} {t t' : FTerm}
    (h : Step freeRecursorTRS t t') {s : S} (h1 : ¬ Fits A s t) (h2 : Fits A s t') :
    s ≠ A.res .recur := by
  intro hs
  subst hs
  cases h with
  | root hr =>
    rcases free_root_shape hr with ⟨b, s0, rfl, -⟩ | ⟨b, s0, n, rfl, -⟩
    · exact h1 ⟨rfl, rfl⟩
    · exact h1 ⟨rfl, rfl⟩
  | arg f pre post hab =>
    apply h1
    simp only [Fits, List.length_append, List.length_cons] at h2 ⊢
    exact h2

section Persistence

variable {S : Type} [DecidableEq S] {A : SortAttach FreeSym S} {inh : S → Nat}

theorem proj_fit_app {s : S} {f : FreeSym} {args : List FTerm} (hs : A.res f = s)
    (hlen : args.length = fArity f) :
    proj A inh s (.app f args) = .app f (projList A inh f 0 args) := by
  simp only [proj, if_pos (And.intro hs hlen)]

theorem proj0_fit_app {s : S} {f : FreeSym} {args : List FTerm} (hs : A.res f = s)
    (hlen : args.length = fArity f) :
    proj0 A inh s (.app f args) = .app f (proj0List A inh f 0 args) := by
  simp only [proj0, if_pos (And.intro hs hlen)]

theorem proj_nofit {s : S} {t : FTerm} (h : ¬ Fits A s t) :
    proj A inh s t = proj0 A inh s (fnf t) := by
  cases t with
  | var x =>
    simp only [Fits] at h
    simp only [proj, proj0, if_neg h, fnf_var]
  | app f args =>
    simp only [Fits] at h
    simp only [proj, if_neg h]

theorem aliens_nofit {s : S} {t : FTerm} (h : ¬ Fits A s t) : aliens A s t = [t] := by
  cases t with
  | var x =>
    simp only [Fits] at h
    simp only [aliens, if_neg h]
  | app f args =>
    simp only [Fits] at h
    simp only [aliens, if_neg h]

theorem aliens_fit_app {s : S} {f : FreeSym} {args : List FTerm} (hs : A.res f = s)
    (hlen : args.length = fArity f) : aliens A s (.app f args) = aliensList A f 0 args := by
  simp only [aliens, if_pos (And.intro hs hlen)]

theorem projList_mid (f : FreeSym) : ∀ (k : Nat) (pre post : List FTerm) (a : FTerm),
    projList A inh f k (pre ++ a :: post) =
      projList A inh f k pre ++
        proj A inh (A.arg f (k + pre.length)) a :: projList A inh f (k + pre.length + 1) post
  | k, [], post, a => by simp [projList]
  | k, x :: xs, post, a => by
      simp only [List.cons_append, projList, projList_mid f (k + 1) xs post a, List.length_cons]
      rw [show k + 1 + xs.length = k + (xs.length + 1) by omega]

theorem aliensList_mid (f : FreeSym) : ∀ (k : Nat) (pre post : List FTerm) (a : FTerm),
    aliensList A f k (pre ++ a :: post) =
      aliensList A f k pre ++
        (aliens A (A.arg f (k + pre.length)) a ++ aliensList A f (k + pre.length + 1) post)
  | k, [], post, a => by simp [aliensList]
  | k, x :: xs, post, a => by
      simp only [List.cons_append, aliensList, aliensList_mid f (k + 1) xs post a,
        List.length_cons, List.append_assoc]
      rw [show k + 1 + xs.length = k + (xs.length + 1) by omega]

theorem aliensList_mem {f : FreeSym} {P : FTerm → FTerm → Prop} :
    ∀ (k : Nat) (args : List FTerm) (B : FTerm),
      (∀ a ∈ args, ∀ s, B ∈ aliens A s a → P B a) → B ∈ aliensList A f k args →
        ∃ a ∈ args, P B a
  | _, [], _, _, h => by simp [aliensList] at h
  | k, x :: xs, B, hP, h => by
      simp only [aliensList, List.mem_append] at h
      rcases h with h | h
      · exact ⟨x, List.mem_cons_self, hP x List.mem_cons_self _ h⟩
      · obtain ⟨a, ha, hPa⟩ := aliensList_mem (k + 1) xs B
          (fun a ha => hP a (List.mem_cons_of_mem _ ha)) h
        exact ⟨a, List.mem_cons_of_mem _ ha, hPa⟩

/-- Principal subterms are subterms. -/
theorem aliens_isSubterm : ∀ (t : FTerm) (s : S) (B : FTerm), B ∈ aliens A s t → IsSubterm B t := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
    intro s B hB
    simp only [aliens] at hB
    split_ifs at hB with h
    · simp at hB
    · simp only [List.mem_singleton] at hB
      subst hB
      exact .refl _
  | happ f args ih =>
    intro s B hB
    simp only [aliens] at hB
    split_ifs at hB with h
    · obtain ⟨a, ha, hsub⟩ := aliensList_mem (P := fun B a => IsSubterm B a) 0 args B
        (fun a ha s' hB' => ih a ha s' B hB') hB
      exact .arg f args ha hsub
    · simp only [List.mem_singleton] at hB
      subst hB
      exact .refl _

/-- The principal subterms of a fitting term lie strictly below it. -/
theorem aliens_fit_below {s : S} {t B : FTerm} (hfit : Fits A s t) (hB : B ∈ aliens A s t) :
    Relation.TransGen (StepOrSub freeRecursorTRS) B t := by
  cases t with
  | var x =>
    simp only [Fits] at hfit
    simp [aliens, hfit] at hB
  | app f args =>
    obtain ⟨hs, hlen⟩ := hfit
    rw [aliens_fit_app hs hlen] at hB
    obtain ⟨a, ha, hsub⟩ := aliensList_mem (P := fun B a => IsSubterm B a) 0 args B
      (fun a _ s' hB' => aliens_isSubterm a s' B hB') hB
    exact Relation.TransGen.tail' hsub.reflTransGen (Or.inr ⟨f, args, rfl, ha⟩)

/-- A term fitting a sort other than the value sort is a constructor layer, so its `proj`-layer
is the `proj0`-layer of its normal form. -/
theorem proj_eq_proj0_fnf (hc : Consistent A) {s : S} (hs : s ≠ A.res .recur) :
    ∀ c : FTerm, SN freeRecursorTRS c → Fits A s c → proj A inh s c = proj0 A inh s (fnf c) := by
  intro c
  induction c using Term.rec' with
  | hvar x =>
    intro _ hfit
    simp only [Fits] at hfit
    simp only [proj, proj0, if_pos hfit, fnf_var]
  | happ f args ih =>
    intro hsn hfit
    obtain ⟨hfs, hlen⟩ := hfit
    cases f with
    | zero =>
      have hnil : args = [] := List.eq_nil_of_length_eq_zero hlen
      subst hnil
      rw [fnf_zero, proj_fit_app hfs hlen, proj0_fit_app hfs hlen]
      simp [projList, proj0List]
    | succ =>
      rcases args with _ | ⟨c1, _ | ⟨c2, rest⟩⟩
      · simp [fArity] at hlen
      · have hc1 : SN freeRecursorTRS c1 := sn_arg hsn (List.mem_singleton.2 rfl)
        have hsucc0 : A.arg .succ 0 = s := by rw [hc.e7, ← hc.e6, hfs]
        rw [fnf_succ hc1, proj_fit_app hfs hlen, proj0_fit_app hfs rfl]
        simp only [projList, proj0List, hsucc0]
        by_cases hfit1 : Fits A s c1
        · rw [ih c1 (List.mem_singleton.2 rfl) hc1 hfit1]
        · rw [proj_nofit hfit1]
      · simp [fArity] at hlen
    | wrap => exact absurd (hfs.symm.trans hc.e2) hs
    | recur => exact absurd hfs.symm hs

/-- A step inside a principal subterm at the top: the projection does not change and the
principal subterms decrease. -/
theorem alien_case (hc : Consistent A) {t t' : FTerm} (h : Step freeRecursorTRS t t') {s : S}
    (hfit : ¬ Fits A s t) (ht : SN freeRecursorTRS t) :
    (∀ B ∈ aliens A s t', SN freeRecursorTRS B) ∧ proj A inh s t = proj A inh s t' ∧
      Relation.CutExpand AlienLt (aliens A s t' : Multiset FTerm) (aliens A s t) := by
  have ht' : SN freeRecursorTRS t' := ht.inv h
  have hnf := fnf_step ht h
  rw [aliens_nofit hfit, proj_nofit hfit]
  by_cases hfit' : Fits A s t'
  · have hs := fits_change h hfit hfit'
    refine ⟨fun B hB => sn_of_isSubterm (aliens_isSubterm t' s B hB) ht', ?_, ?_⟩
    · rw [proj_eq_proj0_fnf hc hs t' ht' hfit', hnf]
    · rw [Multiset.coe_singleton]
      exact Relation.cutExpand_singleton fun B hB =>
        ⟨ht, (aliens_fit_below hfit' (Multiset.mem_coe.1 hB)).tail (Or.inl h)⟩
  · rw [aliens_nofit hfit', proj_nofit hfit', hnf]
    refine ⟨fun B hB => ?_, rfl, ?_⟩
    · simp only [List.mem_singleton] at hB
      subst hB
      exact ht'
    · rw [Multiset.coe_singleton, Multiset.coe_singleton]
      exact Relation.cutExpand_singleton_singleton ⟨ht, .single (Or.inl h)⟩

/-- The simulation: every unsorted step either rewrites the projection by a step of the sorted
system, or keeps the projection and decreases the principal subterms. -/
theorem simulation (hc : Consistent A) {t t' : FTerm} (h : Step freeRecursorTRS t t') :
    ∀ s : S, (∀ B ∈ aliens A s t, SN freeRecursorTRS B) →
      (∀ B ∈ aliens A s t', SN freeRecursorTRS B) ∧
        (Step freeRecursorTRS (proj A inh s t) (proj A inh s t') ∨
          (proj A inh s t = proj A inh s t' ∧
            Relation.CutExpand AlienLt (aliens A s t' : Multiset FTerm) (aliens A s t))) := by
  induction h with
  | @root t0 t1 hr =>
    intro s hSN
    by_cases hfit : Fits A s t0
    · rcases free_root_shape hr with ⟨b, s0, ht, hu⟩ | ⟨b, s0, n, ht, hu⟩
      · rw [ht] at hfit hSN ⊢
        rw [hu]
        obtain ⟨hs, -⟩ := hfit
        subst hs
        have hzero : proj A inh (A.arg .recur 2) (.app .zero []) = .app .zero [] := by
          rw [proj_fit_app hc.e5 rfl]
          simp [projList]
        have hal : aliens A (A.res .recur) (.app .recur [b, s0, .app .zero []]) =
            aliens A (A.res .recur) b ++ (aliens A (A.arg .recur 1) s0 ++
              (aliens A (A.arg .recur 2) (.app .zero []) ++ [])) := by
          rw [aliens_fit_app rfl rfl]
          simp only [aliensList, hc.e1]
        refine ⟨fun B hB => hSN B (by rw [hal]; exact List.mem_append_left _ hB), Or.inl ?_⟩
        rw [proj_fit_app rfl rfl]
        simp only [projList, hzero, hc.e1]
        exact Step.root (free_root_zero _ _)
      · rw [ht] at hfit hSN ⊢
        rw [hu]
        obtain ⟨hs, -⟩ := hfit
        subst hs
        have hsucc : proj A inh (A.arg .recur 2) (.app .succ [n]) =
            .app .succ [proj A inh (A.arg .recur 2) n] := by
          rw [proj_fit_app hc.e6 rfl]
          simp only [projList, hc.e7]
        have hrec : proj A inh (A.res .recur) (.app .recur [b, s0, n]) =
            .app .recur [proj A inh (A.arg .recur 0) b, proj A inh (A.arg .recur 1) s0,
              proj A inh (A.arg .recur 2) n] := by
          rw [proj_fit_app rfl rfl]
          simp only [projList]
        have hal : aliens A (A.res .recur) (.app .recur [b, s0, .app .succ [n]]) =
            aliens A (A.arg .recur 0) b ++ (aliens A (A.arg .recur 1) s0 ++
              ((aliens A (A.arg .recur 2) n ++ []) ++ [])) := by
          rw [aliens_fit_app rfl rfl]
          simp only [aliensList]
          rw [aliens_fit_app hc.e6 rfl]
          simp only [aliensList, hc.e7]
        have hal' : aliens A (A.res .recur) (.app .wrap [s0, .app .recur [b, s0, n]]) =
            aliens A (A.arg .recur 1) s0 ++ ((aliens A (A.arg .recur 0) b ++
              (aliens A (A.arg .recur 1) s0 ++ (aliens A (A.arg .recur 2) n ++ []))) ++ []) := by
          rw [aliens_fit_app hc.e2 rfl]
          simp only [aliensList, hc.e4, hc.e3]
          rw [aliens_fit_app rfl rfl]
          simp only [aliensList]
        refine ⟨fun B hB => hSN B ?_, Or.inl ?_⟩
        · rw [hal'] at hB
          rw [hal]
          simp only [List.mem_append, List.append_nil] at hB ⊢
          tauto
        · rw [proj_fit_app rfl rfl, proj_fit_app hc.e2 rfl]
          simp only [projList, hsucc, hc.e4, hc.e3, hrec]
          exact Step.root (free_root_succ _ _ _)
    · obtain ⟨h1, h2, h3⟩ := alien_case hc (Step.root hr) hfit
        (hSN _ (by rw [aliens_nofit hfit]; exact List.mem_singleton.2 rfl))
      exact ⟨h1, Or.inr ⟨h2, h3⟩⟩
  | @arg f pre post a b hab ih =>
    intro s hSN
    by_cases hfit : Fits A s (.app f (pre ++ a :: post))
    · obtain ⟨hs, hlen⟩ := hfit
      have hlen' : (pre ++ b :: post).length = fArity f := by simpa using hlen
      have hal : aliens A s (.app f (pre ++ a :: post)) = aliensList A f 0 pre ++
          (aliens A (A.arg f pre.length) a ++ aliensList A f (pre.length + 1) post) := by
        rw [aliens_fit_app hs hlen, aliensList_mid]
        simp only [Nat.zero_add]
      have hal' : aliens A s (.app f (pre ++ b :: post)) = aliensList A f 0 pre ++
          (aliens A (A.arg f pre.length) b ++ aliensList A f (pre.length + 1) post) := by
        rw [aliens_fit_app hs hlen', aliensList_mid]
        simp only [Nat.zero_add]
      obtain ⟨hSNb, hcase⟩ := ih (A.arg f pre.length) fun B hB =>
        hSN B (by rw [hal]; exact List.mem_append_right _ (List.mem_append_left _ hB))
      refine ⟨fun B hB => ?_, ?_⟩
      · rw [hal'] at hB
        simp only [List.mem_append] at hB
        rcases hB with hB | hB | hB
        · exact hSN B (by rw [hal]; exact List.mem_append_left _ hB)
        · exact hSNb B hB
        · exact hSN B (by rw [hal]; exact List.mem_append_right _ (List.mem_append_right _ hB))
      · rw [proj_fit_app hs hlen, proj_fit_app hs hlen', projList_mid, projList_mid]
        simp only [Nat.zero_add]
        rcases hcase with hstep | ⟨heq, hce⟩
        · exact Or.inl (Step.arg f _ _ hstep)
        · refine Or.inr ⟨by rw [heq], ?_⟩
          rw [hal, hal']
          simp only [← Multiset.coe_add]
          exact (Relation.cutExpand_add_left _).2 ((Relation.cutExpand_add_right _).2 hce)
    · obtain ⟨h1, h2, h3⟩ := alien_case hc (Step.arg f pre post hab) hfit
        (hSN _ (by rw [aliens_nofit hfit]; exact List.mem_singleton.2 rfl))
      exact ⟨h1, Or.inr ⟨h2, h3⟩⟩

end Persistence

/-! ## 16. Many-sorted persistence: the lifting -/

/-- The invariant of the layer induction: every mismatched principal subterm of `t` at sort `s`
terminates. -/
def persistenceAliensSN {S : Type} [DecidableEq S]
    (A : SortAttach FreeSym S) (s : S) (t : FTerm) : Prop :=
  ∀ B ∈ aliens A s t, SN freeRecursorTRS B

/-- MS-1. The reversed sorted step relation is globally well founded. A term that fits no sort has no
sorted step, because `SortedStep` restricts every source to a well-sorted term, and a well-sorted
source is accessible by the premise. -/
theorem persistence_sorted_wf
    {sigma : Type u} {S : Type}
    (ar : sigma → Nat) (A : SortAttach sigma S) (R : TRS sigma Nat)
    (hST : SortedTerminates ar A R) :
    WellFounded (fun y x => SortedStep ar A R x y) := by
  classical
  refine ⟨fun t => ?_⟩
  by_cases ht : ∃ s, HasSort ar A t s
  · obtain ⟨s, hs⟩ := ht
    exact hST t s hs
  · exact Acc.intro t (fun y hty => False.elim (ht hty.1))

/-- MS-2. Accessibility transfers along an invariant with a strictly decreasing measure. -/
theorem persistence_sn_of_invariant_measure
    {α : Type u} {β : Type v}
    (step : α → α → Prop) (I : α → Prop)
    (measure : α → β) (lt : β → β → Prop)
    (hwf : WellFounded lt)
    (hsim : ∀ {x y}, I x → step x y → I y ∧ lt (measure y) (measure x)) :
    ∀ x, I x → Acc (fun y x => step x y) x := by
  have aux : ∀ q, Acc lt q → ∀ x, measure x = q → I x → Acc (fun y x => step x y) x := by
    intro q hq
    induction hq with
    | intro q _ ih =>
      intro x hx hI
      refine Acc.intro x ?_
      intro y hxy
      obtain ⟨hIy, hlt⟩ := hsim hI hxy
      have hlt' : lt (measure y) q := by simpa only [hx] using hlt
      exact ih (measure y) hlt' y rfl hIy
  intro x hx
  exact aux (measure x) (hwf.apply (measure x)) x rfl hx

/-- MS-2. The lexicographic specialization: the projection decreases, or it stays equal and the
residual strictly decreases. -/
theorem persistence_sn_of_invariant_lex
    {α : Type u} {β : Type v} {γ : Type w}
    (step : α → α → Prop) (I : α → Prop)
    (project : α → β) (residual : α → γ)
    (first : β → β → Prop) (second : γ → γ → Prop)
    (hfirst : WellFounded first) (hsecond : WellFounded second)
    (hsim : ∀ {x y}, I x → step x y →
      I y ∧ (first (project y) (project x) ∨
        (project y = project x ∧ second (residual y) (residual x)))) :
    ∀ x, I x → Acc (fun y x => step x y) x := by
  have hlex : WellFounded (Prod.Lex first second) := by
    refine ⟨?_⟩
    rintro ⟨b, c⟩
    exact Prod.lexAccessible (hfirst.apply b) (fun d => hsecond.apply d) c
  apply persistence_sn_of_invariant_measure step I
    (fun x => (project x, residual x)) (Prod.Lex first second) hlex
  intro x y hx hxy
  obtain ⟨hy, hprogress⟩ := hsim hx hxy
  exact ⟨hy, Prod.lex_def.mpr hprogress⟩

/-- MS-3. The layer theorem: under the invariant that every mismatched principal subterm terminates,
the term terminates, ranked by the projection and the multiset of mismatched subterms. -/
theorem persistence_layer_sn
    {S : Type} [DecidableEq S]
    (A : SortAttach FreeSym S) (inh : S → Nat)
    (hc : Consistent A) (hinh : ∀ s, A.var (inh s) = s)
    (hST : SortedTerminates fArity A freeRecursorTRS)
    (s : S) (t : FTerm) (hgood : persistenceAliensSN A s t) :
    SN freeRecursorTRS t := by
  refine persistence_sn_of_invariant_lex
    (step := Step freeRecursorTRS)
    (I := persistenceAliensSN A s)
    (project := proj A inh s)
    (residual := fun x => (aliens A s x : Multiset FTerm))
    (first := fun y x => SortedStep fArity A freeRecursorTRS x y)
    (second := Relation.CutExpand AlienLt)
    (persistence_sorted_wf fArity A freeRecursorTRS hST)
    (WellFounded.cutExpand alienLt_wf) ?_ t hgood
  intro x y hx hxy
  obtain ⟨hy, hp⟩ := simulation (A := A) (inh := inh) hc hxy s hx
  refine ⟨hy, ?_⟩
  rcases hp with hp | ⟨heq, hcut⟩
  · exact Or.inl ⟨⟨s, hasSort_proj (A := A) (inh := inh) hinh x s⟩, hp⟩
  · exact Or.inr ⟨heq.symm, hcut⟩

/-- MS-4. An argument step preserves the length of the argument list. -/
theorem persistence_argStep_length
    {sigma : Type u} {nu : Type v} {R : TRS sigma nu}
    {xs ys : List (Term sigma nu)} (h : ArgStep R xs ys) :
    xs.length = ys.length := by
  obtain ⟨pre, post, a, b, rfl, rfl, _⟩ := h
  simp only [List.length_append, List.length_cons]

/-- MS-4. A root step at an application keeps the argument length at the declared arity. -/
theorem persistence_root_source_arity
    {f : FreeSym} {args : List FTerm} {z : FTerm}
    (h : rootStep freeRecursorTRS (.app f args) z) :
    args.length = fArity f := by
  rcases free_root_shape h with hzero | hsucc
  · obtain ⟨b, s, heq, _⟩ := hzero
    obtain ⟨rfl, rfl⟩ := Term.app.inj heq
    rfl
  · obtain ⟨b, s, n, heq, _⟩ := hsucc
    obtain ⟨rfl, rfl⟩ := Term.app.inj heq
    rfl

/-- MS-4. A wrong-arity application terminates from its arguments: it has no root step, and every
argument step keeps the arity wrong. -/
theorem persistence_bad_arity_sn
    (f : FreeSym) (args : List FTerm)
    (hlen : args.length ≠ fArity f)
    (hargs : ∀ a ∈ args, SN freeRecursorTRS a) :
    SN freeRecursorTRS (.app f args) := by
  have aux : ∀ xs : List FTerm,
      Acc (fun ys xs => ArgStep freeRecursorTRS xs ys) xs →
      xs.length ≠ fArity f → SN freeRecursorTRS (.app f xs) := by
    intro xs hacc
    induction hacc with
    | intro xs _ ih =>
      intro hbad
      refine Acc.intro _ ?_
      intro z hz
      rcases (step_app_iff freeRecursorTRS f xs z).1 hz with hroot | ⟨ys, hys, rfl⟩
      · exact False.elim (hbad (persistence_root_source_arity hroot))
      · exact ih ys hys (fun heq => hbad ((persistence_argStep_length hys).trans heq))
  exact aux args (accArgs args hargs) hlen

/-- MS-5. The alien invariant of a fitting application follows from termination of its arguments. -/
theorem persistence_aliens_sn_of_args
    {S : Type} [DecidableEq S]
    (A : SortAttach FreeSym S) (f : FreeSym) (args : List FTerm)
    (hlen : args.length = fArity f)
    (hargs : ∀ a ∈ args, SN freeRecursorTRS a) :
    persistenceAliensSN A (A.res f) (.app f args) := by
  intro B hB
  rw [aliens_fit_app (A := A) (f := f) rfl hlen] at hB
  obtain ⟨a, ha, hsub⟩ :=
    aliensList_mem (A := A) (f := f) (P := fun B a => IsSubterm B a) 0 args B
      (fun a _ s haB => aliens_isSubterm (A := A) a s B haB) hB
  exact sn_of_isSubterm hsub (hargs a ha)

/-- MS-5. Every free-recursor term terminates, from sorted termination of the same attachment. -/
theorem freeRecursor_sn_of_sorted
    {S : Type} [DecidableEq S]
    (A : SortAttach FreeSym S) (inh : S → Nat)
    (hc : Consistent A) (hinh : ∀ s, A.var (inh s) = s)
    (hST : SortedTerminates fArity A freeRecursorTRS) :
    ∀ t : FTerm, SN freeRecursorTRS t := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
    exact Acc.intro _ (fun y h => False.elim (not_step_var _ x y h))
  | happ f args ih =>
    by_cases hlen : args.length = fArity f
    · exact persistence_layer_sn A inh hc hinh hST (A.res f) (.app f args)
        (persistence_aliens_sn_of_args A f args hlen ih)
    · exact persistence_bad_arity_sn f args hlen ih

/-- MS-5. The sorted and the unsorted termination of the free recursor are equivalent. -/
theorem freeRecursor_sorted_iff_sn
    {S : Type} [DecidableEq S]
    (A : SortAttach FreeSym S) (inh : S → Nat)
    (hc : Consistent A) (hinh : ∀ s, A.var (inh s) = s) :
    SortedTerminates fArity A freeRecursorTRS ↔
      ∀ t : FTerm, SN freeRecursorTRS t := by
  refine ⟨freeRecursor_sn_of_sorted A inh hc hinh, ?_⟩
  intro hAll
  have hsub : ∀ x, Acc (fun y x => Step freeRecursorTRS x y) x →
      Acc (fun y x => SortedStep fArity A freeRecursorTRS x y) x := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      exact Acc.intro x (fun y hy => ih y hy.2)
  intro t s _
  exact hsub t (hAll t)

/-! ## 16.8 MS-5 strengthening: only sorts used by the rules need replacements -/

/-- A sort is active when some symbol result or some declared argument position has it. -/
def persistenceActiveSort {S : Type} (A : SortAttach FreeSym S) (s : S) : Prop :=
  (∃ f, A.res f = s) ∨ (∃ f i, i < fArity f ∧ A.arg f i = s)

/-- An inhabitant variable for an active sort: variable 0 for the value sort, variable 1 for the
frame sort, and variable 2 otherwise. Which of the three coincides with the active sort is decided
by the rules. -/
def persistenceActiveInh {S : Type} [DecidableEq S]
    (A : SortAttach FreeSym S) (s : S) : Nat :=
  if s = A.var 0 then 0 else if s = A.var 1 then 1 else 2

/-- MS-5. The layer theorem with the global inhabitance equation replaced by typing of the
projection at the fixed sort, which is what the active-sort construction supplies. The premise is
typing, not termination. -/
theorem persistence_layer_sn_of_typed_projection
    {S : Type} [DecidableEq S]
    (A : SortAttach FreeSym S) (inh : S → Nat) (s : S)
    (hc : Consistent A)
    (hproj : ∀ x : FTerm, HasSort fArity A (proj A inh s x) s)
    (hST : SortedTerminates fArity A freeRecursorTRS)
    (t : FTerm) (hgood : persistenceAliensSN A s t) :
    SN freeRecursorTRS t := by
  refine persistence_sn_of_invariant_lex
    (step := Step freeRecursorTRS)
    (I := persistenceAliensSN A s)
    (project := proj A inh s)
    (residual := fun x => (aliens A s x : Multiset FTerm))
    (first := fun y x => SortedStep fArity A freeRecursorTRS x y)
    (second := Relation.CutExpand AlienLt)
    (persistence_sorted_wf fArity A freeRecursorTRS hST)
    (WellFounded.cutExpand alienLt_wf) ?_ t hgood
  intro x y hx hxy
  obtain ⟨hy, hp⟩ := simulation (A := A) (inh := inh) hc hxy s hx
  refine ⟨hy, ?_⟩
  rcases hp with hp | ⟨heq, hcut⟩
  · exact Or.inl ⟨⟨s, hproj x⟩, hp⟩
  · exact Or.inr ⟨heq.symm, hcut⟩

/-! ## MS-6: native two-sort datum and the independent sorted example -/

/-- A many-sorted persistence datum: a finite sort index, an attachment, and one
inhabitant counter used to instantiate every sort for the alignment map. -/
structure manySortedPersistenceData where
  sortCount : Nat
  attach : SortAttach FreeSym (Fin sortCount)
  inh : Fin sortCount → Nat

/-- The laws the row requires: inhabitation of every sort by a term, and a
sort carrying both sides of every rule. -/
def manySortedPersistenceLaws (M : manySortedPersistenceData) : Prop :=
  (∀ s, M.attach.var (M.inh s) = s) ∧
  (∀ rule ∈ freeRecursorTRS, ∃ s,
    HasSort fArity M.attach rule.lhs s ∧
    HasSort fArity M.attach rule.rhs s)

/-- What the row's soundness theorem delivers for a datum: sorted termination. -/
def manySortedPersistenceAccepts (M : manySortedPersistenceData) : Prop :=
  SortedTerminates fArity M.attach freeRecursorTRS

/-- The native two-sort attachment used for the recursor: `recur` and `succ`
consume a counter third/first argument; `zero` and `succ` produce one; only
variable `2` is a counter. -/
def persistenceTwoSortAttach : SortAttach FreeSym (Fin 2) where
  arg := fun f i => match f, i with
    | .recur, 2 => 1
    | .succ, _ => 1
    | _, _ => 0
  res := fun f => match f with
    | .zero => 1
    | .succ => 1
    | _ => 0
  var := fun x => if x = 2 then 1 else 0

/-- The two-sort witness datum: counters inhabit variable `2`, data inhabit
variable `0`. -/
def manySortedPersistenceWitness : manySortedPersistenceData where
  sortCount := 2
  attach := persistenceTwoSortAttach
  inh := fun s => if s = 0 then 0 else 2

theorem persistence_getElem?_none (l : List FTerm) (i : Nat) (h : l.length ≤ i) :
    l[i]? = none := by
  induction l generalizing i with
  | nil => rfl
  | cons a as ih =>
      cases i with
      | zero => simp at h
      | succ i =>
          simp only [List.length_cons] at h
          simpa using ih i (by omega)

theorem manySortedPersistenceWitness_inh (s : Fin 2) :
    persistenceTwoSortAttach.var (manySortedPersistenceWitness.inh s) = s := by
  fin_cases s <;> decide

theorem manySortedPersistenceWitness_zeroRule :
    ∃ s, HasSort fArity persistenceTwoSortAttach zeroRule.lhs s ∧
      HasSort fArity persistenceTwoSortAttach zeroRule.rhs s := by
  refine ⟨0, ?_, ?_⟩
  · show HasSort fArity persistenceTwoSortAttach
      (.app .recur [.var 0, .var 1, .app .zero []]) 0
    rw [hasSort_app_iff]
    refine ⟨rfl, rfl, ?_⟩
    intro i a hi
    match i with
    | 0 =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        rw [← hi, hasSort_var_iff]
        decide
    | 1 =>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq] at hi
        rw [← hi, hasSort_var_iff]
        decide
    | 2 =>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq] at hi
        rw [← hi, hasSort_app_iff]
        refine ⟨rfl, rfl, ?_⟩
        intro j b hj
        simp at hj
    | i + 3 =>
        have hnone : ([.var (0 : Nat), .var 1, .app .zero []] : List FTerm)[i + 3]? =
            none := persistence_getElem?_none _ _ (by simp)
        rw [hnone] at hi
        exact absurd hi (by simp)
  · show HasSort fArity persistenceTwoSortAttach (.var 0) 0
    rw [hasSort_var_iff]
    decide

theorem manySortedPersistenceWitness_succRule :
    ∃ s, HasSort fArity persistenceTwoSortAttach succRule.lhs s ∧
      HasSort fArity persistenceTwoSortAttach succRule.rhs s := by
  refine ⟨0, ?_, ?_⟩
  · show HasSort fArity persistenceTwoSortAttach
      (.app .recur [.var 0, .var 1, .app .succ [.var 2]]) 0
    rw [hasSort_app_iff]
    refine ⟨rfl, rfl, ?_⟩
    intro i a hi
    match i with
    | 0 =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        rw [← hi, hasSort_var_iff]
        decide
    | 1 =>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq] at hi
        rw [← hi, hasSort_var_iff]
        decide
    | 2 =>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq] at hi
        rw [← hi, hasSort_app_iff]
        refine ⟨rfl, rfl, ?_⟩
        intro j b hj
        match j with
        | 0 =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
            rw [← hj, hasSort_var_iff]
            decide
        | j + 1 =>
            have hnone : ([.var (2 : Nat)] : List FTerm)[j + 1]? = none :=
              persistence_getElem?_none _ _ (by simp)
            rw [hnone] at hj
            exact absurd hj (by simp)
    | i + 3 =>
        have hnone :
            ([.var (0 : Nat), .var 1, .app .succ [.var 2]] : List FTerm)[i + 3]? =
              none := persistence_getElem?_none _ _ (by simp)
        rw [hnone] at hi
        exact absurd hi (by simp)
  · show HasSort fArity persistenceTwoSortAttach
      (.app .wrap [.var 1, .app .recur [.var 0, .var 1, .var 2]]) 0
    rw [hasSort_app_iff]
    refine ⟨rfl, rfl, ?_⟩
    intro i a hi
    match i with
    | 0 =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        rw [← hi, hasSort_var_iff]
        decide
    | 1 =>
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.some.injEq] at hi
        rw [← hi, hasSort_app_iff]
        refine ⟨rfl, rfl, ?_⟩
        intro j b hj
        match j with
        | 0 =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
            rw [← hj, hasSort_var_iff]
            decide
        | 1 =>
            simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
              Option.some.injEq] at hj
            rw [← hj, hasSort_var_iff]
            decide
        | 2 =>
            simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
              Option.some.injEq] at hj
            rw [← hj, hasSort_var_iff]
            decide
        | j + 3 =>
            have hnone :
                ([.var (0 : Nat), .var 1, .var 2] : List FTerm)[j + 3]? = none :=
              persistence_getElem?_none _ _ (by simp)
            rw [hnone] at hj
            exact absurd hj (by simp)
    | i + 2 =>
        have hnone :
            ([.var (1 : Nat), .app .recur [.var 0, .var 1, .var 2]] : List FTerm)[i + 2]? =
              none := persistence_getElem?_none _ _ (by simp)
        rw [hnone] at hi
        exact absurd hi (by simp)

theorem manySortedPersistenceWitness_laws :
    manySortedPersistenceLaws manySortedPersistenceWitness := by
  constructor
  · exact manySortedPersistenceWitness_inh
  · intro rule hrule
    simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
    rcases hrule with rfl | rfl
    · exact manySortedPersistenceWitness_zeroRule
    · exact manySortedPersistenceWitness_succRule

theorem persistence_counter_normal :
    ∀ n : FTerm, HasSort fArity persistenceTwoSortAttach n 1 → FNF n := by
  intro n
  induction n using Term.rec' with
  | hvar x =>
      intro hx u hu
      exact not_step_var freeRecursorTRS x u hu
  | happ f args ih =>
      intro h u hu
      obtain ⟨hres, hlen, hargs⟩ := hasSort_app_iff.1 h
      cases f with
      | zero =>
          simp only [fArity] at hlen
          cases args with
          | nil => exact free_no_step_zero u hu
          | cons a as => simp at hlen
      | succ =>
          simp only [fArity] at hlen
          cases args with
          | nil => simp at hlen
          | cons c cs =>
              cases cs with
              | nil =>
                  obtain ⟨c', hc, rfl⟩ := free_step_succ hu
                  exact ih c (by simp)
                    (by simpa [persistenceTwoSortAttach] using hargs 0 c (by simp)) c' hc
              | cons d ds => simp at hlen
      | wrap => exact absurd (show (1 : Fin 2) = 0 from hres) (by decide)
      | recur => exact absurd (show (1 : Fin 2) = 0 from hres) (by decide)

/-- A list of length zero is empty. -/
theorem persistence_eq_nil_of_length_zero {α : Type w} {l : List α} (h : l.length = 0) :
    l = [] := by
  match l with
  | [] => rfl
  | _ :: _ => simp at h

/-- A list of length one is a singleton. -/
theorem persistence_eq_singleton {α : Type w} {l : List α} (h : l.length = 1) :
    ∃ a, l = [a] := by
  match l with
  | [a] => exact ⟨a, rfl⟩
  | [] => simp at h
  | _ :: _ :: _ => simp at h

/-- A list of length two is a pair. -/
theorem persistence_eq_pair {α : Type w} {l : List α} (h : l.length = 2) :
    ∃ a b, l = [a, b] := by
  match l with
  | [a, b] => exact ⟨a, b, rfl⟩
  | [] => simp at h
  | [_] => simp at h
  | _ :: _ :: _ :: _ => simp at h

/-- A list of length three is a triple. -/
theorem persistence_eq_triple {α : Type w} {l : List α} (h : l.length = 3) :
    ∃ a b c, l = [a, b, c] := by
  match l with
  | [a, b, c] => exact ⟨a, b, c, rfl⟩
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => simp at h
  | _ :: _ :: _ :: _ :: _ => simp at h

/-- The recursor application is strongly normalizing when the counter is well sorted and both the
value and frame arguments are strongly normalizing. The root case is supplied by the caller, which
is the only place where the counter's own successor needs the counter induction hypothesis. -/
theorem persistence_recur_sn_of_root (n : FTerm) (hn : FNF n)
    (hroot : ∀ b s u, SN freeRecursorTRS b → SN freeRecursorTRS s →
      rootStep freeRecursorTRS (.app .recur [b, s, n]) u → SN freeRecursorTRS u) :
    ∀ b : FTerm, SN freeRecursorTRS b → ∀ s : FTerm, SN freeRecursorTRS s →
      SN freeRecursorTRS (.app .recur [b, s, n]) := by
  intro b hb
  induction hb with
  | intro b hbch ihb =>
    intro s hs
    induction hs with
    | intro s hsch ihs =>
      refine Acc.intro _ ?_
      intro u hu
      rcases (step_app_iff freeRecursorTRS .recur [b, s, n] u).1 hu with
        hrootstep | ⟨ys, hys, rfl⟩
      · exact hroot b s u (Acc.intro b hbch) (Acc.intro s hsch) hrootstep
      · rcases (argStep_cons_iff freeRecursorTRS b [s, n] ys).1 hys with
          ⟨b', hbb, rfl⟩ | ⟨rest', hrest, rfl⟩
        · exact ihb b' hbb s (Acc.intro s hsch)
        · rcases (argStep_cons_iff freeRecursorTRS s [n] rest').1 hrest with
            ⟨s', hss, rfl⟩ | ⟨rest'', hrest2, rfl⟩
          · exact ihs s' hss
          · rcases (argStep_cons_iff freeRecursorTRS n [] rest'').1 hrest2 with
              ⟨n', hnn, -⟩ | ⟨rest3, hstep, -⟩
            · exact absurd hnn (hn n')
            · exact absurd hstep (not_argStep_nil freeRecursorTRS _)

theorem persistence_recur_sn :
    ∀ n : FTerm, HasSort fArity persistenceTwoSortAttach n 1 →
      ∀ b s : FTerm, SN freeRecursorTRS b → SN freeRecursorTRS s →
        SN freeRecursorTRS (.app .recur [b, s, n]) := by
  intro n
  induction n using Term.rec' with
  | hvar x =>
      intro hn b s hb hs
      refine persistence_recur_sn_of_root (.var x)
        (persistence_counter_normal _ hn) ?_ b hb s hs
      intro b' s' u hb' hs' hr
      exfalso
      rcases free_root_shape hr with ⟨b'', s'', heq, -⟩ | ⟨b'', s'', m'', heq, -⟩
      · simp only [Term.app.injEq] at heq
        have h2 := congrArg (fun l : List FTerm => l[2]?) heq.2
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h2
        exact nomatch h2
      · simp only [Term.app.injEq] at heq
        have h2 := congrArg (fun l : List FTerm => l[2]?) heq.2
        simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h2
        exact nomatch h2
  | happ f args ih =>
      intro hn b s hb hs
      obtain ⟨hres, hlen, hargs⟩ := hasSort_app_iff.1 hn
      cases f with
      | zero =>
          obtain hnil : args = [] :=
            persistence_eq_nil_of_length_zero (by simpa [fArity] using hlen)
          cases hnil
          refine persistence_recur_sn_of_root (.app .zero [])
            (persistence_counter_normal _ hn) ?_ b hb s hs
          intro b' s' u hb' hs' hr
          rcases free_root_shape hr with ⟨b'', s'', heq, hu⟩ | ⟨b'', s'', m'', heq, -⟩
          · simp only [Term.app.injEq] at heq
            have h1 : b' = b'' := by
              have h := congrArg (fun l : List FTerm => l[0]?) heq.2
              simpa using h
            rw [hu, ← h1]
            exact hb'
          · exfalso
            simp only [Term.app.injEq] at heq
            have h2 := congrArg (fun l : List FTerm => l[2]?) heq.2
            simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h2
            exact nomatch h2
      | succ =>
          obtain ⟨m, rfl⟩ := persistence_eq_singleton (by simpa [fArity] using hlen)
          have hm : HasSort fArity persistenceTwoSortAttach m 1 := by
            simpa [persistenceTwoSortAttach] using hargs 0 m (by simp)
          refine persistence_recur_sn_of_root (.app .succ [m])
            (persistence_counter_normal _ hn) ?_ b hb s hs
          intro b' s' u hb' hs' hr
          rcases free_root_shape hr with ⟨b'', s'', heq, -⟩ | ⟨b'', s'', m'', heq, hu⟩
          · exfalso
            simp only [Term.app.injEq] at heq
            have h2 := congrArg (fun l : List FTerm => l[2]?) heq.2
            simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h2
            exact nomatch h2
          · simp only [Term.app.injEq] at heq
            have h1 : b' = b'' := by
              have h := congrArg (fun l : List FTerm => l[0]?) heq.2
              simpa using h
            have h2 : s' = s'' := by
              have h := congrArg (fun l : List FTerm => l[1]?) heq.2
              simpa using h
            have h3 : m = m'' := by
              have h4 : (.app .succ [m] : FTerm) = .app .succ [m''] := by
                have h := congrArg (fun l : List FTerm => l[2]?) heq.2
                simpa using h
              have h5 : [m] = [m''] := (Term.app.inj h4).2
              have h := congrArg (fun l : List FTerm => l[0]?) h5
              simpa using h
            rw [hu, ← h1, ← h2, ← h3]
            refine sn_app_of_not_defined freeRecursorTRS_wrap_not_defined
              [s', .app .recur [b', s', m]] ?_
            intro a ha
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
            rcases ha with h | h
            · rw [h]
              exact hs'
            · rw [h]
              exact ih m (by simp) hm b' s' hb' hs'
      | wrap => exact absurd (show (1 : Fin 2) = 0 from hres) (by decide)
      | recur => exact absurd (show (1 : Fin 2) = 0 from hres) (by decide)

/-- Every well-sorted term of the two-sort assignment is strongly normalizing. -/
theorem persistence_sorted_term_sn :
    ∀ t : FTerm, ∀ s : Fin 2,
      HasSort fArity persistenceTwoSortAttach t s → SN freeRecursorTRS t := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
      intro s hs
      exact Acc.intro _ (fun u hu => False.elim (not_step_var freeRecursorTRS x u hu))
  | happ f args ih =>
      intro s hs
      obtain ⟨hres, hlen, hargs⟩ := hasSort_app_iff.1 hs
      cases f with
      | zero =>
          obtain hnil : args = [] :=
            persistence_eq_nil_of_length_zero (by simpa [fArity] using hlen)
          cases hnil
          refine sn_app_of_not_defined free_not_defined_zero [] ?_
          intro a ha
          simp at ha
      | succ =>
          obtain ⟨c, rfl⟩ := persistence_eq_singleton (by simpa [fArity] using hlen)
          refine sn_app_of_not_defined free_not_defined_succ [c] ?_
          intro a ha
          have hac : a = c := by simpa using ha
          rw [hac]
          exact ih c (by simp) 1
            (by simpa [persistenceTwoSortAttach] using hargs 0 c (by simp))
      | wrap =>
          obtain ⟨p, q, rfl⟩ := persistence_eq_pair (by simpa [fArity] using hlen)
          refine sn_app_of_not_defined freeRecursorTRS_wrap_not_defined [p, q] ?_
          intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with h | h
          · rw [h]
            exact ih p (by simp) 0
              (by simpa [persistenceTwoSortAttach] using hargs 0 p (by simp))
          · rw [h]
            exact ih q (by simp) 0
              (by simpa [persistenceTwoSortAttach] using hargs 1 q (by simp))
      | recur =>
          obtain ⟨b, s', n, rfl⟩ := persistence_eq_triple (by simpa [fArity] using hlen)
          have hb : SN freeRecursorTRS b :=
            ih b (by simp) 0 (by simpa [persistenceTwoSortAttach] using hargs 0 b (by simp))
          have hs' : SN freeRecursorTRS s' :=
            ih s' (by simp) 0 (by simpa [persistenceTwoSortAttach] using hargs 1 s' (by simp))
          have hn : HasSort fArity persistenceTwoSortAttach n 1 := by
            simpa [persistenceTwoSortAttach] using hargs 2 n (by simp)
          exact persistence_recur_sn n hn b s' hb hs'

theorem manySortedPersistenceWitness_accepts :
    manySortedPersistenceAccepts manySortedPersistenceWitness := by
  intro t s ht
  exact Subrelation.accessible (fun h => h.2) (persistence_sorted_term_sn t s ht)

/-! ### MS-7: the row, its feature, its mutations and the one-sort control -/

/-- Verdict: escape. -/
def manySortedPersistenceResult (M : manySortedPersistenceData) : Prop :=
  manySortedPersistenceAccepts M ∧ ∀ t : FTerm, SN freeRecursorTRS t

theorem manySortedPersistence_sound
    (M : manySortedPersistenceData)
    (hL : manySortedPersistenceLaws M)
    (hA : manySortedPersistenceAccepts M) :
    ∀ t : FTerm, SN freeRecursorTRS t := by
  exact freeRecursor_sn_of_sorted M.attach M.inh
    (consistent_of_rules hL.2) hL.1 hA

theorem manySortedPersistenceWitness_result :
    manySortedPersistenceResult manySortedPersistenceWitness :=
  ⟨manySortedPersistenceWitness_accepts,
    manySortedPersistence_sound manySortedPersistenceWitness
      manySortedPersistenceWitness_laws manySortedPersistenceWitness_accepts⟩

theorem freeRecursor_terminates_via_manySorted :
    ∀ t : FTerm, SN freeRecursorTRS t :=
  manySortedPersistenceWitness_result.2

/-- A recursor whose value argument is `zero`, so its argument typing fails at the value sort. -/
def persistenceIllTyped : FTerm :=
  .app .recur [.app .zero [], .var 0, .app .zero []]

/-- A well-sorted recursor redex. -/
def persistenceTypedRedex : FTerm :=
  .app .recur [.var 0, .var 1, .app .zero []]

/-- A well-sorted successor redex. -/
def persistenceSuccRedex : FTerm :=
  .app .recur [.var 0, .var 1, .app .succ [.app .zero []]]

/-- Its contractum. -/
def persistenceSuccTarget : FTerm :=
  .app .wrap [.var 1, .app .recur [.var 0, .var 1, .app .zero []]]

/-- C-MS-01: the ill-typed recursor contracts, no sort accepts the source, and the reduct has
counter sort 1. -/
theorem persistence_ill_typed_step :
    Step freeRecursorTRS persistenceIllTyped (.app .zero []) ∧
      ¬ (∃ s : Fin 2, HasSort fArity persistenceTwoSortAttach persistenceIllTyped s) ∧
      HasSort fArity persistenceTwoSortAttach (.app .zero []) 1 := by
  refine ⟨Step.root (free_root_zero (.app .zero []) (.var 0)), ?_, ?_⟩
  · rintro ⟨s, hs⟩
    obtain ⟨-, -, hargs⟩ := hasSort_app_iff.1 hs
    obtain ⟨hres, -, -⟩ := hasSort_app_iff.1 (hargs 0 (.app .zero []) (by simp))
    exact absurd hres (by decide)
  · exact hasSort_app_iff.mpr ⟨rfl, rfl, by intro j b hb; simp at hb⟩

theorem persistence_succ_redex_root :
    rootStep freeRecursorTRS persistenceSuccRedex persistenceSuccTarget :=
  free_root_succ (.var 0) (.var 1) (.app .zero [])

/-- The mutation: only the result sort of `zero` changes, from 1 to 0. -/
def manySortedPersistenceMutant : manySortedPersistenceData where
  sortCount := 2
  attach := { persistenceTwoSortAttach with
    res := fun f => match f with
      | .zero => 0
      | .succ => 1
      | _ => 0 }
  inh := fun s => if s = 0 then 0 else 2

theorem manySortedPersistence_mutation :
    ¬ manySortedPersistenceLaws manySortedPersistenceMutant := by
  rintro ⟨-, hrules⟩
  have hmem : zeroRule ∈ freeRecursorTRS := by simp [freeRecursorTRS]
  obtain ⟨s0, hlhs, hrhs⟩ := hrules zeroRule hmem
  obtain ⟨-, -, hargs⟩ := hasSort_app_iff.1 hlhs
  obtain ⟨hres, -, -⟩ := hasSort_app_iff.1 (hargs 2 (.app .zero []) (by simp))
  exact absurd hres (by decide)

/-- The bad inhabitant: counter sort 1 is sent to variable 0, whose value sort is 0. -/
def persistenceBadInhabitant : manySortedPersistenceData where
  sortCount := 2
  attach := persistenceTwoSortAttach
  inh := fun s => if s = 0 then 0 else 0

theorem persistenceBadInhabitant_law_failure :
    ¬ (∀ s : Fin 2, persistenceTwoSortAttach.var (persistenceBadInhabitant.inh s) = s) := by
  intro h
  have h1 := h 1
  exact absurd h1 (by decide)

/-- The one-sort attachment: every symbol and every variable has the single sort. -/
def persistenceOneSortAttach : SortAttach FreeSym (Fin 1) where
  arg := fun _ _ => 0
  res := fun _ => 0
  var := fun _ => 0

/-- The one-sort datum. -/
def persistenceOneSortDatum : manySortedPersistenceData where
  sortCount := 1
  attach := persistenceOneSortAttach
  inh := fun _ => 0

theorem persistence_oneSort_app {f : FreeSym} {args : List FTerm}
    (hlen : args.length = fArity f)
    (hargs : ∀ a ∈ args, HasSort fArity persistenceOneSortAttach a 0) :
    HasSort fArity persistenceOneSortAttach (.app f args) 0 := by
  refine hasSort_mk hlen ?_
  have key : ∀ (k : Nat) (l : List FTerm),
      (∀ a ∈ l, HasSort fArity persistenceOneSortAttach a 0) →
      ArgsSorted fArity persistenceOneSortAttach f k l := by
    intro k l
    induction l generalizing k with
    | nil => intro _; trivial
    | cons a as ihl =>
        intro hl
        exact ⟨by simpa [persistenceOneSortAttach] using hl a (by simp),
          ihl (k + 1) (fun b hb => hl b (by simp [hb]))⟩
  exact key 0 args hargs

theorem persistenceOneSortDatum_laws :
    manySortedPersistenceLaws persistenceOneSortDatum := by
  constructor
  · intro s
    apply Fin.ext
    have hs := s.isLt
    simp [persistenceOneSortDatum, persistenceOneSortAttach] at hs ⊢
  · intro rule hrule
    simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
    rcases hrule with rfl | rfl
    · refine ⟨(0 : Fin 1), ?_, ?_⟩
      · change HasSort fArity persistenceOneSortAttach
          (.app .recur [.var 0, .var 1, .app .zero []]) (0 : Fin 1)
        refine persistence_oneSort_app rfl ?_
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl
        · exact HasSort.var 0
        · exact HasSort.var 1
        · refine persistence_oneSort_app rfl (by intro b hb; simp at hb)
      · change HasSort fArity persistenceOneSortAttach (.var 0) (0 : Fin 1)
        exact HasSort.var 0
    · refine ⟨(0 : Fin 1), ?_, ?_⟩
      · change HasSort fArity persistenceOneSortAttach
          (.app .recur [.var 0, .var 1, .app .succ [.var 2]]) (0 : Fin 1)
        refine persistence_oneSort_app rfl ?_
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl
        · exact HasSort.var 0
        · exact HasSort.var 1
        · refine persistence_oneSort_app rfl (by
            intro b hb
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
            rcases hb with rfl
            exact HasSort.var 2)
      · change HasSort fArity persistenceOneSortAttach
          (.app .wrap [.var 1, .app .recur [.var 0, .var 1, .var 2]]) (0 : Fin 1)
        refine persistence_oneSort_app rfl ?_
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact HasSort.var 1
        · refine persistence_oneSort_app rfl (by
            intro b hb
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
            rcases hb with rfl | rfl | rfl
            · exact HasSort.var 0
            · exact HasSort.var 1
            · exact HasSort.var 2)

theorem persistence_one_sort_control :
    manySortedPersistenceLaws persistenceOneSortDatum ∧
      manySortedPersistenceAccepts persistenceOneSortDatum :=
  ⟨persistenceOneSortDatum_laws,
    fun t _ _ => Subrelation.accessible (fun h => h.2)
      (freeRecursor_terminates_via_manySorted t)⟩

/-! ### MS-7: native sorted rewriting and its correspondence with the sorted step -/

/-- An admitted substitution: every image has its declared variable sort. -/
def persistenceSortedSubst {sigma : Type u} {S : Type}
    (ar : sigma → Nat) (A : SortAttach sigma S)
    (σ : Subst sigma Nat) : Prop :=
  ∀ x, HasSort ar A (σ x) (A.var x)

/-- Native sorted rewriting: a source typing and a restricted step with admitted substitutions in
all argument positions. -/
def persistenceNativeSortedStep {sigma : Type u} {S : Type}
    (ar : sigma → Nat) (A : SortAttach sigma S) (R : TRS sigma Nat)
    (t u : Term sigma Nat) : Prop :=
  (∃ s, HasSort ar A t s) ∧
    RStep R (persistenceSortedSubst ar A) (fun _ _ => True) t u

theorem persistence_hasSort_unique {sigma : Type u} {S : Type} {ar : sigma → Nat}
    {A : SortAttach sigma S} {t : Term sigma Nat} {s s' : S}
    (h : HasSort ar A t s) (h' : HasSort ar A t s') : s = s' := by
  induction t using Term.rec' with
  | hvar x =>
      rw [hasSort_var_iff] at h h'
      rw [h, h']
  | happ f args ih =>
      rw [hasSort_app_iff] at h h'
      rw [h.1, h'.1]

theorem persistence_hasSort_subst {sigma : Type u} {S : Type} {ar : sigma → Nat}
    {A : SortAttach sigma S} {σ : Subst sigma Nat} {t : Term sigma Nat} {s : S}
    (h : HasSort ar A t s) (hσ : persistenceSortedSubst ar A σ) :
    HasSort ar A (Subst.apply σ t) s := by
  induction h with
  | var x => exact hσ x
  | app f args hlen hargs ih =>
      rw [Subst.apply_app]
      refine hasSort_app_iff.mpr ⟨rfl, ?_, ?_⟩
      · rw [Subst.applyList_eq_map, List.length_map]
        exact hlen
      · intro i a' hi
        rw [Subst.applyList_eq_map, List.getElem?_map] at hi
        obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hi
        exact ih i a ha

theorem persistence_match_var_sort {sigma : Type u} {S : Type} {ar : sigma → Nat}
    {A : SortAttach sigma S} {σ : Subst sigma Nat} :
    ∀ {t : Term sigma Nat} {s : S}, HasSort ar A t s → ∀ {x : Nat}, x ∈ Term.vars t →
      HasSort ar A (Subst.apply σ t) s → HasSort ar A (σ x) (A.var x) := by
  intro t s h
  induction h with
  | var y =>
      intro x hx h'
      simp only [Term.vars_var, Finset.mem_singleton] at hx
      subst hx
      exact h'
  | app f args hlen hargs ih =>
      intro x hx h'
      rw [Term.vars_app, Term.mem_varsList_iff] at hx
      obtain ⟨a, ha, hxa⟩ := hx
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
      rw [Subst.apply_app, hasSort_app_iff] at h'
      obtain ⟨-, -, hargs'⟩ := h'
      have htyped_sub : HasSort ar A (Subst.apply σ a) (A.arg f i) := by
        refine hargs' i (Subst.apply σ a) ?_
        simp [Subst.applyList_eq_map, List.getElem?_map, hi]
      exact ih i a hi hxa htyped_sub

theorem persistence_map_agree {sigma : Type u} {σ τ : Subst sigma Nat}
    {args : List (Term sigma Nat)}
    (h : ∀ a ∈ args, Subst.apply σ a = Subst.apply τ a) :
    args.map (Subst.apply σ) = args.map (Subst.apply τ) := by
  induction args with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨h a (by simp), ih (fun b hb => h b (by simp [hb]))⟩

theorem persistence_subst_agrees {sigma : Type u} {σ τ : Subst sigma Nat}
    {t : Term sigma Nat} (h : ∀ x, x ∈ Term.vars t → σ x = τ x) :
    Subst.apply σ t = Subst.apply τ t := by
  induction t using Term.rec' with
  | hvar x =>
      exact h x (by simp [Term.vars_var])
  | happ f args ih =>
      rw [Subst.apply_app, Subst.apply_app, Subst.applyList_eq_map, Subst.applyList_eq_map]
      congr 1
      refine persistence_map_agree ?_
      intro a ha
      exact ih a ha (fun x hx => h x (by
        rw [Term.vars_app, Term.mem_varsList_iff]
        exact ⟨a, ha, hx⟩))

theorem persistence_complete_subst {sigma : Type u} {S : Type} {ar : sigma → Nat}
    {A : SortAttach sigma S} {σ : Subst sigma Nat} {rule : Rule sigma Nat} {s : S}
    (_ : HasSort ar A rule.lhs s) (_ : HasSort ar A rule.rhs s)
    (hvars : Term.vars rule.rhs ⊆ Term.vars rule.lhs)
    (hsub : ∀ x, x ∈ Term.vars rule.lhs → HasSort ar A (σ x) (A.var x)) :
    ∃ τ : Subst sigma Nat, persistenceSortedSubst ar A τ ∧
      Subst.apply τ rule.lhs = Subst.apply σ rule.lhs ∧
      Subst.apply τ rule.rhs = Subst.apply σ rule.rhs := by
  refine ⟨fun x => if x ∈ Term.vars rule.lhs then σ x else .var x, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ Term.vars rule.lhs
    · simpa [hx] using hsub x hx
    · simpa [hx] using HasSort.var x
  · exact persistence_subst_agrees (fun x hx => by simp [hx])
  · exact persistence_subst_agrees (fun x hx => by simp [hvars hx])

theorem persistence_step_preserves_sort {sigma : Type u} {S : Type} {ar : sigma → Nat}
    {A : SortAttach sigma S} {R : TRS sigma Nat}
    (hrules : ∀ rule ∈ R, ∃ s, HasSort ar A rule.lhs s ∧ HasSort ar A rule.rhs s)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs) :
    ∀ {t u : Term sigma Nat} {s : S}, HasSort ar A t s → Step R t u → HasSort ar A u s := by
  intro t u s ht hstep
  induction hstep generalizing s with
  | root hroot =>
      obtain ⟨rule, hrule, σ, hl_inst, hr_inst⟩ := hroot
      obtain ⟨s0, hl, hr⟩ := hrules rule hrule
      obtain ⟨f, largs, hlhs⟩ := lhs_eq_app rule
      have hinst : Subst.apply σ rule.lhs = .app f (Subst.applyList σ largs) := by
        rw [hlhs, Subst.apply_app]
      have hs : s = A.res f := by
        rw [hl_inst, hinst] at ht
        exact (hasSort_app_iff.1 ht).1
      have hs0 : s0 = A.res f := by
        rw [hlhs] at hl
        exact (hasSort_app_iff.1 hl).1
      have hss : s = s0 := hs.trans hs0.symm
      have ht0 : HasSort ar A (Subst.apply σ rule.lhs) s0 := by
        rw [hl_inst, hss] at ht
        exact ht
      have hσ : ∀ x, x ∈ Term.vars rule.lhs → HasSort ar A (σ x) (A.var x) :=
        fun x hx => persistence_match_var_sort hl hx ht0
      obtain ⟨τ, hτ, -, hagree_r⟩ :=
        persistence_complete_subst hl hr (hvars rule hrule) hσ
      have hsub := persistence_hasSort_subst hr hτ
      rw [hagree_r] at hsub
      rw [hr_inst, hss]
      exact hsub
  | arg f pre post h ih =>
      refine hasSort_replace ht ?_
      exact ih (s := A.arg f pre.length) (hasSort_arg_mid ht)

theorem persistence_rstep_to_step {sigma : Type u} {nu : Type v} {R : TRS sigma nu}
    {ok : Subst sigma nu → Prop} {act : sigma → Nat → Prop} {t u : Term sigma nu}
    (h : RStep R ok act t u) : Step R t u := by
  induction h with
  | root hroot =>
      obtain ⟨rule, hrule, σ, -, hl, hr⟩ := hroot
      exact Step.root ⟨rule, hrule, σ, hl, hr⟩
  | arg f pre post hact h ih =>
      exact Step.arg f pre post ih

theorem persistence_native_rstep_of_step {sigma : Type u} {S : Type} {ar : sigma → Nat}
    {A : SortAttach sigma S} {R : TRS sigma Nat}
    (hrules : ∀ rule ∈ R, ∃ s, HasSort ar A rule.lhs s ∧ HasSort ar A rule.rhs s)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs) :
    ∀ {t u : Term sigma Nat} {s : S}, HasSort ar A t s → Step R t u →
      RStep R (persistenceSortedSubst ar A) (fun _ _ => True) t u := by
  intro t u s ht hstep
  induction hstep generalizing s with
  | root hroot =>
      obtain ⟨rule, hrule, σ, hl_inst, hr_inst⟩ := hroot
      obtain ⟨s0, hl, hr⟩ := hrules rule hrule
      obtain ⟨f, largs, hlhs⟩ := lhs_eq_app rule
      have hinst : Subst.apply σ rule.lhs = .app f (Subst.applyList σ largs) := by
        rw [hlhs, Subst.apply_app]
      have hs : s = A.res f := by
        rw [hl_inst, hinst] at ht
        exact (hasSort_app_iff.1 ht).1
      have hs0 : s0 = A.res f := by
        rw [hlhs] at hl
        exact (hasSort_app_iff.1 hl).1
      have hss : s = s0 := hs.trans hs0.symm
      have ht0 : HasSort ar A (Subst.apply σ rule.lhs) s0 := by
        rw [hl_inst, hss] at ht
        exact ht
      have hσ : ∀ x, x ∈ Term.vars rule.lhs → HasSort ar A (σ x) (A.var x) :=
        fun x hx => persistence_match_var_sort hl hx ht0
      obtain ⟨τ, hτ, hagree_l, hagree_r⟩ :=
        persistence_complete_subst hl hr (hvars rule hrule) hσ
      exact RStep.root ⟨rule, hrule, τ, hτ, by rw [hagree_l]; exact hl_inst,
        by rw [hagree_r]; exact hr_inst⟩
  | arg f pre post h ih =>
      exact RStep.arg f pre post trivial (ih (s := A.arg f pre.length) (hasSort_arg_mid ht))

theorem persistence_native_step_iff {sigma : Type u} {S : Type} {ar : sigma → Nat}
    {A : SortAttach sigma S} {R : TRS sigma Nat}
    (hrules : ∀ rule ∈ R, ∃ s, HasSort ar A rule.lhs s ∧ HasSort ar A rule.rhs s)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs) :
    ∀ {t u : Term sigma Nat},
      persistenceNativeSortedStep ar A R t u ↔ SortedStep ar A R t u := by
  intro t u
  constructor
  · rintro ⟨ht, hstep⟩
    exact ⟨ht, persistence_rstep_to_step hstep⟩
  · rintro ⟨ht, hstep⟩
    obtain ⟨s, hs⟩ := ht
    exact ⟨⟨s, hs⟩, persistence_native_rstep_of_step hrules hvars hs hstep⟩

theorem persistence_acc_congr {α : Type w} {r s : α → α → Prop}
    (h : ∀ a b, r a b ↔ s a b) : ∀ a, Acc r a ↔ Acc s a := by
  intro a
  constructor
  · intro ha
    induction ha with
    | intro a _ ih =>
        exact Acc.intro _ (fun b hb => ih b ((h b a).2 hb))
  · intro ha
    induction ha with
    | intro a _ ih =>
        exact Acc.intro _ (fun b hb => ih b ((h b a).1 hb))

theorem persistence_native_termination_iff {sigma : Type u} {S : Type} {ar : sigma → Nat}
    {A : SortAttach sigma S} {R : TRS sigma Nat}
    (hrules : ∀ rule ∈ R, ∃ s, HasSort ar A rule.lhs s ∧ HasSort ar A rule.rhs s)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs) :
    (∀ t : Term sigma Nat, (∃ s, HasSort ar A t s) →
        Acc (fun u t => persistenceNativeSortedStep ar A R t u) t) ↔
      (∀ t : Term sigma Nat, (∃ s, HasSort ar A t s) →
        Acc (fun u t => SortedStep ar A R t u) t) := by
  have hiff : ∀ a b : Term sigma Nat,
      (fun u t => persistenceNativeSortedStep ar A R t u) a b ↔
        (fun u t => SortedStep ar A R t u) a b :=
    fun a b => persistence_native_step_iff hrules hvars (t := b) (u := a)
  constructor
  · intro h t ht
    exact (persistence_acc_congr hiff t).1 (h t ht)
  · intro h t ht
    exact (persistence_acc_congr hiff t).2 (h t ht)

theorem persistence_succ_redex_native :
    persistenceNativeSortedStep fArity persistenceTwoSortAttach freeRecursorTRS
      persistenceSuccRedex persistenceSuccTarget := by
  refine ⟨⟨0, ?_⟩, ?_⟩
  · refine hasSort_mk rfl ?_
    refine ⟨?_, ?_, ?_, trivial⟩
    · exact HasSort.var 0
    · exact HasSort.var 1
    · refine hasSort_app_iff.mpr ⟨rfl, rfl, ?_⟩
      intro i a hi
      match i with
      | 0 =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          rw [← hi]
          exact hasSort_app_iff.mpr ⟨rfl, rfl, by intro j b hb; simp at hb⟩
      | n + 1 =>
          have hnone : ([.app .zero []] : List FTerm)[n + 1]? = none :=
            persistence_getElem?_none _ _ (by simp)
          rw [hnone] at hi
          exact absurd hi (by simp)
  · refine RStep.root ⟨succRule, by simp [freeRecursorTRS],
      (fun x => match x with
        | 0 => (.var 0 : FTerm)
        | 1 => .var 1
        | 2 => .app .zero []
        | _ => .var x), ?_, rfl, rfl⟩
    intro x
    match x with
    | 0 => exact HasSort.var 0
    | 1 => exact HasSort.var 1
    | 2 => exact hasSort_app_iff.mpr ⟨rfl, rfl, by intro j b hb; simp at hb⟩
    | n + 3 => exact HasSort.var (n + 3)

/-! ### MS-8: controls that reject incorrect proofs -/

/-- C-MS-01: no sort accepts the ill-typed recursor. -/
theorem persistence_ill_typed_unsorted :
    ¬ ∃ s : Fin 2, HasSort fArity persistenceTwoSortAttach persistenceIllTyped s :=
  persistence_ill_typed_step.2.1

theorem persistence_ill_typed_terminates :
    SN freeRecursorTRS persistenceIllTyped :=
  freeRecursor_terminates_via_manySorted persistenceIllTyped

/-- C-MS-05: `succ [persistenceIllTyped]` fits counter sort 1, its alien list at that sort contains
the ill-typed proper subterm, and the term terminates by the new method. -/
theorem persistence_nested_alien_sn :
    Fits (A := persistenceTwoSortAttach) 1 (.app .succ [persistenceIllTyped]) ∧
      persistenceIllTyped ∈
        aliens (A := persistenceTwoSortAttach) 1 (.app .succ [persistenceIllTyped]) ∧
      SN freeRecursorTRS (.app .succ [persistenceIllTyped]) := by
  have hnot : ¬ Fits (A := persistenceTwoSortAttach) 1 persistenceIllTyped := by
    intro h
    have h1 : persistenceTwoSortAttach.res .recur = 1 := by
      change (persistenceTwoSortAttach.res .recur = 1 ∧
        ([.app .zero [], .var 0, .app .zero []] : List FTerm).length = fArity .recur) at h
      exact h.1
    exact absurd h1 (by decide)
  have hlist : aliens (A := persistenceTwoSortAttach) 1 (.app .succ [persistenceIllTyped]) =
      [persistenceIllTyped] := by
    rw [aliens_fit_app (A := persistenceTwoSortAttach) (s := 1) (f := .succ) rfl rfl]
    simp only [aliensList]
    rw [show persistenceTwoSortAttach.arg .succ 0 = 1 by rfl]
    rw [aliens_nofit (A := persistenceTwoSortAttach) (s := 1) (t := persistenceIllTyped) hnot]
    rfl
  refine ⟨⟨rfl, rfl⟩, ?_, freeRecursor_terminates_via_manySorted _⟩
  rw [hlist]
  simp

/-- C-MS-06: wrong-arity recursors terminate; the last has an argument step and no root step. -/
theorem persistence_wrong_arity_controls :
    SN freeRecursorTRS (.app .recur []) ∧
      SN freeRecursorTRS (.app .recur [.var 0]) ∧
      SN freeRecursorTRS (.app .recur [persistenceTypedRedex]) ∧
      Step freeRecursorTRS (.app .recur [persistenceTypedRedex]) (.app .recur [.var 0]) ∧
      ¬ rootStep freeRecursorTRS (.app .recur [persistenceTypedRedex])
        (.app .recur [.var 0]) := by
  refine ⟨freeRecursor_terminates_via_manySorted _,
    freeRecursor_terminates_via_manySorted _, freeRecursor_terminates_via_manySorted _,
    ?_, ?_⟩
  · exact Step.arg .recur [] [] (Step.root (free_root_zero (.var 0) (.var 1)))
  · intro hr
    exact absurd (persistence_root_source_arity hr) (by decide)

/-- C-MS-07: the successor redex and its contractum are both sorted at 0, and the typed successor
rule contracts natively and in the erased relation. -/
theorem persistence_successor_native_step :
    HasSort fArity persistenceTwoSortAttach persistenceSuccRedex 0 ∧
      HasSort fArity persistenceTwoSortAttach persistenceSuccTarget 0 ∧
      persistenceNativeSortedStep fArity persistenceTwoSortAttach freeRecursorTRS
        persistenceSuccRedex persistenceSuccTarget ∧
      Step freeRecursorTRS persistenceSuccRedex persistenceSuccTarget := by
  refine ⟨?_, ?_, persistence_succ_redex_native,
    persistence_rstep_to_step persistence_succ_redex_native.2⟩
  · refine hasSort_mk rfl ?_
    refine ⟨HasSort.var 0, HasSort.var 1, ?_, trivial⟩
    refine hasSort_app_iff.mpr ⟨rfl, rfl, ?_⟩
    intro j b hb
    match j with
    | 0 =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hb
        rw [← hb]
        exact hasSort_app_iff.mpr ⟨rfl, rfl, by intro k c hc; simp at hc⟩
    | k + 1 =>
        have hnone : ([.app .zero []] : List FTerm)[k + 1]? = none :=
          persistence_getElem?_none _ _ (by simp)
        rw [hnone] at hb
        exact absurd hb (by simp)
  change HasSort fArity persistenceTwoSortAttach
    (.app .wrap [.var 1, .app .recur [.var 0, .var 1, .app .zero []]]) 0
  refine hasSort_mk rfl ?_
  refine ⟨HasSort.var 1, ?_, trivial⟩
  refine hasSort_mk rfl ?_
  refine ⟨HasSort.var 0, HasSort.var 1, ?_, trivial⟩
  exact hasSort_app_iff.mpr ⟨rfl, rfl, by intro j b hb; simp at hb⟩

/-- C-MS-09: both datum mutations fail exactly the law they modify. -/
theorem persistence_sort_mutation_control :
    ¬ manySortedPersistenceLaws manySortedPersistenceMutant ∧
      ¬ (∀ s : Fin 2, persistenceTwoSortAttach.var (persistenceBadInhabitant.inh s) = s) :=
  ⟨manySortedPersistence_mutation, persistenceBadInhabitant_law_failure⟩

/-- C-MS-11: on a one-state loop with a constant projection and an empty abstract step relation,
the transfer hypothesis holds with only equal projections and a self-loop residual, the loop is not
accessible, and the residual relation is not well founded, so equality without residual descent
cannot establish the transfer. -/
theorem persistence_stutter_needs_descent :
    ¬ Acc (fun (_ _ : Unit) => True) () ∧
      (∀ x y : Unit, (fun (_ _ : Unit) => True) x y →
        (fun (_ : Unit) => True) () ∧
          ((fun (_ _ : Unit) => False) () () ∨
            (() = () ∧ (fun (_ _ : Unit) => True) () ()))) ∧
      (∀ x y : Unit, (fun (_ : Unit) => ()) x = (fun (_ : Unit) => ()) y) ∧
      ¬ WellFounded (fun (_ _ : Unit) => True) := by
  refine ⟨not_acc_of_cycle (r := fun (_ _ : Unit) => True) (x := ()) (y := ()) trivial trivial,
    ?_, ?_, ?_⟩
  · intro x y _
    exact ⟨trivial, Or.inr ⟨rfl, trivial⟩⟩
  · intro x y
    rfl
  · intro hw
    exact not_acc_of_cycle (r := fun (_ _ : Unit) => True) (x := ()) (y := ()) trivial trivial
      (hw.apply ())

/-- C-MS-12: two states `true -> false -> false`; the invariant `{true}` makes the measure strictly
decrease on every step whose source satisfies it, one step leaves the invariant, and the loop does
not terminate, so a transfer that omits preservation of the successor invariant fails. -/
theorem persistence_invariant_preservation_needed :
    ¬ Acc (fun y x : Bool => (x = true ∧ y = false) ∨ (x = false ∧ y = false)) true ∧
      (∀ x y : Bool, x = true →
        ((x = true ∧ y = false) ∨ (x = false ∧ y = false)) →
          (if y = true then 1 else 0) < (if x = true then 1 else 0)) ∧
      (∃ x y : Bool, x = true ∧
        ((x = true ∧ y = false) ∨ (x = false ∧ y = false)) ∧ y ≠ true) := by
  have hloop : ¬ Acc (fun y x : Bool => (x = true ∧ y = false) ∨ (x = false ∧ y = false)) true := by
    have hAll : ∀ a : Bool,
        ¬ Acc (fun y x : Bool => (x = true ∧ y = false) ∨ (x = false ∧ y = false)) a := by
      intro a h
      induction h with
      | intro a _ ih =>
          cases a with
          | false => exact ih false (Or.inr ⟨rfl, rfl⟩)
          | true => exact ih false (Or.inl ⟨rfl, rfl⟩)
    exact hAll true
  refine ⟨hloop, ?_, ?_⟩
  · intro x y hx h
    subst hx
    rcases h with ⟨-, rfl⟩ | ⟨h, -⟩
    · decide
    · exact absurd h (by decide)
  · exact ⟨true, false, rfl, Or.inl ⟨rfl, rfl⟩, by decide⟩

/-- The rule `wrap(var 0, var 0) -> var 1`, well sorted at the value sort, with a fresh right
variable. -/
def persistenceFreshRule : Rule FreeSym Nat where
  lhs := .app .wrap [.var 0, .var 0]
  rhs := .var 1
  lhs_isApp := rfl

/-- C-MS-13: the rule `wrap(var 0, var 0) -> var 1` is well sorted at the value sort and its
right-hand variable is fresh; the substitution `0 |-> var 0`, `1 |-> zero` gives a well-sorted source
whose reduct is at counter sort 1 and not at the source sort, so removing the right-variable
condition breaks sort preservation. -/
theorem persistence_rhs_variable_condition_needed :
    (∃ s : Fin 2, HasSort fArity persistenceTwoSortAttach persistenceFreshRule.lhs s ∧
      HasSort fArity persistenceTwoSortAttach persistenceFreshRule.rhs s) ∧
      ((1 : Nat) ∈ Term.vars persistenceFreshRule.rhs ∧
        (1 : Nat) ∉ Term.vars persistenceFreshRule.lhs) ∧
      (∃ t u : FTerm, HasSort fArity persistenceTwoSortAttach t 0 ∧
        Step [persistenceFreshRule] t u ∧ u = .app .zero [] ∧
        HasSort fArity persistenceTwoSortAttach u 1 ∧
        ¬ HasSort fArity persistenceTwoSortAttach u 0) := by
  refine ⟨⟨0, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · show HasSort fArity persistenceTwoSortAttach (.app .wrap [.var 0, .var 0]) 0
    refine hasSort_mk rfl ?_
    exact ⟨.var 0, .var 0, trivial⟩
  · show HasSort fArity persistenceTwoSortAttach (.var 1) 0
    exact .var 1
  · rw [persistenceFreshRule, Term.vars_var]
    simp
  · rw [persistenceFreshRule, Term.vars_app, Term.mem_varsList_iff]
    rintro ⟨a, ha, hxa⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> simp [Term.vars_var] at hxa
  · refine ⟨.app .wrap [.var 0, .var 0], .app .zero [], ?_, ?_, rfl, ?_, ?_⟩
    · refine hasSort_mk rfl ?_
      exact ⟨HasSort.var 0, HasSort.var 0, trivial⟩
    · have hroot : rootStep [persistenceFreshRule] (.app .wrap [.var 0, .var 0])
          (.app .zero []) :=
        rootStep_intro [persistenceFreshRule] (rule := persistenceFreshRule) (by simp)
          (fun x => match x with | 0 => (.var 0 : FTerm) | _ => .app .zero [])
      exact Step.root hroot
    · exact hasSort_app_iff.mpr ⟨rfl, rfl, by intro j b hb; simp at hb⟩
    · intro h
      obtain ⟨hres, -, -⟩ := hasSort_app_iff.1 h
      exact absurd hres (by decide)

/-- C-MS-10: the sorted Toyama system terminates while its ill-sorted loop does not, so sorting
alone transfers no termination for arbitrary rule lists. -/
def persistenceArbitraryTRSCounterexample : Prop :=
  SortedTerminates toyArity toyAttach toyTRS ∧ ¬ SN toyTRS toyLoop ∧ ¬ ZantemaCondition toyTRS

theorem persistence_arbitrary_trs_counterexample : persistenceArbitraryTRSCounterexample :=
  typeIntroductionWitness_feature

/-- The complete witness feature on one example assignment: the datum has two sorts, `recur` and
`zero` have distinct result sorts, the typed successor rule contracts under the native sorted
relation, and the ill-sorted recursor term has an unsorted step, is accepted by no sort, and
terminates by the new method. -/
theorem manySortedPersistenceWitness_feature :
    manySortedPersistenceWitness.sortCount = 2 ∧
      persistenceTwoSortAttach.res .recur ≠ persistenceTwoSortAttach.res .zero ∧
      persistenceNativeSortedStep fArity persistenceTwoSortAttach freeRecursorTRS
        persistenceSuccRedex persistenceSuccTarget ∧
      Step freeRecursorTRS persistenceIllTyped (.app .zero []) ∧
      ¬ (∃ s : Fin 2, HasSort fArity persistenceTwoSortAttach persistenceIllTyped s) ∧
      SN freeRecursorTRS persistenceIllTyped :=
  ⟨rfl, by decide, persistence_succ_redex_native, persistence_ill_typed_step.1,
    persistence_ill_typed_step.2.1, freeRecursor_terminates_via_manySorted _⟩

/-- C-MS-02: the ill-typed source fits result sort 0, does not fit sort 1, and its sort-1 alien
list is exactly the source. -/
theorem persistence_ill_typed_fits :
    Fits (A := persistenceTwoSortAttach) 0 persistenceIllTyped ∧
      ¬ Fits (A := persistenceTwoSortAttach) 1 persistenceIllTyped ∧
      aliens (A := persistenceTwoSortAttach) 1 persistenceIllTyped = [persistenceIllTyped] := by
  refine ⟨?_, ?_, ?_⟩
  · show persistenceTwoSortAttach.res .recur = 0 ∧
        [.app .zero [], .var 0, .app .zero []].length = fArity .recur
    exact ⟨rfl, rfl⟩
  · intro h
    have h1 : persistenceTwoSortAttach.res .recur = 1 := by
      change (persistenceTwoSortAttach.res .recur = 1 ∧
        [.app .zero [], .var 0, .app .zero []].length = fArity .recur) at h
      exact h.1
    exact absurd h1 (by decide)
  · refine aliens_nofit (A := persistenceTwoSortAttach) (s := 1)
      (t := persistenceIllTyped) ?_
    intro h
    have h1 : persistenceTwoSortAttach.res .recur = 1 := by
      change (persistenceTwoSortAttach.res .recur = 1 ∧
        [.app .zero [], .var 0, .app .zero []].length = fArity .recur) at h
      exact h.1
    exact absurd h1 (by decide)

/-- C-MS-03: at sort 1 `proj0` sends the source to `var 2` and its reduct to `zero`, the two
projections are unequal, and no step joins them, so the step-or-equal-stutter simulation of `proj0`
fails. -/
theorem persistence_proj0_no_simulation :
    proj0 (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 1
        persistenceIllTyped = .var 2 ∧
      proj0 (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 1
        (.app .zero []) = .app .zero [] ∧
      proj0 (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 1
          persistenceIllTyped ≠
        proj0 (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 1
          (.app .zero []) ∧
      ¬ (Step freeRecursorTRS
            (proj0 (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 1
              persistenceIllTyped)
            (proj0 (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 1
              (.app .zero [])) ∨
          proj0 (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 1
              persistenceIllTyped =
            proj0 (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 1
              (.app .zero [])) := by
  have h1 : proj0 (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 1
      persistenceIllTyped = .var 2 := by decide
  have h2 : proj0 (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 1
      (.app .zero []) = .app .zero [] := by decide
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [h1, h2]
    exact fun h => nomatch h
  · rw [h1, h2]
    rintro (h | h)
    · exact not_step_var freeRecursorTRS 2 (.app .zero []) h
    · exact absurd h (fun h' => nomatch h')

/-- C-MS-04: `proj` preserves a fitting redex while `proj0` of its normal form is `var 0`, so the
unrestricted equation `proj = proj0` after `fnf` fails. -/
theorem persistence_proj_not_global_fnf :
    proj (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 0
        persistenceTypedRedex = persistenceTypedRedex ∧
      fnf persistenceTypedRedex = .var 0 ∧
      proj0 (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 0
        (fnf persistenceTypedRedex) = .var 0 ∧
      proj (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 0
          persistenceTypedRedex ≠
        proj0 (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 0
          (fnf persistenceTypedRedex) := by
  have hsn : SN freeRecursorTRS persistenceTypedRedex :=
    freeRecursor_terminates_via_manySorted _
  have hstep : StepStar freeRecursorTRS persistenceTypedRedex (.var 0) :=
    StepStar.single (Step.root (free_root_zero (.var 0) (.var 1)))
  have hnf : FNF (.var 0) := fun u h => not_step_var freeRecursorTRS 0 u h
  have hfnf : fnf persistenceTypedRedex = .var 0 := (fnf_unique hsn hstep hnf).symm
  refine ⟨by decide, hfnf, ?_, ?_⟩
  · rw [hfnf]
    decide
  · rw [hfnf]
    decide

/-- C-MS-08: the successor root step duplicates the frame's alien occurrences and grows the term while
termination holds, and the projections make a strict step, so the layer proof uses the strict
projection case rather than a decrease of the alien list or of the term size. -/
theorem persistence_duplication_control :
    Step freeRecursorTRS
        (.app .recur [.var 0, persistenceIllTyped, .app .succ [.app .zero []]])
        (.app .wrap [persistenceIllTyped,
          .app .recur [.var 0, persistenceIllTyped, .app .zero []]]) ∧
      Step freeRecursorTRS
        (proj (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 0
          (.app .recur [.var 0, persistenceIllTyped, .app .succ [.app .zero []]]))
        (proj (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 0
          (.app .wrap [persistenceIllTyped,
            .app .recur [.var 0, persistenceIllTyped, .app .zero []]])) ∧
      SN freeRecursorTRS
        (.app .recur [.var 0, persistenceIllTyped, .app .succ [.app .zero []]]) ∧
      Term.size (.app .recur [.var 0, persistenceIllTyped, .app .succ [.app .zero []]]) <
        Term.size (.app .wrap [persistenceIllTyped,
          .app .recur [.var 0, persistenceIllTyped, .app .zero []]]) ∧
      (aliens (A := persistenceTwoSortAttach) 0
          (.app .recur [.var 0, persistenceIllTyped, .app .succ [.app .zero []]])).length <
        (aliens (A := persistenceTwoSortAttach) 0
          (.app .wrap [persistenceIllTyped,
            .app .recur [.var 0, persistenceIllTyped, .app .zero []]])).length := by
  have hvar0 : proj (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 0
      (.var 0) = .var 0 := by decide
  have hz0 : proj (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 0
      (.app .zero []) = .var 0 := by
    have hnot0 : ¬ Fits (A := persistenceTwoSortAttach) 0 (.app .zero []) := by
      intro h
      change (persistenceTwoSortAttach.res .zero = 0 ∧ ([].length : Nat) = fArity .zero) at h
      exact absurd h.1 (by decide)
    rw [proj_nofit (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh)
      (s := 0) (t := .app .zero []) hnot0, fnf_zero]
    decide
  have hz1 : proj (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 1
      (.app .zero []) = .app .zero [] := by
    rw [proj_fit_app (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh)
      (s := 1) (f := .zero) rfl rfl]
    simp [projList]
  have hsucc1 : proj (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 1
      (.app .succ [.app .zero []]) = .app .succ [.app .zero []] := by
    rw [proj_fit_app (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh)
      (s := 1) (f := .succ) rfl rfl]
    simp only [projList]
    rw [show persistenceTwoSortAttach.arg .succ 0 = 1 by rfl]
    rw [hz1]
  have hcall : proj (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 0
      persistenceIllTyped = .app .recur [.var 0, .var 0, .app .zero []] := by
    rw [show persistenceIllTyped =
        (.app .recur [.app .zero [], .var 0, .app .zero []] : FTerm) from rfl]
    rw [proj_fit_app (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh)
      (s := 0) (f := .recur) rfl rfl]
    simp only [projList]
    rw [show persistenceTwoSortAttach.arg .recur (0 + 1) = 0 by rfl,
      show persistenceTwoSortAttach.arg .recur (0 + 1 + 1) = 1 by rfl,
      show persistenceTwoSortAttach.arg .recur 0 = 0 by rfl]
    rw [hz0, hvar0, hz1]
  have hrec : proj (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 0
      (.app .recur [.var 0, persistenceIllTyped, .app .zero []]) =
      .app .recur [.var 0, .app .recur [.var 0, .var 0, .app .zero []], .app .zero []] := by
    rw [proj_fit_app (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh)
      (s := 0) (f := .recur) rfl rfl]
    simp only [projList]
    rw [show persistenceTwoSortAttach.arg .recur (0 + 1) = 0 by rfl,
      show persistenceTwoSortAttach.arg .recur (0 + 1 + 1) = 1 by rfl,
      show persistenceTwoSortAttach.arg .recur 0 = 0 by rfl]
    rw [hvar0, hcall, hz1]
  have hsrc : proj (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 0
      (.app .recur [.var 0, persistenceIllTyped, .app .succ [.app .zero []]]) =
      .app .recur [.var 0, .app .recur [.var 0, .var 0, .app .zero []],
        .app .succ [.app .zero []]] := by
    rw [proj_fit_app (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh)
      (s := 0) (f := .recur) rfl rfl]
    simp only [projList]
    rw [show persistenceTwoSortAttach.arg .recur (0 + 1) = 0 by rfl,
      show persistenceTwoSortAttach.arg .recur (0 + 1 + 1) = 1 by rfl,
      show persistenceTwoSortAttach.arg .recur 0 = 0 by rfl]
    rw [hvar0, hcall, hsucc1]
  have htgt : proj (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh) 0
      (.app .wrap [persistenceIllTyped, .app .recur [.var 0, persistenceIllTyped, .app .zero []]]) =
      .app .wrap [.app .recur [.var 0, .var 0, .app .zero []],
        .app .recur [.var 0, .app .recur [.var 0, .var 0, .app .zero []], .app .zero []]] := by
    rw [proj_fit_app (A := persistenceTwoSortAttach) (inh := manySortedPersistenceWitness.inh)
      (s := 0) (f := .wrap) rfl rfl]
    simp only [projList]
    rw [show persistenceTwoSortAttach.arg .wrap (0 + 1) = 0 by rfl,
      show persistenceTwoSortAttach.arg .wrap 0 = 0 by rfl]
    rw [hcall, hrec]
  refine ⟨Step.root (free_root_succ (.var 0) persistenceIllTyped (.app .zero [])),
    ?_, freeRecursor_terminates_via_manySorted _, ?_, ?_⟩
  · rw [hsrc, htgt]
    exact Step.root (free_root_succ (.var 0)
      (.app .recur [.var 0, .var 0, .app .zero []]) (.app .zero []))
  · decide
  · decide

/-- Under the rule typing, every sort that appears as a result sort or as a within-arity argument
sort is one of the three variable sorts of the two rules. -/
theorem persistence_active_sort_cases {S : Type} {A : SortAttach FreeSym S}
    (hRules : ∀ rule ∈ freeRecursorTRS, ∃ s,
      HasSort fArity A rule.lhs s ∧ HasSort fArity A rule.rhs s) :
    ∀ s, persistenceActiveSort A s → s = A.var 0 ∨ s = A.var 1 ∨ s = A.var 2 := by
  obtain ⟨s0, hl0, hr0⟩ := hRules zeroRule (by simp [freeRecursorTRS])
  obtain ⟨s1, hl1, hr1⟩ := hRules succRule (by simp [freeRecursorTRS])
  obtain ⟨hs0, -, hargs0⟩ := hasSort_app_iff.1 hl0
  have hr0' := hasSort_var_iff.1 hr0
  have h00 := hasSort_var_iff.1 (hargs0 0 _ rfl)
  have h01 := hasSort_var_iff.1 (hargs0 1 _ rfl)
  have h02 := (hasSort_app_iff.1 (hargs0 2 _ rfl)).1
  obtain ⟨hs1, -, hargs1⟩ := hasSort_app_iff.1 hl1
  have h11 := hasSort_var_iff.1 (hargs1 1 _ rfl)
  obtain ⟨h12, -, hsucc⟩ := hasSort_app_iff.1 (hargs1 2 _ rfl)
  have hsv := hasSort_var_iff.1 (hsucc 0 _ rfl)
  obtain ⟨hw, -, hwargs⟩ := hasSort_app_iff.1 hr1
  have hw0 := hasSort_var_iff.1 (hwargs 0 _ rfl)
  obtain ⟨hw1, -, hrargs⟩ := hasSort_app_iff.1 (hwargs 1 _ rfl)
  have hr2 := hasSort_var_iff.1 (hrargs 2 _ rfl)
  have e_rec : A.res .recur = A.var 0 := hs0.symm.trans hr0'
  have e_zero : A.res .zero = A.var 2 := h02.symm.trans hr2
  have e_succ : A.res .succ = A.var 2 := h12.symm.trans hr2
  have e_wrap : A.res .wrap = A.var 0 := (hw.symm.trans hs1).trans (hs0.symm.trans hr0')
  have e_rec2 : A.arg .recur 2 = A.var 2 := hr2
  have e_wrap1 : A.arg .wrap 1 = A.var 0 := hw1.trans (hs0.symm.trans hr0')
  intro s hs
  rcases hs with ⟨f, rfl⟩ | ⟨f, i, hi, rfl⟩
  · cases f with
    | zero => exact Or.inr (Or.inr e_zero)
    | succ => exact Or.inr (Or.inr e_succ)
    | wrap => exact Or.inl e_wrap
    | recur => exact Or.inl e_rec
  · cases f with
    | zero => exact absurd hi (by simp [fArity])
    | succ =>
        have hi0 : i = 0 := by
          have hlt : i < 1 := by simpa [fArity] using hi
          omega
        subst hi0
        exact Or.inr (Or.inr hsv)
    | wrap =>
        have hlt : i < 2 := by simpa [fArity] using hi
        interval_cases i
        · exact Or.inr (Or.inl hw0)
        · exact Or.inl e_wrap1
    | recur =>
        have hlt : i < 3 := by simpa [fArity] using hi
        interval_cases i
        · exact Or.inl h00
        · exact Or.inr (Or.inl h01)
        · exact Or.inr (Or.inr e_rec2)

/-- The derived inhabitant has the declared variable sort at every active sort. No claim is made
for an inactive sort. -/
theorem persistence_active_inh_spec {S : Type} [DecidableEq S] {A : SortAttach FreeSym S}
    (hRules : ∀ rule ∈ freeRecursorTRS, ∃ s,
      HasSort fArity A rule.lhs s ∧ HasSort fArity A rule.rhs s) :
    ∀ s, persistenceActiveSort A s → A.var (persistenceActiveInh A s) = s := by
  intro s hs
  rcases persistence_active_sort_cases hRules s hs with h | h | h
  · subst h
    rw [persistenceActiveInh, if_pos rfl]
  · subst h
    rw [persistenceActiveInh]
    by_cases h0 : A.var 1 = A.var 0
    · rw [if_pos h0]
      exact h0.symm
    · rw [if_neg h0, if_pos rfl]
  · subst h
    rw [persistenceActiveInh]
    by_cases h0 : A.var 2 = A.var 0
    · rw [if_pos h0]
      exact h0.symm
    · by_cases h1 : A.var 2 = A.var 1
      · rw [if_neg h0, if_pos h1]
        exact h1.symm
      · rw [if_neg h0, if_neg h1]

/-! ### MS-5 strengthening: projections typed from active-sort inhabitance -/

/-- Every `proj0`-layer of an active sort is well sorted, from inhabitance of active sorts only. -/
theorem persistence_hasSort_proj0_active {S : Type} [DecidableEq S]
    (A : SortAttach FreeSym S) (inh : S → Nat)
    (hinh : ∀ s, persistenceActiveSort A s → A.var (inh s) = s) :
    ∀ (t : FTerm) (s : S), persistenceActiveSort A s → HasSort fArity A (proj0 A inh s t) s := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
    intro s hs
    simp only [proj0]
    split_ifs with h
    · rw [← h]
      exact .var x
    · have := HasSort.var (ar := fArity) (A := A) (inh s)
      rwa [hinh s hs] at this
  | happ f args ih =>
    intro s hs
    simp only [proj0]
    split_ifs with h
    · obtain ⟨rfl, hlen⟩ := h
      refine .app f _ (by rw [proj0List_length]; exact hlen) fun i a hi => ?_
      rw [proj0List_getElem?, Option.map_eq_some_iff] at hi
      obtain ⟨b, hb, rfl⟩ := hi
      have hlt : i < fArity f := by
        have := (List.getElem?_eq_some_iff.mp hb).1
        omega
      have hact : persistenceActiveSort A (A.arg f (0 + i)) := by
        simpa using (Or.inr ⟨f, i, hlt, rfl⟩ : persistenceActiveSort A (A.arg f i))
      have := ih b (List.mem_of_getElem? hb) (A.arg f (0 + i)) hact
      simpa using this
    · have := HasSort.var (ar := fArity) (A := A) (inh s)
      rwa [hinh s hs] at this

/-- Every `proj`-layer of an active sort is well sorted, from inhabitance of active sorts only; the
nonfitting case types the `proj0`-layer of the chosen normal form, so no termination premise is
needed. -/
theorem persistence_hasSort_proj_active {S : Type} [DecidableEq S]
    (A : SortAttach FreeSym S) (inh : S → Nat)
    (hinh : ∀ s, persistenceActiveSort A s → A.var (inh s) = s) :
    ∀ (t : FTerm) (s : S), persistenceActiveSort A s → HasSort fArity A (proj A inh s t) s := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
    intro s hs
    simp only [proj]
    split_ifs with h
    · rw [← h]
      exact .var x
    · have := HasSort.var (ar := fArity) (A := A) (inh s)
      rwa [hinh s hs] at this
  | happ f args ih =>
    intro s hs
    simp only [proj]
    split_ifs with h
    · obtain ⟨rfl, hlen⟩ := h
      refine .app f _ (by rw [projList_length]; exact hlen) fun i a hi => ?_
      rw [projList_getElem?, Option.map_eq_some_iff] at hi
      obtain ⟨b, hb, rfl⟩ := hi
      have hlt : i < fArity f := by
        have := (List.getElem?_eq_some_iff.mp hb).1
        omega
      have hact : persistenceActiveSort A (A.arg f (0 + i)) := by
        simpa using (Or.inr ⟨f, i, hlt, rfl⟩ : persistenceActiveSort A (A.arg f i))
      have := ih b (List.mem_of_getElem? hb) (A.arg f (0 + i)) hact
      simpa using this
    · exact persistence_hasSort_proj0_active A inh hinh _ s hs

/-- MS-5 strengthening. Every free-recursor term terminates when the two rules are well sorted under
an arbitrary sort assignment and the sorted system terminates. The type exposes no inhabitance
function and no decidability instance; the inhabitant is derived from the rules and used classically
inside. -/
theorem freeRecursor_sorted_persistence {S : Type} (A : SortAttach FreeSym S)
    (hRules : ∀ rule ∈ freeRecursorTRS, ∃ s,
      HasSort fArity A rule.lhs s ∧ HasSort fArity A rule.rhs s)
    (hST : SortedTerminates fArity A freeRecursorTRS) :
    ∀ t : FTerm, SN freeRecursorTRS t := by
  classical
  have hinh : ∀ s, persistenceActiveSort A s → A.var (persistenceActiveInh A s) = s :=
    persistence_active_inh_spec hRules
  intro t
  induction t using Term.rec' with
  | hvar x =>
    exact Acc.intro _ (fun y h => False.elim (not_step_var _ x y h))
  | happ f args ih =>
    by_cases hlen : args.length = fArity f
    · refine persistence_layer_sn_of_typed_projection A (persistenceActiveInh A) (A.res f)
        (consistent_of_rules hRules) (fun x => ?_) hST (.app f args)
        (persistence_aliens_sn_of_args A f args hlen ih)
      exact persistence_hasSort_proj_active A (persistenceActiveInh A) hinh x (A.res f)
        (Or.inl ⟨f, rfl⟩)
    · exact persistence_bad_arity_sn f args hlen ih

/-- MS-5 strengthening. Rule-typed sorted termination of the free recursor is equivalent to
termination of every term. -/
theorem freeRecursor_sorted_persistence_iff {S : Type} (A : SortAttach FreeSym S)
    (hRules : ∀ rule ∈ freeRecursorTRS, ∃ s,
      HasSort fArity A rule.lhs s ∧ HasSort fArity A rule.rhs s) :
    SortedTerminates fArity A freeRecursorTRS ↔ ∀ t : FTerm, SN freeRecursorTRS t := by
  refine ⟨freeRecursor_sorted_persistence A hRules, ?_⟩
  intro hAll
  have hsub : ∀ x, Acc (fun y x => Step freeRecursorTRS x y) x →
      Acc (fun y x => SortedStep fArity A freeRecursorTRS x y) x := by
    intro x hx
    induction hx with
    | intro x _ ih =>
      exact Acc.intro x (fun y hy => ih y hy.2)
  intro t s _
  exact hsub t (hAll t)

/-! ### MS-5 control: a three-sort assignment with one unused sort -/

/-- The two witness sorts read as sorts of `Fin 3`, leaving sort 2 unused. -/
def persistenceTwoSortToThree : Fin 2 → Fin 3
  | 0 => 0
  | 1 => 1

theorem persistenceTwoSortToThree_ne_two (s : Fin 2) : persistenceTwoSortToThree s ≠ 2 := by
  fin_cases s <;> decide

/-- A three-sort attachment: the witness attachment transported along the embedding, so sort 2 holds
no symbol result, no declared argument sort and no variable sort. -/
def persistenceUnusedSortAttach : SortAttach FreeSym (Fin 3) where
  arg := fun f i => persistenceTwoSortToThree (persistenceTwoSortAttach.arg f i)
  res := fun f => persistenceTwoSortToThree (persistenceTwoSortAttach.res f)
  var := fun x => persistenceTwoSortToThree (persistenceTwoSortAttach.var x)

/-- HasSort transports along a sort map that commutes with the attachment. -/
theorem persistence_hasSort_map {S S' : Type} (φ : S → S')
    {A : SortAttach FreeSym S} {A' : SortAttach FreeSym S'}
    (harg : ∀ f i, φ (A.arg f i) = A'.arg f i)
    (hres : ∀ f, φ (A.res f) = A'.res f)
    (hvar : ∀ x, φ (A.var x) = A'.var x) :
    ∀ {t : FTerm} {s : S}, HasSort fArity A t s → HasSort fArity A' t (φ s) := by
  intro t s h
  induction h with
  | var x =>
    rw [hvar x]
    exact .var x
  | app f args hlen hargs ih =>
    rw [hres f]
    refine .app f args hlen fun i a hi => ?_
    have := ih i a hi
    rwa [harg f i] at this

theorem persistenceUnusedSort_rules :
    ∀ rule ∈ freeRecursorTRS, ∃ s : Fin 3,
      HasSort fArity persistenceUnusedSortAttach rule.lhs s ∧
        HasSort fArity persistenceUnusedSortAttach rule.rhs s := by
  intro rule hrule
  obtain ⟨s, hl, hr⟩ := manySortedPersistenceWitness_laws.2 rule hrule
  exact ⟨persistenceTwoSortToThree s,
    persistence_hasSort_map persistenceTwoSortToThree (fun _ _ => rfl) (fun _ => rfl)
      (fun _ => rfl) hl,
    persistence_hasSort_map persistenceTwoSortToThree (fun _ _ => rfl) (fun _ => rfl)
      (fun _ => rfl) hr⟩

/-- MS-5 control. With `Fin 3` and sort 2 unused, no function inhabits every sort, sort 2 is inactive,
the rules are still well sorted, the sorted system still terminates, and the rule-only persistence
theorem still applies. The control is downstream: it consumes the two-sort all-term theorem. -/
theorem persistence_unused_sort_control :
    (¬ ∃ inh : Fin 3 → Nat, ∀ s, persistenceUnusedSortAttach.var (inh s) = s) ∧
      ¬ persistenceActiveSort persistenceUnusedSortAttach 2 ∧
      (∀ rule ∈ freeRecursorTRS, ∃ s : Fin 3,
        HasSort fArity persistenceUnusedSortAttach rule.lhs s ∧
          HasSort fArity persistenceUnusedSortAttach rule.rhs s) ∧
      SortedTerminates fArity persistenceUnusedSortAttach freeRecursorTRS ∧
      (∀ t : FTerm, SN freeRecursorTRS t) := by
  have hAll : ∀ t : FTerm, SN freeRecursorTRS t := freeRecursor_terminates_via_manySorted
  have hST : SortedTerminates fArity persistenceUnusedSortAttach freeRecursorTRS :=
    fun t _ _ => Subrelation.accessible (fun h => h.2) (hAll t)
  refine ⟨?_, ?_, persistenceUnusedSort_rules, hST, ?_⟩
  · rintro ⟨inh, h⟩
    exact persistenceTwoSortToThree_ne_two _ (h 2)
  · rintro (⟨f, h⟩ | ⟨f, i, -, h⟩)
    · exact persistenceTwoSortToThree_ne_two _ h
    · exact persistenceTwoSortToThree_ne_two _ h
  · exact freeRecursor_sorted_persistence persistenceUnusedSortAttach
      persistenceUnusedSort_rules hST

end OperatorKO7.Methods.OrientationClosure.MethodRowsSortedConstrained



