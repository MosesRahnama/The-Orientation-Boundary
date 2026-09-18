import Mathlib
import OperatorKO7.Meta.Rewriting.Rewrite
import OperatorKO7.Meta.Methods.OrientationClosure.SchemaCore
import OperatorKO7.Meta.Methods.OrientationClosure.CellClassification
import OperatorKO7.Meta.Methods.OrientationClosure.PolynomialOrientationDecision
import OperatorKO7.Meta.Methods.OrientationClosure.PathOrderNativeSemantics

/-!
# KBO method rows of the Orientation Boundary closeout

Eight rows of `RDRSMethodFamily`: `standardKBO`, `subtermCoefficientKBO`, `kboWithStatus`,
`generalizedKBO`, `transfiniteKBO`, `lambdaFreeKBO`, `polynomialKBO`, `acKBO`.

Part 1 is one first-order KBO core over an arbitrary signature (`Meta.Rewriting.Term`), shared by
the standard, subterm-coefficient, status, transfinite and AC rows. Part 2 is the generalized KBO
over a weakly monotone strictly simple algebra, shared by the generalized and polynomial rows.
Part 3 is the lambda-free higher-order KBO.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.MethodRowsKBO

open OperatorKO7.Meta.Rewriting (Term Subst)

universe u

/-! ## Part 1. The shared first-order KBO core -/

/-- Argument status of a function symbol: lexicographic (Becker, Blanchette, Waldmann, Wand 2017,
Definition 4, on tuples of equal length) or multiset (ibid., Definition 6, Huet–Oppen form). -/
inductive KStatus
  | lex
  | mul
  deriving DecidableEq, Repr

/-- Native data of a first-order Knuth–Bendix order over symbol names `sigma` with weights in `W`.
`arOK f n` says that `f` may be applied to `n` arguments (for a ranked signature, `n = ar f`). -/
structure KBOCore (sigma : Type) (W : Type u) where
  /-- Admissible arities of each symbol. -/
  arOK : sigma → ℕ → Prop
  /-- Variable weight. -/
  w0 : W
  /-- Symbol weights. -/
  weight : sigma → W
  /-- Subterm coefficient of argument position `i` of `f`. -/
  coeff : sigma → ℕ → ℕ
  /-- Strict precedence: `prec f g` means `f ≻ g`. -/
  prec : sigma → sigma → Prop
  /-- Argument status. -/
  status : sigma → KStatus

section Eval

variable {sigma nu : Type} {V : Type u} [AddCommMonoid V]

mutual
/-- Weighted evaluation of a first-order term: variables are valued by `v`, symbol `f`
contributes `ws f`, and argument position `i` of `f` is scaled by the coefficient `c f i`. -/
def ev (c : sigma → ℕ → ℕ) (ws : sigma → V) (v : nu → V) : Term sigma nu → V
  | .var x => v x
  | .app f args => ws f + evL c ws v f 0 args
/-- Weighted evaluation of an argument list of `f`, starting at argument position `i`. -/
def evL (c : sigma → ℕ → ℕ) (ws : sigma → V) (v : nu → V) (f : sigma) :
    ℕ → List (Term sigma nu) → V
  | _, [] => 0
  | i, a :: as => c f i • ev c ws v a + evL c ws v f (i + 1) as
end

@[simp] theorem ev_var (c : sigma → ℕ → ℕ) (ws : sigma → V) (v : nu → V) (x : nu) :
    ev c ws v (.var x : Term sigma nu) = v x := rfl

@[simp] theorem ev_app (c : sigma → ℕ → ℕ) (ws : sigma → V) (v : nu → V) (f : sigma)
    (args : List (Term sigma nu)) :
    ev c ws v (.app f args) = ws f + evL c ws v f 0 args := rfl

@[simp] theorem evL_nil (c : sigma → ℕ → ℕ) (ws : sigma → V) (v : nu → V) (f : sigma) (i : ℕ) :
    evL c ws v f i ([] : List (Term sigma nu)) = 0 := rfl

@[simp] theorem evL_cons (c : sigma → ℕ → ℕ) (ws : sigma → V) (v : nu → V) (f : sigma) (i : ℕ)
    (a : Term sigma nu) (as : List (Term sigma nu)) :
    evL c ws v f i (a :: as) = c f i • ev c ws v a + evL c ws v f (i + 1) as := rfl

/-- Splitting a weighted argument sum at an append. -/
theorem evL_append (c : sigma → ℕ → ℕ) (ws : sigma → V) (v : nu → V) (f : sigma) :
    ∀ (i : ℕ) (l₁ l₂ : List (Term sigma nu)),
      evL c ws v f i (l₁ ++ l₂) = evL c ws v f i l₁ + evL c ws v f (i + l₁.length) l₂
  | i, [], l₂ => by simp
  | i, a :: l₁, l₂ => by
      rw [List.cons_append, evL_cons, evL_cons, evL_append c ws v f (i + 1) l₁ l₂,
        List.length_cons, show i + 1 + l₁.length = i + (l₁.length + 1) by omega, add_assoc]

/-- Evaluation commutes with first-order substitution. -/
theorem ev_subst (c : sigma → ℕ → ℕ) (ws : sigma → V) (v : nu → V) (σ : Subst sigma nu) :
    ∀ t : Term sigma nu,
      ev c ws v (Subst.apply σ t) = ev c ws (fun y => ev c ws v (σ y)) t := by
  intro t
  induction t using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
      rw [Subst.apply_app, ev_app, ev_app, Subst.applyList_eq_map]
      congr 1
      suffices h : ∀ (l : List (Term sigma nu)),
          (∀ a ∈ l, ev c ws v (Subst.apply σ a) = ev c ws (fun y => ev c ws v (σ y)) a) →
            ∀ i, evL c ws v f i (l.map (Subst.apply σ)) =
              evL c ws (fun y => ev c ws v (σ y)) f i l from h args ih 0
      intro l hl
      induction l with
      | nil => intro i; rfl
      | cons a as ihl =>
          intro i
          rw [List.map_cons, evL_cons, evL_cons, hl a (by simp),
            ihl (fun b hb => hl b (by simp [hb])) (i + 1)]

/-- Evaluation depends only on the values of the variables that occur. -/
theorem ev_congr [DecidableEq nu] (c : sigma → ℕ → ℕ) (ws : sigma → V) (v v' : nu → V) :
    ∀ t : Term sigma nu, (∀ y ∈ Term.vars t, v y = v' y) → ev c ws v t = ev c ws v' t := by
  intro t
  induction t using Term.rec' with
  | hvar x => intro h; exact h x (by simp)
  | happ f args ih =>
      intro h
      rw [ev_app, ev_app]
      congr 1
      suffices hs : ∀ (l : List (Term sigma nu)), (∀ a ∈ l, (∀ y ∈ Term.vars a, v y = v' y) →
          ev c ws v a = ev c ws v' a) → (∀ a ∈ l, ∀ y ∈ Term.vars a, v y = v' y) →
            ∀ i, evL c ws v f i l = evL c ws v' f i l from
        hs args ih (fun a ha y hy => h y (by
          rw [Term.vars_app, Term.mem_varsList_iff]; exact ⟨a, ha, hy⟩)) 0
      intro l hl hvars
      induction l with
      | nil => intro i; rfl
      | cons a as ihl =>
          intro i
          rw [evL_cons, evL_cons, hl a (by simp) (hvars a (by simp)),
            ihl (fun b hb => hl b (by simp [hb])) (fun b hb => hvars b (by simp [hb])) (i + 1)]

end Eval

/-! ### Weighted occurrence counts and single-variable linearity -/

section Count

variable {sigma nu : Type} [DecidableEq nu]

/-- Weighted occurrence count of the variable `x` in `t`: the sum over the occurrences of `x`
of the product of the subterm coefficients on the path (Ludwig and Waldmann 2007, Definition 16
summed over positions; the variable coefficient `vc(x, t)` of Yamada, Kusakari, Sakabe 2015,
Section 2.1.4). With all coefficients `1` it is the occurrence count `|t|_x`. -/
def cnt (c : sigma → ℕ → ℕ) (x : nu) (t : Term sigma nu) : ℕ :=
  ev c (fun _ => (0 : ℕ)) (fun y => if y = x then 1 else 0) t

theorem cnt_var (c : sigma → ℕ → ℕ) (x y : nu) :
    cnt c x (.var y : Term sigma nu) = if y = x then 1 else 0 := rfl

theorem cnt_app (c : sigma → ℕ → ℕ) (x : nu) (f : sigma) (args : List (Term sigma nu)) :
    cnt c x (.app f args) =
      evL c (fun _ => (0 : ℕ)) (fun y => if y = x then 1 else 0) f 0 args := by
  simp [cnt]

variable {V : Type u} [AddCommMonoid V]

/-- Single-variable linearity of weighted evaluation: changing the value of one variable from `b`
to `a` changes the evaluation by `cnt x t` copies of the difference, expressed without
subtraction. -/
theorem ev_update_linear (c : sigma → ℕ → ℕ) (ws : sigma → V) (v : nu → V) (x : nu) (a b : V) :
    ∀ t : Term sigma nu,
      ev c ws (Function.update v x a) t + cnt c x t • b =
        ev c ws (Function.update v x b) t + cnt c x t • a := by
  intro t
  induction t using Term.rec' with
  | hvar y =>
      rw [ev_var, ev_var, cnt_var]
      by_cases hy : y = x
      · subst hy
        simp [add_comm]
      · simp [hy]
  | happ f args ih =>
      rw [ev_app, ev_app, cnt_app]
      suffices hs : ∀ (l : List (Term sigma nu)), (∀ t ∈ l,
          ev c ws (Function.update v x a) t + cnt c x t • b =
            ev c ws (Function.update v x b) t + cnt c x t • a) → ∀ i,
          evL c ws (Function.update v x a) f i l +
              evL c (fun _ => (0 : ℕ)) (fun y => if y = x then 1 else 0) f i l • b =
            evL c ws (Function.update v x b) f i l +
              evL c (fun _ => (0 : ℕ)) (fun y => if y = x then 1 else 0) f i l • a by
        rw [add_assoc, add_assoc, hs args ih 0]
      intro l hl
      induction l with
      | nil => intro i; simp
      | cons t ts ihl =>
          intro i
          have h1 := hl t (by simp)
          have h2 := ihl (fun s hs => hl s (by simp [hs])) (i + 1)
          simp only [cnt] at h1
          simp only [evL_cons, smul_eq_mul, add_nsmul, ← smul_smul]
          calc _ = c f i • (ev c ws (Function.update v x a) t +
                  ev c (fun _ => (0 : ℕ)) (fun y => if y = x then 1 else 0) t • b) +
                (evL c ws (Function.update v x a) f (i + 1) ts +
                  evL c (fun _ => (0 : ℕ)) (fun y => if y = x then 1 else 0) f (i + 1) ts • b) := by
                rw [nsmul_add]; abel
            _ = c f i • (ev c ws (Function.update v x b) t +
                  ev c (fun _ => (0 : ℕ)) (fun y => if y = x then 1 else 0) t • a) +
                (evL c ws (Function.update v x b) f (i + 1) ts +
                  evL c (fun _ => (0 : ℕ)) (fun y => if y = x then 1 else 0) f (i + 1) ts • a) := by
                rw [h1, h2]
            _ = _ := by rw [nsmul_add]; abel

end Count

/-! ### Order-theoretic arithmetic in the weight monoid -/

section OrderedWeight

variable {W : Type u} [AddCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W]

theorem nsmul_le_nsmul_of_le' {a b : W} (h : a ≤ b) : ∀ n : ℕ, n • a ≤ n • b
  | 0 => by simp
  | n + 1 => by
      rw [succ_nsmul, succ_nsmul]
      exact add_le_add (nsmul_le_nsmul_of_le' h n) h

theorem nsmul_lt_nsmul_of_lt' {a b : W} (h : a < b) : ∀ {n : ℕ}, 1 ≤ n → n • a < n • b
  | 0, hn => absurd hn (by norm_num)
  | n + 1, _ => by
      rw [succ_nsmul, succ_nsmul]
      exact add_lt_add_of_le_of_lt (nsmul_le_nsmul_of_le' h.le n) h

theorem le_nsmul_of_one_le' {a : W} (ha : 0 ≤ a) {n : ℕ} (hn : 1 ≤ n) : a ≤ n • a := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [succ_nsmul]
  exact le_add_of_nonneg_left (nsmul_nonneg ha m)

theorem lt_nsmul_of_two_le' {a : W} (ha : 0 < a) {n : ℕ} (hn : 2 ≤ n) : a < n • a := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [succ_nsmul, succ_nsmul]
  calc a < a + a := lt_add_of_pos_left a ha
    _ ≤ m • a + a + a := add_le_add_right (le_add_of_nonneg_left (nsmul_nonneg ha.le m)) a

/-- A part of a sum of nonnegative parts is strictly below the sum as soon as one other part is
positive or the part itself is strictly enlarged. -/
theorem lt_add_add_of_parts {x w A cb B : W} (hw : 0 ≤ w) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx : x ≤ cb) (hstrict : 0 < w ∨ 0 < A ∨ 0 < B ∨ x < cb) : x < w + (A + (cb + B)) := by
  rcases hstrict with h | h | h | h
  · calc x ≤ cb := hx
      _ ≤ A + (cb + B) := (le_add_of_nonneg_right hB).trans (le_add_of_nonneg_left hA)
      _ < w + (A + (cb + B)) := lt_add_of_pos_left _ h
  · calc x ≤ cb + B := le_add_of_le_of_nonneg hx hB
      _ < A + (cb + B) := lt_add_of_pos_left _ h
      _ ≤ w + (A + (cb + B)) := le_add_of_nonneg_left hw
  · calc x ≤ cb := hx
      _ < cb + B := lt_add_of_pos_right _ h
      _ ≤ A + (cb + B) := le_add_of_nonneg_left hA
      _ ≤ w + (A + (cb + B)) := le_add_of_nonneg_left hw
  · calc x < cb := h
      _ ≤ cb + B := le_add_of_nonneg_right hB
      _ ≤ A + (cb + B) := le_add_of_nonneg_left hA
      _ ≤ w + (A + (cb + B)) := le_add_of_nonneg_left hw

variable {sigma nu : Type}

theorem ev_nonneg (c : sigma → ℕ → ℕ) {ws : sigma → W} {v : nu → W}
    (hws : ∀ f, 0 ≤ ws f) (hv : ∀ x, 0 ≤ v x) : ∀ t : Term sigma nu, 0 ≤ ev c ws v t := by
  intro t
  induction t using Term.rec' with
  | hvar x => exact hv x
  | happ f args ih =>
      rw [ev_app]
      refine add_nonneg (hws f) ?_
      suffices h : ∀ (l : List (Term sigma nu)), (∀ a ∈ l, 0 ≤ ev c ws v a) →
          ∀ i, 0 ≤ evL c ws v f i l from h args ih 0
      intro l hl
      induction l with
      | nil => intro i; simp
      | cons a as ihl =>
          intro i
          rw [evL_cons]
          exact add_nonneg (nsmul_nonneg (hl a (by simp)) _)
            (ihl (fun b hb => hl b (by simp [hb])) _)

theorem evL_nonneg (c : sigma → ℕ → ℕ) {ws : sigma → W} {v : nu → W}
    (hws : ∀ f, 0 ≤ ws f) (hv : ∀ x, 0 ≤ v x) (f : sigma) :
    ∀ (l : List (Term sigma nu)) (i : ℕ), 0 ≤ evL c ws v f i l
  | [], _ => by simp
  | a :: as, i => by
      rw [evL_cons]
      exact add_nonneg (nsmul_nonneg (ev_nonneg c hws hv a) _) (evL_nonneg c hws hv f as (i + 1))

theorem ev_le_evL_of_mem (c : sigma → ℕ → ℕ) {ws : sigma → W} {v : nu → W}
    (hws : ∀ f, 0 ≤ ws f) (hv : ∀ x, 0 ≤ v x) (hc : ∀ f i, 1 ≤ c f i) (f : sigma) :
    ∀ (l : List (Term sigma nu)) (i : ℕ) (b : Term sigma nu), b ∈ l →
      ev c ws v b ≤ evL c ws v f i l
  | [], _, _, hb => absurd hb (by simp)
  | a :: as, i, b, hb => by
      rw [evL_cons]
      rcases List.mem_cons.1 hb with rfl | hb'
      · exact le_add_of_le_of_nonneg (le_nsmul_of_one_le' (ev_nonneg c hws hv _) (hc f i))
          (evL_nonneg c hws hv f as (i + 1))
      · exact le_add_of_nonneg_of_le (nsmul_nonneg (ev_nonneg c hws hv a) _)
          (ev_le_evL_of_mem c hws hv hc f as (i + 1) b hb')

end OrderedWeight

/-! ### Lexicographic and multiset extensions -/

section Ext

variable {α : Type}

/-- `LexLT r l' l`: the lists have the same length and `l'` is below `l` at the first position
where they differ (Becker et al. 2017, Definition 4, restricted to tuples of equal length). -/
def LexLT (r : α → α → Prop) (l' l : List α) : Prop :=
  l'.length = l.length ∧ ∃ (i : ℕ) (hi' : i < l'.length) (hi : i < l.length),
    l'.take i = l.take i ∧ r l'[i] l[i]

/-- The lexicographic comparison restricted to lists whose elements are accessible. -/
def LexA (r : α → α → Prop) (l' l : List α) : Prop :=
  LexLT r l' l ∧ ∀ a ∈ l', Acc r a

/-- Lists of accessible elements are accessible for the lexicographic comparison. -/
theorem acc_lexA (r : α → α → Prop) :
    ∀ (n : ℕ) (l : List α), l.length = n → (∀ a ∈ l, Acc r a) → Acc (LexA r) l := by
  intro n
  induction n with
  | zero =>
      intro l hl _
      refine Acc.intro _ ?_
      rintro l' ⟨⟨_, i, _, hi, _⟩, _⟩
      rw [List.length_eq_zero_iff.1 hl] at hi
      simp at hi
  | succ n ihn =>
      have key : ∀ a, Acc r a → ∀ l₀ : List α, l₀.length = n → (∀ b ∈ l₀, Acc r b) →
          Acc (LexA r) (a :: l₀) := by
        intro a ha
        induction ha with
        | intro a _ iha =>
            intro l₀ hl₀ hacc₀
            have hA : Acc (LexA r) l₀ := ihn l₀ hl₀ hacc₀
            revert hl₀ hacc₀
            induction hA with
            | intro l₀ _ ihl =>
                intro hl₀ hacc₀
                refine Acc.intro _ ?_
                rintro l' ⟨⟨hlen, i, hi', hi, htake, hr⟩, hacc'⟩
                cases l' with
                | nil => simp at hlen
                | cons a' l₀' =>
                    have hlen' : l₀'.length = l₀.length := by simpa using hlen
                    cases i with
                    | zero =>
                        have hr0 : r a' a := by simpa using hr
                        exact iha a' hr0 l₀' (hlen'.trans hl₀)
                          (fun b hb => hacc' b (by simp [hb]))
                    | succ j =>
                        have ht : a' = a ∧ l₀'.take j = l₀.take j := by simpa using htake
                        obtain ⟨rfl, htj⟩ := ht
                        have hj' : j < l₀'.length := by simpa using hi'
                        have hj : j < l₀.length := by simpa using hi
                        have hrj : r l₀'[j] l₀[j] := by simpa using hr
                        exact ihl l₀' ⟨⟨hlen', j, hj', hj, htj, hrj⟩,
                            fun b hb => hacc' b (by simp [hb])⟩
                          (hlen'.trans hl₀) (fun b hb => hacc' b (by simp [hb]))
      intro l hl hacc
      cases l with
      | nil => simp at hl
      | cons a l₀ =>
          exact key a (hacc a (by simp)) l₀ (by simpa using hl)
            (fun b hb => hacc b (by simp [hb]))

variable [DecidableEq α]

/-- The Huet–Oppen multiset extension (Becker et al. 2017, Definition 6): `HOGt r B A` states that
`B` is above `A`, with `r x y` read as `x` above `y`. -/
def HOGt (r : α → α → Prop) (B A : Multiset α) : Prop :=
  B ≠ A ∧ ∀ y, Multiset.count y B < Multiset.count y A →
    ∃ x, r x y ∧ Multiset.count x A < Multiset.count x B

/-- A Dershowitz–Manna replacement is a finite chain of single-element replacements
(`Relation.CutExpand`). -/
theorem transGen_cutExpand_of_dominated (rs : α → α → Prop) :
    ∀ (X : Multiset α), X ≠ 0 → ∀ (K Y : Multiset α), (∀ y ∈ Y, ∃ x ∈ X, rs y x) →
      Relation.TransGen (Relation.CutExpand rs) (K + Y) (K + X) := by
  intro X
  induction X using Multiset.induction_on with
  | empty => intro h; exact absurd rfl h
  | cons x X₀ ih =>
      intro _ K Y hdom
      by_cases hX₀ : X₀ = 0
      · subst hX₀
        refine Relation.TransGen.single ⟨Y, x, ?_, ?_⟩
        · intro y hy
          obtain ⟨x', hx', hr⟩ := hdom y hy
          rw [Multiset.mem_cons] at hx'
          rcases hx' with rfl | hx'
          · exact hr
          · simp at hx'
        · rw [← Multiset.singleton_add, add_zero]; abel
      · classical
        let P : α → Prop := fun y => ∃ x₀ ∈ X₀, rs y x₀
        have hY : Y.filter P + Y.filter (fun y => ¬ P y) = Y := Multiset.filter_add_not P Y
        have h1 : Relation.TransGen (Relation.CutExpand rs) (K + {x} + Y.filter P)
            (K + {x} + X₀) :=
          ih hX₀ (K + {x}) (Y.filter P) (fun y hy => (Multiset.mem_filter.1 hy).2)
        have h2 : Relation.CutExpand rs (K + Y) (K + Y.filter P + {x}) := by
          refine ⟨Y.filter (fun y => ¬ P y), x, ?_, ?_⟩
          · intro y hy
            obtain ⟨hyY, hnP⟩ := Multiset.mem_filter.1 hy
            obtain ⟨x', hx', hr⟩ := hdom y hyY
            rcases Multiset.mem_cons.1 hx' with rfl | hx'
            · exact hr
            · exact absurd ⟨x', hx', hr⟩ hnP
          · conv_lhs => rw [← hY]
            abel
        have e1 : K + {x} + Y.filter P = K + Y.filter P + {x} := by abel
        have e2 : K + {x} + X₀ = K + x ::ₘ X₀ := by rw [← Multiset.singleton_add]; abel
        rw [e1, e2] at h1
        exact Relation.TransGen.head h2 h1

/-- A Huet–Oppen step is a finite chain of single-element replacements. -/
theorem hoGt_transGen (r : α → α → Prop) {B A : Multiset α} (h : HOGt r B A) :
    Relation.TransGen (Relation.CutExpand (fun y x => r x y)) A B := by
  obtain ⟨hne, hdom⟩ := h
  have hX : B - A ≠ 0 := by
    intro h0
    have hle : ∀ z, Multiset.count z B ≤ Multiset.count z A := by
      intro z
      have hz := congrArg (Multiset.count z) h0
      rw [Multiset.count_sub, Multiset.count_zero] at hz
      omega
    by_cases hall : ∀ z, Multiset.count z A ≤ Multiset.count z B
    · exact hne (Multiset.ext.2 (fun z => le_antisymm (hle z) (hall z)))
    · push_neg at hall
      obtain ⟨y, hy⟩ := hall
      obtain ⟨x, _, hx⟩ := hdom y hy
      have := hle x
      omega
  have hdecA : A ∩ B + (A - B) = A := by rw [add_comm, Multiset.sub_add_inter]
  have hdecB : A ∩ B + (B - A) = B := by
    rw [Multiset.inter_comm, add_comm, Multiset.sub_add_inter]
  have hmain := transGen_cutExpand_of_dominated (fun y x => r x y) (B - A) hX (A ∩ B) (A - B)
    (by
      intro y hy
      have hy' : Multiset.count y B < Multiset.count y A := by
        have := Multiset.count_pos.2 hy
        rw [Multiset.count_sub] at this
        omega
      obtain ⟨x, hrx, hx⟩ := hdom y hy'
      refine ⟨x, ?_, hrx⟩
      rw [← Multiset.count_pos, Multiset.count_sub]
      omega)
  rwa [hdecA, hdecB] at hmain

end Ext

/-! ### Well-formed terms and weights -/

section KBODefs

variable {sigma nu : Type} {W : Type u}

namespace KBOCore

variable (M : KBOCore sigma W)

/-- Well-formed terms: every application uses an admissible arity. -/
inductive WFT : Term sigma nu → Prop
  | var (x : nu) : WFT (.var x)
  | app (f : sigma) (args : List (Term sigma nu)) (har : M.arOK f args.length)
      (hargs : ∀ a ∈ args, WFT a) : WFT (.app f args)

end KBOCore

/-- Iterated unary application `g (g (... (g u)))`. -/
def tower (g : sigma) : ℕ → Term sigma nu → Term sigma nu
  | 0, u => u
  | k + 1, u => .app g [tower g k u]

theorem wft_args (M : KBOCore sigma W) {f : sigma} {args : List (Term sigma nu)}
    (h : M.WFT (.app f args)) : ∀ b ∈ args, M.WFT b := by
  cases h with
  | app _ _ _ hargs => exact hargs

theorem wft_arOK (M : KBOCore sigma W) {f : sigma} {args : List (Term sigma nu)}
    (h : M.WFT (.app f args)) : M.arOK f args.length := by
  cases h with
  | app _ _ har _ => exact har

end KBODefs

section KBOWeight

variable {sigma nu : Type} {W : Type u} [AddCommMonoid W]

namespace KBOCore

variable (M : KBOCore sigma W)

/-- Term weight (Knuth and Bendix 1970; with subterm coefficients, Ludwig and Waldmann 2007,
Definition 13, and Yamada, Kusakari, Sakabe 2015, Section 2.1.4). -/
def wt (t : Term sigma nu) : W := ev M.coeff M.weight (fun _ => M.w0) t

/-- The weight-preserving unary symbol at this application: one argument, weight `0`,
coefficient `1`. -/
abbrev Special (f : sigma) (args : List (Term sigma nu)) : Prop :=
  args.length = 1 ∧ M.weight f = 0 ∧ M.coeff f 0 = 1

end KBOCore

theorem wt_var (M : KBOCore sigma W) (x : nu) : M.wt (.var x : Term sigma nu) = M.w0 := rfl

theorem wt_app (M : KBOCore sigma W) (f : sigma) (args : List (Term sigma nu)) :
    M.wt (.app f args) = M.weight f + evL M.coeff M.weight (fun _ => M.w0) f 0 args := rfl

end KBOWeight

section KBOLaws

variable {sigma nu : Type} {W : Type u} [AddCommMonoid W] [LinearOrder W]

/-- Admissibility laws of the core (Ludwig and Waldmann 2007, Definitions 2, 15, 17; Becker et al.
2017, Definition 8): positive variable weight, nonnegative symbol weights, constants at least the
variable weight, positive subterm coefficients, a unary weight-zero symbol is used only with one
argument and lies above every other symbol, and the precedence is a well-founded strict order. -/
structure KBOCore.Laws (M : KBOCore sigma W) : Prop where
  w0_pos : 0 < M.w0
  weight_nonneg : ∀ f, 0 ≤ M.weight f
  const_ge : ∀ f, M.arOK f 0 → M.w0 ≤ M.weight f
  coeff_pos : ∀ f i, 1 ≤ M.coeff f i
  special_unary : ∀ f, M.arOK f 1 → M.weight f = 0 → ∀ n, M.arOK f n → n = 1
  special_max : ∀ f, M.arOK f 1 → M.weight f = 0 → ∀ g, g ≠ f → M.prec f g
  prec_irrefl : ∀ f, ¬ M.prec f f
  prec_trans : ∀ f g h, M.prec f g → M.prec g h → M.prec f h
  prec_wf : WellFounded (fun g f => M.prec f g)

/-- A special head admits only one argument and lies above every other symbol. -/
theorem special_of_wft (M : KBOCore sigma W) (hL : M.Laws) {g : sigma}
    {us : List (Term sigma nu)} (hwu : M.WFT (.app g us)) (hsp : M.Special g us) :
    ∀ h, h ≠ g → M.prec g h := by
  obtain ⟨hlen, hw0, _⟩ := hsp
  have har : M.arOK g 1 := by
    have := wft_arOK M hwu
    rwa [hlen] at this
  exact hL.special_max g har hw0

end KBOLaws

section KBOOrdered

variable {sigma nu : Type} {W : Type u} [AddCommMonoid W] [LinearOrder W]
  [IsOrderedCancelAddMonoid W]

variable (M : KBOCore sigma W)

theorem wt_nonneg (hL : M.Laws) (t : Term sigma nu) : 0 ≤ M.wt t :=
  ev_nonneg _ hL.weight_nonneg (fun _ => hL.w0_pos.le) t

theorem wt_arg_le (hL : M.Laws) {f : sigma} {args : List (Term sigma nu)} {b : Term sigma nu}
    (hb : b ∈ args) : M.wt b ≤ M.wt (.app f args) := by
  rw [wt_app]
  exact le_add_of_nonneg_of_le (hL.weight_nonneg f)
    (ev_le_evL_of_mem _ hL.weight_nonneg (fun _ => hL.w0_pos.le) hL.coeff_pos f args 0 b hb)

theorem wt_ge_w0 (hL : M.Laws) {t : Term sigma nu} (ht : M.WFT t) : M.w0 ≤ M.wt t := by
  induction ht with
  | var x => exact le_rfl
  | app f args har hargs ih =>
      cases args with
      | nil =>
          rw [wt_app, evL_nil, add_zero]
          exact hL.const_ge f har
      | cons a as => exact le_trans (ih a (by simp)) (wt_arg_le M hL (by simp))

theorem wt_pos (hL : M.Laws) {t : Term sigma nu} (ht : M.WFT t) : 0 < M.wt t :=
  lt_of_lt_of_le hL.w0_pos (wt_ge_w0 M hL ht)

/-- Arguments of an application with well-formed arguments are strictly lighter unless the head
is the weight-preserving unary symbol. -/
theorem wt_arg_lt (hL : M.Laws) {f : sigma} {args : List (Term sigma nu)}
    (hwf : ∀ a ∈ args, M.WFT a) (hns : ¬ M.Special f args) {b : Term sigma nu}
    (hb : b ∈ args) : M.wt b < M.wt (.app f args) := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hb
  have hbpos : 0 < M.wt b := wt_pos M hL (hwf b (by simp))
  have hws := hL.weight_nonneg
  have hv : ∀ _ : nu, (0 : W) ≤ M.w0 := fun _ => hL.w0_pos.le
  rw [wt_app, evL_append, evL_cons, zero_add]
  refine lt_add_add_of_parts (hws f) (evL_nonneg _ hws hv f pre 0)
    (evL_nonneg _ hws hv f post _) (le_nsmul_of_one_le' hbpos.le (hL.coeff_pos _ _)) ?_
  cases pre with
  | cons p ps =>
      right; left
      exact lt_of_lt_of_le (wt_pos M hL (hwf p (by simp)))
        (ev_le_evL_of_mem _ hws hv hL.coeff_pos f (p :: ps) 0 p (by simp))
  | nil =>
      cases post with
      | cons p ps =>
          right; right; left
          exact lt_of_lt_of_le (wt_pos M hL (hwf p (by simp)))
            (ev_le_evL_of_mem _ hws hv hL.coeff_pos f (p :: ps) _ p (by simp))
      | nil =>
          by_cases hw0 : M.weight f = 0
          · right; right; right
            have hc : M.coeff f 0 ≠ 1 := fun hc => hns ⟨by simp, hw0, hc⟩
            have hc2 : 2 ≤ M.coeff f ([] : List (Term sigma nu)).length := by
              have := hL.coeff_pos f 0
              simp only [List.length_nil]
              omega
            exact lt_nsmul_of_two_le' hbpos hc2
          · left
            exact lt_of_le_of_ne (hws f) (Ne.symm hw0)

end KBOOrdered

/-! ### The KBO relation -/

section KBORel

variable {sigma nu : Type} {W : Type u} [AddCommMonoid W] [LinearOrder W] [DecidableEq sigma]
  [DecidableEq nu]

/-- The (coefficient-weighted) variable condition: no variable counts more in `t` than in `s`. -/
def KBOCore.VC (M : KBOCore sigma W) (s t : Term sigma nu) : Prop :=
  ∀ x, cnt M.coeff x t ≤ cnt M.coeff x s

/-- The KBO comparison `Gt M s t` (`s ≻ t`). Clauses, for the variable condition and weights:
`weight` (heavier), `varR` (equal weight, non-variable above a variable; Becker et al. 2017,
Definition 8, F2), `prec` (equal weight, root precedence), `lex` and `mul` (equal weight, same
root, argument status). -/
inductive Gt (M : KBOCore sigma W) : Term sigma nu → Term sigma nu → Prop
  | weight {s t : Term sigma nu} (hvc : M.VC s t) (hw : M.wt t < M.wt s) : Gt M s t
  | varR {f : sigma} {args : List (Term sigma nu)} {x : nu}
      (hvc : M.VC (.app f args) (.var x)) (hw : M.wt (.app f args) = M.wt (.var x)) :
      Gt M (.app f args) (.var x)
  | prec {f g : sigma} {ss ts : List (Term sigma nu)}
      (hvc : M.VC (.app f ss) (.app g ts)) (hw : M.wt (.app f ss) = M.wt (.app g ts))
      (hp : M.prec f g) : Gt M (.app f ss) (.app g ts)
  | lex {f : sigma} {ss ts : List (Term sigma nu)}
      (hvc : M.VC (.app f ss) (.app f ts)) (hw : M.wt (.app f ss) = M.wt (.app f ts))
      (hst : M.status f = .lex) (hlen : ss.length = ts.length) (i : ℕ)
      (hi : i < ss.length) (hti : i < ts.length) (hpre : ss.take i = ts.take i)
      (hgt : Gt M ss[i] ts[i]) : Gt M (.app f ss) (.app f ts)
  | mul {f : sigma} {ss ts : List (Term sigma nu)}
      (hvc : M.VC (.app f ss) (.app f ts)) (hw : M.wt (.app f ss) = M.wt (.app f ts))
      (hst : M.status f = .mul) (hne : (ss : Multiset (Term sigma nu)) ≠ ts)
      (pick : Term sigma nu → Term sigma nu)
      (hpick : ∀ y, Multiset.count y (ss : Multiset (Term sigma nu)) <
        Multiset.count y (ts : Multiset (Term sigma nu)) → Gt M (pick y) y)
      (hcnt : ∀ y, Multiset.count y (ss : Multiset (Term sigma nu)) <
        Multiset.count y (ts : Multiset (Term sigma nu)) →
          Multiset.count (pick y) (ts : Multiset (Term sigma nu)) <
            Multiset.count (pick y) (ss : Multiset (Term sigma nu))) :
      Gt M (.app f ss) (.app f ts)

/-- The reversed KBO on well-formed terms: `KR M t s` says the well-formed `t` is below the
well-formed `s`. -/
def KR (M : KBOCore sigma W) (t s : Term sigma nu) : Prop :=
  M.WFT t ∧ M.WFT s ∧ Gt M s t

variable (M : KBOCore sigma W)

theorem gt_wt_le {s t : Term sigma nu} (h : Gt M s t) : M.wt t ≤ M.wt s := by
  cases h with
  | weight _ hw => exact hw.le
  | varR _ hw => exact hw.symm.le
  | prec _ hw _ => exact hw.symm.le
  | lex _ hw _ _ _ _ _ _ _ => exact hw.symm.le
  | mul _ hw _ _ _ _ _ => exact hw.symm.le

theorem gt_vc {s t : Term sigma nu} (h : Gt M s t) : M.VC s t := by
  cases h with
  | weight hvc _ => exact hvc
  | varR hvc _ => exact hvc
  | prec hvc _ _ => exact hvc
  | lex hvc _ _ _ _ _ _ _ _ => exact hvc
  | mul hvc _ _ _ _ _ _ => exact hvc

/-- Irreflexivity of the KBO. -/
theorem gt_irrefl (hL : M.Laws) : ∀ s : Term sigma nu, ¬ Gt M s s := by
  intro s
  induction s using Term.rec' with
  | hvar x =>
      intro h
      cases h with
      | weight _ hw => exact lt_irrefl _ hw
  | happ f args ih =>
      intro h
      cases h with
      | weight _ hw => exact lt_irrefl _ hw
      | prec _ _ hp => exact hL.prec_irrefl f hp
      | lex _ _ _ _ i hi _ _ hgt => exact ih _ (List.getElem_mem hi) hgt
      | mul _ _ _ hne _ _ _ => exact hne rfl

theorem gt_ne (hL : M.Laws) {s t : Term sigma nu} (h : Gt M s t) : s ≠ t := by
  rintro rfl
  exact gt_irrefl M hL s h

theorem kr_irrefl (hL : M.Laws) (a : Term sigma nu) : ¬ KR M a a :=
  fun h => gt_irrefl M hL a h.2.2

end KBORel

/-! ### Well-foundedness -/

section KBOWF

variable {sigma nu : Type} {W : Type u} [AddCommMonoid W] [LinearOrder W]
  [IsOrderedCancelAddMonoid W] [DecidableEq sigma] [DecidableEq nu]

variable (M : KBOCore sigma W)

/-- Accessibility of every well-formed term: the KBO on well-formed terms is well founded. The
proof is a nested induction on weight, root precedence, and the argument status, with no
finiteness assumption on the signature; the precedence is well founded (automatic for a finite
signature). -/
theorem acc_kr [WellFoundedLT W] (hL : M.Laws) :
    ∀ s : Term sigma nu, M.WFT s → Acc (KR M) s := by
  haveI : IsIrrefl (Term sigma nu) (KR M) := ⟨kr_irrefl M hL⟩
  suffices H : ∀ (a : W) (s : Term sigma nu), M.WFT s → M.wt s = a → Acc (KR M) s from
    fun s hs => H _ s hs rfl
  intro a
  refine WellFounded.induction
    (C := fun a => ∀ s : Term sigma nu, M.WFT s → M.wt s = a → Acc (KR M) s)
    (wellFounded_lt (α := W)) a ?_
  intro a IH
  have hlow : ∀ t : Term sigma nu, M.WFT t → M.wt t < a → Acc (KR M) t :=
    fun t ht hlt => IH _ hlt t ht rfl
  have hvar : ∀ x : nu, M.wt (.var x : Term sigma nu) = a → Acc (KR M) (.var x) := by
    intro x hx
    refine Acc.intro _ (fun t ht => ?_)
    obtain ⟨htw, _, hgt⟩ := ht
    cases hgt with
    | weight _ hw => exact hlow t htw (lt_of_lt_of_eq hw hx)
  have node : ∀ f : sigma, ∀ args : List (Term sigma nu), M.WFT (.app f args) →
      (∀ b ∈ args, Acc (KR M) b) → M.wt (.app f args) = a → Acc (KR M) (.app f args) := by
    intro f
    refine WellFounded.induction
      (C := fun f => ∀ args : List (Term sigma nu), M.WFT (.app f args) →
        (∀ b ∈ args, Acc (KR M) b) → M.wt (.app f args) = a → Acc (KR M) (.app f args))
      hL.prec_wf f ?_
    intro f IHf
    have precCase : ∀ (g : sigma) (us : List (Term sigma nu)), M.prec f g →
        M.WFT (.app g us) → M.wt (.app g us) = a → Acc (KR M) (.app g us) := by
      intro g us hp hwu hwua
      have hwfus := wft_args M hwu
      have hns : ¬ M.Special g us := by
        intro hsp
        have hne : f ≠ g := fun h => hL.prec_irrefl f (by rw [← h] at hp; exact hp)
        have hgf := special_of_wft M hL hwu hsp f hne
        exact hL.prec_irrefl f (hL.prec_trans f g f hp hgf)
      exact IHf g hp us hwu
        (fun b hb => hlow b (hwfus b hb) ((wt_arg_lt M hL hwfus hns hb).trans_eq hwua)) hwua
    intro args hwf hacc hwa
    cases hst : M.status f with
    | lex =>
        have hA : Acc (LexA (KR M)) args := acc_lexA (KR M) args.length args rfl hacc
        revert hwf hacc hwa
        induction hA with
        | intro args _ IHl =>
            intro hwf hacc hwa
            refine Acc.intro _ (fun u hu => ?_)
            obtain ⟨hwu, _, hgt⟩ := hu
            cases hgt with
            | weight _ hw => exact hlow u hwu (hw.trans_eq hwa)
            | varR _ hw => exact hvar _ (hw.symm.trans hwa)
            | prec _ hw hp => exact precCase _ _ hp hwu (hw.symm.trans hwa)
            | mul _ _ hst' _ _ _ _ => exact absurd (hst'.symm.trans hst) (by decide)
            | @lex _ _ us _ hw _ hlen i hi hti hpre hgt' =>
                have hwfargs := wft_args M hwf
                have hwfus := wft_args M hwu
                have hwua : M.wt (.app f us) = a := hw.symm.trans hwa
                have haccus : ∀ b ∈ us, Acc (KR M) b := by
                  intro b hb
                  by_cases hsp : M.Special f us
                  · obtain ⟨hus1, _, _⟩ := hsp
                    obtain ⟨j, hj, hjb⟩ := List.mem_iff_getElem.1 hb
                    have hji : j = i := by omega
                    subst hji
                    rw [← hjb]
                    exact (hacc _ (List.getElem_mem hi)).inv
                      ⟨hwfus _ (List.getElem_mem hj), hwfargs _ (List.getElem_mem hi), hgt'⟩
                  · exact hlow b (hwfus b hb) ((wt_arg_lt M hL hwfus hsp hb).trans_eq hwua)
                exact IHl us ⟨⟨hlen.symm, i, hti, hi, hpre.symm,
                    ⟨hwfus _ (List.getElem_mem hti), hwfargs _ (List.getElem_mem hi), hgt'⟩⟩,
                  haccus⟩ hwu haccus hwua
    | mul =>
        have hA : Acc (Relation.TransGen (Relation.CutExpand (KR M)))
            (args : Multiset (Term sigma nu)) :=
          (Relation.acc_of_singleton
            (fun b hb => (hacc b (Multiset.mem_coe.1 hb)).cutExpand)).transGen
        suffices H : ∀ m, Acc (Relation.TransGen (Relation.CutExpand (KR M))) m →
            ∀ args : List (Term sigma nu), (args : Multiset (Term sigma nu)) = m →
              M.WFT (.app f args) → (∀ b ∈ args, Acc (KR M) b) → M.wt (.app f args) = a →
                Acc (KR M) (.app f args) from H _ hA args rfl hwf hacc hwa
        intro m hm
        induction hm with
        | intro m _ IHm =>
            intro args hargs hwf hacc hwa
            subst hargs
            refine Acc.intro _ (fun u hu => ?_)
            obtain ⟨hwu, _, hgt⟩ := hu
            cases hgt with
            | weight _ hw => exact hlow u hwu (hw.trans_eq hwa)
            | varR _ hw => exact hvar _ (hw.symm.trans hwa)
            | prec _ hw hp => exact precCase _ _ hp hwu (hw.symm.trans hwa)
            | lex _ _ hst' _ _ _ _ _ _ => exact absurd (hst'.symm.trans hst) (by decide)
            | @mul _ _ us _ hw _ hne pick hpick hcnt =>
                have hwfargs := wft_args M hwf
                have hwfus := wft_args M hwu
                have hwua : M.wt (.app f us) = a := hw.symm.trans hwa
                have hHO : HOGt (fun x y => KR M y x) (args : Multiset (Term sigma nu))
                    (us : Multiset (Term sigma nu)) := by
                  refine ⟨hne, fun y hy => ⟨pick y, ⟨?_, ?_, hpick y hy⟩, hcnt y hy⟩⟩
                  · have hyus : y ∈ (us : Multiset (Term sigma nu)) := by
                      rw [← Multiset.count_pos]; omega
                    exact hwfus y (Multiset.mem_coe.1 hyus)
                  · have hpa : pick y ∈ (args : Multiset (Term sigma nu)) := by
                      have := hcnt y hy
                      rw [← Multiset.count_pos]; omega
                    exact hwfargs _ (Multiset.mem_coe.1 hpa)
                have hstep := hoGt_transGen (fun x y => KR M y x) hHO
                have haccus : ∀ b ∈ us, Acc (KR M) b := by
                  intro b hb
                  by_cases hsp : M.Special f us
                  · obtain ⟨hus1, hw0, _⟩ := hsp
                    have har1 : M.arOK f 1 := by
                      have := wft_arOK M hwu
                      rwa [hus1] at this
                    have hargs1 : args.length = 1 :=
                      hL.special_unary f har1 hw0 _ (wft_arOK M hwf)
                    obtain ⟨b0, rfl⟩ := List.length_eq_one_iff.1 hus1
                    obtain ⟨c0, rfl⟩ := List.length_eq_one_iff.1 hargs1
                    have hbb : b = b0 := List.mem_singleton.1 hb
                    subst hbb
                    have hne' : b ≠ c0 := by
                      rintro rfl
                      exact hne rfl
                    have hy : Multiset.count b ([c0] : Multiset (Term sigma nu)) <
                        Multiset.count b ([b] : Multiset (Term sigma nu)) := by
                      simp [hne']
                    have hpc : pick b = c0 := by
                      have h3 := hcnt b hy
                      by_contra hpc'
                      have h0 : Multiset.count (pick b) ([c0] : Multiset (Term sigma nu)) = 0 := by
                        simp [hpc']
                      omega
                    have hgtb : Gt M c0 b := by
                      have := hpick b hy
                      rwa [hpc] at this
                    exact (hacc c0 (by simp)).inv ⟨hwfus b (by simp), hwfargs c0 (by simp), hgtb⟩
                  · exact hlow b (hwfus b hb) ((wt_arg_lt M hL hwfus hsp hb).trans_eq hwua)
                exact IHm _ hstep us rfl hwu haccus hwua
  intro s hs hsa
  revert hs hsa
  induction s using Term.rec' with
  | hvar x => intro _ hsa; exact hvar x hsa
  | happ f args ih =>
      intro hs hsa
      have hwfargs := wft_args M hs
      refine node f args hs (fun b hb => ?_) hsa
      rcases (wt_arg_le M hL (f := f) hb).lt_or_eq with hlt | heq
      · exact hlow b (hwfargs b hb) (hlt.trans_eq hsa)
      · exact ih b hb (hwfargs b hb) (heq.trans hsa)

/-- The KBO on well-formed terms is well founded. -/
theorem kr_wellFounded [WellFoundedLT W] (hL : M.Laws) :
    WellFounded (KR M : Term sigma nu → Term sigma nu → Prop) :=
  ⟨fun s => by
    by_cases hs : M.WFT s
    · exact acc_kr M hL s hs
    · exact Acc.intro s (fun t ht => absurd ht.2.1 hs)⟩

end KBOWF

/-! ### Finite maximal elements, list helpers and the Huet–Oppen extension -/

section ExtTrans

variable {α : Type}

/-- In a finite set on which `r` is transitive and irreflexive some element has no `r`-larger
element in the set. -/
theorem exists_maximal_of_trans_irrefl (r : α → α → Prop) (D : Finset α) (hD : D.Nonempty)
    (htr : ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, r a b → r b c → r a c) (hirr : ∀ a ∈ D, ¬ r a a) :
    ∃ m ∈ D, ∀ y ∈ D, ¬ r y m := by
  let R : D → D → Prop := fun x y => r x.1 y.1
  haveI : IsTrans D R := ⟨fun a b c hab hbc => htr a.1 a.2 b.1 b.2 c.1 c.2 hab hbc⟩
  haveI : IsIrrefl D R := ⟨fun a h => hirr a.1 a.2 h⟩
  have hwf : WellFounded R := Finite.wellFounded_of_trans_of_irrefl R
  obtain ⟨x0, hx0⟩ := hD
  obtain ⟨m, _, hm⟩ := hwf.has_min Set.univ ⟨⟨x0, hx0⟩, trivial⟩
  exact ⟨m.1, m.2, fun y hy hr => hm ⟨y, hy⟩ trivial hr⟩

theorem take_eq_take_of_le {l₁ l₂ : List α} {m n : ℕ} (hmn : m ≤ n)
    (h : l₁.take n = l₂.take n) : l₁.take m = l₂.take m := by
  have := congrArg (List.take m) h
  rwa [List.take_take, List.take_take, min_eq_left hmn] at this

theorem getElem_eq_of_take_eq {l₁ l₂ : List α} {n k : ℕ} (h : l₁.take n = l₂.take n)
    (hk : k < n) (h₁ : k < l₁.length) (h₂ : k < l₂.length) : l₁[k] = l₂[k] := by
  induction l₁ generalizing l₂ n k with
  | nil => simp at h₁
  | cons a l₁ ih =>
      cases l₂ with
      | nil => simp at h₂
      | cons b l₂ =>
          cases n with
          | zero => omega
          | succ n =>
              simp only [List.take_succ_cons, List.cons.injEq] at h
              cases k with
              | zero => exact h.1
              | succ k => exact ih h.2 (by omega) (by simpa using h₁) (by simpa using h₂)

theorem getElem_length_cons (pre post : List α) (a : α) (h : pre.length < (pre ++ a :: post).length) :
    (pre ++ a :: post)[pre.length] = a := by
  rw [List.getElem_append_right (le_refl _)]
  simp

variable [DecidableEq α]

theorem count_ctx (pre post : List α) (a y : α) :
    Multiset.count y ((pre ++ a :: post : List α) : Multiset α) =
      List.count y pre + List.count y post + (if a = y then 1 else 0) := by
  rw [Multiset.coe_count, List.count_append, List.count_cons]
  by_cases h : a = y
  · subst h
    simp
    omega
  · simp [h]

/-- Transitivity of the Huet–Oppen extension from transitivity and irreflexivity on the
elements involved (Becker et al. 2017, property X4). -/
theorem hoGt_trans (r : α → α → Prop) {S T U : Multiset α}
    (htr : ∀ a ∈ S + T + U, ∀ b ∈ S + T + U, ∀ c ∈ S + T + U, r a b → r b c → r a c)
    (hirr : ∀ a ∈ S + T + U, ¬ r a a) (h1 : HOGt r S T) (h2 : HOGt r T U) :
    HOGt r S U := by
  classical
  obtain ⟨hne1, hd1⟩ := h1
  obtain ⟨hne2, hd2⟩ := h2
  have hmem : ∀ a, (0 < Multiset.count a S ∨ 0 < Multiset.count a T ∨
      0 < Multiset.count a U) → a ∈ (S + T + U).toFinset := by
    intro a ha
    rw [Multiset.mem_toFinset, Multiset.mem_add, Multiset.mem_add, ← Multiset.count_pos,
      ← Multiset.count_pos, ← Multiset.count_pos]
    tauto
  have htrF : ∀ a ∈ (S + T + U).toFinset, ∀ b ∈ (S + T + U).toFinset,
      ∀ c ∈ (S + T + U).toFinset, r a b → r b c → r a c := by
    intro a ha b hb c hc
    exact htr a (Multiset.mem_toFinset.1 ha) b (Multiset.mem_toFinset.1 hb) c
      (Multiset.mem_toFinset.1 hc)
  have hirrF : ∀ a ∈ (S + T + U).toFinset, ¬ r a a :=
    fun a ha => hirr a (Multiset.mem_toFinset.1 ha)
  refine ⟨?_, ?_⟩
  · intro hSU
    obtain ⟨y0, hy0⟩ : ∃ y, Multiset.count y S ≠ Multiset.count y T := by
      by_contra hcon
      push_neg at hcon
      exact hne1 (Multiset.ext.2 hcon)
    obtain ⟨m, hmD, hmax⟩ := exists_maximal_of_trans_irrefl r
      ((S + T + U).toFinset.filter (fun y => Multiset.count y S ≠ Multiset.count y T))
      ⟨y0, Finset.mem_filter.2 ⟨hmem y0 (by omega), hy0⟩⟩
      (fun a ha b hb c hc => htrF a (Finset.mem_of_mem_filter a ha) b
        (Finset.mem_of_mem_filter b hb) c (Finset.mem_of_mem_filter c hc))
      (fun a ha => hirrF a (Finset.mem_of_mem_filter a ha))
    have hmne := (Finset.mem_filter.1 hmD).2
    rcases lt_or_gt_of_ne hmne with hlt | hgt
    · obtain ⟨x, hrx, hx⟩ := hd1 m hlt
      exact hmax x (Finset.mem_filter.2 ⟨hmem x (by omega), by omega⟩) hrx
    · have hlt' : Multiset.count m T < Multiset.count m U := by rw [← hSU]; exact hgt
      obtain ⟨x, hrx, hx⟩ := hd2 m hlt'
      rw [← hSU] at hx
      exact hmax x (Finset.mem_filter.2 ⟨hmem x (by omega), by omega⟩) hrx
  · intro z hz
    obtain ⟨m, hmD, hmax⟩ := exists_maximal_of_trans_irrefl r
      ((S + T + U).toFinset.filter (fun y => (y = z ∨ r y z) ∧
        (Multiset.count y T < Multiset.count y U ∨ Multiset.count y S < Multiset.count y T)))
      ⟨z, Finset.mem_filter.2 ⟨hmem z (by omega), Or.inl rfl, by omega⟩⟩
      (fun a ha b hb c hc => htrF a (Finset.mem_of_mem_filter a ha) b
        (Finset.mem_of_mem_filter b hb) c (Finset.mem_of_mem_filter c hc))
      (fun a ha => hirrF a (Finset.mem_of_mem_filter a ha))
    obtain ⟨hmF, hmz, hmc⟩ := Finset.mem_filter.1 hmD
    have hzF : z ∈ (S + T + U).toFinset := hmem z (by omega)
    have hrxz : ∀ x ∈ (S + T + U).toFinset, r x m → r x z := by
      intro x hx hxm
      rcases hmz with rfl | hmz
      · exact hxm
      · exact htrF x hx m hmF z hzF hxm hmz
    rcases hmc with hc | hc
    · obtain ⟨x, hrx, hx⟩ := hd2 m hc
      have hxF : x ∈ (S + T + U).toFinset := hmem x (by omega)
      by_cases hxS : Multiset.count x U < Multiset.count x S
      · exact ⟨x, hrxz x hxF hrx, hxS⟩
      · exact absurd hrx (hmax x (Finset.mem_filter.2
          ⟨hxF, Or.inr (hrxz x hxF hrx), Or.inr (by omega)⟩))
    · obtain ⟨x, hrx, hx⟩ := hd1 m hc
      have hxF : x ∈ (S + T + U).toFinset := hmem x (by omega)
      by_cases hxS : Multiset.count x U < Multiset.count x S
      · exact ⟨x, hrxz x hxF hrx, hxS⟩
      · exact absurd hrx (hmax x (Finset.mem_filter.2
          ⟨hxF, Or.inr (hrxz x hxF hrx), Or.inl (by omega)⟩))

/-- The structural part of a Huet–Oppen step: the excess of the larger multiset is nonempty and
both multisets split over their intersection. -/
theorem hoGt_decomp (r : α → α → Prop) {B A : Multiset α} (h : HOGt r B A) :
    B - A ≠ 0 ∧ A ∩ B + (B - A) = B ∧ A ∩ B + (A - B) = A := by
  obtain ⟨hne, hdom⟩ := h
  refine ⟨?_, by rw [Multiset.inter_comm, add_comm, Multiset.sub_add_inter],
    by rw [add_comm, Multiset.sub_add_inter]⟩
  intro h0
  have hle : ∀ z, Multiset.count z B ≤ Multiset.count z A := by
    intro z
    have hz := congrArg (Multiset.count z) h0
    rw [Multiset.count_sub, Multiset.count_zero] at hz
    omega
  by_cases hall : ∀ z, Multiset.count z A ≤ Multiset.count z B
  · exact hne (Multiset.ext.2 (fun z => le_antisymm (hle z) (hall z)))
  · push_neg at hall
    obtain ⟨y, hy⟩ := hall
    obtain ⟨x, _, hx⟩ := hdom y hy
    have := hle x
    omega

/-- A Dershowitz–Manna step for a strict order is a Huet–Oppen step (the two extensions agree
on strict partial orders; Becker et al. 2017, remark after Definition 6). -/
theorem dm_to_hoGt (r : α → α → Prop) (htr : ∀ a b c, r a b → r b c → r a c)
    (hirr : ∀ a, ¬ r a a) {K X Y : Multiset α} (hX : X ≠ 0)
    (hdom : ∀ y ∈ Y, ∃ x ∈ X, r x y) : HOGt r (K + X) (K + Y) := by
  classical
  refine ⟨?_, ?_⟩
  · intro hKXY
    have hXY : X = Y := add_left_cancel hKXY
    subst hXY
    obtain ⟨x0, hx0⟩ := Multiset.exists_mem_of_ne_zero hX
    obtain ⟨m, hmX, hmax⟩ := exists_maximal_of_trans_irrefl r X.toFinset
      ⟨x0, Multiset.mem_toFinset.2 hx0⟩ (fun a _ b _ c _ => htr a b c) (fun a _ => hirr a)
    obtain ⟨x, hxX, hrx⟩ := hdom m (Multiset.mem_toFinset.1 hmX)
    exact hmax x (Multiset.mem_toFinset.2 hxX) hrx
  · intro z hz
    rw [Multiset.count_add, Multiset.count_add] at hz
    have hzY : z ∈ Y := by rw [← Multiset.count_pos]; omega
    obtain ⟨x1, hx1X, hrx1⟩ := hdom z hzY
    obtain ⟨m, hmD, hmax⟩ := exists_maximal_of_trans_irrefl r
      (X.toFinset.filter (fun w => r w z))
      ⟨x1, Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hx1X, hrx1⟩⟩
      (fun a _ b _ c _ => htr a b c) (fun a _ => hirr a)
    obtain ⟨hmX, hmz⟩ := Finset.mem_filter.1 hmD
    refine ⟨m, hmz, ?_⟩
    rw [Multiset.count_add, Multiset.count_add]
    by_contra hcon
    have hmY : m ∈ Y := by
      have := Multiset.count_pos.2 (Multiset.mem_toFinset.1 hmX)
      rw [← Multiset.count_pos]
      omega
    obtain ⟨x, hxX, hrx⟩ := hdom m hmY
    exact hmax x (Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hxX, htr x m z hrx hmz⟩) hrx

end ExtTrans

/-! ### Transitivity -/

section KBOTrans

variable {sigma nu : Type} {W : Type u} [AddCommMonoid W] [LinearOrder W] [DecidableEq sigma]
  [DecidableEq nu]

variable (M : KBOCore sigma W)

theorem gt_trans_aux (hL : M.Laws) : ∀ (N : ℕ) (s t u : Term sigma nu),
    s.size ≤ N → t.size ≤ N → u.size ≤ N → Gt M s t → Gt M t u → Gt M s u := by
  intro N
  induction N with
  | zero =>
      intro s _ _ hs
      have := Term.one_le_size s
      omega
  | succ N ih =>
      intro s t u hs ht hu hst htu
      have hvc : M.VC s u := fun x => (gt_vc M htu x).trans (gt_vc M hst x)
      rcases (gt_wt_le M hst).lt_or_eq with hlt1 | heq1
      · exact Gt.weight hvc (lt_of_le_of_lt (gt_wt_le M htu) hlt1)
      rcases (gt_wt_le M htu).lt_or_eq with hlt2 | heq2
      · exact Gt.weight hvc (lt_of_lt_of_le hlt2 (gt_wt_le M hst))
      have hwsu : M.wt s = M.wt u := (heq2.trans heq1).symm
      cases hst with
      | weight _ hw => exact absurd hw (by rw [heq1]; exact lt_irrefl _)
      | varR _ _ =>
          cases htu with
          | weight _ hw => exact absurd hw (by rw [heq2]; exact lt_irrefl _)
      | prec _ _ hp1 =>
          cases htu with
          | weight _ hw => exact absurd hw (by rw [heq2]; exact lt_irrefl _)
          | varR _ _ => exact Gt.varR hvc hwsu
          | prec _ _ hp2 => exact Gt.prec hvc hwsu (hL.prec_trans _ _ _ hp1 hp2)
          | lex _ _ _ _ _ _ _ _ _ => exact Gt.prec hvc hwsu hp1
          | mul _ _ _ _ _ _ _ => exact Gt.prec hvc hwsu hp1
      | @lex f ss ts _ _ hst1 hlen1 i hi hti hpre1 hgt1 =>
          cases htu with
          | weight _ hw => exact absurd hw (by rw [heq2]; exact lt_irrefl _)
          | varR _ _ => exact Gt.varR hvc hwsu
          | prec _ _ hp2 => exact Gt.prec hvc hwsu hp2
          | mul _ _ hst2 _ _ _ _ => exact absurd (hst2.symm.trans hst1) (by decide)
          | @lex _ _ us _ _ _ hlen2 j hj htj hpre2 hgt2 =>
              rcases lt_trichotomy i j with hij | hij | hij
              · have hpre : ss.take i = us.take i :=
                  hpre1.trans (take_eq_take_of_le hij.le hpre2)
                have hei : ts[i] = us[i]'(by omega) :=
                  getElem_eq_of_take_eq hpre2 hij hti (by omega)
                exact Gt.lex hvc hwsu hst1 (hlen1.trans hlen2) i hi (by omega) hpre
                  (by rw [← hei]; exact hgt1)
              · subst hij
                have hs' : ss[i].size ≤ N := by
                  have := Term.size_lt_of_mem (f := f) (List.getElem_mem hi); omega
                have ht' : ts[i].size ≤ N := by
                  have := Term.size_lt_of_mem (f := f) (List.getElem_mem hti); omega
                have hu' : us[i].size ≤ N := by
                  have := Term.size_lt_of_mem (f := f) (List.getElem_mem htj); omega
                exact Gt.lex hvc hwsu hst1 (hlen1.trans hlen2) i hi htj (hpre1.trans hpre2)
                  (ih _ _ _ hs' ht' hu' hgt1 hgt2)
              · have hpre : ss.take j = us.take j :=
                  (take_eq_take_of_le hij.le hpre1).trans hpre2
                have hej : ss[j]'(by omega) = ts[j] :=
                  getElem_eq_of_take_eq hpre1 hij (by omega) hj
                exact Gt.lex hvc hwsu hst1 (hlen1.trans hlen2) j (by omega) htj hpre
                  (by rw [hej]; exact hgt2)
      | @mul f ss ts _ _ hst1 hne1 pick1 hpick1 hcnt1 =>
          cases htu with
          | weight _ hw => exact absurd hw (by rw [heq2]; exact lt_irrefl _)
          | varR _ _ => exact Gt.varR hvc hwsu
          | prec _ _ hp2 => exact Gt.prec hvc hwsu hp2
          | lex _ _ hst2 _ _ _ _ _ _ => exact absurd (hst2.symm.trans hst1) (by decide)
          | @mul _ _ us _ _ _ hne2 pick2 hpick2 hcnt2 =>
              have hHO1 : HOGt (Gt M) (ss : Multiset (Term sigma nu)) ts :=
                ⟨hne1, fun y hy => ⟨pick1 y, hpick1 y hy, hcnt1 y hy⟩⟩
              have hHO2 : HOGt (Gt M) (ts : Multiset (Term sigma nu)) us :=
                ⟨hne2, fun y hy => ⟨pick2 y, hpick2 y hy, hcnt2 y hy⟩⟩
              have hsz : ∀ a ∈ (ss : Multiset (Term sigma nu)) + ts + us, a.size ≤ N := by
                intro a ha
                simp only [Multiset.mem_add, Multiset.mem_coe] at ha
                rcases ha with (ha | ha) | ha
                · have := Term.size_lt_of_mem (f := f) ha; omega
                · have := Term.size_lt_of_mem (f := f) ha; omega
                · have := Term.size_lt_of_mem (f := f) ha; omega
              obtain ⟨hne, hdom⟩ := hoGt_trans (Gt M)
                (fun a ha b hb c hc hab hbc => ih a b c (hsz a ha) (hsz b hb) (hsz c hc) hab hbc)
                (fun a _ => gt_irrefl M hL a) hHO1 hHO2
              have hdom' : ∀ y, ∃ x, Multiset.count y (ss : Multiset (Term sigma nu)) <
                  Multiset.count y (us : Multiset (Term sigma nu)) →
                    Gt M x y ∧ Multiset.count x (us : Multiset (Term sigma nu)) <
                      Multiset.count x (ss : Multiset (Term sigma nu)) := by
                intro y
                by_cases hy : Multiset.count y (ss : Multiset (Term sigma nu)) <
                    Multiset.count y (us : Multiset (Term sigma nu))
                · obtain ⟨x, hx⟩ := hdom y hy
                  exact ⟨x, fun _ => hx⟩
                · exact ⟨y, fun h => absurd h hy⟩
              choose pick hpick using hdom'
              exact Gt.mul hvc hwsu hst1 hne pick (fun y hy => (hpick y hy).1)
                (fun y hy => (hpick y hy).2)

/-- Transitivity of the KBO. -/
theorem gt_trans (hL : M.Laws) {s t u : Term sigma nu} (hst : Gt M s t) (htu : Gt M t u) :
    Gt M s u :=
  gt_trans_aux M hL (max (max s.size t.size) u.size) s t u (by omega) (by omega) (by omega)
    hst htu

end KBOTrans

/-! ### Closure under contexts -/

section CtxEval

variable {sigma nu : Type} {V : Type u} [AddCommMonoid V]

theorem evL_ctx_eq (c : sigma → ℕ → ℕ) (ws : sigma → V) (v : nu → V) (f : sigma) (i : ℕ)
    (pre post : List (Term sigma nu)) {a b : Term sigma nu} (h : ev c ws v a = ev c ws v b) :
    evL c ws v f i (pre ++ a :: post) = evL c ws v f i (pre ++ b :: post) := by
  rw [evL_append, evL_append, evL_cons, evL_cons, h]

end CtxEval

section CtxOrdered

variable {sigma nu : Type} {W : Type u} [AddCommMonoid W] [LinearOrder W]
  [IsOrderedCancelAddMonoid W]

theorem evL_ctx_le (c : sigma → ℕ → ℕ) (ws : sigma → W) (v : nu → W) (f : sigma) (i : ℕ)
    (pre post : List (Term sigma nu)) {a b : Term sigma nu} (h : ev c ws v a ≤ ev c ws v b) :
    evL c ws v f i (pre ++ a :: post) ≤ evL c ws v f i (pre ++ b :: post) := by
  rw [evL_append, evL_append, evL_cons, evL_cons]
  exact add_le_add_left (add_le_add_right (nsmul_le_nsmul_of_le' h _) _) _

theorem evL_ctx_lt (c : sigma → ℕ → ℕ) (ws : sigma → W) (v : nu → W) (f : sigma) (i : ℕ)
    (pre post : List (Term sigma nu)) {a b : Term sigma nu} (hc : 1 ≤ c f (i + pre.length))
    (h : ev c ws v a < ev c ws v b) :
    evL c ws v f i (pre ++ a :: post) < evL c ws v f i (pre ++ b :: post) := by
  rw [evL_append, evL_append, evL_cons, evL_cons]
  exact add_lt_add_left (add_lt_add_right (nsmul_lt_nsmul_of_lt' h hc) _) _

end CtxOrdered

section KBOCtx

variable {sigma nu : Type} {W : Type u} [AddCommMonoid W] [LinearOrder W]
  [IsOrderedCancelAddMonoid W] [DecidableEq sigma] [DecidableEq nu]

variable (M : KBOCore sigma W)

/-- Closure of the KBO under one-position argument contexts, the congruence of
`Meta.Rewriting.Step.arg`. -/
theorem gt_ctx (hL : M.Laws) {s t : Term sigma nu} (h : Gt M s t) (f : sigma)
    (pre post : List (Term sigma nu)) :
    Gt M (.app f (pre ++ s :: post)) (.app f (pre ++ t :: post)) := by
  have hvc : M.VC (.app f (pre ++ s :: post)) (.app f (pre ++ t :: post)) := by
    intro x
    rw [cnt_app, cnt_app]
    exact evL_ctx_le _ _ _ f 0 pre post (gt_vc M h x)
  rcases (gt_wt_le M h).lt_or_eq with hlt | heq
  · refine Gt.weight hvc ?_
    rw [wt_app, wt_app]
    exact add_lt_add_left (evL_ctx_lt _ _ _ f 0 pre post (hL.coeff_pos _ _) hlt) _
  · have hw : M.wt (.app f (pre ++ s :: post)) = M.wt (.app f (pre ++ t :: post)) := by
      rw [wt_app, wt_app, evL_ctx_eq _ _ _ f 0 pre post heq]
    have hne : s ≠ t := gt_ne M hL h
    cases hst : M.status f with
    | lex =>
        refine Gt.lex hvc hw hst (by simp) pre.length (by simp) (by simp) (by simp) ?_
        rw [getElem_length_cons, getElem_length_cons]
        exact h
    | mul =>
        refine Gt.mul hvc hw hst ?_ (fun _ => s) ?_ ?_
        · intro heq'
          have := congrArg (Multiset.count s) heq'
          rw [count_ctx, count_ctx] at this
          simp [Ne.symm hne] at this
        · intro y hy
          rw [count_ctx, count_ctx] at hy
          by_cases hty : t = y
          · subst hty
            exact h
          · exfalso
            by_cases hsy : s = y <;> simp [hty, hsy] at hy
        · intro y _
          rw [count_ctx, count_ctx]
          simp [Ne.symm hne]

end KBOCtx

/-! ### Closure under substitutions -/

section SubstEval

variable {sigma nu : Type}

theorem ev_zero_zero (c : sigma → ℕ → ℕ) :
    ∀ t : Term sigma nu, ev c (fun _ => (0 : ℕ)) (fun _ => (0 : ℕ)) t = 0 := by
  intro t
  induction t using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
      rw [ev_app, zero_add]
      suffices h : ∀ (l : List (Term sigma nu)),
          (∀ a ∈ l, ev c (fun _ => (0 : ℕ)) (fun _ => (0 : ℕ)) a = 0) →
            ∀ i, evL c (fun _ => (0 : ℕ)) (fun _ => (0 : ℕ)) f i l = 0 from h args ih 0
      intro l hl
      induction l with
      | nil => intro i; rfl
      | cons a as ihl =>
          intro i
          rw [evL_cons, hl a (by simp), ihl (fun b hb => hl b (by simp [hb])) (i + 1)]
          simp

theorem tower_succ (g : sigma) (k : ℕ) (u : Term sigma nu) :
    tower g (k + 1) u = .app g [tower g k u] := rfl

theorem tower_app_self (g : sigma) (u : Term sigma nu) :
    ∀ k, tower g k (.app g [u]) = tower g (k + 1) u
  | 0 => rfl
  | k + 1 => by
      change Term.app g [tower g k (.app g [u])] = Term.app g [tower g (k + 1) u]
      rw [tower_app_self g u k]

theorem subst_tower (σ : Subst sigma nu) (g : sigma) (u : Term sigma nu) :
    ∀ k, Subst.apply σ (tower g k u) = tower g k (Subst.apply σ u)
  | 0 => rfl
  | k + 1 => by
      change Subst.apply σ (Term.app g [tower g k u]) = Term.app g [tower g k (Subst.apply σ u)]
      rw [Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil, subst_tower σ g u k]

theorem length_applyList (σ : Subst sigma nu) (l : List (Term sigma nu)) :
    (Subst.applyList σ l).length = l.length := by
  rw [Subst.applyList_eq_map, List.length_map]

theorem getElem_applyList (σ : Subst sigma nu) (l : List (Term sigma nu)) (i : ℕ)
    (h : i < (Subst.applyList σ l).length) :
    (Subst.applyList σ l)[i] = Subst.apply σ (l[i]'(by rwa [length_applyList] at h)) := by
  simp [Subst.applyList_eq_map]

theorem take_applyList (σ : Subst sigma nu) (l : List (Term sigma nu)) (i : ℕ) :
    (Subst.applyList σ l).take i = Subst.applyList σ (l.take i) := by
  rw [Subst.applyList_eq_map, Subst.applyList_eq_map, List.map_take]

theorem wft_tower {W : Type u} (M : KBOCore sigma W) {g : sigma} (har : M.arOK g 1)
    {u : Term sigma nu} (hu : M.WFT u) : ∀ k, M.WFT (tower g k u)
  | 0 => hu
  | k + 1 => KBOCore.WFT.app g [tower g k u] har (by
      intro a ha
      rw [List.mem_singleton] at ha
      subst ha
      exact wft_tower M har hu k)

variable [DecidableEq nu]

theorem cnt_subst (c : sigma → ℕ → ℕ) (x : nu) (σ : Subst sigma nu) (t : Term sigma nu) :
    cnt c x (Subst.apply σ t) = ev c (fun _ => (0 : ℕ)) (fun y => cnt c x (σ y)) t :=
  ev_subst c _ _ σ t

theorem cnt_tower (c : sigma → ℕ → ℕ) {g : sigma} (hc : c g 0 = 1) (x : nu)
    (u : Term sigma nu) : ∀ k, cnt c x (tower g k u) = cnt c x u
  | 0 => rfl
  | k + 1 => by
      rw [tower_succ, cnt_app, evL_cons, evL_nil, hc, one_nsmul, add_zero]
      exact cnt_tower c hc x u k

end SubstEval

section SubstWeight

variable {sigma nu : Type} {W : Type u} [AddCommMonoid W]

theorem wt_subst (M : KBOCore sigma W) (σ : Subst sigma nu) (t : Term sigma nu) :
    M.wt (Subst.apply σ t) = ev M.coeff M.weight (fun y => M.wt (σ y)) t :=
  ev_subst _ _ _ σ t

theorem wt_tower (M : KBOCore sigma W) {g : sigma} (hw : M.weight g = 0) (hc : M.coeff g 0 = 1)
    (u : Term sigma nu) : ∀ k, M.wt (tower g k u) = M.wt u
  | 0 => rfl
  | k + 1 => by
      rw [tower_succ, wt_app, evL_cons, evL_nil, hw, hc, one_nsmul, zero_add, add_zero]
      exact wt_tower M hw hc u k

end SubstWeight

section SubstMono

variable {sigma nu : Type} {W : Type u} [AddCommMonoid W] [LinearOrder W]
  [IsOrderedCancelAddMonoid W] [DecidableEq nu]

/-- One step of the monotonicity argument: raising one variable value preserves a comparison when
that variable counts at least as much on the larger side. -/
theorem ev_update_step (c : sigma → ℕ → ℕ) (ws : sigma → W) {s t : Term sigma nu}
    (hcnt : ∀ x, cnt c x t ≤ cnt c x s) (w : nu → W) (x : nu) (b a : W) (hwx : w x = b)
    (hba : b ≤ a) (h : ev c ws w t ≤ ev c ws w s) :
    ev c ws (Function.update w x a) t ≤ ev c ws (Function.update w x a) s := by
  have hself : Function.update w x b = w := by rw [← hwx]; exact Function.update_eq_self x w
  have ht := ev_update_linear c ws w x a b t
  have hs := ev_update_linear c ws w x a b s
  rw [hself] at ht hs
  obtain ⟨e, he⟩ : ∃ e, cnt c x s = cnt c x t + e :=
    ⟨cnt c x s - cnt c x t, by have := hcnt x; omega⟩
  refine le_of_add_le_add_right (?_ : ev c ws (Function.update w x a) t + cnt c x s • b ≤
    ev c ws (Function.update w x a) s + cnt c x s • b)
  calc ev c ws (Function.update w x a) t + cnt c x s • b
      = ev c ws (Function.update w x a) t + cnt c x t • b + e • b := by
        rw [he, add_nsmul, add_assoc]
    _ = ev c ws w t + cnt c x t • a + e • b := by rw [ht]
    _ ≤ ev c ws w s + cnt c x t • a + e • a :=
        add_le_add (add_le_add_right h _) (nsmul_le_nsmul_of_le' hba e)
    _ = ev c ws w s + cnt c x s • a := by rw [he, add_nsmul, add_assoc]
    _ = ev c ws (Function.update w x a) s + cnt c x s • b := hs.symm

theorem ev_update_step_lt (c : sigma → ℕ → ℕ) (ws : sigma → W) {s t : Term sigma nu}
    (hcnt : ∀ x, cnt c x t ≤ cnt c x s) (w : nu → W) (x : nu) (b a : W) (hwx : w x = b)
    (hba : b ≤ a) (h : ev c ws w t < ev c ws w s) :
    ev c ws (Function.update w x a) t < ev c ws (Function.update w x a) s := by
  have hself : Function.update w x b = w := by rw [← hwx]; exact Function.update_eq_self x w
  have ht := ev_update_linear c ws w x a b t
  have hs := ev_update_linear c ws w x a b s
  rw [hself] at ht hs
  obtain ⟨e, he⟩ : ∃ e, cnt c x s = cnt c x t + e :=
    ⟨cnt c x s - cnt c x t, by have := hcnt x; omega⟩
  refine lt_of_add_lt_add_right (?_ : ev c ws (Function.update w x a) t + cnt c x s • b <
    ev c ws (Function.update w x a) s + cnt c x s • b)
  calc ev c ws (Function.update w x a) t + cnt c x s • b
      = ev c ws (Function.update w x a) t + cnt c x t • b + e • b := by
        rw [he, add_nsmul, add_assoc]
    _ = ev c ws w t + cnt c x t • a + e • b := by rw [ht]
    _ < ev c ws w s + cnt c x t • a + e • a :=
        add_lt_add_of_lt_of_le (add_lt_add_right h _) (nsmul_le_nsmul_of_le' hba e)
    _ = ev c ws w s + cnt c x s • a := by rw [he, add_nsmul, add_assoc]
    _ = ev c ws (Function.update w x a) s + cnt c x s • b := hs.symm

omit [AddCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W] in
theorem update_ite_insert (v : nu → W) (b : W) (x : nu) (D : Finset nu) :
    (fun y => if y ∈ insert x D then v y else b) =
      Function.update (fun y => if y ∈ D then v y else b) x (v x) := by
  funext y
  by_cases hy : y = x
  · subst hy
    simp
  · simp [Function.update, hy]

/-- Monotonicity of weighted evaluation in the variable values: a comparison at the base value `b`
for every variable persists for all values above `b`, provided no variable counts more on the
smaller side. -/
theorem ev_le_of_cnt_le (c : sigma → ℕ → ℕ) (ws : sigma → W) {s t : Term sigma nu} (b : W)
    (hcnt : ∀ x, cnt c x t ≤ cnt c x s)
    (hbase : ev c ws (fun _ => b) t ≤ ev c ws (fun _ => b) s)
    (v : nu → W) (hv : ∀ x, b ≤ v x) : ev c ws v t ≤ ev c ws v s := by
  have key : ∀ D : Finset nu, ev c ws (fun y => if y ∈ D then v y else b) t ≤
      ev c ws (fun y => if y ∈ D then v y else b) s := by
    intro D
    induction D using Finset.induction_on with
    | empty => simpa using hbase
    | @insert x D hxD ih =>
        rw [update_ite_insert]
        exact ev_update_step c ws hcnt _ x b (v x) (by simp [hxD]) (hv x) ih
  have e : ∀ u : Term sigma nu, (∀ y ∈ Term.vars u, y ∈ Term.vars t ∪ Term.vars s) →
      ev c ws (fun y => if y ∈ Term.vars t ∪ Term.vars s then v y else b) u = ev c ws v u :=
    fun u hu => ev_congr c ws _ _ u (fun y hy => by simp [hu y hy])
  have hS := key (Term.vars t ∪ Term.vars s)
  rwa [e t (fun y hy => Finset.mem_union_left _ hy),
    e s (fun y hy => Finset.mem_union_right _ hy)] at hS

theorem ev_lt_of_cnt_le (c : sigma → ℕ → ℕ) (ws : sigma → W) {s t : Term sigma nu} (b : W)
    (hcnt : ∀ x, cnt c x t ≤ cnt c x s)
    (hbase : ev c ws (fun _ => b) t < ev c ws (fun _ => b) s)
    (v : nu → W) (hv : ∀ x, b ≤ v x) : ev c ws v t < ev c ws v s := by
  have key : ∀ D : Finset nu, ev c ws (fun y => if y ∈ D then v y else b) t <
      ev c ws (fun y => if y ∈ D then v y else b) s := by
    intro D
    induction D using Finset.induction_on with
    | empty => simpa using hbase
    | @insert x D hxD ih =>
        rw [update_ite_insert]
        exact ev_update_step_lt c ws hcnt _ x b (v x) (by simp [hxD]) (hv x) ih
  have e : ∀ u : Term sigma nu, (∀ y ∈ Term.vars u, y ∈ Term.vars t ∪ Term.vars s) →
      ev c ws (fun y => if y ∈ Term.vars t ∪ Term.vars s then v y else b) u = ev c ws v u :=
    fun u hu => ev_congr c ws _ _ u (fun y hy => by simp [hu y hy])
  have hS := key (Term.vars t ∪ Term.vars s)
  rwa [e t (fun y hy => Finset.mem_union_left _ hy),
    e s (fun y hy => Finset.mem_union_right _ hy)] at hS

end SubstMono

section KBOSubst

variable {sigma nu : Type} {W : Type u} [AddCommMonoid W] [LinearOrder W]
  [IsOrderedCancelAddMonoid W] [DecidableEq sigma] [DecidableEq nu]

variable (M : KBOCore sigma W)

omit [AddCommMonoid W] [LinearOrder W] [IsOrderedCancelAddMonoid W] [DecidableEq sigma] in
theorem vc_subst {s t : Term sigma nu} (h : M.VC s t) (σ : Subst sigma nu) :
    M.VC (Subst.apply σ s) (Subst.apply σ t) := by
  intro x
  show cnt M.coeff x (Subst.apply σ t) ≤ cnt M.coeff x (Subst.apply σ s)
  rw [cnt_subst, cnt_subst]
  exact ev_le_of_cnt_le M.coeff _ (0 : ℕ) h (by rw [ev_zero_zero, ev_zero_zero]) _
    (fun _ => Nat.zero_le _)

omit [DecidableEq sigma] in
theorem wt_subst_le (hL : M.Laws) (σ : Subst sigma nu) (hσ : ∀ x, M.WFT (σ x))
    {s t : Term sigma nu} (hvc : M.VC s t) (hw : M.wt t ≤ M.wt s) :
    M.wt (Subst.apply σ t) ≤ M.wt (Subst.apply σ s) := by
  rw [wt_subst, wt_subst]
  exact ev_le_of_cnt_le M.coeff M.weight M.w0 hvc hw _ (fun x => wt_ge_w0 M hL (hσ x))

omit [DecidableEq sigma] in
theorem wt_subst_lt (hL : M.Laws) (σ : Subst sigma nu) (hσ : ∀ x, M.WFT (σ x))
    {s t : Term sigma nu} (hvc : M.VC s t) (hw : M.wt t < M.wt s) :
    M.wt (Subst.apply σ t) < M.wt (Subst.apply σ s) := by
  rw [wt_subst, wt_subst]
  exact ev_lt_of_cnt_le M.coeff M.weight M.w0 hvc hw _ (fun x => wt_ge_w0 M hL (hσ x))

/-- A well-formed non-variable term of variable weight containing `x` is a tower of the special
unary symbol over `x`; this identifies the clause `varR` (Becker et al. 2017, Definition 8, F2)
with the clause `s = f^n(x)` of Ludwig and Waldmann 2007, Definition 2 (KBO2a). -/
theorem shape_of_wt_eq_w0 (hL : M.Laws) (x : nu) : ∀ s : Term sigma nu, M.WFT s →
    (∀ y, s ≠ .var y) → M.wt s = M.w0 → 1 ≤ cnt M.coeff x s →
      ∃ ι k, 1 ≤ k ∧ M.arOK ι 1 ∧ M.weight ι = 0 ∧ M.coeff ι 0 = 1 ∧
        s = tower ι k (.var x) := by
  intro s
  induction s using Term.rec' with
  | hvar y => intro _ hnv; exact absurd rfl (hnv y)
  | happ f args ih =>
      intro hwf _ hw hcnt
      have hwfargs := wft_args M hwf
      have hne : args ≠ [] := by
        rintro rfl
        rw [cnt_app, evL_nil] at hcnt
        omega
      have hsp : M.Special f args := by
        by_contra hns
        obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil args hne
        have h1 := wt_arg_lt M hL hwfargs hns ha
        have h2 := wt_ge_w0 M hL (hwfargs a ha)
        rw [hw] at h1
        exact absurd (lt_of_le_of_lt h2 h1) (lt_irrefl _)
      obtain ⟨hlen, hw0, hc1⟩ := hsp
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hlen
      have har : M.arOK f 1 := wft_arOK M hwf
      have hwa : M.wt a = M.w0 := by
        rw [wt_app, evL_cons, evL_nil, hw0, hc1, one_nsmul, zero_add, add_zero] at hw
        exact hw
      have hcnta : 1 ≤ cnt M.coeff x a := by
        rw [cnt_app, evL_cons, evL_nil, hc1, one_nsmul, add_zero] at hcnt
        exact hcnt
      cases a with
      | var y =>
          have hy : y = x := by
            rw [cnt_var] at hcnta
            by_contra h
            simp [h] at hcnta
          subst hy
          exact ⟨f, 1, le_rfl, har, hw0, hc1, rfl⟩
      | app g bs =>
          obtain ⟨ι, k, hk, harι, hwι, hcι, hshape⟩ :=
            ih _ (by simp) (hwfargs _ (by simp)) (fun y h => by cases h) hwa hcnta
          have hfι : f = ι := by
            by_contra hne'
            exact hL.prec_irrefl f (hL.prec_trans f ι f
              (hL.special_max f har hw0 ι (Ne.symm hne')) (hL.special_max ι harι hwι f hne'))
          subst hfι
          refine ⟨f, k + 1, by omega, har, hw0, hc1, ?_⟩
          rw [hshape, tower_succ]

omit [IsOrderedCancelAddMonoid W] in
/-- The special unary symbol towers strictly above its argument. -/
theorem gt_tower (hL : M.Laws) {ι : sigma} (har : M.arOK ι 1) (hw : M.weight ι = 0)
    (hc : M.coeff ι 0 = 1) : ∀ u : Term sigma nu, M.WFT u → ∀ k, 1 ≤ k →
      Gt M (tower ι k u) u := by
  intro u
  induction u using Term.rec' with
  | hvar y =>
      intro _ k hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact Gt.varR (fun x => le_of_eq (cnt_tower M.coeff hc x (.var y) (k' + 1)).symm)
        (wt_tower M hw hc (.var y) (k' + 1))
  | happ g us ih =>
      intro hwu k hk
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      by_cases hg : g = ι
      · subst hg
        have hlen : us.length = 1 := hL.special_unary g har hw _ (wft_arOK M hwu)
        obtain ⟨u', rfl⟩ := List.length_eq_one_iff.1 hlen
        have hu' : M.WFT u' := wft_args M hwu u' (by simp)
        have hgt' : Gt M (tower g (k' + 1) u') u' := ih u' (by simp) hu' (k' + 1) (by omega)
        have hne : tower g (k' + 1) u' ≠ u' := gt_ne M hL hgt'
        rw [tower_app_self, tower_succ]
        have hvc' : M.VC (.app g [tower g (k' + 1) u']) (.app g [u']) := by
          intro x
          have e1 : cnt M.coeff x (.app g [tower g (k' + 1) u']) = cnt M.coeff x u' :=
            (cnt_tower M.coeff hc x (tower g (k' + 1) u') 1).trans
              (cnt_tower M.coeff hc x u' (k' + 1))
          have e2 : cnt M.coeff x (.app g [u']) = cnt M.coeff x u' :=
            cnt_tower M.coeff hc x u' 1
          exact le_of_eq (e2.trans e1.symm)
        have hwt' : M.wt (.app g [tower g (k' + 1) u']) = M.wt (.app g [u']) :=
          ((wt_tower M hw hc (tower g (k' + 1) u') 1).trans (wt_tower M hw hc u' (k' + 1))).trans
            (wt_tower M hw hc u' 1).symm
        cases hst : M.status g with
        | lex => exact Gt.lex hvc' hwt' hst rfl 0 (by simp) (by simp) rfl hgt'
        | mul =>
            refine Gt.mul hvc' hwt' hst ?_ (fun _ => tower g (k' + 1) u') ?_ ?_
            · intro h
              have := congrArg (Multiset.count (tower g (k' + 1) u')) h
              simp [hne] at this
            · intro y hy
              have hyu : y = u' := by
                by_contra hyu
                simp [hyu] at hy
              subst hyu
              exact hgt'
            · intro y _
              simp [hne]
      · exact Gt.prec (fun x => le_of_eq (cnt_tower M.coeff hc x (.app g us) (k' + 1)).symm)
          (wt_tower M hw hc (.app g us) (k' + 1)) (hL.special_max ι har hw g hg)

/-- Stability of the KBO under substitutions with well-formed images. -/
theorem gt_subst (hL : M.Laws) (σ : Subst sigma nu) (hσ : ∀ x, M.WFT (σ x)) :
    ∀ {s t : Term sigma nu}, Gt M s t → M.WFT s → M.WFT t →
      Gt M (Subst.apply σ s) (Subst.apply σ t) := by
  intro s t h
  induction h with
  | weight hvc hw =>
      intro _ _
      exact Gt.weight (vc_subst M hvc σ) (wt_subst_lt M hL σ hσ hvc hw)
  | @varR f args x hvc hw =>
      intro hs _
      obtain ⟨ι, k, hk, har, hwι, hcι, hshape⟩ := shape_of_wt_eq_w0 M hL x (.app f args) hs
        (fun y h => by cases h) hw (by simpa [cnt_var] using hvc x)
      rw [hshape, subst_tower]
      exact gt_tower M hL har hwι hcι (σ x) (hσ x) k hk
  | @prec f g ss ts hvc hw hp =>
      intro _ _
      rcases (wt_subst_le M hL σ hσ hvc (le_of_eq hw.symm)).lt_or_eq with hlt | heq
      · exact Gt.weight (vc_subst M hvc σ) hlt
      · exact Gt.prec (vc_subst M hvc σ) heq.symm hp
  | @lex f ss ts hvc hw hst hlen i hi hti hpre hgt ih =>
      intro hs ht
      rcases (wt_subst_le M hL σ hσ hvc (le_of_eq hw.symm)).lt_or_eq with hlt | heq
      · exact Gt.weight (vc_subst M hvc σ) hlt
      · have hgt' := ih (wft_args M hs _ (List.getElem_mem hi))
          (wft_args M ht _ (List.getElem_mem hti))
        refine Gt.lex (vc_subst M hvc σ) heq.symm hst
          (by rw [length_applyList, length_applyList, hlen]) i
          (by rw [length_applyList]; exact hi) (by rw [length_applyList]; exact hti)
          (by rw [take_applyList, take_applyList, hpre]) ?_
        rw [getElem_applyList, getElem_applyList]
        exact hgt'
  | @mul f ss ts hvc hw hst hne pick hpick hcnt ih =>
      intro hs ht
      rcases (wt_subst_le M hL σ hσ hvc (le_of_eq hw.symm)).lt_or_eq with hlt | heq
      · exact Gt.weight (vc_subst M hvc σ) hlt
      · have hwfss := wft_args M hs
        have hwfts := wft_args M ht
        have hHO : HOGt (Gt M) (ss : Multiset (Term sigma nu)) (ts : Multiset (Term sigma nu)) :=
          ⟨hne, fun y hy => ⟨pick y, hpick y hy, hcnt y hy⟩⟩
        obtain ⟨hX, hdB, hdA⟩ := hoGt_decomp (Gt M) hHO
        have hmapB : ((Subst.applyList σ ss : List (Term sigma nu)) : Multiset (Term sigma nu)) =
            ((ts : Multiset (Term sigma nu)) ∩ ss).map (Subst.apply σ) +
              ((ss : Multiset (Term sigma nu)) - ts).map (Subst.apply σ) := by
          rw [← Multiset.map_add, hdB, Subst.applyList_eq_map, Multiset.map_coe]
        have hmapA : ((Subst.applyList σ ts : List (Term sigma nu)) : Multiset (Term sigma nu)) =
            ((ts : Multiset (Term sigma nu)) ∩ ss).map (Subst.apply σ) +
              ((ts : Multiset (Term sigma nu)) - ss).map (Subst.apply σ) := by
          rw [← Multiset.map_add, hdA, Subst.applyList_eq_map, Multiset.map_coe]
        have hHO' : HOGt (Gt M)
            ((Subst.applyList σ ss : List (Term sigma nu)) : Multiset (Term sigma nu))
            ((Subst.applyList σ ts : List (Term sigma nu)) : Multiset (Term sigma nu)) := by
          rw [hmapB, hmapA]
          refine dm_to_hoGt (Gt M) (fun a b c hab hbc => gt_trans M hL hab hbc)
            (gt_irrefl M hL) ?_ ?_
          · intro h0
            exact hX (Multiset.map_eq_zero.1 h0)
          · intro y' hy'
            obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hy'
            have hy2 : Multiset.count y (ss : Multiset (Term sigma nu)) <
                Multiset.count y (ts : Multiset (Term sigma nu)) := by
              have := Multiset.count_pos.2 hy
              rw [Multiset.count_sub] at this
              omega
            have hpy := hcnt y hy2
            refine ⟨Subst.apply σ (pick y), Multiset.mem_map_of_mem _ ?_, ?_⟩
            · rw [← Multiset.count_pos, Multiset.count_sub]
              omega
            · have hpyss : pick y ∈ ss := by
                rw [← Multiset.mem_coe, ← Multiset.count_pos]
                omega
              have hyts : y ∈ ts := by
                rw [← Multiset.mem_coe, ← Multiset.count_pos]
                omega
              exact ih y hy2 (hwfss _ hpyss) (hwfts _ hyts)
        obtain ⟨hne', hdom'⟩ := hHO'
        have hdom'' : ∀ y, ∃ x,
            Multiset.count y ((Subst.applyList σ ss : List (Term sigma nu)) :
              Multiset (Term sigma nu)) <
            Multiset.count y ((Subst.applyList σ ts : List (Term sigma nu)) :
              Multiset (Term sigma nu)) →
            Gt M x y ∧ Multiset.count x ((Subst.applyList σ ts : List (Term sigma nu)) :
              Multiset (Term sigma nu)) <
            Multiset.count x ((Subst.applyList σ ss : List (Term sigma nu)) :
              Multiset (Term sigma nu)) := by
          intro y
          by_cases hy : Multiset.count y ((Subst.applyList σ ss : List (Term sigma nu)) :
              Multiset (Term sigma nu)) <
              Multiset.count y ((Subst.applyList σ ts : List (Term sigma nu)) :
                Multiset (Term sigma nu))
          · obtain ⟨x, hx⟩ := hdom' y hy
            exact ⟨x, fun _ => hx⟩
          · exact ⟨y, fun h => absurd h hy⟩
        choose pick' hpick' using hdom''
        exact Gt.mul (vc_subst M hvc σ) heq.symm hst hne' pick' (fun y hy => (hpick' y hy).1)
          (fun y hy => (hpick' y hy).2)

/-- The core KBO is a reduction order on well-formed terms: irreflexive, transitive, well founded,
closed under argument contexts and under substitutions with well-formed images. -/
theorem kbo_reductionOrder [WellFoundedLT W] (hL : M.Laws) :
    (∀ s : Term sigma nu, ¬ Gt M s s) ∧
    (∀ s t u : Term sigma nu, Gt M s t → Gt M t u → Gt M s u) ∧
    WellFounded (KR M : Term sigma nu → Term sigma nu → Prop) ∧
    (∀ s t : Term sigma nu, Gt M s t → ∀ (f : sigma) (pre post : List (Term sigma nu)),
      Gt M (.app f (pre ++ s :: post)) (.app f (pre ++ t :: post))) ∧
    (∀ σ : Subst sigma nu, (∀ x, M.WFT (σ x)) → ∀ s t : Term sigma nu, Gt M s t →
      M.WFT s → M.WFT t → Gt M (Subst.apply σ s) (Subst.apply σ t)) :=
  ⟨gt_irrefl M hL, fun _ _ _ => gt_trans M hL, kr_wellFounded M hL,
    fun _ _ h f pre post => gt_ctx M hL h f pre post,
    fun σ hσ _ _ h hs ht => gt_subst M hL σ hσ h hs ht⟩

/-- An application with well-formed arguments and a non-special head is above each argument (the
subterm property at such heads). -/
theorem gt_arg (hL : M.Laws) {f : sigma} {args : List (Term sigma nu)}
    (hwf : ∀ a ∈ args, M.WFT a) (hns : ¬ M.Special f args) {b : Term sigma nu}
    (hb : b ∈ args) : Gt M (.app f args) b :=
  Gt.weight (fun x => by
      rw [cnt_app]
      exact ev_le_evL_of_mem _ (fun _ => le_rfl) (fun _ => Nat.zero_le _) hL.coeff_pos f args 0
        b hb)
    (wt_arg_lt M hL hwf hns hb)

end KBOSubst

section KBORO

variable {sigma : Type} {W : Type u} [AddCommMonoid W] [LinearOrder W] [DecidableEq sigma]

/-- The reduction-order properties of the KBO of a core, on well-formed terms with variables in
`nu`: irreflexive, transitive, well founded, closed under argument contexts and under
substitutions with well-formed images. -/
def KBOReductionOrder (nu : Type) [DecidableEq nu] (M : KBOCore sigma W) : Prop :=
  (∀ s : Term sigma nu, ¬ Gt M s s) ∧
  (∀ s t u : Term sigma nu, Gt M s t → Gt M t u → Gt M s u) ∧
  WellFounded (KR M : Term sigma nu → Term sigma nu → Prop) ∧
  (∀ s t : Term sigma nu, Gt M s t → ∀ (f : sigma) (pre post : List (Term sigma nu)),
    Gt M (.app f (pre ++ s :: post)) (.app f (pre ++ t :: post))) ∧
  (∀ σ : Subst sigma nu, (∀ x, M.WFT (σ x)) → ∀ s t : Term sigma nu, Gt M s t →
    M.WFT s → M.WFT t → Gt M (Subst.apply σ s) (Subst.apply σ t))

/-- The core KBO over an arbitrary signature is a reduction order under its admissibility laws;
the signature hypothesis is a well-founded precedence (automatic for a finite signature). -/
theorem kbo_isReductionOrder [IsOrderedCancelAddMonoid W] [WellFoundedLT W] (nu : Type)
    [DecidableEq nu] (M : KBOCore sigma W) (hL : M.Laws) : KBOReductionOrder nu M :=
  kbo_reductionOrder M hL

end KBORO

/-! ## Part 1b. The free schema over its ranked signature -/

/-- The four symbols of the free recursor schema. -/
inductive SchemaSym
  | zero
  | succ
  | wrap
  | recur
  deriving DecidableEq, Repr, Fintype

/-- Arities of the schema symbols. -/
def schemaAr : SchemaSym → ℕ
  | .zero => 0
  | .succ => 1
  | .wrap => 2
  | .recur => 3

/-- The free schema `SchemaCore.FreeTerm` as first-order terms over `SchemaSym`. -/
def embed {ν : Type} : SchemaCore.FreeTerm ν → Term SchemaSym ν
  | .var x => .var x
  | .zero => .app .zero []
  | .succ t => .app .succ [embed t]
  | .wrap s t => .app .wrap [embed s, embed t]
  | .recur b s n => .app .recur [embed b, embed s, embed n]

theorem wft_embed {W : Type u} (M : KBOCore SchemaSym W) (har : ∀ f, M.arOK f (schemaAr f))
    {ν : Type} : ∀ t : SchemaCore.FreeTerm ν, M.WFT (embed t)
  | .var x => .var x
  | .zero => .app _ _ (har .zero) (by simp)
  | .succ t => .app _ _ (har .succ) (by simpa using wft_embed M har t)
  | .wrap s t => .app _ _ (har .wrap) (by simp [wft_embed M har s, wft_embed M har t])
  | .recur b s n => .app _ _ (har .recur)
      (by simp [wft_embed M har b, wft_embed M har s, wft_embed M har n])

/-- A strict precedence on the finite schema signature is well founded. -/
theorem schema_prec_wf (prec : SchemaSym → SchemaSym → Prop) (hirr : ∀ f, ¬ prec f f)
    (htr : ∀ f g h, prec f g → prec g h → prec f h) : WellFounded (fun g f => prec f g) := by
  haveI : IsTrans SchemaSym (fun g f => prec f g) := ⟨fun a b c hab hbc => htr c b a hbc hab⟩
  haveI : IsIrrefl SchemaSym (fun g f => prec f g) := ⟨fun a h => hirr a h⟩
  exact Finite.wellFounded_of_trans_of_irrefl _

/-- A precedence read off a rank function. -/
def rankPrec (rk : SchemaSym → ℕ) (f g : SchemaSym) : Prop := rk g < rk f

theorem rankPrec_irrefl (rk : SchemaSym → ℕ) (f : SchemaSym) : ¬ rankPrec rk f f :=
  lt_irrefl _

theorem rankPrec_trans (rk : SchemaSym → ℕ) (f g h : SchemaSym) (hfg : rankPrec rk f g)
    (hgh : rankPrec rk g h) : rankPrec rk f h :=
  lt_trans hgh hfg

/-- Rank `recur ≻ wrap ≻ succ ≻ zero`. -/
def schemaRank : SchemaSym → ℕ
  | .zero => 0
  | .succ => 1
  | .wrap => 2
  | .recur => 3

/-- Rank `succ ≻ recur ≻ wrap ≻ zero` (the unary symbol on top). -/
def wsRank : SchemaSym → ℕ
  | .zero => 0
  | .wrap => 1
  | .recur => 2
  | .succ => 3

/-- Admissibility of a core over the schema signature from its schema-level conditions. -/
theorem schemaCore_laws {W : Type u} [AddCommMonoid W] [LinearOrder W]
    (M : KBOCore SchemaSym W) (har : ∀ f n, M.arOK f n ↔ n = schemaAr f)
    (hw0 : 0 < M.w0) (hwn : ∀ f, 0 ≤ M.weight f) (hzero : M.w0 ≤ M.weight .zero)
    (hc : ∀ f i, 1 ≤ M.coeff f i)
    (hsucc : M.weight .succ = 0 → ∀ g, g ≠ .succ → M.prec .succ g)
    (hirr : ∀ f, ¬ M.prec f f) (htr : ∀ f g h, M.prec f g → M.prec g h → M.prec f h) :
    M.Laws where
  w0_pos := hw0
  weight_nonneg := hwn
  const_ge f hf := by
    rw [har] at hf
    cases f with
    | zero => exact hzero
    | succ => exact absurd hf (by decide)
    | wrap => exact absurd hf (by decide)
    | recur => exact absurd hf (by decide)
  coeff_pos := hc
  special_unary f hf _ n hn := by
    rw [har] at hf hn
    omega
  special_max f hf hw g hg := by
    rw [har] at hf
    cases f with
    | succ => exact hsucc hw g hg
    | zero => exact absurd hf (by decide)
    | wrap => exact absurd hf (by decide)
    | recur => exact absurd hf (by decide)
  prec_irrefl := hirr
  prec_trans := htr
  prec_wf := schema_prec_wf M.prec hirr htr

section SchemaKBO

variable {W : Type u} [AddCommMonoid W] [LinearOrder W]

/-- Acceptance of the free duplicating rule `SchemaCore.RootStep.recurSucc` by a KBO over the
schema signature: every instance, transported by `embed`, is oriented. -/
def KBOAcceptsDup (M : KBOCore SchemaSym W) : Prop :=
  ∀ b s n : SchemaCore.FreeTerm ℕ,
    Gt M (embed (.recur b s (.succ n))) (embed (.wrap s (.recur b s n)))

/-- The adapter: acceptance is the orientation of every embedded `RootStep` step other than the
zero rule, that is, of every embedded `RootStep.recurSucc` step. -/
theorem kboAcceptsDup_iff (M : KBOCore SchemaSym W) :
    KBOAcceptsDup M ↔ ∀ t u : SchemaCore.FreeTerm ℕ, SchemaCore.RootStep t u →
      (∀ b s, t ≠ .recur b s .zero) → Gt M (embed t) (embed u) := by
  constructor
  · intro h t u hst hz
    cases hst with
    | recurZero _ _ => exact absurd rfl (hz _ _)
    | recurSucc b s n => exact h b s n
  · intro h b s n
    exact h _ _ (SchemaCore.RootStep.recurSucc b s n) (fun b' s' heq => by cases heq)

/-- The variable-condition obstruction over an arbitrary signature: a pair whose smaller side
counts some variable more (with subterm coefficients) is not related. -/
theorem kbo_not_gt_of_cnt_lt {sigma nu : Type} [DecidableEq sigma] [DecidableEq nu]
    (M : KBOCore sigma W) {l r : Term sigma nu} {x : nu}
    (hx : cnt M.coeff x l < cnt M.coeff x r) : ¬ Gt M l r :=
  fun h => absurd (gt_vc M h x) (not_le.2 hx)

end SchemaKBO

/-- The weighted count of the payload variable `1` on embedded free terms. -/
def payloadCount (c : SchemaSym → ℕ → ℕ) (t : SchemaCore.FreeTerm ℕ) : ℕ := cnt c 1 (embed t)

theorem payloadCount_var (c : SchemaSym → ℕ → ℕ) (y : ℕ) :
    payloadCount c (.var y) = if y = 1 then 1 else 0 := rfl

theorem payloadCount_zero (c : SchemaSym → ℕ → ℕ) : payloadCount c .zero = 0 := rfl

theorem payloadCount_succ (c : SchemaSym → ℕ → ℕ) (t : SchemaCore.FreeTerm ℕ) :
    payloadCount c (.succ t) = c .succ 0 * payloadCount c t := by
  simp [payloadCount, cnt, embed]

theorem payloadCount_wrap (c : SchemaSym → ℕ → ℕ) (s t : SchemaCore.FreeTerm ℕ) :
    payloadCount c (.wrap s t) = c .wrap 0 * payloadCount c s + c .wrap 1 * payloadCount c t := by
  simp [payloadCount, cnt, embed]

theorem payloadCount_recur (c : SchemaSym → ℕ → ℕ) (b s n : SchemaCore.FreeTerm ℕ) :
    payloadCount c (.recur b s n) =
      c .recur 0 * payloadCount c b + c .recur 1 * payloadCount c s +
        c .recur 2 * payloadCount c n := by
  simp [payloadCount, cnt, embed, add_assoc]

/-- A payload family with unbounded payload count. -/
def payTower : ℕ → SchemaCore.FreeTerm ℕ
  | 0 => .var 1
  | k + 1 => .wrap (.var 1) (payTower k)

theorem payloadCount_payTower (c : SchemaSym → ℕ → ℕ) (hc : ∀ f i, 1 ≤ c f i) :
    ∀ k, k + 1 ≤ payloadCount c (payTower k)
  | 0 => by simp [payTower, payloadCount_var]
  | k + 1 => by
      rw [payTower, payloadCount_wrap, payloadCount_var, if_pos rfl]
      have h1 := payloadCount_payTower c hc k
      nlinarith [Nat.mul_le_mul_right (payloadCount c (payTower k)) (hc .wrap 1), hc .wrap 0]

/-- The weighted payload count has unbounded wrapper margin at base and counter `zero` (the
first predicate of the P3.2 barrier cell). -/
theorem payload_wrapUnbounded (c : SchemaSym → ℕ → ℕ) (hc : ∀ f i, 1 ≤ c f i) :
    CellClassification.WrapUnboundedAt (S := SchemaCore.freeSchema ℕ) (payloadCount c)
      .zero .zero := by
  intro K
  refine ⟨payTower K, ?_⟩
  show payloadCount c (.recur .zero (payTower K) .zero) + K <
    payloadCount c (.wrap (payTower K) (.recur .zero (payTower K) .zero))
  rw [payloadCount_wrap, payloadCount_recur, payloadCount_zero]
  simp only [mul_zero, zero_add, add_zero]
  have h1 := payloadCount_payTower c hc K
  nlinarith [Nat.mul_le_mul_right (payloadCount c (payTower K)) (hc .wrap 0),
    Nat.mul_le_mul_right (c .recur 1 * payloadCount c (payTower K)) (hc .wrap 1)]

/-- The weighted payload count has bounded counter gain at base and counter `zero` (the second
predicate of the P3.2 barrier cell). -/
theorem payload_gainBounded (c : SchemaSym → ℕ → ℕ) :
    CellClassification.GainBoundedAt (S := SchemaCore.freeSchema ℕ) (payloadCount c)
      .zero .zero := by
  refine ⟨0, fun s => ?_⟩
  show payloadCount c (.recur .zero s (.succ .zero)) ≤ payloadCount c (.recur .zero s .zero) + 0
  rw [payloadCount_recur, payloadCount_recur, payloadCount_succ, payloadCount_zero]
  simp

/-- The strict form of the P3.2 barrier cell: unbounded wrapper margin and bounded counter gain at
a fixed base and counter produce an instance whose right side is strictly larger. -/
theorem barrier_cell_strict_reversal {S : OperatorKO7.StepDuplicating.StepDuplicatingSchema}
    (M : S.T → ℕ) (b n : S.T) (hw : CellClassification.WrapUnboundedAt M b n)
    (hg : CellClassification.GainBoundedAt M b n) :
    ∃ s, M (S.recur b s (S.succ n)) < M (S.wrap s (S.recur b s n)) := by
  obtain ⟨K, hK⟩ := hg
  obtain ⟨s, hs⟩ := hw K
  exact ⟨s, lt_of_le_of_lt (hK s) hs⟩

section SchemaKBOBarrier

variable {W : Type u} [AddCommMonoid W] [LinearOrder W]

/-- The KBO barrier on the free schema, derived from the P3.2 barrier cell: the weighted payload
count has unbounded wrapper margin and bounded counter gain at base and counter `zero`, so some
instance violates the coefficient-weighted variable condition that every KBO clause requires. Only
positivity of the subterm coefficients is used. -/
theorem kbo_rejects_dup (M : KBOCore SchemaSym W) (hc : ∀ f i, 1 ≤ M.coeff f i) :
    ¬ KBOAcceptsDup M := by
  intro hacc
  obtain ⟨s, hs⟩ := barrier_cell_strict_reversal (S := SchemaCore.freeSchema ℕ)
    (payloadCount M.coeff) .zero .zero (payload_wrapUnbounded M.coeff hc)
    (payload_gainBounded M.coeff)
  exact absurd (gt_vc M (hacc .zero s .zero) 1) (not_le.2 hs)

end SchemaKBOBarrier

/-! ## Row `standardKBO` -/

/-- Native data of the standard Knuth–Bendix order on the schema signature: variable weight,
symbol weights, precedence. -/
structure standardKBOData where
  /-- Variable weight. -/
  w0 : ℕ
  /-- Symbol weights. -/
  weight : SchemaSym → ℕ
  /-- Strict precedence. -/
  prec : SchemaSym → SchemaSym → Prop

/-- Admissibility of the standard Knuth–Bendix order: Knuth and Bendix 1970, in the form with the
variable condition of Dick, Kalmus, Martin 1990 (Acta Informatica 28) and Baader and Nipkow 1998
(Term Rewriting and All That, Section 5.4), restated as Ludwig and Waldmann 2007 (LPAR, LNCS 4790),
Definition 2 with admissibility conditions (i) and (ii): a positive variable weight, the constant
at least the variable weight, a unary symbol of weight zero above every other symbol, and a strict
precedence (well founded on the finite signature). -/
structure standardKBOLaws (M : standardKBOData) : Prop where
  w0_pos : 0 < M.w0
  zero_ge : M.w0 ≤ M.weight .zero
  succ_max : M.weight .succ = 0 → ∀ g, g ≠ .succ → M.prec .succ g
  prec_irrefl : ∀ f, ¬ M.prec f f
  prec_trans : ∀ f g h, M.prec f g → M.prec g h → M.prec f h

/-- The standard KBO as the core with unit subterm coefficients and lexicographic status. -/
def standardKBOCore (M : standardKBOData) : KBOCore SchemaSym ℕ where
  arOK f n := n = schemaAr f
  w0 := M.w0
  weight := M.weight
  coeff _ _ := 1
  prec := M.prec
  status _ := .lex

theorem standardKBOCore_laws {M : standardKBOData} (h : standardKBOLaws M) :
    (standardKBOCore M).Laws :=
  schemaCore_laws _ (fun _ _ => Iff.rfl) h.w0_pos (fun _ => Nat.zero_le _) h.zero_ge
    (fun _ _ => le_rfl) h.succ_max h.prec_irrefl h.prec_trans

/-- The standard KBO of admissible data is a reduction order on well-formed terms over the schema
signature (for an arbitrary signature, `kbo_isReductionOrder` at unit coefficients and
lexicographic status). -/
theorem standardKBO_order (M : standardKBOData) (h : standardKBOLaws M) (ν : Type)
    [DecidableEq ν] : KBOReductionOrder ν (standardKBOCore M) :=
  kbo_isReductionOrder ν _ (standardKBOCore_laws h)

/-- Acceptance of the free duplicating rule by the standard KBO. -/
def standardKBOAccepts (M : standardKBOData) : Prop := KBOAcceptsDup (standardKBOCore M)

/-- Verdict: barrier. The standard KBO does not orient the free duplicating rule. -/
def standardKBOResult (M : standardKBOData) : Prop := ¬ standardKBOAccepts M

/-- The barrier holds for every datum (P3.2 cell via `kbo_rejects_dup`); the admissibility laws
are not used by it. -/
theorem standardKBO_rejects (M : standardKBOData) : standardKBOResult M :=
  kbo_rejects_dup (standardKBOCore M) (fun _ _ => le_rfl)

theorem standardKBO_universal : ∀ M, standardKBOLaws M → standardKBOResult M :=
  fun M _ => standardKBO_rejects M

/-- A standard KBO: all weights `1`, precedence `recur ≻ wrap ≻ succ ≻ zero`. -/
def standardKBOWitness : standardKBOData where
  w0 := 1
  weight _ := 1
  prec := rankPrec schemaRank

theorem standardKBOWitness_laws : standardKBOLaws standardKBOWitness where
  w0_pos := by decide
  zero_ge := le_rfl
  succ_max h := absurd h (by decide)
  prec_irrefl := rankPrec_irrefl _
  prec_trans := rankPrec_trans _

theorem standardKBOWitness_result : standardKBOResult standardKBOWitness :=
  standardKBO_rejects _

/-- Controls: the payload variable is duplicated (count `1` on the left and `2` on the right of the
pattern instance), and a nonduplicating rule, the zero rule `recur b s zero → b`, is oriented at
every instance. -/
theorem standardKBOWitness_feature :
    (cnt (standardKBOCore standardKBOWitness).coeff 1
        (embed (.recur (.var 0) (.var 1) (.succ (.var 2)) : SchemaCore.FreeTerm ℕ)) = 1 ∧
      cnt (standardKBOCore standardKBOWitness).coeff 1
        (embed (.wrap (.var 1) (.recur (.var 0) (.var 1) (.var 2)) :
          SchemaCore.FreeTerm ℕ)) = 2) ∧
    ∀ b s : SchemaCore.FreeTerm ℕ,
      Gt (standardKBOCore standardKBOWitness) (embed (.recur b s .zero)) (embed b) := by
  refine ⟨⟨by decide, by decide⟩, fun b s => ?_⟩
  exact gt_arg _ (standardKBOCore_laws standardKBOWitness_laws)
    (fun a ha => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> exact wft_embed _ (fun _ => rfl) _)
    (by simp [KBOCore.Special]) (by simp)

/-- Mutation: the variable weight of the witness set to `0`; admissibility fails. -/
theorem standardKBO_mutation : ¬ standardKBOLaws { standardKBOWitness with w0 := 0 } :=
  fun h => lt_irrefl 0 h.w0_pos

/-! ## Row `subtermCoefficientKBO` -/

/-- Native data of the Knuth–Bendix order with subterm coefficients: variable weight, symbol
weights, a positive coefficient per argument position, precedence. -/
structure subtermCoefficientKBOData where
  /-- Variable weight. -/
  w0 : ℕ
  /-- Symbol weights. -/
  weight : SchemaSym → ℕ
  /-- Subterm coefficient of argument position `i` of `f`. -/
  coeff : SchemaSym → ℕ → ℕ
  /-- Strict precedence. -/
  prec : SchemaSym → SchemaSym → Prop

/-- Admissibility of the Knuth–Bendix order with subterm coefficients: the transfinite KBO of
Ludwig and Waldmann 2007 (LPAR, LNCS 4790), Definitions 12, 13, 15, 16 and 17, at natural weights
and positive natural coefficients per argument position, as restated by Yamada, Kusakari, Sakabe
2015 (Science of Computer Programming 111), Section 2.1.4, with Theorem 6 there; the weight is
`w(f) + Σ sc(f, i) · w(s_i)` and the variable condition compares `vc(x, ·)`. -/
structure subtermCoefficientKBOLaws (M : subtermCoefficientKBOData) : Prop where
  w0_pos : 0 < M.w0
  zero_ge : M.w0 ≤ M.weight .zero
  coeff_pos : ∀ f i, 1 ≤ M.coeff f i
  succ_max : M.weight .succ = 0 → ∀ g, g ≠ .succ → M.prec .succ g
  prec_irrefl : ∀ f, ¬ M.prec f f
  prec_trans : ∀ f g h, M.prec f g → M.prec g h → M.prec f h

/-- The KBO with subterm coefficients as the core with lexicographic status. -/
def subtermCoefficientKBOCore (M : subtermCoefficientKBOData) : KBOCore SchemaSym ℕ where
  arOK f n := n = schemaAr f
  w0 := M.w0
  weight := M.weight
  coeff := M.coeff
  prec := M.prec
  status _ := .lex

theorem subtermCoefficientKBOCore_laws {M : subtermCoefficientKBOData}
    (h : subtermCoefficientKBOLaws M) : (subtermCoefficientKBOCore M).Laws :=
  schemaCore_laws _ (fun _ _ => Iff.rfl) h.w0_pos (fun _ => Nat.zero_le _) h.zero_ge
    h.coeff_pos h.succ_max h.prec_irrefl h.prec_trans

theorem subtermCoefficientKBO_order (M : subtermCoefficientKBOData)
    (h : subtermCoefficientKBOLaws M) (ν : Type) [DecidableEq ν] :
    KBOReductionOrder ν (subtermCoefficientKBOCore M) :=
  kbo_isReductionOrder ν _ (subtermCoefficientKBOCore_laws h)

def subtermCoefficientKBOAccepts (M : subtermCoefficientKBOData) : Prop :=
  KBOAcceptsDup (subtermCoefficientKBOCore M)

/-- Verdict: barrier. No KBO with positive subterm coefficients orients the free duplicating
rule. -/
def subtermCoefficientKBOResult (M : subtermCoefficientKBOData) : Prop :=
  ¬ subtermCoefficientKBOAccepts M

/-- The barrier, derived from the P3.2 cell; coefficient positivity is the premise used. -/
theorem subtermCoefficientKBO_universal :
    ∀ M, subtermCoefficientKBOLaws M → subtermCoefficientKBOResult M :=
  fun M h => kbo_rejects_dup (subtermCoefficientKBOCore M) h.coeff_pos

/-- Coefficients of the witness: the payload position of `recur` has coefficient `2`. -/
def scCoeff : SchemaSym → ℕ → ℕ
  | .recur, 1 => 2
  | _, _ => 1

/-- Weights of the witness: `succ` weighs `2`, every other symbol `1`. -/
def scWeight : SchemaSym → ℕ
  | .succ => 2
  | _ => 1

def subtermCoefficientKBOWitness : subtermCoefficientKBOData where
  w0 := 1
  weight := scWeight
  coeff := scCoeff
  prec := rankPrec schemaRank

theorem scCoeff_pos (f : SchemaSym) (i : ℕ) : 1 ≤ scCoeff f i := by
  unfold scCoeff
  split <;> omega

theorem subtermCoefficientKBOWitness_laws :
    subtermCoefficientKBOLaws subtermCoefficientKBOWitness where
  w0_pos := by decide
  zero_ge := le_rfl
  coeff_pos := scCoeff_pos
  succ_max h := absurd h (by decide)
  prec_irrefl := rankPrec_irrefl _
  prec_trans := rankPrec_trans _

theorem subtermCoefficientKBOWitness_result :
    subtermCoefficientKBOResult subtermCoefficientKBOWitness :=
  subtermCoefficientKBO_universal _ subtermCoefficientKBOWitness_laws

/-- Controls: the weighted count differs from the ordinary count (payload coefficient `2`), and
on the pattern instance the payload counts `2` on the left and `1 + 1 · 2 = 3` on the right. -/
theorem subtermCoefficientKBOWitness_feature :
    cnt scCoeff 1 (embed (.recur (.var 0) (.var 1) (.var 2) : SchemaCore.FreeTerm ℕ)) = 2 ∧
    cnt (fun _ _ => 1) 1 (embed (.recur (.var 0) (.var 1) (.var 2) : SchemaCore.FreeTerm ℕ)) = 1 ∧
    cnt scCoeff 1 (embed (.recur (.var 0) (.var 1) (.succ (.var 2)) : SchemaCore.FreeTerm ℕ)) = 2 ∧
    cnt scCoeff 1 (embed (.wrap (.var 1) (.recur (.var 0) (.var 1) (.var 2)) :
      SchemaCore.FreeTerm ℕ)) = 3 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- The witness with the coefficient of the first wrapper position set to `0`. -/
def scCoeffMutant : SchemaSym → ℕ → ℕ
  | .wrap, 0 => 0
  | .recur, 1 => 2
  | _, _ => 1

/-- Mutation: the coefficient of the first `wrap` position of the witness set to `0`. Coefficient
positivity then fails, and the mutated order accepts the duplicating rule (by weight, with the
weighted variable condition met), so positivity is load-bearing for the barrier. -/
theorem subtermCoefficientKBO_mutation :
    ¬ subtermCoefficientKBOLaws { subtermCoefficientKBOWitness with coeff := scCoeffMutant } ∧
      subtermCoefficientKBOAccepts
        { subtermCoefficientKBOWitness with coeff := scCoeffMutant } := by
  refine ⟨fun h => absurd (h.coeff_pos .wrap 0) (by decide), fun b s n => ?_⟩
  refine Gt.weight (fun x => ?_) ?_
  · simp only [embed, cnt_app, ev_app, zero_add, evL_cons, evL_nil, smul_eq_mul, subtermCoefficientKBOCore,
      scCoeffMutant]
    omega
  · simp only [embed, KBOCore.wt, ev_app, evL_cons, evL_nil, smul_eq_mul,
      subtermCoefficientKBOCore, subtermCoefficientKBOWitness, scCoeffMutant, scWeight]
    omega

/-! ## Row `kboWithStatus` -/

/-- Native data of the Knuth–Bendix order with argument status: variable weight, symbol weights,
precedence, status per symbol. -/
structure kboWithStatusData where
  /-- Variable weight. -/
  w0 : ℕ
  /-- Symbol weights. -/
  weight : SchemaSym → ℕ
  /-- Strict precedence. -/
  prec : SchemaSym → SchemaSym → Prop
  /-- Argument status. -/
  status : SchemaSym → KStatus

/-- Admissibility of the Knuth–Bendix order with status: Becker, Blanchette, Waldmann, Wand 2017
(CADE-26, LNCS 10395), Definition 8 at natural weights, with the lexicographic extension
(Definition 4) or the Huet–Oppen multiset extension (Definition 6) per symbol: `ε > 0`, constants at
least `ε`, a unary symbol of weight zero above every other symbol, and a strict precedence
(Definition 8 asks for a well-founded total order; totality is not used). -/
structure kboWithStatusLaws (M : kboWithStatusData) : Prop where
  w0_pos : 0 < M.w0
  zero_ge : M.w0 ≤ M.weight .zero
  succ_max : M.weight .succ = 0 → ∀ g, g ≠ .succ → M.prec .succ g
  prec_irrefl : ∀ f, ¬ M.prec f f
  prec_trans : ∀ f g h, M.prec f g → M.prec g h → M.prec f h

def kboWithStatusCore (M : kboWithStatusData) : KBOCore SchemaSym ℕ where
  arOK f n := n = schemaAr f
  w0 := M.w0
  weight := M.weight
  coeff _ _ := 1
  prec := M.prec
  status := M.status

theorem kboWithStatusCore_laws {M : kboWithStatusData} (h : kboWithStatusLaws M) :
    (kboWithStatusCore M).Laws :=
  schemaCore_laws _ (fun _ _ => Iff.rfl) h.w0_pos (fun _ => Nat.zero_le _) h.zero_ge
    (fun _ _ => le_rfl) h.succ_max h.prec_irrefl h.prec_trans

theorem kboWithStatus_order (M : kboWithStatusData) (h : kboWithStatusLaws M) (ν : Type)
    [DecidableEq ν] : KBOReductionOrder ν (kboWithStatusCore M) :=
  kbo_isReductionOrder ν _ (kboWithStatusCore_laws h)

def kboWithStatusAccepts (M : kboWithStatusData) : Prop := KBOAcceptsDup (kboWithStatusCore M)

/-- Verdict: barrier. No KBO with status orients the free duplicating rule. -/
def kboWithStatusResult (M : kboWithStatusData) : Prop := ¬ kboWithStatusAccepts M

/-- The barrier holds for every datum (P3.2 cell); the admissibility laws are not used by it. -/
theorem kboWithStatus_rejects (M : kboWithStatusData) : kboWithStatusResult M :=
  kbo_rejects_dup (kboWithStatusCore M) (fun _ _ => le_rfl)

theorem kboWithStatus_universal : ∀ M, kboWithStatusLaws M → kboWithStatusResult M :=
  fun M _ => kboWithStatus_rejects M

/-- Weights of the status witness: `succ` weighs `0` (the special unary symbol). -/
def wsWeight : SchemaSym → ℕ
  | .succ => 0
  | _ => 1

/-- Status of the witness: multiset status on `wrap`, lexicographic elsewhere. -/
def wsStatus : SchemaSym → KStatus
  | .wrap => .mul
  | _ => .lex

def kboWithStatusWitness : kboWithStatusData where
  w0 := 1
  weight := wsWeight
  prec := rankPrec wsRank
  status := wsStatus

theorem kboWithStatusWitness_laws : kboWithStatusLaws kboWithStatusWitness where
  w0_pos := by decide
  zero_ge := le_rfl
  succ_max _ g hg := by
    cases g with
    | zero => show wsRank .zero < wsRank .succ; decide
    | wrap => show wsRank .wrap < wsRank .succ; decide
    | recur => show wsRank .recur < wsRank .succ; decide
    | succ => exact absurd rfl hg
  prec_irrefl := rankPrec_irrefl _
  prec_trans := rankPrec_trans _

theorem kboWithStatusWitness_result : kboWithStatusResult kboWithStatusWitness :=
  kboWithStatus_rejects _

/-- Controls: a strict-weight comparison, an equal-weight precedence comparison, the zero-weight
unary symbol above its argument, a comparison through the multiset status of `wrap`, the
multiset status refusing a pair that the lexicographic status would accept, and a comparison
lifted through a common context. -/
theorem kboWithStatusWitness_feature :
    Gt (kboWithStatusCore kboWithStatusWitness)
      (embed (.wrap .zero .zero : SchemaCore.FreeTerm ℕ)) (embed .zero) ∧
    Gt (kboWithStatusCore kboWithStatusWitness)
      (embed (.succ .zero : SchemaCore.FreeTerm ℕ)) (embed .zero) ∧
    Gt (kboWithStatusCore kboWithStatusWitness)
      (embed (.succ (.var 0) : SchemaCore.FreeTerm ℕ)) (.var 0) ∧
    Gt (kboWithStatusCore kboWithStatusWitness)
      (embed (.wrap .zero (.succ .zero) : SchemaCore.FreeTerm ℕ))
      (embed (.wrap .zero .zero)) ∧
    ¬ Gt (kboWithStatusCore kboWithStatusWitness)
      (embed (.wrap (.succ .zero) .zero : SchemaCore.FreeTerm ℕ))
      (embed (.wrap .zero (.succ .zero))) ∧
    Gt (kboWithStatusCore kboWithStatusWitness)
      (embed (.recur (.succ .zero) .zero .zero : SchemaCore.FreeTerm ℕ))
      (embed (.recur .zero .zero .zero)) := by
  have hL := kboWithStatusCore_laws kboWithStatusWitness_laws
  have h2 : Gt (kboWithStatusCore kboWithStatusWitness)
      (embed (.succ .zero : SchemaCore.FreeTerm ℕ)) (embed .zero) :=
    Gt.prec (fun _ => Nat.zero_le _) (by decide)
      (show wsRank .zero < wsRank .succ by decide)
  have hcnt0 : Multiset.count (embed (.succ .zero : SchemaCore.FreeTerm ℕ))
      (([embed .zero, embed .zero] : List (Term SchemaSym ℕ)) : Multiset (Term SchemaSym ℕ)) <
      Multiset.count (embed (.succ .zero : SchemaCore.FreeTerm ℕ))
        (([embed .zero, embed (.succ .zero)] : List (Term SchemaSym ℕ)) :
          Multiset (Term SchemaSym ℕ)) := by decide
  refine ⟨Gt.weight (fun _ => Nat.zero_le _) (by decide), h2,
    gt_tower _ hL (ι := .succ) rfl rfl rfl (.var 0) (.var 0) 1 le_rfl, ?_, ?_,
    gt_ctx _ hL h2 .recur [] [embed .zero, embed .zero]⟩
  · refine Gt.mul (fun _ => Nat.zero_le _) (by decide) rfl (by decide)
      (fun _ => embed (.succ .zero)) ?_ (fun _ _ => hcnt0)
    intro y hy
    by_cases hy0 : y = embed .zero
    · subst hy0
      exact h2
    · exfalso
      have hy0' : embed (.zero : SchemaCore.FreeTerm ℕ) ≠ y := Ne.symm hy0
      simp [hy0, hy0'] at hy
  · intro h
    change Gt (kboWithStatusCore kboWithStatusWitness)
      (.app .wrap [embed (.succ .zero), embed .zero])
      (.app .wrap [embed .zero, embed (.succ .zero)]) at h
    cases h with
    | weight _ hw => exact absurd hw (by decide)
    | prec _ _ hp => exact lt_irrefl _ hp
    | lex _ _ hst _ _ _ _ _ _ => exact absurd hst (by decide)
    | mul _ _ _ hne _ _ _ => exact hne (Multiset.coe_eq_coe.2 (List.Perm.swap _ _ _))

/-- Mutation: the precedence of the witness replaced by `recur ≻ wrap ≻ succ ≻ zero`, which puts
the zero-weight unary symbol below `recur`; admissibility fails. -/
theorem kboWithStatus_mutation :
    ¬ kboWithStatusLaws { kboWithStatusWitness with prec := rankPrec schemaRank } :=
  fun h => absurd (h.succ_max rfl .recur (by decide))
    (show ¬ schemaRank .recur < schemaRank .succ by decide)

/-! ## Row `transfiniteKBO` -/

/-- Native data of the transfinite Knuth–Bendix order: a natural variable weight, ordinal symbol
weights given as ordinal notations below `ε₀` (the syntactic ordinals of the pinned sources),
natural subterm coefficients, precedence. -/
structure transfiniteKBOData where
  /-- Variable weight `φ₀ ∈ ℕ_{>0}`. -/
  w0 : ℕ
  /-- Ordinal symbol weights, as notations below `ε₀`. -/
  weight : SchemaSym → ONote
  /-- Subterm coefficients. -/
  coeff : SchemaSym → ℕ → ℕ
  /-- Strict precedence. -/
  prec : SchemaSym → SchemaSym → Prop

/-- Admissibility of the transfinite Knuth–Bendix order: Ludwig and Waldmann 2007 (LPAR, LNCS 4790),
Definition 17, with ordinal symbol weights (Definition 11) combined by the Hessenberg sum
(Definition 7; `NatOrdinal` addition), admissibility Definition 15 (i) and (ii), and subterm
coefficients restricted to positive naturals (the finite-coefficient transfinite KBO of Yamada,
Kusakari, Sakabe 2015, Section 2.1.4; with unit coefficients it is Becker et al. 2017,
Definition 8 at ordinal weights). -/
structure transfiniteKBOLaws (M : transfiniteKBOData) : Prop where
  w0_pos : 0 < M.w0
  zero_ge : (M.w0 : Ordinal) ≤ ONote.repr (M.weight .zero)
  coeff_pos : ∀ f i, 1 ≤ M.coeff f i
  succ_max : ONote.repr (M.weight .succ) = 0 → ∀ g, g ≠ .succ → M.prec .succ g
  prec_irrefl : ∀ f, ¬ M.prec f f
  prec_trans : ∀ f g h, M.prec f g → M.prec g h → M.prec f h

/-- The transfinite KBO as the core with weights in `NatOrdinal` (ordinals with the Hessenberg sum)
and lexicographic status. -/
noncomputable def transfiniteKBOCore (M : transfiniteKBOData) : KBOCore SchemaSym NatOrdinal where
  arOK f n := n = schemaAr f
  w0 := (M.w0 : NatOrdinal)
  weight f := Ordinal.toNatOrdinal (ONote.repr (M.weight f))
  coeff := M.coeff
  prec := M.prec
  status _ := .lex

theorem natOrdinal_natCast_pos {n : ℕ} (hn : 0 < n) : (0 : NatOrdinal) < (n : NatOrdinal) := by
  rw [← Ordinal.toNatOrdinal_natCast, ← Ordinal.toNatOrdinal_zero]
  exact Ordinal.toNatOrdinal.lt_iff_lt.2 (by exact_mod_cast hn)

theorem transfiniteKBOCore_laws {M : transfiniteKBOData} (h : transfiniteKBOLaws M) :
    (transfiniteKBOCore M).Laws :=
  schemaCore_laws _ (fun _ _ => Iff.rfl) (natOrdinal_natCast_pos h.w0_pos)
    (fun _ => NatOrdinal.zero_le _)
    (by
      show (M.w0 : NatOrdinal) ≤ Ordinal.toNatOrdinal (ONote.repr (M.weight .zero))
      rw [← Ordinal.toNatOrdinal_natCast]
      exact Ordinal.toNatOrdinal.le_iff_le.2 h.zero_ge)
    h.coeff_pos (fun hw => h.succ_max ((Ordinal.toNatOrdinal_eq_zero _).1 hw))
    h.prec_irrefl h.prec_trans

theorem transfiniteKBO_order (M : transfiniteKBOData) (h : transfiniteKBOLaws M) (ν : Type)
    [DecidableEq ν] : KBOReductionOrder ν (transfiniteKBOCore M) :=
  kbo_isReductionOrder ν _ (transfiniteKBOCore_laws h)

def transfiniteKBOAccepts (M : transfiniteKBOData) : Prop :=
  KBOAcceptsDup (transfiniteKBOCore M)

/-- Verdict: barrier. No transfinite KBO orients the free duplicating rule. -/
def transfiniteKBOResult (M : transfiniteKBOData) : Prop := ¬ transfiniteKBOAccepts M

theorem transfiniteKBO_universal : ∀ M, transfiniteKBOLaws M → transfiniteKBOResult M :=
  fun M h => kbo_rejects_dup (transfiniteKBOCore M) h.coeff_pos

/-- Weights of the transfinite witness: `succ` weighs `0`, `wrap` weighs `ω`, the others `1`. -/
def tkWeight : SchemaSym → ONote
  | .succ => 0
  | .wrap => ONote.omega
  | _ => 1

def transfiniteKBOWitness : transfiniteKBOData where
  w0 := 1
  weight := tkWeight
  coeff _ _ := 1
  prec := rankPrec wsRank

theorem transfiniteKBOWitness_laws : transfiniteKBOLaws transfiniteKBOWitness where
  w0_pos := by decide
  zero_ge := by simp [transfiniteKBOWitness, tkWeight]
  coeff_pos _ _ := le_rfl
  succ_max _ g hg := by
    cases g with
    | zero => show wsRank .zero < wsRank .succ; decide
    | wrap => show wsRank .wrap < wsRank .succ; decide
    | recur => show wsRank .recur < wsRank .succ; decide
    | succ => exact absurd rfl hg
  prec_irrefl := rankPrec_irrefl _
  prec_trans := rankPrec_trans _

theorem transfiniteKBOWitness_result : transfiniteKBOResult transfiniteKBOWitness :=
  transfiniteKBO_universal _ transfiniteKBOWitness_laws

theorem repr_omega' : ONote.repr ONote.omega = Ordinal.omega0 := by
  simp [ONote.omega]

/-- Controls: an infinite weight (every term containing `wrap` is heavier than every natural
number), ordinal absorption (`1 + ω = ω` for ordinal addition, while the Hessenberg sum used by the
method is strictly monotone, `1 ♯ ω ≠ ω`), and the zero-weight unary symbol above its argument. -/
theorem transfiniteKBOWitness_feature :
    (∀ n : ℕ, (n : NatOrdinal) < (transfiniteKBOCore transfiniteKBOWitness).wt
      (embed (.wrap .zero .zero : SchemaCore.FreeTerm ℕ))) ∧
    ((1 : Ordinal) + Ordinal.omega0 = Ordinal.omega0 ∧
      Ordinal.toNatOrdinal 1 + Ordinal.toNatOrdinal Ordinal.omega0 ≠
        Ordinal.toNatOrdinal Ordinal.omega0) ∧
    Gt (transfiniteKBOCore transfiniteKBOWitness)
      (embed (.succ (.var 0) : SchemaCore.FreeTerm ℕ)) (.var 0) := by
  refine ⟨fun n => ?_, ⟨Ordinal.one_add_omega0, ne_of_gt (lt_add_of_pos_left _ ?_)⟩, ?_⟩
  · have hω : (transfiniteKBOCore transfiniteKBOWitness).weight .wrap =
        Ordinal.toNatOrdinal Ordinal.omega0 := by
      simp [transfiniteKBOCore, transfiniteKBOWitness, tkWeight, repr_omega']
    have h1 : (n : NatOrdinal) < Ordinal.toNatOrdinal Ordinal.omega0 := by
      rw [← Ordinal.toNatOrdinal_natCast]
      exact Ordinal.toNatOrdinal.lt_iff_lt.2 (Ordinal.nat_lt_omega0 n)
    rw [show embed (.wrap .zero .zero : SchemaCore.FreeTerm ℕ) =
        .app .wrap [embed .zero, embed .zero] from rfl, wt_app, hω]
    exact lt_of_lt_of_le h1 (le_add_of_nonneg_right
      (evL_nonneg _ (fun _ => NatOrdinal.zero_le _) (fun _ => NatOrdinal.zero_le _) _ _ _))
  · rw [← Ordinal.toNatOrdinal_zero]
    exact Ordinal.toNatOrdinal.lt_iff_lt.2 zero_lt_one
  · exact gt_tower _ (transfiniteKBOCore_laws transfiniteKBOWitness_laws) (ι := .succ) rfl
      (by simp [transfiniteKBOCore, transfiniteKBOWitness, tkWeight]) rfl (.var 0) (.var 0) 1
      le_rfl

/-- Mutation: the variable weight of the witness set to `0`; admissibility fails. -/
theorem transfiniteKBO_mutation : ¬ transfiniteKBOLaws { transfiniteKBOWitness with w0 := 0 } :=
  fun h => lt_irrefl 0 h.w0_pos

/-! ## Part 2. The generalized KBO over a weakly monotone strictly simple algebra -/

/-- Native data of a generalized Knuth–Bendix order over symbol names `sigma` and a carrier `A`:
an interpretation of every symbol on argument lists, a strict and a weak carrier comparison, and a
strict precedence. -/
structure GKBOCore (sigma : Type) (A : Type) where
  /-- Interpretation of a symbol on the list of its argument values. -/
  interp : sigma → List A → A
  /-- Strict carrier comparison: `lt a b` means `a < b`. -/
  lt : A → A → Prop
  /-- Weak carrier comparison: `le a b` means `a ≤ b`. -/
  le : A → A → Prop
  /-- Strict precedence: `prec f g` means `f ≻ g`. -/
  prec : sigma → sigma → Prop

section GEval

variable {sigma nu A : Type}

mutual
/-- Value of a term in the algebra of `M` under the assignment `α`. -/
def aev (M : GKBOCore sigma A) (α : nu → A) : Term sigma nu → A
  | .var x => α x
  | .app f args => M.interp f (aevL M α args)
/-- Values of an argument list in the algebra of `M`. -/
def aevL (M : GKBOCore sigma A) (α : nu → A) : List (Term sigma nu) → List A
  | [] => []
  | a :: as => aev M α a :: aevL M α as
end

theorem aev_var (M : GKBOCore sigma A) (α : nu → A) (x : nu) :
    aev M α (.var x : Term sigma nu) = α x := rfl

theorem aev_app (M : GKBOCore sigma A) (α : nu → A) (f : sigma) (args : List (Term sigma nu)) :
    aev M α (.app f args) = M.interp f (aevL M α args) := rfl

theorem aevL_eq_map (M : GKBOCore sigma A) (α : nu → A) :
    ∀ l : List (Term sigma nu), aevL M α l = l.map (aev M α)
  | [] => rfl
  | a :: as => by
      show aev M α a :: aevL M α as = aev M α a :: as.map (aev M α)
      rw [aevL_eq_map M α as]

/-- Evaluation of an application `f (pre ++ a :: post)`. -/
theorem aev_app_ctx (M : GKBOCore sigma A) (α : nu → A) (f : sigma)
    (pre post : List (Term sigma nu)) (a : Term sigma nu) :
    aev M α (.app f (pre ++ a :: post)) =
      M.interp f (pre.map (aev M α) ++ aev M α a :: post.map (aev M α)) := by
  rw [aev_app, aevL_eq_map, List.map_append, List.map_cons]

/-- Evaluation commutes with substitution. -/
theorem aev_subst (M : GKBOCore sigma A) (α : nu → A) (σ : Subst sigma nu) :
    ∀ t : Term sigma nu, aev M α (Subst.apply σ t) = aev M (fun y => aev M α (σ y)) t := by
  intro t
  induction t using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
      rw [Subst.apply_app, aev_app, aev_app, Subst.applyList_eq_map, aevL_eq_map, aevL_eq_map,
        List.map_map]
      congr 1
      exact List.map_congr_left (fun a ha => ih a ha)

end GEval

section GRel

variable {sigma nu A : Type}

/-- The generalized Knuth–Bendix order (Yamada, Kusakari, Sakabe 2015, Science of Computer
Programming 111, Definition 3, with a strict precedence and lexicographic status; the generalized
KBO of Middeldorp and Zantema 1997, Theoretical Computer Science 175): `s ≻ t` if `s` is above `t`
in the algebra under every assignment (`alg`), or `s` is weakly above `t` under every assignment and
the roots are compared by precedence (`prec`) or are equal with lexicographically decreasing
arguments (`lex`). -/
inductive GGt (M : GKBOCore sigma A) : Term sigma nu → Term sigma nu → Prop
  | alg {s t : Term sigma nu} (h : ∀ α : nu → A, M.lt (aev M α t) (aev M α s)) : GGt M s t
  | prec {f g : sigma} {ss ts : List (Term sigma nu)}
      (hge : ∀ α : nu → A, M.le (aev M α (.app g ts)) (aev M α (.app f ss)))
      (hp : M.prec f g) : GGt M (.app f ss) (.app g ts)
  | lex {f : sigma} {ss ts : List (Term sigma nu)}
      (hge : ∀ α : nu → A, M.le (aev M α (.app f ts)) (aev M α (.app f ss)))
      (hlen : ss.length = ts.length) (i : ℕ) (hi : i < ss.length) (hti : i < ts.length)
      (hpre : ss.take i = ts.take i) (hgt : GGt M ss[i] ts[i]) : GGt M (.app f ss) (.app f ts)

/-- The reversed generalized KBO: `GKR M t s` says `t` is below `s`. -/
def GKR (M : GKBOCore sigma A) : Term sigma nu → Term sigma nu → Prop := fun t s => GGt M s t

/-- Admissibility of the generalized KBO (Yamada, Kusakari, Sakabe 2015, Science of Computer
Programming 111, Definition 3 and Theorem 7): an inhabited carrier with a well-founded strict order
and a compatible preorder containing it, every symbol interpretation weakly monotone and strictly
simple in each argument, and a well-founded strict precedence. -/
structure GKBOCore.Laws (M : GKBOCore sigma A) : Prop where
  inh : Nonempty A
  lt_wf : WellFounded M.lt
  lt_irrefl : ∀ a, ¬ M.lt a a
  lt_trans : ∀ a b c, M.lt a b → M.lt b c → M.lt a c
  le_refl : ∀ a, M.le a a
  le_trans : ∀ a b c, M.le a b → M.le b c → M.le a c
  lt_le : ∀ a b, M.lt a b → M.le a b
  lt_of_lt_le : ∀ a b c, M.lt a b → M.le b c → M.lt a c
  lt_of_le_lt : ∀ a b c, M.le a b → M.lt b c → M.lt a c
  mono : ∀ (f : sigma) (pre post : List A) (a b : A), M.le a b →
    M.le (M.interp f (pre ++ a :: post)) (M.interp f (pre ++ b :: post))
  simple : ∀ (f : sigma) (pre post : List A) (a : A), M.lt a (M.interp f (pre ++ a :: post))
  prec_irrefl : ∀ f, ¬ M.prec f f
  prec_trans : ∀ f g h, M.prec f g → M.prec g h → M.prec f h
  prec_wf : WellFounded (fun g f => M.prec f g)

variable (M : GKBOCore sigma A)

theorem ggt_ge (hL : M.Laws) {s t : Term sigma nu} (h : GGt M s t) :
    ∀ α : nu → A, M.le (aev M α t) (aev M α s) := by
  cases h with
  | alg h => exact fun α => hL.lt_le _ _ (h α)
  | prec hge _ => exact hge
  | lex hge _ _ _ _ _ _ => exact hge

/-- Strict simplicity at the term level: an argument is below its application. -/
theorem aev_arg_lt (hL : M.Laws) (α : nu → A) {f : sigma} {args : List (Term sigma nu)}
    {b : Term sigma nu} (hb : b ∈ args) : M.lt (aev M α b) (aev M α (.app f args)) := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hb
  rw [aev_app_ctx]
  exact hL.simple f _ _ _

/-- The subterm property of the generalized KBO. -/
theorem ggt_arg (hL : M.Laws) {f : sigma} {args : List (Term sigma nu)} {b : Term sigma nu}
    (hb : b ∈ args) : GGt M (.app f args) b :=
  GGt.alg fun α => aev_arg_lt M hL α hb

/-- Irreflexivity of the generalized KBO. -/
theorem ggt_irrefl (hL : M.Laws) : ∀ s : Term sigma nu, ¬ GGt M s s := by
  obtain ⟨a0⟩ := hL.inh
  intro s
  induction s using Term.rec' with
  | hvar x =>
      intro h
      cases h with
      | alg h => exact hL.lt_irrefl _ (h fun _ => a0)
  | happ f args ih =>
      intro h
      cases h with
      | alg h => exact hL.lt_irrefl _ (h fun _ => a0)
      | prec _ hp => exact hL.prec_irrefl f hp
      | lex _ _ i hi _ _ hgt => exact ih _ (List.getElem_mem hi) hgt

/-- Transitivity of the generalized KBO. -/
theorem ggt_trans (hL : M.Laws) {s t u : Term sigma nu} (hst : GGt M s t) (htu : GGt M t u) :
    GGt M s u := by
  induction hst generalizing u with
  | alg h1 =>
      have h2 := ggt_ge M hL htu
      exact GGt.alg fun α => hL.lt_of_le_lt _ _ _ (h2 α) (h1 α)
  | @prec f g ss ts hge1 hp1 =>
      cases htu with
      | alg h2 => exact GGt.alg fun α => hL.lt_of_lt_le _ _ _ (h2 α) (hge1 α)
      | @prec _ k _ us hge2 hp2 =>
          exact GGt.prec (fun α => hL.le_trans _ _ _ (hge2 α) (hge1 α))
            (hL.prec_trans _ _ _ hp1 hp2)
      | @lex _ _ us hge2 _ _ _ _ _ _ =>
          exact GGt.prec (fun α => hL.le_trans _ _ _ (hge2 α) (hge1 α)) hp1
  | @lex f ss ts hge1 hlen1 i hi hti hpre1 hgt1 ih =>
      cases htu with
      | alg h2 => exact GGt.alg fun α => hL.lt_of_lt_le _ _ _ (h2 α) (hge1 α)
      | @prec _ k _ us hge2 hp2 =>
          exact GGt.prec (fun α => hL.le_trans _ _ _ (hge2 α) (hge1 α)) hp2
      | @lex _ _ us hge2 hlen2 j hj htj hpre2 hgt2 =>
          have hge : ∀ α : nu → A, M.le (aev M α (.app f us)) (aev M α (.app f ss)) :=
            fun α => hL.le_trans _ _ _ (hge2 α) (hge1 α)
          rcases lt_trichotomy i j with hij | hij | hij
          · have hpre : ss.take i = us.take i := hpre1.trans (take_eq_take_of_le hij.le hpre2)
            have hei : ts[i] = us[i]'(by omega) := getElem_eq_of_take_eq hpre2 hij hti (by omega)
            exact GGt.lex hge (hlen1.trans hlen2) i hi (by omega) hpre
              (by rw [← hei]; exact hgt1)
          · subst hij
            exact GGt.lex hge (hlen1.trans hlen2) i hi htj (hpre1.trans hpre2) (ih hgt2)
          · have hpre : ss.take j = us.take j := (take_eq_take_of_le hij.le hpre1).trans hpre2
            have hej : ss[j]'(by omega) = ts[j] := getElem_eq_of_take_eq hpre1 hij (by omega) hj
            exact GGt.lex hge (hlen1.trans hlen2) j (by omega) htj hpre
              (by rw [hej]; exact hgt2)

/-- Closure of the generalized KBO under one-position argument contexts: weak monotonicity gives
the weak comparison and the lexicographic clause the strict one, whichever clause compared the two
arguments. -/
theorem ggt_ctx (hL : M.Laws) {s t : Term sigma nu} (h : GGt M s t) (f : sigma)
    (pre post : List (Term sigma nu)) :
    GGt M (.app f (pre ++ s :: post)) (.app f (pre ++ t :: post)) := by
  refine GGt.lex (fun α => ?_) (by simp) pre.length (by simp) (by simp) (by simp) ?_
  · rw [aev_app_ctx, aev_app_ctx]
    exact hL.mono f _ _ _ _ (ggt_ge M hL h α)
  · rw [getElem_length_cons, getElem_length_cons]
    exact h

/-- Closure of the generalized KBO under every substitution. -/
theorem ggt_subst (σ : Subst sigma nu) :
    ∀ {s t : Term sigma nu}, GGt M s t → GGt M (Subst.apply σ s) (Subst.apply σ t) := by
  intro s t h
  induction h with
  | alg h => exact GGt.alg fun α => by rw [aev_subst, aev_subst]; exact h _
  | @prec f g ss ts hge hp =>
      have h1 : ∀ α : nu → A, M.le (aev M α (Subst.apply σ (.app g ts)))
          (aev M α (Subst.apply σ (.app f ss))) := by
        intro α
        rw [aev_subst, aev_subst]
        exact hge _
      rw [Subst.apply_app, Subst.apply_app] at h1 ⊢
      exact GGt.prec h1 hp
  | @lex f ss ts hge hlen i hi hti hpre hgt ih =>
      have h1 : ∀ α : nu → A, M.le (aev M α (Subst.apply σ (.app f ts)))
          (aev M α (Subst.apply σ (.app f ss))) := by
        intro α
        rw [aev_subst, aev_subst]
        exact hge _
      rw [Subst.apply_app, Subst.apply_app] at h1 ⊢
      refine GGt.lex h1 (by rw [length_applyList, length_applyList, hlen]) i
        (by rw [length_applyList]; exact hi) (by rw [length_applyList]; exact hti)
        (by rw [take_applyList, take_applyList, hpre]) ?_
      rw [getElem_applyList, getElem_applyList]
      exact ih

/-- Accessibility of every term: the generalized KBO is well founded. The proof is a nested
induction on the value under one fixed assignment (the carrier order is well founded and every
clause is weakly decreasing), on the precedence, and on the lexicographic extension; strict
simplicity makes the arguments of a term accessible. -/
theorem ggt_acc (hL : M.Laws) : ∀ s : Term sigma nu, Acc (GKR M) s := by
  obtain ⟨a0⟩ := hL.inh
  suffices H : ∀ (a : A) (s : Term sigma nu), M.le (aev M (fun _ => a0) s) a →
      Acc (GKR M) s from
    fun s => H _ s (hL.le_refl _)
  intro a
  refine WellFounded.induction
    (C := fun a => ∀ s : Term sigma nu, M.le (aev M (fun _ => a0) s) a → Acc (GKR M) s)
    hL.lt_wf a ?_
  intro a IH
  have hlow : ∀ t : Term sigma nu, M.lt (aev M (fun _ => a0) t) a → Acc (GKR M) t :=
    fun t ht => IH _ ht t (hL.le_refl _)
  have hargs : ∀ (f : sigma) (args : List (Term sigma nu)),
      M.le (aev M (fun _ => a0) (.app f args)) a → ∀ b ∈ args, Acc (GKR M) b :=
    fun f args h b hb => hlow b (hL.lt_of_lt_le _ _ _ (aev_arg_lt M hL _ hb) h)
  have node : ∀ (f : sigma) (args : List (Term sigma nu)),
      M.le (aev M (fun _ => a0) (.app f args)) a → Acc (GKR M) (.app f args) := by
    intro f
    refine WellFounded.induction
      (C := fun f => ∀ args : List (Term sigma nu),
        M.le (aev M (fun _ => a0) (.app f args)) a → Acc (GKR M) (.app f args))
      hL.prec_wf f ?_
    intro f IHf args hle
    have hA : Acc (LexA (GKR M)) args := acc_lexA (GKR M) args.length args rfl (hargs f args hle)
    revert hle
    induction hA with
    | intro args _ IHl =>
        intro hle
        refine Acc.intro _ (fun u hu => ?_)
        have hu' : GGt M (.app f args) u := hu
        cases hu' with
        | alg h => exact hlow u (hL.lt_of_lt_le _ _ _ (h fun _ => a0) hle)
        | @prec _ g _ us hge hp => exact IHf g hp us (hL.le_trans _ _ _ (hge fun _ => a0) hle)
        | @lex _ _ us hge hlen i hi hti hpre hgt =>
            have hle' : M.le (aev M (fun _ => a0) (.app f us)) a :=
              hL.le_trans _ _ _ (hge fun _ => a0) hle
            exact IHl us ⟨⟨hlen.symm, i, hti, hi, hpre.symm, hgt⟩, hargs f us hle'⟩ hle'
  intro s hs
  cases s with
  | var x =>
      refine Acc.intro _ (fun t ht => ?_)
      have ht' : GGt M (.var x) t := ht
      cases ht' with
      | alg h => exact hlow t (hL.lt_of_lt_le _ _ _ (h fun _ => a0) hs)
  | app f args => exact node f args hs

/-- The generalized KBO is well founded. -/
theorem ggt_wellFounded (hL : M.Laws) :
    WellFounded (GKR M : Term sigma nu → Term sigma nu → Prop) :=
  ⟨ggt_acc M hL⟩

end GRel

section GRO

variable {sigma A : Type}

/-- The reduction-order properties of a generalized KBO with variables in `nu`: irreflexive,
transitive, well founded, closed under argument contexts and under all substitutions. -/
def GKBOReductionOrder (nu : Type) (M : GKBOCore sigma A) : Prop :=
  (∀ s : Term sigma nu, ¬ GGt M s s) ∧
  (∀ s t u : Term sigma nu, GGt M s t → GGt M t u → GGt M s u) ∧
  WellFounded (GKR M : Term sigma nu → Term sigma nu → Prop) ∧
  (∀ s t : Term sigma nu, GGt M s t → ∀ (f : sigma) (pre post : List (Term sigma nu)),
    GGt M (.app f (pre ++ s :: post)) (.app f (pre ++ t :: post))) ∧
  (∀ (σ : Subst sigma nu) (s t : Term sigma nu), GGt M s t →
    GGt M (Subst.apply σ s) (Subst.apply σ t))

/-- The generalized KBO over an arbitrary signature is a reduction order under its admissibility
laws; the signature hypothesis is a well-founded precedence (automatic for a finite signature). -/
theorem gkbo_isReductionOrder (nu : Type) (M : GKBOCore sigma A) (hL : M.Laws) :
    GKBOReductionOrder nu M :=
  ⟨ggt_irrefl M hL, fun _ _ _ => ggt_trans M hL, ggt_wellFounded M hL,
    fun _ _ h f pre post => ggt_ctx M hL h f pre post, fun σ _ _ h => ggt_subst M σ h⟩

/-- Every full rewrite step generated by rules oriented by a generalized KBO is itself oriented
by that generalized KBO. This is the arbitrary-signature, arbitrary-TRS method adapter. -/
theorem gkbo_of_step (M : GKBOCore sigma A) {nu : Type}
    {R : OperatorKO7.Meta.Rewriting.TRS sigma nu}
    (hL : M.Laws) (hR : ∀ rule ∈ R, GGt M rule.lhs rule.rhs) {s t : Term sigma nu}
    (h : OperatorKO7.Meta.Rewriting.Step R s t) : GGt M s t := by
  induction h with
  | root hroot =>
      obtain ⟨rule, hrule, θ, rfl, rfl⟩ := hroot
      exact ggt_subst M θ (hR rule hrule)
  | arg f pre post _ ih => exact ggt_ctx M hL ih f pre post

/-- Generalized-KBO termination for every first-order TRS over every signature: admissibility of
the algebra and orientation of all rules imply well-foundedness of full rewriting. -/
theorem gkbo_step_wf (M : GKBOCore sigma A) (hL : M.Laws) {nu : Type}
    {R : OperatorKO7.Meta.Rewriting.TRS sigma nu}
    (hR : ∀ rule ∈ R, GGt M rule.lhs rule.rhs) :
    WellFounded (fun u t : Term sigma nu => OperatorKO7.Meta.Rewriting.Step R t u) :=
  Subrelation.wf (fun {_ _} h => gkbo_of_step M hL hR h) (ggt_wellFounded M hL)

end GRO

/-! ### The schema signature as a generalized-KBO algebra -/

theorem append_cons_len_one {α : Type} {pre post : List α} {a : α}
    (h : (pre ++ a :: post).length = 1) : pre = [] ∧ post = [] := by
  rcases pre with _ | ⟨p, ps⟩ <;> rcases post with _ | ⟨q, qs⟩ <;> simp_all

theorem append_cons_len_two {α : Type} {pre post : List α} {a : α}
    (h : (pre ++ a :: post).length = 2) :
    (pre = [] ∧ ∃ c, post = [c]) ∨ (∃ c, pre = [c] ∧ post = []) := by
  rcases pre with _ | ⟨p, _ | ⟨p', ps⟩⟩ <;> rcases post with _ | ⟨q, _ | ⟨q', qs⟩⟩ <;> simp_all

theorem append_cons_len_three {α : Type} {pre post : List α} {a : α}
    (h : (pre ++ a :: post).length = 3) :
    (pre = [] ∧ ∃ c d, post = [c, d]) ∨ (∃ c d, pre = [c] ∧ post = [d]) ∨
      (∃ c d, pre = [c, d] ∧ post = []) := by
  rcases pre with _ | ⟨p, _ | ⟨p', _ | ⟨p'', ps⟩⟩⟩ <;>
    rcases post with _ | ⟨q, _ | ⟨q', _ | ⟨q'', qs⟩⟩⟩ <;> simp_all

/-- The schema signature interpreted on argument lists: the constructor functions at their ranked
arities, and the argument sum plus one at every other arity (the adapter from the ranked algebra to
the unranked term syntax). -/
def schemaListInterp (z : ℕ) (sc : ℕ → ℕ) (wr : ℕ → ℕ → ℕ) (rc : ℕ → ℕ → ℕ → ℕ) :
    SchemaSym → List ℕ → ℕ
  | .zero, [] => z
  | .succ, [a] => sc a
  | .wrap, [a, b] => wr a b
  | .recur, [a, b, c] => rc a b c
  | _, l => l.sum + 1

theorem schemaListInterp_off (z : ℕ) (sc : ℕ → ℕ) (wr : ℕ → ℕ → ℕ) (rc : ℕ → ℕ → ℕ → ℕ)
    (f : SchemaSym) (l : List ℕ) (h : l.length ≠ schemaAr f) :
    schemaListInterp z sc wr rc f l = l.sum + 1 := by
  cases f <;> rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, l⟩⟩⟩⟩ <;>
    first | rfl | exact absurd rfl h

theorem schemaListInterp_mono {z : ℕ} {sc : ℕ → ℕ} {wr : ℕ → ℕ → ℕ} {rc : ℕ → ℕ → ℕ → ℕ}
    (hs : ∀ {a b}, a ≤ b → sc a ≤ sc b)
    (hw1 : ∀ {a b} c, a ≤ b → wr a c ≤ wr b c) (hw2 : ∀ c {a b}, a ≤ b → wr c a ≤ wr c b)
    (hr1 : ∀ {a b} c d, a ≤ b → rc a c d ≤ rc b c d)
    (hr2 : ∀ c {a b} d, a ≤ b → rc c a d ≤ rc c b d)
    (hr3 : ∀ c d {a b}, a ≤ b → rc c d a ≤ rc c d b)
    (f : SchemaSym) (pre post : List ℕ) {a b : ℕ} (hab : a ≤ b) :
    schemaListInterp z sc wr rc f (pre ++ a :: post) ≤
      schemaListInterp z sc wr rc f (pre ++ b :: post) := by
  by_cases hl : (pre ++ a :: post).length = schemaAr f
  · cases f with
    | zero => simp [schemaAr] at hl
    | succ =>
        obtain ⟨rfl, rfl⟩ := append_cons_len_one hl
        exact hs hab
    | wrap =>
        rcases append_cons_len_two hl with ⟨rfl, c, rfl⟩ | ⟨c, rfl, rfl⟩
        · exact hw1 c hab
        · exact hw2 c hab
    | recur =>
        rcases append_cons_len_three hl with ⟨rfl, c, d, rfl⟩ | ⟨c, d, rfl, rfl⟩ |
          ⟨c, d, rfl, rfl⟩
        · exact hr1 c d hab
        · exact hr2 c d hab
        · exact hr3 c d hab
  · have hl' : (pre ++ b :: post).length ≠ schemaAr f := by simpa using hl
    rw [schemaListInterp_off z sc wr rc f _ hl, schemaListInterp_off z sc wr rc f _ hl']
    simp only [List.sum_append, List.sum_cons]
    omega

theorem schemaListInterp_simple {z : ℕ} {sc : ℕ → ℕ} {wr : ℕ → ℕ → ℕ} {rc : ℕ → ℕ → ℕ → ℕ}
    (hs : ∀ a, a < sc a) (hw : ∀ a b, a < wr a b ∧ b < wr a b)
    (hr : ∀ a b c, a < rc a b c ∧ b < rc a b c ∧ c < rc a b c)
    (f : SchemaSym) (pre post : List ℕ) (a : ℕ) :
    a < schemaListInterp z sc wr rc f (pre ++ a :: post) := by
  by_cases hl : (pre ++ a :: post).length = schemaAr f
  · cases f with
    | zero => simp [schemaAr] at hl
    | succ =>
        obtain ⟨rfl, rfl⟩ := append_cons_len_one hl
        exact hs a
    | wrap =>
        rcases append_cons_len_two hl with ⟨rfl, c, rfl⟩ | ⟨c, rfl, rfl⟩
        · exact (hw a c).1
        · exact (hw c a).2
    | recur =>
        rcases append_cons_len_three hl with ⟨rfl, c, d, rfl⟩ | ⟨c, d, rfl, rfl⟩ |
          ⟨c, d, rfl, rfl⟩
        · exact (hr a c d).1
        · exact (hr c a d).2.1
        · exact (hr c d a).2.2
  · rw [schemaListInterp_off z sc wr rc f _ hl]
    simp only [List.sum_append, List.sum_cons]
    omega

/-- The free duplicating rule `recur b s (succ n) → wrap s (recur b s n)` over the schema
signature, with the variables `b, s, n` named `0, 1, 2`. -/
def dupLhs : Term SchemaSym ℕ := embed (.recur (.var 0) (.var 1) (.succ (.var 2)))

def dupRhs : Term SchemaSym ℕ := embed (.wrap (.var 1) (.recur (.var 0) (.var 1) (.var 2)))

/-- The zero rule `recur b s zero → b` over the schema signature. -/
def zeroLhs : Term SchemaSym ℕ := embed (.recur (.var 0) (.var 1) .zero)

def zeroRhs : Term SchemaSym ℕ := embed (.var 0)

/-- The assignment or substitution `0 ↦ b, 1 ↦ s`, every other variable `↦ n`. -/
def triSubst {X : Type} (b s n : X) : ℕ → X
  | 0 => b
  | 1 => s
  | _ => n

/-- Substitution commutes with the embedding of the free schema. -/
theorem subst_embed (τ : ℕ → SchemaCore.FreeTerm ℕ) :
    ∀ t : SchemaCore.FreeTerm ℕ,
      Subst.apply (fun x => embed (τ x)) (embed t) = embed (SchemaCore.FreeTerm.subst τ t)
  | .var _ => rfl
  | .zero => rfl
  | .succ t => by
      show Subst.apply _ (Term.app SchemaSym.succ [embed t]) =
        Term.app SchemaSym.succ [embed (SchemaCore.FreeTerm.subst τ t)]
      rw [Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil, subst_embed τ t]
  | .wrap s t => by
      show Subst.apply _ (Term.app SchemaSym.wrap [embed s, embed t]) =
        Term.app SchemaSym.wrap
          [embed (SchemaCore.FreeTerm.subst τ s), embed (SchemaCore.FreeTerm.subst τ t)]
      rw [Subst.apply_app, Subst.applyList_cons, Subst.applyList_cons, Subst.applyList_nil,
        subst_embed τ s, subst_embed τ t]
  | .recur b s n => by
      show Subst.apply _ (Term.app SchemaSym.recur [embed b, embed s, embed n]) =
        Term.app SchemaSym.recur [embed (SchemaCore.FreeTerm.subst τ b),
          embed (SchemaCore.FreeTerm.subst τ s), embed (SchemaCore.FreeTerm.subst τ n)]
      rw [Subst.apply_app, Subst.applyList_cons, Subst.applyList_cons, Subst.applyList_cons,
        Subst.applyList_nil, subst_embed τ b, subst_embed τ s, subst_embed τ n]

/-- A relation closed under argument contexts is closed under the embedded one-hole contexts of
the free schema. -/
theorem embed_plug_ctx (R : Term SchemaSym ℕ → Term SchemaSym ℕ → Prop)
    (hctx : ∀ s t, R s t → ∀ (f : SchemaSym) (pre post : List (Term SchemaSym ℕ)),
      R (.app f (pre ++ s :: post)) (.app f (pre ++ t :: post)))
    {l r : SchemaCore.FreeTerm ℕ} (h : R (embed l) (embed r)) :
    ∀ C : SchemaCore.FreeContext ℕ, R (embed (C.plug l)) (embed (C.plug r))
  | .hole => h
  | .succ C => hctx _ _ (embed_plug_ctx R hctx h C) .succ [] []
  | .wrapLeft C t => hctx _ _ (embed_plug_ctx R hctx h C) .wrap [] [embed t]
  | .wrapRight s C => hctx _ _ (embed_plug_ctx R hctx h C) .wrap [embed s] []
  | .recurBase C s n => hctx _ _ (embed_plug_ctx R hctx h C) .recur [] [embed s, embed n]
  | .recurStep b C n => hctx _ _ (embed_plug_ctx R hctx h C) .recur [embed b] [embed n]
  | .recurCounter b s C => hctx _ _ (embed_plug_ctx R hctx h C) .recur [embed b, embed s] []

/-- The adapter from an order on first-order terms to termination of the free schema: a relation
that is well founded, closed under argument contexts and substitutions, and orients the two open
rules, orients every step of `SchemaCore.ContextStep`, so the contextual free recursor terminates. -/
theorem schema_termination_of_order (R : Term SchemaSym ℕ → Term SchemaSym ℕ → Prop)
    (hwf : WellFounded (fun t s => R s t))
    (hctx : ∀ s t, R s t → ∀ (f : SchemaSym) (pre post : List (Term SchemaSym ℕ)),
      R (.app f (pre ++ s :: post)) (.app f (pre ++ t :: post)))
    (hsub : ∀ (σ : Subst SchemaSym ℕ) (s t : Term SchemaSym ℕ), R s t →
      R (Subst.apply σ s) (Subst.apply σ t))
    (hdup : R dupLhs dupRhs) (hzero : R zeroLhs zeroRhs) :
    WellFounded (fun u t : SchemaCore.FreeTerm ℕ => SchemaCore.ContextStep t u) := by
  have hroot : ∀ t u : SchemaCore.FreeTerm ℕ, SchemaCore.RootStep t u →
      R (embed t) (embed u) := by
    intro t u h
    cases h with
    | recurZero _ s =>
        have := hsub (fun x => embed (triSubst u s u x)) _ _ hzero
        rwa [zeroLhs, zeroRhs, subst_embed, subst_embed] at this
    | recurSucc b s n =>
        have := hsub (fun x => embed (triSubst b s n x)) _ _ hdup
        rwa [dupLhs, dupRhs, subst_embed, subst_embed] at this
  apply Subrelation.wf (r := InvImage (fun t s => R s t) embed)
  · intro u t h
    cases h with
    | lift C hst => exact embed_plug_ctx R hctx (hroot _ _ hst) C
  · exact InvImage.wf embed hwf

/-! ## Row `generalizedKBO` -/

/-- Native data of the generalized Knuth–Bendix order on the schema signature over the natural
numbers: the interpretation of each constructor and a precedence. -/
structure generalizedKBOData where
  /-- Interpretation of `zero`. -/
  zeroI : ℕ
  /-- Interpretation of `succ`. -/
  succI : ℕ → ℕ
  /-- Interpretation of `wrap`. -/
  wrapI : ℕ → ℕ → ℕ
  /-- Interpretation of `recur`. -/
  recurI : ℕ → ℕ → ℕ → ℕ
  /-- Strict precedence. -/
  prec : SchemaSym → SchemaSym → Prop

/-- Admissibility of the generalized Knuth–Bendix order: Yamada, Kusakari, Sakabe 2015 (Science of
Computer Programming 111), Definition 3 with the hypotheses of Theorem 7, over the well-founded
algebra `(ℕ, >, ≥)` (the generalized KBO of Middeldorp and Zantema 1997, Theoretical Computer
Science 175): every constructor interpretation is weakly monotone and strictly simple in each
argument, and the precedence is a strict order (well founded on the finite signature). -/
structure generalizedKBOLaws (D : generalizedKBOData) : Prop where
  succ_mono : ∀ {a b}, a ≤ b → D.succI a ≤ D.succI b
  wrap_mono_left : ∀ {a b} c, a ≤ b → D.wrapI a c ≤ D.wrapI b c
  wrap_mono_right : ∀ c {a b}, a ≤ b → D.wrapI c a ≤ D.wrapI c b
  recur_mono_1 : ∀ {a b} c d, a ≤ b → D.recurI a c d ≤ D.recurI b c d
  recur_mono_2 : ∀ c {a b} d, a ≤ b → D.recurI c a d ≤ D.recurI c b d
  recur_mono_3 : ∀ c d {a b}, a ≤ b → D.recurI c d a ≤ D.recurI c d b
  succ_simple : ∀ a, a < D.succI a
  wrap_simple : ∀ a b, a < D.wrapI a b ∧ b < D.wrapI a b
  recur_simple : ∀ a b c, a < D.recurI a b c ∧ b < D.recurI a b c ∧ c < D.recurI a b c
  prec_irrefl : ∀ f, ¬ D.prec f f
  prec_trans : ∀ f g h, D.prec f g → D.prec g h → D.prec f h

/-- The generalized KBO of the data: the ranked constructor functions through
`schemaListInterp`, the natural order, and the precedence. -/
def generalizedKBOCore (D : generalizedKBOData) : GKBOCore SchemaSym ℕ where
  interp := schemaListInterp D.zeroI D.succI D.wrapI D.recurI
  lt := (· < ·)
  le := (· ≤ ·)
  prec := D.prec

theorem generalizedKBOCore_laws {D : generalizedKBOData} (h : generalizedKBOLaws D) :
    (generalizedKBOCore D).Laws where
  inh := ⟨0⟩
  lt_wf := wellFounded_lt
  lt_irrefl := lt_irrefl
  lt_trans _ _ _ := lt_trans
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  lt_le _ _ := le_of_lt
  lt_of_lt_le _ _ _ := lt_of_lt_of_le
  lt_of_le_lt _ _ _ := lt_of_le_of_lt
  mono f pre post _ _ hab := schemaListInterp_mono h.succ_mono h.wrap_mono_left
    h.wrap_mono_right h.recur_mono_1 h.recur_mono_2 h.recur_mono_3 f pre post hab
  simple f pre post a :=
    schemaListInterp_simple h.succ_simple h.wrap_simple h.recur_simple f pre post a
  prec_irrefl := h.prec_irrefl
  prec_trans := h.prec_trans
  prec_wf := schema_prec_wf D.prec h.prec_irrefl h.prec_trans

/-- The generalized KBO of admissible data is a reduction order on first-order terms over the
schema signature (for an arbitrary signature, `gkbo_isReductionOrder`). -/
theorem generalizedKBO_order (D : generalizedKBOData) (h : generalizedKBOLaws D) (ν : Type) :
    GKBOReductionOrder ν (generalizedKBOCore D) :=
  gkbo_isReductionOrder ν _ (generalizedKBOCore_laws h)

/-- The two free rules compared by the generalized KBO: the duplicating rule is oriented exactly
when the algebra orients it strictly, or weakly with `recur ≻ wrap`. -/
theorem gAccepts_dup_iff (D : generalizedKBOData) :
    GGt (generalizedKBOCore D) dupLhs dupRhs ↔
      (∀ b s n, D.wrapI s (D.recurI b s n) < D.recurI b s (D.succI n)) ∨
        ((∀ b s n, D.wrapI s (D.recurI b s n) ≤ D.recurI b s (D.succI n)) ∧
          D.prec .recur .wrap) := by
  constructor
  · intro h
    change GGt (generalizedKBOCore D)
      (.app .recur [.var 0, .var 1, .app .succ [.var 2]])
      (.app .wrap [.var 1, .app .recur [.var 0, .var 1, .var 2]]) at h
    cases h with
    | alg h => exact Or.inl fun b s n => h (triSubst b s n)
    | prec hge hp => exact Or.inr ⟨fun b s n => hge (triSubst b s n), hp⟩
  · rintro (h | ⟨h, hp⟩)
    · exact GGt.alg fun α => h (α 0) (α 1) (α 2)
    · show GGt (generalizedKBOCore D)
        (.app .recur [.var 0, .var 1, .app .succ [.var 2]])
        (.app .wrap [.var 1, .app .recur [.var 0, .var 1, .var 2]])
      exact GGt.prec (fun α => h (α 0) (α 1) (α 2)) hp

/-- The zero rule is oriented exactly when the algebra orients it strictly. -/
theorem gAccepts_zero_iff (D : generalizedKBOData) :
    GGt (generalizedKBOCore D) zeroLhs zeroRhs ↔ ∀ b s, b < D.recurI b s D.zeroI := by
  constructor
  · intro h
    change GGt (generalizedKBOCore D) (.app .recur [.var 0, .var 1, .app .zero []]) (.var 0) at h
    cases h with
    | alg h => exact fun b s => h (triSubst b s b)
  · intro h
    exact GGt.alg fun α => h (α 0) (α 1)

/-- Acceptance of the free two-rule system by the generalized KBO: both open rules are oriented
(the instances and the contexts follow by `ggt_subst` and `ggt_ctx`). -/
def generalizedKBOAccepts (D : generalizedKBOData) : Prop :=
  GGt (generalizedKBOCore D) dupLhs dupRhs ∧ GGt (generalizedKBOCore D) zeroLhs zeroRhs

/-- Verdict: escape. The generalized KBO orients both free rules, and its soundness theorem gives
termination of the contextual free recursor. -/
def generalizedKBOResult (D : generalizedKBOData) : Prop :=
  generalizedKBOAccepts D ∧
    WellFounded (fun u t : SchemaCore.FreeTerm ℕ => SchemaCore.ContextStep t u)

/-- Soundness of the generalized KBO on the free schema: acceptance by admissible data proves
termination of `SchemaCore.ContextStep`. -/
theorem generalizedKBO_sound : ∀ D, generalizedKBOLaws D → generalizedKBOAccepts D →
    WellFounded (fun u t : SchemaCore.FreeTerm ℕ => SchemaCore.ContextStep t u) := by
  intro D hD hacc
  have hL := generalizedKBOCore_laws hD
  exact schema_termination_of_order (GGt (generalizedKBOCore D)) (ggt_wellFounded _ hL)
    (fun _ _ h f pre post => ggt_ctx _ hL h f pre post) (fun σ _ _ h => ggt_subst _ σ h)
    hacc.1 hacc.2

/-- The coupled algebra of the P2.4 region at `α = 1, β = 2`: `zero = 0`, `succ n = n + 1`,
`wrap s y = s + y + 1`, `recur b s n = (n + 1)(s + b + 2)`, with `recur ≻ wrap ≻ succ ≻ zero`. -/
def generalizedKBOWitness : generalizedKBOData where
  zeroI := 0
  succI := PolynomialRegion.successorEval
  wrapI := PolynomialRegion.wrapperEval
  recurI := PolynomialRegion.recursorEval 1 2
  prec := rankPrec schemaRank

theorem generalizedKBOWitness_laws : generalizedKBOLaws generalizedKBOWitness where
  succ_mono := fun {a b} hab => by
    simp only [generalizedKBOWitness, PolynomialRegion.successorEval]
    omega
  wrap_mono_left := fun {a b} c hab => by
    simp only [generalizedKBOWitness, PolynomialRegion.wrapperEval]
    omega
  wrap_mono_right := fun c {a b} hab => by
    simp only [generalizedKBOWitness, PolynomialRegion.wrapperEval]
    omega
  recur_mono_1 := fun {a b} c d hab => by
    simp only [generalizedKBOWitness, PolynomialRegion.recursorEval]
    exact Nat.mul_le_mul_left _ (by omega)
  recur_mono_2 := fun c {a b} d hab => by
    simp only [generalizedKBOWitness, PolynomialRegion.recursorEval]
    exact Nat.mul_le_mul_left _ (by omega)
  recur_mono_3 := fun c d {a b} hab => by
    simp only [generalizedKBOWitness, PolynomialRegion.recursorEval]
    exact Nat.mul_le_mul_right _ (by omega)
  succ_simple a := by
    simp only [generalizedKBOWitness, PolynomialRegion.successorEval]
    omega
  wrap_simple a b := by
    simp only [generalizedKBOWitness, PolynomialRegion.wrapperEval]
    omega
  recur_simple a b c := by
    show a < (c + 1) * (1 * b + a + 2) ∧ b < (c + 1) * (1 * b + a + 2) ∧
      c < (c + 1) * (1 * b + a + 2)
    have e : (c + 1) * (1 * b + a + 2) = c * (b + a + 2) + (b + a + 2) := by ring
    have hc : c ≤ c * (b + a + 2) := Nat.le_mul_of_pos_right c (by omega)
    rw [e]
    generalize c * (b + a + 2) = X at hc ⊢
    omega
  prec_irrefl := rankPrec_irrefl _
  prec_trans := rankPrec_trans _

/-- The witness orients both free rules through the algebra clause, by the P2.4 region theorems
`orientsSuccessor_of_region` and `orientsZero_of_region`. -/
theorem generalizedKBOWitness_accepts : generalizedKBOAccepts generalizedKBOWitness := by
  refine ⟨(gAccepts_dup_iff _).2 (Or.inl fun b s n => ?_), (gAccepts_zero_iff _).2 fun b s => ?_⟩
  · exact PolynomialRegion.orientsSuccessor_of_region (α := 1) (β := 2) le_rfl le_rfl b s n
  · exact PolynomialRegion.orientsZero_of_region (α := 1) (β := 2) le_rfl le_rfl b s

theorem generalizedKBOWitness_result : generalizedKBOResult generalizedKBOWitness :=
  ⟨generalizedKBOWitness_accepts,
    generalizedKBO_sound _ generalizedKBOWitness_laws generalizedKBOWitness_accepts⟩

/-- Exact method identity for the generalized-KBO row. `GGt` is a reduction order for every
admissible `GKBOCore`, and its rule-orientation condition proves termination of every first-order
TRS, independently of the free recursor witness used by the catalogue row. -/
theorem generalizedKBO_methodIdentity :
    (∀ {σ A ν : Type} (M : GKBOCore σ A), M.Laws →
      (R : OperatorKO7.Meta.Rewriting.TRS σ ν) →
      (∀ rule ∈ R, GGt M rule.lhs rule.rhs) →
        WellFounded (fun u t : Term σ ν => OperatorKO7.Meta.Rewriting.Step R t u)) ∧
      generalizedKBOLaws generalizedKBOWitness ∧
      generalizedKBOAccepts generalizedKBOWitness := by
  refine ⟨?_, generalizedKBOWitness_laws, generalizedKBOWitness_accepts⟩
  intro σ A ν M hL R hR
  exact gkbo_step_wf M hL hR

/-- Rank of the old comparator's quasi-precedence (`base, succ ↦ 0`, `wrap ↦ 1`, `recur ↦ 2`). -/
def gAddRank : SchemaSym → ℕ
  | .zero => 0
  | .succ => 0
  | .wrap => 1
  | .recur => 2

/-- The additive algebra of the old comparator's witness `generalizedNatKBOWitness` (every symbol
and every variable weighs `1`), with its quasi-precedence made strict. -/
def generalizedKBOAdditive : generalizedKBOData where
  zeroI := 1
  succI a := a + 1
  wrapI a b := a + b + 1
  recurI a b c := a + b + c + 1
  prec := rankPrec gAddRank

theorem generalizedKBOAdditive_laws : generalizedKBOLaws generalizedKBOAdditive where
  succ_mono hab := by simp only [generalizedKBOAdditive]; omega
  wrap_mono_left _ hab := by simp only [generalizedKBOAdditive]; omega
  wrap_mono_right _ hab := by simp only [generalizedKBOAdditive]; omega
  recur_mono_1 _ _ hab := by simp only [generalizedKBOAdditive]; omega
  recur_mono_2 _ _ hab := by simp only [generalizedKBOAdditive]; omega
  recur_mono_3 _ _ hab := by simp only [generalizedKBOAdditive]; omega
  succ_simple _ := by simp only [generalizedKBOAdditive]; omega
  wrap_simple _ _ := by simp only [generalizedKBOAdditive]; omega
  recur_simple _ _ _ := by simp only [generalizedKBOAdditive]; omega
  prec_irrefl := rankPrec_irrefl _
  prec_trans := rankPrec_trans _

/-- Controls. R12 regression: the old comparator `GeneralizedKBOGt generalizedNatKBOWitness`
relates `wrap base base` to `succ (succ base)` and loses the comparison under the unary context
`succ`, while the generalized KBO with the same weights keeps it; a weight tie resolved by the
precedence and a weight tie resolved by the lexicographic arguments in the coupled witness; and the
counter/payload coupling of the witness recursor (not additive in the payload and counter). -/
theorem generalizedKBOWitness_feature :
    (PathOrderNativeSemantics.GeneralizedKBOGt PathOrderNativeSemantics.generalizedNatKBOWitness
        (.wrap .base .base) (.succ (.succ .base)) ∧
      ¬ PathOrderNativeSemantics.GeneralizedKBOGt PathOrderNativeSemantics.generalizedNatKBOWitness
        (.succ (.wrap .base .base)) (.succ (.succ (.succ .base)))) ∧
    (GGt (generalizedKBOCore generalizedKBOAdditive)
        (embed (.wrap .zero .zero : SchemaCore.FreeTerm ℕ)) (embed (.succ (.succ .zero))) ∧
      GGt (generalizedKBOCore generalizedKBOAdditive)
        (embed (.succ (.wrap .zero .zero) : SchemaCore.FreeTerm ℕ))
        (embed (.succ (.succ (.succ .zero))))) ∧
    GGt (generalizedKBOCore generalizedKBOWitness)
      (embed (.wrap .zero .zero : SchemaCore.FreeTerm ℕ)) (embed (.succ .zero)) ∧
    GGt (generalizedKBOCore generalizedKBOWitness)
      (embed (.recur (.succ .zero) .zero .zero : SchemaCore.FreeTerm ℕ))
      (embed (.recur .zero (.succ .zero) .zero)) ∧
    generalizedKBOWitness.recurI 0 1 1 + generalizedKBOWitness.recurI 0 0 0 ≠
      generalizedKBOWitness.recurI 0 1 0 + generalizedKBOWitness.recurI 0 0 1 := by
  have hA := generalizedKBOCore_laws generalizedKBOAdditive_laws
  have hadd : GGt (generalizedKBOCore generalizedKBOAdditive)
      (embed (.wrap .zero .zero : SchemaCore.FreeTerm ℕ)) (embed (.succ (.succ .zero))) :=
    GGt.prec (fun _ => le_refl _) (show gAddRank .succ < gAddRank .wrap by decide)
  refine ⟨⟨?_, ?_⟩, ⟨hadd, ggt_ctx _ hA hadd .succ [] []⟩, ?_, ?_, by decide⟩
  · constructor
    · intro v
      cases v <;> decide
    · exact Or.inr ⟨rfl, by decide⟩
  · rintro ⟨_, hw | ⟨_, hp⟩⟩
    · norm_num [PathOrderNativeSemantics.generalizedKBOWeight,
        PathOrderNativeSemantics.generalizedNatKBOWitness] at hw
    · norm_num [PathOrderNativeSemantics.generalizedRootRank,
        PathOrderNativeSemantics.generalizedNatKBOWitness, PathOrderNativeSemantics.methodRoot] at hp
  · exact GGt.prec (fun _ => le_refl _) (show schemaRank .succ < schemaRank .wrap by decide)
  · exact GGt.lex (fun _ => le_refl _) rfl 0 (by decide) (by decide) rfl
      (GGt.alg fun _ => Nat.zero_lt_one)

/-- Mutation: the witness recursor replaced by the uncoupled `b + s + n + 2`; the duplicating rule
is then neither strictly nor weakly oriented at `b = 0, s = 1, n = 0`, so the result fails. -/
theorem generalizedKBO_mutation :
    ¬ generalizedKBOResult { generalizedKBOWitness with recurI := fun b s n => b + s + n + 2 } := by
  rintro ⟨⟨hdup, _⟩, _⟩
  rcases (gAccepts_dup_iff _).1 hdup with h | ⟨h, _⟩
  · exact absurd (h 0 1 0) (by decide)
  · exact absurd (h 0 1 0) (by decide)

/-! ## Row `polynomialKBO` -/

section PolyKBO

open OperatorKO7.Methods.OrientationClosure.PolynomialOrientationDecision (WMono RMono wEval rEval)

theorem wEval_mono' (W : List WMono) {s s' y y' : ℕ} (hs : s ≤ s') (hy : y ≤ y') :
    wEval W s y ≤ wEval W s' y' := by
  induction W with
  | nil => simp [wEval]
  | cons m W ih =>
      simp only [wEval]
      exact Nat.add_le_add (by gcongr) ih

/-- Native data of the polynomial Knuth–Bendix order on the schema signature: a natural-coefficient
polynomial interpretation (`zero ↦ z`, `succ n ↦ slope * n + a`, the wrapper and recursor monomial
tables of P3.5) and a precedence. -/
structure polynomialKBOData where
  /-- Interpretation of `zero`. -/
  z : ℕ
  /-- Successor slope. -/
  slope : ℕ
  /-- Successor offset. -/
  a : ℕ
  /-- Wrapper monomials `coeff * s ^ sDeg * y ^ yDeg`. -/
  W : List WMono
  /-- Recursor monomials `coeff * b ^ bDeg * s ^ sDeg * n ^ nDeg`. -/
  R : List RMono
  /-- Strict precedence. -/
  prec : SchemaSym → SchemaSym → Prop

/-- Admissibility of the polynomial Knuth–Bendix order: the generalized KBO of Yamada, Kusakari,
Sakabe 2015 (Science of Computer Programming 111), Definition 3 with the hypotheses of Theorem 7,
whose weakly monotone algebra is a natural-coefficient polynomial interpretation (monotone by
construction): positive successor slope and offset, the wrapper and recursor polynomials strictly
simple in each argument, and a strict precedence. -/
structure polynomialKBOLaws (P : polynomialKBOData) : Prop where
  slope_pos : 1 ≤ P.slope
  a_pos : 1 ≤ P.a
  wrap_simple : ∀ s y, s < wEval P.W s y ∧ y < wEval P.W s y
  recur_simple : ∀ b s n, b < rEval P.R b s n ∧ s < rEval P.R b s n ∧ n < rEval P.R b s n
  prec_irrefl : ∀ f, ¬ P.prec f f
  prec_trans : ∀ f g h, P.prec f g → P.prec g h → P.prec f h

/-- The polynomial KBO as the generalized KBO of its polynomial algebra. -/
def polynomialKBOGen (P : polynomialKBOData) : generalizedKBOData where
  zeroI := P.z
  succI n := P.slope * n + P.a
  wrapI := wEval P.W
  recurI := rEval P.R
  prec := P.prec

theorem polynomialKBOGen_laws {P : polynomialKBOData} (h : polynomialKBOLaws P) :
    generalizedKBOLaws (polynomialKBOGen P) where
  succ_mono := fun {a b} hab => Nat.add_le_add_right (Nat.mul_le_mul_left _ hab) _
  wrap_mono_left := fun {a b} c hab => wEval_mono' P.W hab le_rfl
  wrap_mono_right := fun c {a b} hab => wEval_mono' P.W le_rfl hab
  recur_mono_1 := fun {a b} c d hab =>
    PolynomialOrientationDecision.rEval_mono P.R hab le_rfl le_rfl
  recur_mono_2 := fun c {a b} d hab =>
    PolynomialOrientationDecision.rEval_mono P.R le_rfl hab le_rfl
  recur_mono_3 := fun c d {a b} hab =>
    PolynomialOrientationDecision.rEval_mono P.R le_rfl le_rfl hab
  succ_simple n := by
    show n < P.slope * n + P.a
    have h1 := Nat.le_mul_of_pos_left n (show 0 < P.slope by have := h.slope_pos; omega)
    have h2 := h.a_pos
    omega
  wrap_simple := h.wrap_simple
  recur_simple := h.recur_simple
  prec_irrefl := h.prec_irrefl
  prec_trans := h.prec_trans

theorem polynomialKBO_order (P : polynomialKBOData) (h : polynomialKBOLaws P) (ν : Type) :
    GKBOReductionOrder ν (generalizedKBOCore (polynomialKBOGen P)) :=
  generalizedKBO_order _ (polynomialKBOGen_laws h) ν

/-- Acceptance of the free two-rule system by the polynomial KBO. -/
def polynomialKBOAccepts (P : polynomialKBOData) : Prop :=
  generalizedKBOAccepts (polynomialKBOGen P)

/-- Verdict: escape. The polynomial KBO orients both free rules for the coupled tables, and its
soundness theorem gives termination of the contextual free recursor. -/
def polynomialKBOResult (P : polynomialKBOData) : Prop :=
  polynomialKBOAccepts P ∧
    WellFounded (fun u t : SchemaCore.FreeTerm ℕ => SchemaCore.ContextStep t u)

theorem polynomialKBO_sound : ∀ P, polynomialKBOLaws P → polynomialKBOAccepts P →
    WellFounded (fun u t : SchemaCore.FreeTerm ℕ => SchemaCore.ContextStep t u) :=
  fun _ h hacc => generalizedKBO_sound _ (polynomialKBOGen_laws h) hacc

/-- Classification of the polynomial KBO on the free schema (from the P3.5 criteria): the tables are
accepted exactly when the zero rule is oriented by the interpretation, and the duplicating rule is
oriented strictly by the interpretation or weakly with `recur ≻ wrap`. -/
theorem polynomialKBO_classification (P : polynomialKBOData) :
    polynomialKBOAccepts P ↔
      PolynomialOrientationDecision.OrientsZero P.R P.z ∧
        (PolynomialOrientationDecision.OrientsSucc P.W P.R P.slope P.a ∨
          ((∀ b s n, wEval P.W s (rEval P.R b s n) ≤ rEval P.R b s (P.slope * n + P.a)) ∧
            P.prec .recur .wrap)) := by
  unfold polynomialKBOAccepts generalizedKBOAccepts
  rw [gAccepts_dup_iff, gAccepts_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h2, h1⟩

/-- At unit slope the classification is decided by the P3.5 procedures `decideZero` and
`decideSuccUnit`. -/
theorem polynomialKBO_decides (P : polynomialKBOData) (hslope : P.slope = 1) :
    polynomialKBOAccepts P ↔
      PolynomialOrientationDecision.decideZero P.R P.z = true ∧
        (PolynomialOrientationDecision.decideSuccUnit P.W P.R P.a = true ∨
          ((∀ b s n, wEval P.W s (rEval P.R b s n) ≤ rEval P.R b s (n + P.a)) ∧
            P.prec .recur .wrap)) := by
  rw [polynomialKBO_classification, PolynomialOrientationDecision.decideZero_iff,
    PolynomialOrientationDecision.decideSuccUnit_iff]
  simp only [PolynomialOrientationDecision.OrientsSucc, hslope, one_mul]

/-- The coupled P2.4 tables: `zero = 0`, `succ n = n + 1`, `wrap = s + y + 1`,
`recur = (n + 1)(s + b + 2)`, with `recur ≻ wrap ≻ succ ≻ zero`. -/
def polynomialKBOWitness : polynomialKBOData where
  z := 0
  slope := 1
  a := 1
  W := PolynomialOrientationDecision.regionW
  R := PolynomialOrientationDecision.regionR 1 2
  prec := rankPrec schemaRank

theorem polynomialKBOWitness_laws : polynomialKBOLaws polynomialKBOWitness where
  slope_pos := le_rfl
  a_pos := le_rfl
  wrap_simple s y := by
    show s < wEval PolynomialOrientationDecision.regionW s y ∧
      y < wEval PolynomialOrientationDecision.regionW s y
    rw [PolynomialOrientationDecision.wEval_regionW]
    simp only [PolynomialRegion.wrapperEval]
    omega
  recur_simple b s n := by
    show b < rEval (PolynomialOrientationDecision.regionR 1 2) b s n ∧
      s < rEval (PolynomialOrientationDecision.regionR 1 2) b s n ∧
      n < rEval (PolynomialOrientationDecision.regionR 1 2) b s n
    rw [PolynomialOrientationDecision.rEval_regionR]
    simp only [PolynomialRegion.recursorEval]
    have e : (n + 1) * (1 * s + b + 2) = n * (s + b + 2) + (s + b + 2) := by ring
    have hn : n ≤ n * (s + b + 2) := Nat.le_mul_of_pos_right n (by omega)
    rw [e]
    generalize n * (s + b + 2) = X at hn ⊢
    omega
  prec_irrefl := rankPrec_irrefl _
  prec_trans := rankPrec_trans _

/-- The witness is accepted: the P3.5 decision `region_decides` accepts the tables at
`α = 1, β = 2`. -/
theorem polynomialKBOWitness_accepts : polynomialKBOAccepts polynomialKBOWitness := by
  have h := (PolynomialOrientationDecision.rootRuleOrients_iff 0 1 1 _ _).1
    ((PolynomialOrientationDecision.decideRootUnit_iff 0 1 _ _).1
      ((PolynomialOrientationDecision.region_decides 1 2).2 ⟨le_rfl, le_rfl⟩))
  exact (polynomialKBO_classification _).2 ⟨h.1, Or.inl h.2⟩

theorem polynomialKBOWitness_result : polynomialKBOResult polynomialKBOWitness :=
  ⟨polynomialKBOWitness_accepts,
    polynomialKBO_sound _ polynomialKBOWitness_laws polynomialKBOWitness_accepts⟩

/-- The tables at `α = 1, β = 1`, outside the interpretation region of P2.4. -/
def polynomialKBOTie : polynomialKBOData :=
  { polynomialKBOWitness with R := PolynomialOrientationDecision.regionR 1 1 }

/-- A linear recursor table `b + s + n + 2` without counter/payload coupling. -/
def polynomialKBOLinearR : List RMono := [⟨1, 1, 0, 0⟩, ⟨1, 0, 1, 0⟩, ⟨1, 0, 0, 1⟩, ⟨2, 0, 0, 0⟩]

/-- Controls. The witness recursor has a nonlinear monomial coupling payload and counter
(`s * n`); the admissible tables at `α = 1, β = 1` are rejected by the interpretation alone
(`decideRootUnit` returns `false`) and accepted by the polynomial KBO through the precedence clause
`recur ≻ wrap` at the weight tie; the uncoupled linear recursor table is rejected. -/
theorem polynomialKBOWitness_feature :
    (∃ m ∈ polynomialKBOWitness.R, 0 < m.coeff ∧ 1 ≤ m.sDeg ∧ 1 ≤ m.nDeg) ∧
    (polynomialKBOLaws polynomialKBOTie ∧ polynomialKBOAccepts polynomialKBOTie ∧
      PolynomialOrientationDecision.decideRootUnit 0 1 PolynomialOrientationDecision.regionW
        (PolynomialOrientationDecision.regionR 1 1) = false) ∧
    ¬ polynomialKBOAccepts { polynomialKBOWitness with R := polynomialKBOLinearR } := by
  refine ⟨⟨⟨1, 0, 1, 1⟩, by simp [polynomialKBOWitness, PolynomialOrientationDecision.regionR],
    by decide, le_rfl, le_rfl⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine ⟨le_rfl, le_rfl, polynomialKBOWitness_laws.wrap_simple, fun b s n => ?_,
      rankPrec_irrefl _, rankPrec_trans _⟩
    show b < rEval (PolynomialOrientationDecision.regionR 1 1) b s n ∧
      s < rEval (PolynomialOrientationDecision.regionR 1 1) b s n ∧
      n < rEval (PolynomialOrientationDecision.regionR 1 1) b s n
    rw [PolynomialOrientationDecision.rEval_regionR]
    simp only [PolynomialRegion.recursorEval]
    have e : (n + 1) * (1 * s + b + 1) = n * (s + b + 1) + (s + b + 1) := by ring
    have hn : n ≤ n * (s + b + 1) := Nat.le_mul_of_pos_right n (by omega)
    rw [e]
    generalize n * (s + b + 1) = X at hn ⊢
    omega
  · refine (polynomialKBO_classification _).2 ⟨fun b s => ?_, Or.inr ⟨fun b s n => ?_, ?_⟩⟩
    · show b < rEval (PolynomialOrientationDecision.regionR 1 1) b s 0
      rw [PolynomialOrientationDecision.rEval_regionR]
      simp only [PolynomialRegion.recursorEval]
      omega
    · show wEval PolynomialOrientationDecision.regionW s
          (rEval (PolynomialOrientationDecision.regionR 1 1) b s n) ≤
        rEval (PolynomialOrientationDecision.regionR 1 1) b s (1 * n + 1)
      rw [PolynomialOrientationDecision.wEval_regionW, PolynomialOrientationDecision.rEval_regionR,
        PolynomialOrientationDecision.rEval_regionR]
      simp only [PolynomialRegion.wrapperEval, PolynomialRegion.recursorEval]
      have e : (1 * n + 1 + 1) * (1 * s + b + 1) =
          (n + 1) * (1 * s + b + 1) + (s + b + 1) := by ring
      rw [e]
      generalize (n + 1) * (1 * s + b + 1) = X
      omega
    · show schemaRank .wrap < schemaRank .recur
      decide
  · exact Bool.eq_false_iff.2 fun h =>
      absurd ((PolynomialOrientationDecision.region_decides 1 1).1 h).2 (by decide)
  · intro hacc
    obtain ⟨_, hd⟩ := (polynomialKBO_classification _).1 hacc
    rcases hd with h | ⟨h, _⟩
    · exact absurd (h 0 1 0) (by decide)
    · exact absurd (h 0 1 0) (by decide)

/-- Mutation: the payload coefficient of the witness recursor set to `0` (`regionR 0 2`); strict
simplicity in the payload fails at `b = 0, s = 2, n = 0`. -/
theorem polynomialKBO_mutation :
    ¬ polynomialKBOLaws { polynomialKBOWitness with R := PolynomialOrientationDecision.regionR 0 2 } :=
  fun h => absurd (h.recur_simple 0 2 0).2.1 (by decide)

end PolyKBO

/-! ## Row `lambdaFreeKBO` -/

/-- Native data of the lambda-free higher-order (applicative) Knuth–Bendix order: variable weight,
constant symbol weights, the weight added by each application, and a precedence rank on the
constants. -/
structure lambdaFreeKBOData where
  /-- Variable weight `ε`. -/
  w0 : ℕ
  /-- Constant symbol weights. -/
  weight : SchemaSym → ℕ
  /-- Weight added by each application. -/
  appWeight : ℕ
  /-- Precedence rank on constants. -/
  precRank : SchemaSym → ℕ

/-- Admissibility of the lambda-free higher-order Knuth–Bendix order: Becker, Blanchette,
Waldmann, Wand 2017 (CADE-26, LNCS 10395, "A Transfinite Knuth–Bendix Order for Lambda-Free
Higher-Order Terms"), Definition 9 (the applicative KBO `>ap`, the first-order KBO composed with
the applicative encoding, where the application symbol carries weight `0` and the lowest
precedence), at natural weights and restricted to the basic positive-weight case of Section 4.3:
a positive variable weight `ε`, a positive weight for every constant, and a positive application
weight. -/
structure lambdaFreeKBOLaws (M : lambdaFreeKBOData) : Prop where
  /-- Positivity of the variable weight. -/
  w0_pos : 0 < M.w0
  /-- Positivity of every constant weight. -/
  weight_pos : ∀ f, 0 < M.weight f
  /-- Positivity of the application weight. -/
  appWeight_pos : 0 < M.appWeight

/-- Applicative (lambda-free) terms: a variable, a constant of the schema signature, and binary
application. The first-order free schema embeds into these terms through the curried adapter
`lfCurry`. -/
inductive lambdaFreeTerm (ν : Type) where
  | var : ν → lambdaFreeTerm ν
  | const : SchemaSym → lambdaFreeTerm ν
  | app : lambdaFreeTerm ν → lambdaFreeTerm ν → lambdaFreeTerm ν
  deriving DecidableEq, Repr

mutual
/-- The applicative encoding (currying) of a first-order term: a variable stays a variable, and
the arguments of a symbol are applied to it from left to right. -/
def lfCurry {ν : Type} : Term SchemaSym ν → lambdaFreeTerm ν
  | .var x => .var x
  | .app f args => lfCurryArgs (.const f) args

/-- Currying of an argument list with an accumulator. -/
def lfCurryArgs {ν : Type} (acc : lambdaFreeTerm ν) : List (Term SchemaSym ν) → lambdaFreeTerm ν
  | [] => acc
  | a :: as => lfCurryArgs (.app acc (lfCurry a)) as
end

/-- Occurrence count of a variable in an applicative term. -/
def lfCount {ν : Type} [DecidableEq ν] (x : ν) : lambdaFreeTerm ν → ℕ
  | .var y => if y = x then 1 else 0
  | .const _ => 0
  | .app a b => lfCount x a + lfCount x b

/-- Applicative weight: the variable weight at variables, the symbol weight at constants, and
the application weight plus the weights of both subterms at applications. -/
def lfWeight (M : lambdaFreeKBOData) {ν : Type} : lambdaFreeTerm ν → ℕ
  | .var _ => M.w0
  | .const f => M.weight f
  | .app a b => M.appWeight + lfWeight M a + lfWeight M b

/-- Root rank of an applicative term: variables at `0`, constants above `0` by the precedence
rank, and applications at rank `1`, so the application symbol has the lowest precedence
(Definition 9). -/
def lfRootRank (M : lambdaFreeKBOData) {ν : Type} : lambdaFreeTerm ν → ℕ
  | .var _ => 0
  | .const f => M.precRank f + 1
  | .app _ _ => 1

/-- The comparison key of the applicative KBO: weight first, then root rank. -/
def lfKey (M : lambdaFreeKBOData) {ν : Type} (t : lambdaFreeTerm ν) : ℕ × ℕ :=
  (lfWeight M t, lfRootRank M t)

/-- The native applicative comparison: the variable condition `vars#(t) ⊇ vars#(s)` together
with the weight clause (F1) and the head-precedence clause (F3) of the applicative KBO, as the
lexicographic product of weight and root rank. -/
def lambdaFreeKBOGt (M : lambdaFreeKBOData) {ν : Type} [DecidableEq ν]
    (s t : lambdaFreeTerm ν) : Prop :=
  (∀ x, lfCount x t ≤ lfCount x s) ∧
    Prod.Lex (fun a b : ℕ => a < b) (fun a b : ℕ => a < b) (lfKey M t) (lfKey M s)

/-- The key order is irreflexive. -/
theorem lfKeyLT_irrefl (p : ℕ × ℕ) :
    ¬ Prod.Lex (fun a b : ℕ => a < b) (fun a b : ℕ => a < b) p p := by
  intro h
  rcases (Prod.lex_def.1 h) with h | ⟨-, h⟩ <;> exact absurd h (lt_irrefl _)

/-- The key order is transitive. -/
theorem lfKeyLT_trans {p q r : ℕ × ℕ}
    (hpq : Prod.Lex (fun a b : ℕ => a < b) (fun a b : ℕ => a < b) p q)
    (hqr : Prod.Lex (fun a b : ℕ => a < b) (fun a b : ℕ => a < b) q r) :
    Prod.Lex (fun a b : ℕ => a < b) (fun a b : ℕ => a < b) p r := by
  rcases (Prod.lex_def.1 hpq) with h | ⟨e, h⟩ <;>
    rcases (Prod.lex_def.1 hqr) with h' | ⟨e', h'⟩
  · exact Prod.lex_def.2 (Or.inl (lt_trans h h'))
  · exact Prod.lex_def.2 (Or.inl (by rw [← e']; exact h))
  · exact Prod.lex_def.2 (Or.inl (by rw [e]; exact h'))
  · exact Prod.lex_def.2 (Or.inr ⟨e.trans e', lt_trans h h'⟩)

/-- The applicative comparison is irreflexive. -/
theorem lambdaFreeKBOGt_irrefl (M : lambdaFreeKBOData) {ν : Type} [DecidableEq ν]
    (s : lambdaFreeTerm ν) : ¬ lambdaFreeKBOGt M s s :=
  fun h => lfKeyLT_irrefl _ h.2

/-- The applicative comparison is transitive. -/
theorem lambdaFreeKBOGt_trans (M : lambdaFreeKBOData) {ν : Type} [DecidableEq ν] :
    Transitive (lambdaFreeKBOGt (ν := ν) M) :=
  fun _ _ _ hst htu => ⟨fun x => (htu.1 x).trans (hst.1 x), lfKeyLT_trans htu.2 hst.2⟩

/-- The applicative comparison is well founded. -/
theorem lambdaFreeKBOGt_wf (M : lambdaFreeKBOData) {ν : Type} [DecidableEq ν] :
    WellFounded (fun y x : lambdaFreeTerm ν => lambdaFreeKBOGt M x y) :=
  Subrelation.wf (fun {_ _} h => h.2)
    (InvImage.wf (lfKey M) (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf))

/-- The unit-coefficient weighted evaluation of an argument list is the list sum. -/
theorem lfEvL_eq_sum {ν : Type} [DecidableEq ν] (v : ν) (f : SchemaSym) (ws : SchemaSym → ℕ)
    (i : ℕ) (l : List (Term SchemaSym ν)) :
    evL (fun _ _ => (1 : ℕ)) ws (fun y => if y = v then 1 else 0) f i l =
      (l.map (fun a => ev (fun _ _ => (1 : ℕ)) ws (fun y => if y = v then 1 else 0) a)).sum := by
  induction l generalizing i with
  | nil => simp
  | cons a as ih =>
      rw [evL_cons, List.map_cons, List.sum_cons, ih (i + 1)]
      simp

/-- Counting commutes with currying, at every accumulator. -/
theorem lfCount_curryArgs {ν : Type} [DecidableEq ν] (v : ν) (acc : lambdaFreeTerm ν)
    (l : List (Term SchemaSym ν)) :
    lfCount v (lfCurryArgs acc l) =
      lfCount v acc + (l.map (fun a => lfCount v (lfCurry a))).sum := by
  induction l generalizing acc with
  | nil => simp [lfCurryArgs]
  | cons a as ih =>
      rw [lfCurryArgs, ih (.app acc (lfCurry a))]
      simp only [List.map_cons, List.sum_cons, lfCount]
      omega

/-- The variable count of the applicative image is the variable count of the first-order term. -/
theorem lfCount_curry {ν : Type} [DecidableEq ν] (v : ν) :
    ∀ t : Term SchemaSym ν, lfCount v (lfCurry t) = cnt (fun _ _ => (1 : ℕ)) v t := by
  intro t
  induction t using Term.rec' with
  | hvar x => rfl
  | happ f args ih =>
      rw [lfCurry, lfCount_curryArgs]
      have hmap : (args.map (fun a => lfCount v (lfCurry a))) =
          (args.map (fun a => cnt (fun _ _ => (1 : ℕ)) v a)) := by
        apply List.map_congr_left
        intro a ha
        exact ih a ha
      rw [hmap]
      simp only [cnt, ev_app]
      rw [lfEvL_eq_sum]
      simp [lfCount]

/-- The weight of a curried term, at every accumulator. -/
theorem lfWeight_curryArgs (M : lambdaFreeKBOData) {ν : Type} (acc : lambdaFreeTerm ν)
    (l : List (Term SchemaSym ν)) :
    lfWeight M (lfCurryArgs acc l) =
      lfWeight M acc + l.length * M.appWeight +
        (l.map (fun a => lfWeight M (lfCurry a))).sum := by
  induction l generalizing acc with
  | nil => simp [lfCurryArgs]
  | cons a as ih =>
      rw [lfCurryArgs, ih (.app acc (lfCurry a))]
      simp only [List.length_cons, List.map_cons, List.sum_cons, lfWeight]
      ring

/-- The weight of the curried image of a symbol application. -/
theorem lfWeight_curry_app (M : lambdaFreeKBOData) {ν : Type} (f : SchemaSym)
    (args : List (Term SchemaSym ν)) :
    lfWeight M (lfCurry (.app f args)) =
      M.weight f + args.length * M.appWeight +
        (args.map (fun a => lfWeight M (lfCurry a))).sum := by
  rw [lfCurry, lfWeight_curryArgs]
  simp [lfWeight]

/-- The weight of the curried image of the recursor node. -/
theorem lfWeight_curry_embed_recur (M : lambdaFreeKBOData) {ν : Type}
    (b s n : SchemaCore.FreeTerm ν) :
    lfWeight M (lfCurry (embed (.recur b s n))) =
      M.weight .recur + 3 * M.appWeight + lfWeight M (lfCurry (embed b)) +
        lfWeight M (lfCurry (embed s)) + lfWeight M (lfCurry (embed n)) := by
  rw [show embed (.recur b s n) = .app .recur [embed b, embed s, embed n] from rfl]
  rw [lfWeight_curry_app]
  simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  ring

/-- The weighted count of an embedded recursor node. -/
theorem cnt_embed_recur {ν : Type} [DecidableEq ν] (c : SchemaSym → ℕ → ℕ) (x : ν)
    (b s n : SchemaCore.FreeTerm ν) :
    cnt c x (embed (.recur b s n)) =
      c .recur 0 * cnt c x (embed b) + c .recur 1 * cnt c x (embed s) +
        c .recur 2 * cnt c x (embed n) := by
  simp [cnt, embed, add_assoc]

/-- The weighted count of the embedded constant `zero`. -/
theorem cnt_embed_zero {ν : Type} [DecidableEq ν] (c : SchemaSym → ℕ → ℕ) (x : ν) :
    cnt c x (embed (.zero : SchemaCore.FreeTerm ν)) = 0 := by
  simp [cnt, embed]

/-- Applicative substitution. -/
def lfSubst {ν : Type} (σ : ν → lambdaFreeTerm ν) : lambdaFreeTerm ν → lambdaFreeTerm ν
  | .var x => σ x
  | .const f => .const f
  | .app a b => .app (lfSubst σ a) (lfSubst σ b)

/-- Open substitution control: the applicative weight is monotone under every substitution whose
images are at least the variable weight. -/
theorem lfWeight_subst_le (M : lambdaFreeKBOData) {ν : Type} (σ : ν → lambdaFreeTerm ν)
    (hσ : ∀ x, M.w0 ≤ lfWeight M (σ x)) :
    ∀ t : lambdaFreeTerm ν, lfWeight M t ≤ lfWeight M (lfSubst σ t)
  | .var x => hσ x
  | .const _ => le_rfl
  | .app a b => by
      simp only [lfSubst, lfWeight]
      exact add_le_add (add_le_add le_rfl (lfWeight_subst_le M σ hσ a))
        (lfWeight_subst_le M σ hσ b)

/-- Acceptance of the free duplicating rule by the lambda-free higher-order KBO, through the
curried adapter `lfCurry`: every instance, transported by `embed` and curried, is oriented. -/
def lambdaFreeKBOAccepts (M : lambdaFreeKBOData) : Prop :=
  ∀ b s n : SchemaCore.FreeTerm ℕ,
    lambdaFreeKBOGt M (lfCurry (embed (.recur b s (.succ n))))
      (lfCurry (embed (.wrap s (.recur b s n))))

/-- The lambda-free higher-order (applicative) KBO does not orient the free duplicating rule: its
variable condition refuses the payload duplication for every weight system, and the curried
adapter preserves the payload counts.

Verdict: barrier.
-/
def lambdaFreeKBOResult (M : lambdaFreeKBOData) : Prop := ¬ lambdaFreeKBOAccepts M

/-- The barrier holds for every datum, through the P3.2 cell on the curried payload counts; the
admissibility laws are not used by it. -/
theorem lambdaFreeKBO_rejects (M : lambdaFreeKBOData) : lambdaFreeKBOResult M := by
  intro hacc
  obtain ⟨s, hs⟩ := barrier_cell_strict_reversal (S := SchemaCore.freeSchema ℕ)
    (payloadCount (fun _ _ => (1 : ℕ))) .zero .zero
    (payload_wrapUnbounded (fun _ _ => (1 : ℕ)) (fun _ _ => le_rfl))
    (payload_gainBounded (fun _ _ => (1 : ℕ)))
  have hvc := (hacc .zero s .zero).1 1
  rw [lfCount_curry, lfCount_curry] at hvc
  exact absurd hvc (not_le.2 hs)

theorem lambdaFreeKBO_universal : ∀ M, lambdaFreeKBOLaws M → lambdaFreeKBOResult M :=
  fun M _ => lambdaFreeKBO_rejects M

/-- A lambda-free higher-order KBO: variable weight `1`, all symbol weights `1`, application
weight `1`, precedence rank `recur ≻ wrap ≻ succ ≻ zero`. -/
def lambdaFreeKBOWitness : lambdaFreeKBOData where
  w0 := 1
  weight _ := 1
  appWeight := 1
  precRank := schemaRank

theorem lambdaFreeKBOWitness_laws : lambdaFreeKBOLaws lambdaFreeKBOWitness where
  w0_pos := by decide
  weight_pos f := by cases f <;> decide
  appWeight_pos := by decide

theorem lambdaFreeKBOWitness_result : lambdaFreeKBOResult lambdaFreeKBOWitness :=
  lambdaFreeKBO_rejects _

/-- Controls. The application condition: an application is strictly above each of its parts. The
open substitution: the nonduplicating zero rule is oriented at every open instance (arbitrary
open `b`, `s`), the payload counts at the open duplicating pattern are `1` on the left and `2` on
the right, and the applicative weight is monotone under substitution with images at least the
variable weight. The applicative terms outside the first-order image: the constant `zero` applied
to `zero` is strictly above `zero`. -/
theorem lambdaFreeKBOWitness_feature :
    lambdaFreeKBOGt lambdaFreeKBOWitness (.app (.const .succ) (.var 0)) (.var 0) ∧
    lambdaFreeKBOGt (ν := ℕ) lambdaFreeKBOWitness (.app (.const .zero) (.const .zero))
      (.const .zero) ∧
    (∀ b s : SchemaCore.FreeTerm ℕ,
      lambdaFreeKBOGt lambdaFreeKBOWitness (lfCurry (embed (.recur b s .zero)))
        (lfCurry (embed b))) ∧
    (lfCount (1 : ℕ)
        (lfCurry (embed (.recur (.var 0) (.var 1) (.succ (.var 2)) :
          SchemaCore.FreeTerm ℕ))) = 1 ∧
      lfCount (1 : ℕ)
        (lfCurry (embed (.wrap (.var 1) (.recur (.var 0) (.var 1) (.var 2)) :
          SchemaCore.FreeTerm ℕ))) = 2) ∧
    lfWeight lambdaFreeKBOWitness
        (lfCurry (embed (.recur (.var 0) (.var 1) .zero : SchemaCore.FreeTerm ℕ))) ≤
      lfWeight lambdaFreeKBOWitness
        (lfSubst (fun x => if x = 0 then .app (.const .zero) (.const .zero) else .var x)
          (lfCurry (embed (.recur (.var 0) (.var 1) .zero : SchemaCore.FreeTerm ℕ)))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, Prod.lex_def.2 (Or.inl ?_)⟩
    · intro x
      by_cases h : (0 : ℕ) = x <;> simp [lfCount, h]
    · norm_num [lfKey, lfWeight, lambdaFreeKBOWitness]
  · refine ⟨?_, Prod.lex_def.2 (Or.inl ?_)⟩
    · intro x
      simp [lfCount]
    · norm_num [lfKey, lfWeight, lambdaFreeKBOWitness]
  · intro b s
    refine ⟨?_, Prod.lex_def.2 (Or.inl ?_)⟩
    · intro x
      rw [lfCount_curry, lfCount_curry]
      rw [cnt_embed_recur, cnt_embed_zero]
      omega
    · simp only [lfKey]
      rw [lfWeight_curry_embed_recur]
      simp [lambdaFreeKBOWitness]
      omega
  · constructor <;> rw [lfCount_curry (ν := ℕ) (1 : ℕ)] <;> decide
  · exact lfWeight_subst_le _ _
      (fun x => by by_cases h : x = 0 <;> simp [lfWeight, h, lambdaFreeKBOWitness]) _

/-- Mutation: the application weight of the witness set to `0`; positivity of the application
weight fails, while the variable-condition barrier is independent of it. -/
theorem lambdaFreeKBO_mutation :
    ¬ lambdaFreeKBOLaws { lambdaFreeKBOWitness with appWeight := 0 } ∧
      lambdaFreeKBOResult { lambdaFreeKBOWitness with appWeight := 0 } :=
  ⟨fun h => absurd h.appWeight_pos (by decide), lambdaFreeKBO_rejects _⟩

/-! ## Row `acKBO` -/

/-- One associative-commutative step of the wrapper on first-order schema terms: commutativity,
associativity, and congruence in every argument position. -/
inductive ACStep {ν : Type} : Term SchemaSym ν → Term SchemaSym ν → Prop
  | commWrap (a b : Term SchemaSym ν) : ACStep (.app .wrap [a, b]) (.app .wrap [b, a])
  | assocWrap (a b c : Term SchemaSym ν) :
      ACStep (.app .wrap [.app .wrap [a, b], c]) (.app .wrap [a, .app .wrap [b, c]])
  | underSucc {a b : Term SchemaSym ν} : ACStep a b → ACStep (.app .succ [a]) (.app .succ [b])
  | underWrapLeft {a b : Term SchemaSym ν} (c : Term SchemaSym ν) :
      ACStep a b → ACStep (.app .wrap [a, c]) (.app .wrap [b, c])
  | underWrapRight (c : Term SchemaSym ν) {a b : Term SchemaSym ν} :
      ACStep a b → ACStep (.app .wrap [c, a]) (.app .wrap [c, b])
  | underRecurFirst (s n : Term SchemaSym ν) {a b : Term SchemaSym ν} :
      ACStep a b → ACStep (.app .recur [a, s, n]) (.app .recur [b, s, n])
  | underRecurSecond (b : Term SchemaSym ν) {a b' : Term SchemaSym ν} (n : Term SchemaSym ν) :
      ACStep a b' → ACStep (.app .recur [b, a, n]) (.app .recur [b, b', n])
  | underRecurThird (b s : Term SchemaSym ν) {a b' : Term SchemaSym ν} :
      ACStep a b' → ACStep (.app .recur [b, s, a]) (.app .recur [b, s, b'])

/-- The AC equivalence of the wrapper: the reflexive, symmetric, transitive closure of `ACStep`. -/
abbrev ACEquiv {ν : Type} (s t : Term SchemaSym ν) : Prop := Relation.EqvGen ACStep s t

/-- Unit-coefficient evaluation is invariant under one AC step. -/
theorem ev_one_ACStep {ν : Type} (ws : SchemaSym → ℕ) (v : ν → ℕ) {s t : Term SchemaSym ν}
    (h : ACStep s t) : ev (fun _ _ => (1 : ℕ)) ws v s = ev (fun _ _ => (1 : ℕ)) ws v t := by
  induction h with
  | commWrap a b =>
      simp only [ev_app, evL_cons, evL_nil, one_smul, add_zero]
      omega
  | assocWrap a b c =>
      simp only [ev_app, evL_cons, evL_nil, one_smul, add_zero]
      omega
  | underSucc _ ih =>
      simp only [ev_app, evL_cons, evL_nil, one_smul, add_zero]
      rw [ih]
  | underWrapLeft _ _ ih =>
      simp only [ev_app, evL_cons, evL_nil, one_smul, add_zero]
      rw [ih]
  | underWrapRight _ _ ih =>
      simp only [ev_app, evL_cons, evL_nil, one_smul, add_zero]
      rw [ih]
  | underRecurFirst _ _ _ ih =>
      simp only [ev_app, evL_cons, evL_nil, one_smul, add_zero]
      rw [ih]
  | underRecurSecond _ _ _ ih =>
      simp only [ev_app, evL_cons, evL_nil, one_smul, add_zero]
      rw [ih]
  | underRecurThird _ _ _ ih =>
      simp only [ev_app, evL_cons, evL_nil, one_smul, add_zero]
      rw [ih]

/-- The payload count is invariant under one AC step. -/
theorem cnt_one_ACStep {ν : Type} [DecidableEq ν] (x : ν) {s t : Term SchemaSym ν}
    (h : ACStep s t) :
    cnt (fun _ _ => (1 : ℕ)) x s = cnt (fun _ _ => (1 : ℕ)) x t :=
  ev_one_ACStep (fun _ => 0) (fun y => if y = x then 1 else 0) h

/-- Unit-coefficient evaluation is invariant under the full AC equivalence. -/
theorem ev_one_AC {ν : Type} (ws : SchemaSym → ℕ) (v : ν → ℕ) {s t : Term SchemaSym ν}
    (h : ACEquiv s t) : ev (fun _ _ => (1 : ℕ)) ws v s = ev (fun _ _ => (1 : ℕ)) ws v t := by
  induction h with
  | rel _ _ hxy => exact ev_one_ACStep ws v hxy
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihxy ihyz => exact ihxy.trans ihyz

/-- The payload count is invariant under the full AC equivalence. -/
theorem cnt_one_AC {ν : Type} [DecidableEq ν] (x : ν) {s t : Term SchemaSym ν}
    (h : ACEquiv s t) :
    cnt (fun _ _ => (1 : ℕ)) x s = cnt (fun _ _ => (1 : ℕ)) x t :=
  ev_one_AC (fun _ => 0) (fun y => if y = x then 1 else 0) h

/-- Symbol code of the AC occurrence multiset. The wrapper carries code `0` because the
top-flattening erases wrapper occurrences. -/
def acSymCode : SchemaSym → ℕ
  | .zero => 1
  | .succ => 2
  | .wrap => 0
  | .recur => 3

mutual
/-- The AC occurrence multiset of a term: at the wrapper the occurrence multiset is the multiset
union of the argument contents, which is the top-flattening of the AC symbol; at every other
symbol it is the symbol code plus the union over the arguments; every variable contributes `0`.
This is the flattened occurrence fingerprint of Yamada, Winkler, Hirokawa and Middeldorp 2014
(FLOPS 2014, LNCS 8475, "AC-KBO Revisited"), Definition 3. -/
def acBag {ν : Type} : Term SchemaSym ν → Multiset ℕ
  | .var _ => {0}
  | .app f args => (if f = .wrap then 0 else {acSymCode f}) + acBagL args

/-- Occurrence multiset of an argument list. -/
def acBagL {ν : Type} : List (Term SchemaSym ν) → Multiset ℕ
  | [] => 0
  | a :: as => acBag a + acBagL as
end

/-- The occurrence multiset is invariant under one AC step. -/
theorem acBag_ACStep {ν : Type} {s t : Term SchemaSym ν} (h : ACStep s t) :
    acBag s = acBag t := by
  induction h with
  | commWrap a b =>
      simpa [acBag, acBagL] using Multiset.add_comm (acBag a) (acBag b)
  | assocWrap a b c =>
      simpa [acBag, acBagL] using Multiset.add_assoc (acBag a) (acBag b) (acBag c)
  | underSucc _ ih => simp [acBag, acBagL, ih]
  | underWrapLeft _ _ ih => simp [acBag, acBagL, ih]
  | underWrapRight _ _ ih => simp [acBag, acBagL, ih]
  | underRecurFirst _ _ _ ih => simp [acBag, acBagL, ih]
  | underRecurSecond _ _ _ ih => simp [acBag, acBagL, ih]
  | underRecurThird _ _ _ ih => simp [acBag, acBagL, ih]

/-- The occurrence multiset is invariant under the full AC equivalence. -/
theorem acBag_AC {ν : Type} {s t : Term SchemaSym ν} (h : ACEquiv s t) :
    acBag s = acBag t := by
  induction h with
  | rel _ _ hxy => exact acBag_ACStep hxy
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihxy ihyz => exact ihxy.trans ihyz

/-- Native data of the catalogue's AC-invariant comparison control: variable weight, symbol
weights, and a precedence rank on symbols. Full AC-KBO is handled below through its defining
variable-condition interface; this finite key is not presented as Definition 5.1 of AC-KBO. -/
structure acKBOData where
  /-- Variable weight. -/
  w0 : ℕ
  /-- Symbol weights. -/
  weight : SchemaSym → ℕ
  /-- Precedence rank. -/
  precRank : SchemaSym → ℕ

/-- Admissibility of the finite AC-invariant comparison control. The fields are the two basic
weight conditions used by KBO. The universal AC-KBO barrier below uses the exact variable
condition shared by every AC-KBO comparison and does not identify this key with the full order. -/
structure acKBOLaws (M : acKBOData) : Prop where
  /-- Positivity of the variable weight. -/
  w0_pos : 0 < M.w0
  /-- The constant `zero` weighs at least the variable weight. -/
  zero_ge : M.w0 ≤ M.weight .zero

/-- The unit-coefficient weight of a term, invariant under AC by construction. -/
def acWt (M : acKBOData) {ν : Type} (t : Term SchemaSym ν) : ℕ :=
  ev (fun _ _ => (1 : ℕ)) M.weight (fun _ => M.w0) t

/-- Root rank of a term: variables `0`, applications the precedence rank plus `1`. -/
def acRootRank (M : acKBOData) {ν : Type} : Term SchemaSym ν → ℕ
  | .var _ => 0
  | .app f _ => M.precRank f + 1

/-- The comparison key: weight and root rank, then the flattened occurrence multiset. -/
def acKey (M : acKBOData) {ν : Type} (t : Term SchemaSym ν) : (ℕ × ℕ) × Multiset ℕ :=
  ((acWt M t, acRootRank M t), acBag t)

/-- The key order: weight and root rank lexicographically, then the Dershowitz–Manna multiset
order on the flattened occurrence multisets. -/
def acKeyLT (a b : (ℕ × ℕ) × Multiset ℕ) : Prop :=
  Prod.Lex (Prod.Lex (fun x y : ℕ => x < y) (fun x y : ℕ => x < y))
    Multiset.IsDershowitzMannaLT a b

/-- The AC-invariant comparison: the variable condition of the KBO together with the key order. -/
def acKBOGt (M : acKBOData) {ν : Type} [DecidableEq ν] (s t : Term SchemaSym ν) : Prop :=
  (∀ x, cnt (fun _ _ => (1 : ℕ)) x t ≤ cnt (fun _ _ => (1 : ℕ)) x s) ∧
    acKeyLT (acKey M t) (acKey M s)

/-- Root rank is invariant under one AC step. -/
theorem acRootRank_ACStep (M : acKBOData) {ν : Type} {s t : Term SchemaSym ν}
    (h : ACStep s t) : acRootRank M s = acRootRank M t := by
  cases h <;> rfl

/-- Root rank is invariant under the full AC equivalence. -/
theorem acRootRank_AC (M : acKBOData) {ν : Type} {s t : Term SchemaSym ν} (h : ACEquiv s t) :
    acRootRank M s = acRootRank M t := by
  induction h with
  | rel _ _ hxy => exact acRootRank_ACStep M hxy
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihxy ihyz => exact ihxy.trans ihyz

/-- The weight is invariant under the full AC equivalence. -/
theorem acWt_AC (M : acKBOData) {ν : Type} {s t : Term SchemaSym ν} (h : ACEquiv s t) :
    acWt M s = acWt M t :=
  ev_one_AC M.weight (fun _ => M.w0) h

/-- The whole key is invariant under the full AC equivalence. -/
theorem acKey_AC (M : acKBOData) {ν : Type} {s t : Term SchemaSym ν} (h : ACEquiv s t) :
    acKey M s = acKey M t := by
  unfold acKey
  rw [acWt_AC M h, acRootRank_AC M h, acBag_AC h]

/-- The key order on two natural numbers is irreflexive. -/
theorem prodLexNat_irrefl (p : ℕ × ℕ) :
    ¬ Prod.Lex (fun a b : ℕ => a < b) (fun a b : ℕ => a < b) p p := by
  rw [Prod.lex_def]
  intro h
  rcases h with h | ⟨-, h⟩ <;> exact absurd h (lt_irrefl _)

/-- The key order on two natural numbers is transitive. -/
theorem prodLexNat_trans {p q r : ℕ × ℕ}
    (hpq : Prod.Lex (fun a b : ℕ => a < b) (fun a b : ℕ => a < b) p q)
    (hqr : Prod.Lex (fun a b : ℕ => a < b) (fun a b : ℕ => a < b) q r) :
    Prod.Lex (fun a b : ℕ => a < b) (fun a b : ℕ => a < b) p r := by
  rcases (Prod.lex_def.1 hpq) with h | ⟨e, h⟩ <;>
    rcases (Prod.lex_def.1 hqr) with h' | ⟨e', h'⟩
  · exact Prod.lex_def.2 (Or.inl (lt_trans h h'))
  · exact Prod.lex_def.2 (Or.inl (by rw [← e']; exact h))
  · exact Prod.lex_def.2 (Or.inl (by rw [e]; exact h'))
  · exact Prod.lex_def.2 (Or.inr ⟨e.trans e', lt_trans h h'⟩)

/-- The Dershowitz–Manna multiset order is irreflexive (its own well-foundedness plus
asymmetry). -/
theorem dershowitzManna_irrefl (B : Multiset ℕ) : ¬ Multiset.IsDershowitzMannaLT B B :=
  fun h => (Multiset.wellFounded_isDershowitzMannaLT (α := ℕ)).asymmetric B B h h

/-- The key order is irreflexive. -/
theorem acKeyLT_irrefl (k : (ℕ × ℕ) × Multiset ℕ) : ¬ acKeyLT k k := by
  unfold acKeyLT
  rw [Prod.lex_def]
  intro h
  rcases h with h | ⟨-, h⟩
  · exact prodLexNat_irrefl _ h
  · exact dershowitzManna_irrefl _ h

/-- The key order is transitive. -/
theorem acKeyLT_trans {a b c : (ℕ × ℕ) × Multiset ℕ} (hbc : acKeyLT c b) (hab : acKeyLT b a) :
    acKeyLT c a := by
  unfold acKeyLT at hbc hab ⊢
  rw [Prod.lex_def] at hbc hab ⊢
  rcases hbc with hbc | ⟨eqcb, hbc⟩
  · rcases hab with hab | ⟨eqba, hab⟩
    · exact Or.inl (prodLexNat_trans hbc hab)
    · exact Or.inl (by rw [← eqba]; exact hbc)
  · rcases hab with hab | ⟨eqba, hab⟩
    · exact Or.inl (by rw [eqcb]; exact hab)
    · exact Or.inr ⟨eqcb.trans eqba, Multiset.IsDershowitzMannaLT.trans hbc hab⟩

/-- The key order is well founded. -/
theorem acKeyLT_wf : WellFounded acKeyLT := by
  unfold acKeyLT
  exact WellFounded.prod_lex (WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf)
    (Multiset.wellFounded_isDershowitzMannaLT (α := ℕ))

/-- The AC-invariant comparison is irreflexive. -/
theorem acKBOGt_irrefl (M : acKBOData) {ν : Type} [DecidableEq ν] (s : Term SchemaSym ν) :
    ¬ acKBOGt M s s :=
  fun h => acKeyLT_irrefl _ h.2

/-- The AC-invariant comparison is transitive. -/
theorem acKBOGt_trans (M : acKBOData) {ν : Type} [DecidableEq ν] :
    Transitive (acKBOGt (ν := ν) M) :=
  fun _ _ _ hst htu => ⟨fun x => (htu.1 x).trans (hst.1 x), acKeyLT_trans htu.2 hst.2⟩

/-- The AC-invariant comparison is well founded. -/
theorem acKBOGt_wf (M : acKBOData) {ν : Type} [DecidableEq ν] :
    WellFounded (fun y x : Term SchemaSym ν => acKBOGt M x y) :=
  Subrelation.wf (fun {_ _} h => h.2) (InvImage.wf (acKey M) acKeyLT_wf)

/-- AC invariance of the comparison: AC-equivalent representatives compare in the same way with
every pair of third terms. -/
theorem acKBOGt_invariant (M : acKBOData) {ν : Type} [DecidableEq ν]
    {x x' y y' : Term SchemaSym ν} (hx : ACEquiv x x') (hy : ACEquiv y y') :
    acKBOGt M x y ↔ acKBOGt M x' y' := by
  have hkx := acKey_AC M hx
  have hky := acKey_AC M hy
  unfold acKBOGt
  rw [hkx, hky]
  constructor
  · intro h
    exact ⟨fun v => by rw [← cnt_one_AC v hx, ← cnt_one_AC v hy]; exact h.1 v, h.2⟩
  · intro h
    exact ⟨fun v => by rw [cnt_one_AC v hx, cnt_one_AC v hy]; exact h.1 v, h.2⟩

/-- Acceptance of the free duplicating rule by the AC-invariant comparison: every instance,
transported by `embed`, is oriented. -/
def acKBOAccepts (M : acKBOData) : Prop :=
  ∀ b s n : SchemaCore.FreeTerm ℕ,
    acKBOGt M (embed (.recur b s (.succ n))) (embed (.wrap s (.recur b s n)))

/-- The AC-invariant comparison does not orient the free duplicating rule: the AC equivalence
preserves every payload count, so the KBO variable condition refuses the payload duplication for
every weight system and every AC treatment.

Verdict: barrier.
-/
def acKBOResult (M : acKBOData) : Prop := ¬ acKBOAccepts M

/-- The barrier holds for every datum, through the P3.2 cell on the unit-coefficient payload
counts; the admissibility laws are not used by it. -/
theorem acKBO_rejects (M : acKBOData) : acKBOResult M := by
  intro hacc
  obtain ⟨s, hs⟩ := barrier_cell_strict_reversal (S := SchemaCore.freeSchema ℕ)
    (payloadCount (fun _ _ => (1 : ℕ))) .zero .zero
    (payload_wrapUnbounded (fun _ _ => (1 : ℕ)) (fun _ _ => le_rfl))
    (payload_gainBounded (fun _ _ => (1 : ℕ)))
  exact absurd ((hacc .zero s .zero).1 1) (not_le.2 hs)

theorem acKBO_universal : ∀ M, acKBOLaws M → acKBOResult M :=
  fun M _ => acKBO_rejects M

/-- The method-level interface needed by the duplicator theorem. Every AC-KBO comparison has
this variable condition: if `s > t`, each variable occurs at least as often in `s` as in `t`.
The remaining Definition 5.1 cases may decide comparisons only after this condition holds. -/
structure ACKBONecessaryComparison where
  gt : Term SchemaSym ℕ → Term SchemaSym ℕ → Prop
  variableCondition : ∀ {s t}, gt s t →
    ∀ x, cnt (fun _ _ => (1 : ℕ)) x t ≤ cnt (fun _ _ => (1 : ℕ)) x s

/-- Orientation of every instance of the duplicating recursor rule by a comparison satisfying
the AC-KBO variable condition. -/
def ACKBOOrientsDuplicator (K : ACKBONecessaryComparison) : Prop :=
  ∀ b s n : SchemaCore.FreeTerm ℕ,
    K.gt (embed (.recur b s (.succ n))) (embed (.wrap s (.recur b s n)))

/-- Universal AC-KBO barrier. No comparison satisfying the defining KBO variable condition can
orient every instance of the payload-duplicating recursor rule, regardless of weights,
precedence, AC flattening, or the later cases of the AC-KBO definition. -/
theorem no_ACKBO_variableCondition_orients_duplicator
    (K : ACKBONecessaryComparison) : ¬ ACKBOOrientsDuplicator K := by
  intro hacc
  obtain ⟨s, hs⟩ := barrier_cell_strict_reversal (S := SchemaCore.freeSchema ℕ)
    (payloadCount (fun _ _ => (1 : ℕ))) .zero .zero
    (payload_wrapUnbounded (fun _ _ => (1 : ℕ)) (fun _ _ => le_rfl))
    (payload_gainBounded (fun _ _ => (1 : ℕ)))
  exact absurd (K.variableCondition (hacc .zero s .zero) 1) (not_le.2 hs)

/-- The catalogue control comparison instantiates the exact necessary-condition interface. -/
def acKBOControlNecessaryComparison (M : acKBOData) : ACKBONecessaryComparison where
  gt := acKBOGt M
  variableCondition h := h.1

/-- Exact method identity for the AC-KBO row: the row's barrier is a theorem about every
AC-KBO comparison because it uses only AC-KBO's mandatory variable condition. The finite key
model is retained separately as a non-vacuous AC-invariant regression control. -/
theorem acKBO_methodIdentity :
    (∀ K : ACKBONecessaryComparison, ¬ ACKBOOrientsDuplicator K) ∧
      (∀ M : acKBOData,
        ACKBOOrientsDuplicator (acKBOControlNecessaryComparison M) ↔ acKBOAccepts M) := by
  refine ⟨no_ACKBO_variableCondition_orients_duplicator, ?_⟩
  intro M
  rfl

/-- An AC-invariant KBO: variable weight `1`, all symbol weights `1`, precedence rank
`recur ≻ wrap ≻ succ ≻ zero`. -/
def acKBOWitness : acKBOData where
  w0 := 1
  weight _ := 1
  precRank := schemaRank

theorem acKBOWitness_laws : acKBOLaws acKBOWitness where
  w0_pos := by decide
  zero_ge := by decide

theorem acKBOWitness_result : acKBOResult acKBOWitness :=
  acKBO_rejects _

/-- Left representative of the nontrivial AC class of the wrapper. -/
def acRepLeft : Term SchemaSym ℕ := embed (.wrap (.var 0) (.var 1) : SchemaCore.FreeTerm ℕ)

/-- Right representative of the nontrivial AC class of the wrapper. -/
def acRepRight : Term SchemaSym ℕ := embed (.wrap (.var 1) (.var 0) : SchemaCore.FreeTerm ℕ)

/-- The two representatives are AC-equivalent. -/
theorem acReps_eqv : ACEquiv acRepLeft acRepRight :=
  Relation.EqvGen.rel _ _ (ACStep.commWrap _ _)

/-- The two representatives are distinct and compare equally under the new comparison: neither
is above the other, because the whole key is AC-invariant. -/
theorem acReps_equal :
    acRepLeft ≠ acRepRight ∧
      ¬ acKBOGt acKBOWitness acRepLeft acRepRight ∧
      ¬ acKBOGt acKBOWitness acRepRight acRepLeft := by
  refine ⟨by decide, ?_, ?_⟩
  · intro h
    have h2 := h.2
    rw [← acKey_AC acKBOWitness acReps_eqv] at h2
    exact acKeyLT_irrefl _ h2
  · intro h
    have h2 := h.2
    rw [acKey_AC acKBOWitness acReps_eqv] at h2
    exact acKeyLT_irrefl _ h2

/-- Controls. The AC invariance: the nontrivial equivalent representatives compare equally with
every third term. Nontrivial representatives compare equally: the pair `wrap 0 1` and `wrap 1 0`
is distinct, AC-equivalent, and neither is above the other, so the repaired comparator has no
self-loop on the AC class (the AC analogue of defect C12) and no reflexive comparison. The
multiset status on the AC symbol: at equal weight and equal root rank, `succ (succ (succ zero))`
is strictly above `succ (wrap zero zero)`, decided exactly by the Dershowitz–Manna order on the
flattened occurrence multisets `{1,1,2} < {1,2,2,2}`. The top-flattening: the association-nested
and the association-flat wrapper have the same occurrence multiset. -/
theorem acKBOWitness_feature :
    (ACEquiv acRepLeft acRepRight ∧ acRepLeft ≠ acRepRight ∧
      ¬ acKBOGt acKBOWitness acRepLeft acRepRight ∧
      ¬ acKBOGt acKBOWitness acRepRight acRepLeft) ∧
    (∀ z : Term SchemaSym ℕ,
      acKBOGt acKBOWitness acRepLeft z ↔ acKBOGt acKBOWitness acRepRight z) ∧
    acKBOGt acKBOWitness (embed (.succ (.succ (.succ .zero)) : SchemaCore.FreeTerm ℕ))
      (embed (.succ (.wrap .zero .zero) : SchemaCore.FreeTerm ℕ)) ∧
    acBag (embed (.wrap (.var 0) (.wrap (.var 1) (.var 2)) : SchemaCore.FreeTerm ℕ)) =
      acBag (embed (.wrap (.wrap (.var 1) (.var 0)) (.var 2) : SchemaCore.FreeTerm ℕ)) := by
  refine ⟨⟨acReps_eqv, acReps_equal⟩,
    fun z => acKBOGt_invariant _ acReps_eqv (Relation.EqvGen.refl z), ?_, ?_⟩
  · refine ⟨?_, Prod.lex_def.2 (Or.inr ⟨?_, ?_⟩)⟩
    · intro x
      simp [cnt, embed]
    · decide
    · refine ⟨({1, 2} : Multiset ℕ), ({1} : Multiset ℕ), ({2, 2} : Multiset ℕ),
        ?_, ?_, ?_, ?_⟩
      · decide
      · decide
      · decide
      · intro y hy
        have hy1 : y = 1 := by simpa using hy
        subst hy1
        exact ⟨2, by decide, by decide⟩
  · decide

/-- Mutation: the variable weight of the witness set to `0`; positivity of the variable weight
fails, while the duplicator barrier is independent of it. -/
theorem acKBO_mutation :
    ¬ acKBOLaws { acKBOWitness with w0 := 0 } ∧
      acKBOResult { acKBOWitness with w0 := 0 } :=
  ⟨fun h => absurd h.w0_pos (by decide), acKBO_rejects _⟩

/-! ## AC regression controls C12 and C13 -/

section NativeComparatorControls

open OperatorKO7.SymbolicComparatorBarrier
open OperatorKO7.Methods.PathOrderRows
open OperatorKO7.Methods.OrientationClosure.PathOrderNativeSemantics

/-- C12 fixture: the old lex-status KBO used by the provisional AC comparator. -/
def c12LexKBO : NativeKBOData :=
  { nativeKBOWithStatusWitness with status := fun _ => .lex }

/-- C12 left AC representative. -/
def c12Left : STerm := .wrap (.succ .base) .base

/-- C12 right AC representative. -/
def c12Right : STerm := .wrap .base (.succ .base)

/-- C12 regression: the old lex-status AC comparator relates an AC term to itself, so it is not
an order (it fails well-foundedness through its own self-loop). Permanent control for the AC
row's repair. -/
theorem acKBO_C12_selfLoop : NativeACKBOGt c12LexKBO c12Left c12Left := by
  refine ⟨c12Left, c12Right, Relation.EqvGen.refl _,
    Relation.EqvGen.rel _ _ (ACRearrange.commWrap _ _), ?_⟩
  apply NativeKBOGt.wrapLexLeft
  · rfl
  · intro v
    cases v <;> decide
  · rfl
  · apply NativeKBOGt.precedence
    · intro v
      cases v <;> decide
    · rfl
    · decide

/-- C13 regression: the tied generalized-KBO comparison of `wrap base base` and
`succ (succ base)` is lost under the unary successsor context, so the old comparison is not
context-compatible where the existing generalizedKBO row states the context-compatibility
theorem. Permanent control for the AC row's unary-context diagnostic. -/
theorem acKBO_C13_contextLoss :
    GeneralizedKBOGt generalizedNatKBOWitness (.wrap .base .base) (.succ (.succ .base)) ∧
      ¬ GeneralizedKBOGt generalizedNatKBOWitness
        (.succ (.wrap .base .base)) (.succ (.succ (.succ .base))) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro v
      cases v <;> decide
    · exact Or.inr ⟨rfl, by decide⟩
  · rintro ⟨_, hw | ⟨_, hp⟩⟩
    · norm_num [generalizedKBOWeight, generalizedNatKBOWitness] at hw
    · norm_num [generalizedRootRank, generalizedNatKBOWitness, methodRoot] at hp

end NativeComparatorControls

end OperatorKO7.Methods.OrientationClosure.MethodRowsKBO
