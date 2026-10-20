import Mathlib.Computability.Primrec
import Mathlib.Data.Vector.Basic
import OperatorKO7.Meta.HigherOrderRewriting_SystemTSyntax

/-!
# System T represents every pairing-free primitive recursive function

Relation: `Step` (full contextual one-step reduction of the shared System T carrier)
and its reflexive-transitive closure `StepStar`.
Closure: multi-step `StepStar` for representation; one-step `Step` only as a generator
of `StepStar`.
Strategy: full `Step`, not `stepLO`. The fuelled evaluator `normalizeFuel` appears only
in a `decide` fixture on a closed addition term.
Trust: kernel-only; `decide` fixtures; Mathlib `Nat.Primrec'` / `Nat.Primrec` /
`Primrec.nat_iff`. Target axiom set is the Lean baseline.
Scope: every `Nat.Primrec'` function of every arity, represented by a closed well-typed
System T term of type `naryTy n`; the unary corollary `primrecRepresentation` is the
statement consumed by lane L7a.

Does not prove: that System T represents every total computable function, or that
equality of System T terms is undecidable (that is L7a, using this corollary).
-/

set_option autoImplicit false

namespace OperatorKO7.HigherOrderRewritingPrimrecRepresentation

open OperatorKO7.HigherOrderRewritingSystemT
open List.Vector

#check @Nat.Primrec'
#check @Nat.Primrec'.of_prim
#check @Nat.Primrec'.prim_iff₁
#check @Primrec.nat_iff
#check @Nat.Primrec
#check @List.Vector

/-! ## N-ary types, spines, and numerals -/

/-- The n-ary type `nat → ⋯ → nat` with `n` arrows. -/
def naryTy : Nat → SysTTy
  | 0 => .nat
  | n + 1 => .arrow .nat (naryTy n)

/-- Left-nested application of `t` to a list of arguments. -/
def apps (t : SysTTerm) : List SysTTerm → SysTTerm
  | [] => t
  | a :: as => apps (.app t a) as

/-- Church-free numerals of a length-indexed vector, in head-to-tail order. -/
def numerals : {n : Nat} → List.Vector ℕ n → List SysTTerm
  | 0, _ => []
  | _ + 1, v => natLit (head v) :: numerals (tail v)

/--
Proves: `naryTy 0` is `nat`.
Does not prove: any other arity equation.
Relation: definitional equality of `SysTTy`.
Closure: not applicable.
Strategy: not applicable.
Trust: `decide`.
Scope: arity 0.
-/
theorem naryTy_zero_eq : naryTy 0 = .nat := by decide

/--
Proves: `naryTy 2` is `nat → nat → nat`.
Does not prove: any other arity equation.
Relation: definitional equality of `SysTTy`.
Closure: not applicable.
Strategy: not applicable.
Trust: `decide`.
Scope: arity 2.
-/
theorem naryTy_two_eq : naryTy 2 = .arrow .nat (.arrow .nat .nat) := by decide

/--
Proves: `apps` on a singleton is a single `app`.
Does not prove: the n-ary case.
Relation: definitional equality of `SysTTerm`.
Closure: not applicable.
Strategy: not applicable.
Trust: `decide`.
Scope: one argument.
-/
theorem apps_singleton_eq :
    apps .zero [.succ .zero] = .app .zero (.succ .zero) := by decide

/--
Proves: `apps` on two arguments is left-nested.
Does not prove: the empty spine.
Relation: definitional equality of `SysTTerm`.
Closure: not applicable.
Strategy: not applicable.
Trust: `decide`.
Scope: two arguments.
-/
theorem apps_two_eq :
    apps .zero [.zero, .succ .zero] = .app (.app .zero .zero) (.succ .zero) := by decide

/--
Proves: numerals of the empty vector are `[]`.
Does not prove: any positive length.
Relation: definitional equality.
Closure: not applicable.
Strategy: not applicable.
Trust: `decide`.
Scope: arity 0.
-/
theorem numerals_nil_eq : numerals (nil : List.Vector ℕ 0) = [] := by decide

/--
Proves: numerals of the singleton `0` are `[zero]`.
Does not prove: any other value.
Relation: definitional equality.
Closure: not applicable.
Strategy: not applicable.
Trust: `decide`.
Scope: the 1-vector `cons 0 nil`.
-/
theorem numerals_singleton_eq :
    numerals (cons 0 (nil : List.Vector ℕ 0)) = [.zero] := by decide

/--
Proves: a closed well-typed n-ary System T term `t` computes `f` on every numeral vector.
Does not prove: uniqueness of `t`, or representation of functions outside `Nat.Primrec'`.
Relation: `HasType` in the empty context, and `StepStar` of `apps t (numerals v)`.
Closure: reflexive-transitive.
Strategy: full `Step`.
Trust: kernel-only.
Scope: every arity `n` and every `f : List.Vector ℕ n → ℕ`.
-/
def RepresentsN {n : Nat} (t : SysTTerm) (f : List.Vector ℕ n → ℕ) : Prop :=
  HasType [] t (naryTy n) ∧ ∀ v : List.Vector ℕ n, StepStar (apps t (numerals v)) (natLit (f v))

/-! ## Closedness and substitution on closed terms -/

/-- Every free de Bruijn index of `t` is strictly below `c`. -/
private def ClosedBelow (c : Nat) : SysTTerm → Prop
  | .var n => n < c
  | .lam _ b => ClosedBelow (c + 1) b
  | .app f a => ClosedBelow c f ∧ ClosedBelow c a
  | .zero => True
  | .succ t => ClosedBelow c t
  | .natrec z s n => ClosedBelow c z ∧ ClosedBelow c s ∧ ClosedBelow c n

/-- A term with no free variable. -/
private def Closed (t : SysTTerm) : Prop := ClosedBelow 0 t

private theorem closedBelow_mono {c c' : Nat} {t : SysTTerm} (hle : c ≤ c')
    (h : ClosedBelow c t) : ClosedBelow c' t := by
  induction t generalizing c c' with
  | var n => exact Nat.lt_of_lt_of_le h hle
  | lam A b ih => exact ih (Nat.succ_le_succ hle) h
  | app f a ihf iha => exact ⟨ihf hle h.1, iha hle h.2⟩
  | zero => trivial
  | succ t ih => exact ih hle h
  | natrec z s n ihz ihs ihn =>
      exact ⟨ihz hle h.1, ihs hle h.2.1, ihn hle h.2.2⟩

private theorem shift_of_closedBelow (d c : Nat) {t : SysTTerm}
    (h : ClosedBelow c t) : shift d c t = t := by
  induction t generalizing c with
  | var n =>
      simp only [shift]
      split_ifs with hlt
      · rfl
      · exact (hlt h).elim
  | lam A b ih =>
      simp only [shift]
      exact congrArg (SysTTerm.lam A) (ih (c + 1) h)
  | app f a ihf iha =>
      simp only [shift]
      exact congrArg₂ SysTTerm.app (ihf c h.1) (iha c h.2)
  | zero => rfl
  | succ t ih =>
      simp only [shift]
      exact congrArg SysTTerm.succ (ih c h)
  | natrec z s n ihz ihs ihn =>
      simp only [shift]
      rw [ihz c h.1, ihs c h.2.1, ihn c h.2.2]

private theorem shift_of_closed (d c : Nat) {t : SysTTerm} (h : Closed t) :
    shift d c t = t :=
  shift_of_closedBelow d c (closedBelow_mono (Nat.zero_le c) h)

private theorem subst_of_closedBelow (j : Nat) (u : SysTTerm) {t : SysTTerm}
    (h : ClosedBelow j t) : subst j u t = t := by
  induction t generalizing j u with
  | var n =>
      simp only [subst]
      split_ifs with hlt heq
      · rfl
      · have : n < j := h
        omega
      · have : n < j := h
        omega
  | lam A b ih =>
      simp only [subst]
      exact congrArg (SysTTerm.lam A) (ih (j + 1) (shift 1 0 u) h)
  | app f a ihf iha =>
      simp only [subst]
      exact congrArg₂ SysTTerm.app (ihf j u h.1) (iha j u h.2)
  | zero => rfl
  | succ t ih =>
      simp only [subst]
      exact congrArg SysTTerm.succ (ih j u h)
  | natrec z s n ihz ihs ihn =>
      simp only [subst]
      rw [ihz j u h.1, ihs j u h.2.1, ihn j u h.2.2]

private theorem subst_of_closed (j : Nat) (u : SysTTerm) {t : SysTTerm} (h : Closed t) :
    subst j u t = t :=
  subst_of_closedBelow j u (closedBelow_mono (Nat.zero_le j) h)

private theorem closedBelow_natLit (c k : Nat) : ClosedBelow c (natLit k) := by
  induction k with
  | zero => trivial
  | succ k ih => exact ih

private theorem closed_natLit (k : Nat) : Closed (natLit k) :=
  closedBelow_natLit 0 k

private theorem numerals_length {n : Nat} (v : List.Vector ℕ n) :
    (numerals v).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [numerals, ih]

private theorem numerals_cons {n : Nat} (x : ℕ) (v : List.Vector ℕ n) :
    numerals (cons x v) = natLit x :: numerals v :=
  rfl

private theorem numerals_head_tail {n : Nat} (v : List.Vector ℕ (n + 1)) :
    numerals v = natLit (head v) :: numerals (tail v) :=
  rfl

private theorem closed_mem_numerals {n : Nat} (v : List.Vector ℕ n) :
    ∀ a ∈ numerals v, Closed a := by
  induction n with
  | zero => intro a h; cases h
  | succ n ih =>
      intro a h
      rw [numerals_head_tail] at h
      cases h with
      | head => exact closed_natLit (head v)
      | tail _ ha => exact ih (tail v) a ha

private theorem mem_cons_head {α : Type} (a : α) (l : List α) : a ∈ a :: l :=
  List.mem_cons.mpr (Or.inl rfl)

private theorem mem_cons_tail {α : Type} {a b : α} {l : List α} (h : a ∈ l) : a ∈ b :: l :=
  List.mem_cons.mpr (Or.inr h)

private theorem getD_cons_zero {α : Type} (a : α) (l : List α) (d : α) :
    (a :: l).getD 0 d = a :=
  rfl

private theorem getD_cons_succ {α : Type} (a : α) (l : List α) (n : Nat) (d : α) :
    (a :: l).getD (n + 1) d = l.getD n d :=
  rfl

private theorem numerals_getD_zero {n : Nat} (v : List.Vector ℕ (n + 1)) :
    (numerals v).getD 0 .zero = natLit (head v) :=
  getD_cons_zero (natLit (head v)) (numerals (tail v)) SysTTerm.zero

private theorem numerals_getD_succ {n : Nat} (v : List.Vector ℕ (n + 1)) (j : Nat) :
    (numerals v).getD (j + 1) .zero = (numerals (tail v)).getD j .zero :=
  getD_cons_succ (natLit (head v)) (numerals (tail v)) j SysTTerm.zero

private theorem getD_numerals {n : Nat} (v : List.Vector ℕ n) (j : Nat) (hj : j < n) :
    (numerals v).getD j .zero = natLit (v.get ⟨j, hj⟩) := by
  induction n generalizing j with
  | zero => exact (Nat.not_lt_zero j hj).elim
  | succ n ih =>
      cases j with
      | zero =>
          simp [numerals, get_zero]
      | succ j =>
          have hj' : j < n := Nat.succ_lt_succ_iff.mp hj
          simp only [numerals, getD_cons_succ]
          have hget : v.get ⟨j + 1, hj⟩ = (tail v).get ⟨j, hj'⟩ := by
            rw [← cons_head_tail v]
            rfl
          rw [hget]
          exact ih (tail v) j hj'

private theorem numerals_get {n : Nat} (v : List.Vector ℕ n) (i : Fin n) :
    (numerals v).getD i.val .zero = natLit (v.get i) :=
  getD_numerals v i.val i.isLt

/-! ## `StepStar` congruence -/

private theorem stepStar_appL {f f' : SysTTerm} (a : SysTTerm) (h : StepStar f f') :
    StepStar (.app f a) (.app f' a) :=
  Relation.ReflTransGen.lift (fun t => SysTTerm.app t a) (fun _ _ hs => Step.appL a hs) h

private theorem stepStar_appR (f : SysTTerm) {a a' : SysTTerm} (h : StepStar a a') :
    StepStar (.app f a) (.app f a') :=
  Relation.ReflTransGen.lift (SysTTerm.app f) (fun _ _ hs => Step.appR f hs) h

private theorem stepStar_succ {t t' : SysTTerm} (h : StepStar t t') :
    StepStar (.succ t) (.succ t') :=
  Relation.ReflTransGen.lift SysTTerm.succ (fun _ _ hs => Step.succ hs) h

private theorem stepStar_natrec_z {z z' : SysTTerm} (s n : SysTTerm) (h : StepStar z z') :
    StepStar (.natrec z s n) (.natrec z' s n) :=
  Relation.ReflTransGen.lift (fun t => SysTTerm.natrec t s n)
    (fun _ _ hs => Step.recZ s n hs) h

private theorem stepStar_natrec_s (z : SysTTerm) {s s' : SysTTerm} (n : SysTTerm)
    (h : StepStar s s') :
    StepStar (.natrec z s n) (.natrec z s' n) :=
  Relation.ReflTransGen.lift (fun t => SysTTerm.natrec z t n)
    (fun _ _ hs => Step.recS z n hs) h

private theorem stepStar_natrec_n (z s : SysTTerm) {n n' : SysTTerm} (h : StepStar n n') :
    StepStar (.natrec z s n) (.natrec z s n') :=
  Relation.ReflTransGen.lift (SysTTerm.natrec z s) (fun _ _ hs => Step.recN z s hs) h

private theorem stepStar_apps_fn {t t' : SysTTerm} (h : StepStar t t') (as : List SysTTerm) :
    StepStar (apps t as) (apps t' as) := by
  induction as generalizing t t' with
  | nil => exact h
  | cons a as ih => exact ih (stepStar_appL a h)

private theorem stepStar_natrec_zero (z s : SysTTerm) :
    StepStar (.natrec z s (natLit 0)) z :=
  Relation.ReflTransGen.single (Step.recZero z s)

private theorem stepStar_natrec_succ (z s : SysTTerm) (k : Nat) :
    StepStar (.natrec z s (natLit (k + 1)))
      (.app (.app s (natLit k)) (.natrec z s (natLit k))) :=
  Relation.ReflTransGen.single (Step.recSucc z s (natLit k))

/-! ## Nested lambdas, bound variables, and instantiation -/

private def naryLams : Nat → SysTTerm → SysTTerm
  | 0, b => b
  | n + 1, b => .lam .nat (naryLams n b)

private theorem naryLams_succ (n : Nat) (b : SysTTerm) :
    naryLams (n + 1) b = .lam .nat (naryLams n b) :=
  rfl

/-- The n bound variables in application order: `var (n-1), …, var 0`. -/
private def boundVars : Nat → List SysTTerm
  | 0 => []
  | n + 1 => SysTTerm.var n :: boundVars n

private theorem boundVars_length (n : Nat) : (boundVars n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [boundVars, ih]

private theorem boundVars_getD (n j : Nat) (hj : j < n) :
    (boundVars n).getD j .zero = .var (n - 1 - j) := by
  induction n generalizing j with
  | zero => exact (Nat.not_lt_zero j hj).elim
  | succ n ih =>
      cases j with
      | zero =>
          simp [boundVars]
      | succ j =>
          have hj' : j < n := Nat.succ_lt_succ_iff.mp hj
          simp only [boundVars, getD_cons_succ]
          have : n - (j + 1) = n - 1 - j := by omega
          simpa [this] using ih j hj'

private theorem mem_boundVars {n : Nat} {t : SysTTerm} (ht : t ∈ boundVars n) :
    ∃ k, k < n ∧ t = .var k := by
  induction n with
  | zero => cases ht
  | succ n ih =>
      simp only [boundVars, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact ⟨n, Nat.lt_succ_self n, rfl⟩
      · obtain ⟨k, hk, rfl⟩ := ih ht
        exact ⟨k, Nat.lt_succ_of_lt hk, rfl⟩

/-- Sequential substitution of `args` starting at de Bruijn offset `off`, first argument
at the highest index. On closed arguments this is parallel lookup. -/
private def instFrom (off : Nat) : List SysTTerm → SysTTerm → SysTTerm
  | [], t => t
  | a :: as, t => instFrom off as (subst (off + as.length) a t)

private theorem subst_naryLams_of_closed (n j : Nat) (u b : SysTTerm) (hc : Closed u) :
    subst j u (naryLams n b) = naryLams n (subst (j + n) u b) := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
      have hs : shift 1 0 u = u := shift_of_closed 1 0 hc
      simp only [naryLams, subst, hs]
      rw [ih (j + 1)]
      simp [Nat.add_comm, Nat.add_left_comm]

private theorem instFrom_app (off : Nat) (args : List SysTTerm) (f a : SysTTerm) :
    instFrom off args (.app f a) = .app (instFrom off args f) (instFrom off args a) := by
  induction args generalizing f a with
  | nil => rfl
  | cons x xs ih =>
      simp only [instFrom, subst]
      exact ih _ _

private theorem instFrom_succ (off : Nat) (args : List SysTTerm) (t : SysTTerm) :
    instFrom off args (.succ t) = .succ (instFrom off args t) := by
  induction args generalizing t with
  | nil => rfl
  | cons x xs ih =>
      simp only [instFrom, subst]
      exact ih _

private theorem instFrom_zero (off : Nat) (args : List SysTTerm) :
    instFrom off args .zero = .zero := by
  induction args with
  | nil => rfl
  | cons x xs ih =>
      simp only [instFrom, subst]
      exact ih

private theorem instFrom_natrec (off : Nat) (args : List SysTTerm) (z s n : SysTTerm) :
    instFrom off args (.natrec z s n) =
      .natrec (instFrom off args z) (instFrom off args s) (instFrom off args n) := by
  induction args generalizing z s n with
  | nil => rfl
  | cons x xs ih =>
      simp only [instFrom, subst]
      exact ih _ _ _

private theorem instFrom_lam (off : Nat) (args : List SysTTerm) (A : SysTTy) (b : SysTTerm)
    (hc : ∀ x ∈ args, Closed x) :
    instFrom off args (.lam A b) = .lam A (instFrom (off + 1) args b) := by
  induction args generalizing off b with
  | nil => rfl
  | cons x xs ih =>
      have hx : Closed x := hc x (mem_cons_head x xs)
      have hxs : ∀ y ∈ xs, Closed y := fun y hy => hc y (mem_cons_tail hy)
      have hs : shift 1 0 x = x := shift_of_closed 1 0 hx
      simp only [instFrom]
      have hsubst : subst (off + xs.length) x (.lam A b) =
          .lam A (subst (off + xs.length + 1) x b) := by
        simp [subst, hs]
      rw [hsubst, ih off (subst (off + xs.length + 1) x b) hxs]
      simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

private theorem instFrom_of_closedBelow (off : Nat) (args : List SysTTerm) {t : SysTTerm}
    (h : ClosedBelow off t) : instFrom off args t = t := by
  induction args generalizing t with
  | nil => rfl
  | cons x xs ih =>
      have hs : subst (off + xs.length) x t = t :=
        subst_of_closedBelow (off + xs.length) x (closedBelow_mono (Nat.le_add_right off xs.length) h)
      simp only [instFrom, hs]
      exact ih h

private theorem instFrom_of_closed (off : Nat) (args : List SysTTerm) {t : SysTTerm}
    (h : Closed t) : instFrom off args t = t :=
  instFrom_of_closedBelow off args (closedBelow_mono (Nat.zero_le off) h)

private theorem instFrom_var_lt (off : Nat) (args : List SysTTerm) (k : Nat) (hk : k < off) :
    instFrom off args (.var k) = .var k := by
  induction args with
  | nil => rfl
  | cons x xs ih =>
      have hk' : k < off + xs.length := Nat.lt_of_lt_of_le hk (Nat.le_add_right off xs.length)
      simp only [instFrom, subst, hk']
      exact ih

private theorem instFrom_var_hit (off : Nat) (args : List SysTTerm)
    (hc : ∀ x ∈ args, Closed x) (k : Nat) (h1 : off ≤ k) (h2 : k < off + args.length) :
    instFrom off args (.var k) = args.getD (off + args.length - 1 - k) .zero := by
  induction args generalizing k with
  | nil =>
      simp at h2
      omega
  | cons x xs ih =>
      have hx : Closed x := hc x (mem_cons_head x xs)
      have hxs : ∀ y ∈ xs, Closed y := fun y hy => hc y (mem_cons_tail hy)
      simp only [instFrom]
      have hk_le : k ≤ off + xs.length := by
        have : k < off + (xs.length + 1) := by simpa [List.length_cons] using h2
        omega
      by_cases hlt : k < off + xs.length
      · have hsubst : subst (off + xs.length) x (.var k) = .var k := by
          simp [subst, hlt]
        rw [hsubst, ih hxs k h1 hlt]
        have hidx : off + (x :: xs).length - 1 - k = (off + xs.length - 1 - k) + 1 := by
          simp [List.length_cons]; omega
        rw [hidx, getD_cons_succ]
      · have hk_eq : k = off + xs.length := Nat.le_antisymm hk_le (Nat.le_of_not_gt hlt)
        have hsubst : subst (off + xs.length) x (.var k) = x := by
          simp only [subst]
          rw [if_neg (by omega), if_pos hk_eq]
        rw [hsubst, instFrom_of_closed off xs hx]
        have hidx : off + (x :: xs).length - 1 - k = 0 := by
          simp [List.length_cons, hk_eq]
        rw [hidx, getD_cons_zero]

private theorem instFrom_var_hit_index (off : Nat) (args : List SysTTerm)
    (hc : ∀ x ∈ args, Closed x) (k idx : Nat)
    (h1 : off ≤ k) (h2 : k < off + args.length)
    (hidx : off + args.length - 1 - k = idx) :
    instFrom off args (.var k) = args.getD idx .zero := by
  rw [← hidx]
  exact instFrom_var_hit off args hc k h1 h2

private theorem instFrom_apps (off : Nat) (args : List SysTTerm) (t : SysTTerm)
    (as : List SysTTerm) :
    instFrom off args (apps t as) =
      apps (instFrom off args t) (as.map (instFrom off args)) := by
  induction as generalizing t with
  | nil => rfl
  | cons a as ih =>
      simp only [apps, List.map]
      rw [ih, instFrom_app]

private theorem subst_apps (j : Nat) (u t : SysTTerm) (as : List SysTTerm) :
    subst j u (apps t as) = apps (subst j u t) (as.map (subst j u)) := by
  induction as generalizing t with
  | nil => rfl
  | cons a as ih =>
      simp only [apps, List.map]
      rw [ih, subst]

private theorem stepStar_apps_naryLams (args : List SysTTerm) (b : SysTTerm)
    (hc : ∀ a ∈ args, Closed a) :
    StepStar (apps (naryLams args.length b) args) (instFrom 0 args b) := by
  induction args generalizing b with
  | nil => exact Relation.ReflTransGen.refl
  | cons a as ih =>
      have ha : Closed a := hc a (mem_cons_head a as)
      have has : ∀ x ∈ as, Closed x := fun x hx => hc x (mem_cons_tail hx)
      have hbeta : Step (.app (.lam .nat (naryLams as.length b)) a)
          (subst 0 a (naryLams as.length b)) :=
        Step.beta .nat (naryLams as.length b) a
      have hsubst : subst 0 a (naryLams as.length b) = naryLams as.length (subst as.length a b) := by
        simpa using subst_naryLams_of_closed as.length 0 a b ha
      have h1 : StepStar
          (apps (.app (.lam .nat (naryLams as.length b)) a) as)
          (apps (naryLams as.length (subst as.length a b)) as) := by
        have hcong := stepStar_apps_fn (Relation.ReflTransGen.single hbeta) as
        simpa [hsubst] using hcong
      have h2 := ih (subst as.length a b) has
      have happs : apps (naryLams (a :: as).length b) (a :: as) =
          apps (.app (.lam .nat (naryLams as.length b)) a) as := rfl
      have hinst : instFrom 0 (a :: as) b = instFrom 0 as (subst as.length a b) := by
        simp only [instFrom, Nat.zero_add]
      rw [happs, hinst]
      exact h1.trans h2

/-! ## Typing lemmas -/

private theorem getElem?_mono {Γ Δ : List SysTTy}
    (hmono : ∀ (n : Nat) (B : SysTTy), Γ[n]? = some B → Δ[n]? = some B)
    {n : Nat} {A : SysTTy} (hget : Γ[n]? = some A) : Δ[n]? = some A :=
  hmono n A hget

private theorem hasType_mono {Γ : List SysTTy} {t : SysTTerm} {ty : SysTTy}
    (h : HasType Γ t ty) (Δ : List SysTTy)
    (hmono : ∀ (n : Nat) (B : SysTTy), Γ[n]? = some B → Δ[n]? = some B) :
    HasType Δ t ty := by
  induction h generalizing Δ with
  | var hget => exact HasType.var (getElem?_mono hmono hget)
  | @lam Γ A B b hb ih =>
      refine HasType.lam (ih (A :: Δ) ?_)
      intro n C hget
      cases n with
      | zero => simpa using hget
      | succ n =>
          have hΓ : Γ[n]? = some C := by simpa using hget
          simpa using hmono n C hΓ
  | app hf ha ihf iha => exact HasType.app (ihf Δ hmono) (iha Δ hmono)
  | zero => exact HasType.zero
  | succ ht ih => exact HasType.succ (ih Δ hmono)
  | natrec hz hs hn ihz ihs ihn =>
      exact HasType.natrec (ihz Δ hmono) (ihs Δ hmono) (ihn Δ hmono)

private theorem hasType_nil_weaken {Δ : List SysTTy} {t : SysTTerm} {A : SysTTy}
    (h : HasType [] t A) : HasType Δ t A :=
  hasType_mono h Δ (fun n B hget => by simp at hget)

private theorem getElem?_replicate_nat (n k : Nat) (hk : k < n) :
    (List.replicate n SysTTy.nat)[k]? = some SysTTy.nat := by
  induction n generalizing k with
  | zero => exact (Nat.not_lt_zero k hk).elim
  | succ n ih =>
      cases k with
      | zero =>
          simp [List.replicate]
      | succ k =>
          have hk' : k < n := Nat.succ_lt_succ_iff.mp hk
          simpa [List.replicate] using ih k hk'

private theorem hasType_replicate_var {n k : Nat} (hk : k < n) :
    HasType (List.replicate n SysTTy.nat) (.var k) .nat :=
  HasType.var (getElem?_replicate_nat n k hk)

private theorem replicate_cons_comm (n : Nat) (Γ : List SysTTy) :
    List.replicate n SysTTy.nat ++ SysTTy.nat :: Γ =
      SysTTy.nat :: (List.replicate n SysTTy.nat ++ Γ) := by
  induction n with
  | zero => simp [List.replicate]
  | succ n ih => simp [List.replicate, ih]

private theorem hasType_naryLams {n : Nat} {b : SysTTerm} {Γ : List SysTTy}
    (h : HasType (List.replicate n SysTTy.nat ++ Γ) b .nat) :
    HasType Γ (naryLams n b) (naryTy n) := by
  induction n generalizing Γ with
  | zero => simpa [naryLams, naryTy] using h
  | succ n ih =>
      refine HasType.lam ?_
      have h' : HasType (List.replicate n SysTTy.nat ++ SysTTy.nat :: Γ) b .nat := by
        simpa [List.replicate, replicate_cons_comm n Γ] using h
      exact ih h'

private theorem hasType_apps {Γ : List SysTTy} {t : SysTTerm} {as : List SysTTerm}
    (ht : HasType Γ t (naryTy as.length))
    (has : ∀ a ∈ as, HasType Γ a .nat) : HasType Γ (apps t as) .nat := by
  induction as generalizing t with
  | nil => simpa [apps, naryTy] using ht
  | cons a as ih =>
      have ha : HasType Γ a .nat := has a (mem_cons_head a as)
      have ht' : HasType Γ (.app t a) (naryTy as.length) :=
        HasType.app (by simpa [naryTy] using ht) ha
      exact ih ht' (fun x hx => has x (mem_cons_tail hx))

private theorem getElem?_some_lt {α : Type} {l : List α} {n : Nat} {a : α}
    (h : l[n]? = some a) : n < l.length := by
  induction l generalizing n with
  | nil => simp at h
  | cons b l ih =>
      cases n with
      | zero => simp
      | succ n =>
          exact Nat.succ_lt_succ (ih (by simpa using h))

private theorem hasType_boundVars (n : Nat) (Γ : List SysTTy)
    (hΓ : ∀ k, k < n → Γ[k]? = some SysTTy.nat) :
    ∀ t ∈ boundVars n, HasType Γ t .nat := by
  intro t ht
  obtain ⟨k, hk, rfl⟩ := mem_boundVars ht
  exact HasType.var (hΓ k hk)

private theorem hasType_natLit {Γ : List SysTTy} (k : Nat) : HasType Γ (natLit k) .nat := by
  induction k with
  | zero => exact HasType.zero
  | succ k ih => exact HasType.succ ih

private theorem closed_of_hasType_nil {t : SysTTerm} {A : SysTTy} (h : HasType [] t A) :
    Closed t := by
  have aux : ∀ {Γ : List SysTTy} {t : SysTTerm} {A : SysTTy},
      HasType Γ t A → ClosedBelow Γ.length t := by
    intro Γ t A h
    induction h with
    | var hget => exact getElem?_some_lt hget
    | lam _ ih => exact ih
    | app _ _ ihf iha => exact ⟨ihf, iha⟩
    | zero => trivial
    | succ _ ih => exact ih
    | natrec _ _ _ ihz ihs ihn => exact ⟨ihz, ihs, ihn⟩
  simpa [Closed] using aux h

private theorem getD_map {α β : Type} (f : α → β) (l : List α) (i : Nat) (dα : α) (dβ : β)
    (hi : i < l.length) : (l.map f).getD i dβ = f (l.getD i dα) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
      cases i with
      | zero => simp [List.map]
      | succ i =>
          simp only [List.map, getD_cons_succ]
          exact ih i (by simp at hi; omega)

private theorem list_eq_getD {α : Type} (l₁ l₂ : List α) (d : α)
    (hlen : l₁.length = l₂.length)
    (h : ∀ i, i < l₁.length → l₁.getD i d = l₂.getD i d) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => rfl
      | cons => simp at hlen
  | cons a l₁ ih =>
      cases l₂ with
      | nil => simp at hlen
      | cons b l₂ =>
          have ha : a = b := by
            have := h 0 (by simp)
            simpa [getD_cons_zero] using this
          have hlen' : l₁.length = l₂.length := by simp at hlen; exact hlen
          have h' : ∀ i, i < l₁.length → l₁.getD i d = l₂.getD i d := by
            intro i hi
            have := h (i + 1) (by simp; omega)
            simpa [getD_cons_succ] using this
          rw [ha, ih l₂ hlen' h']

private theorem map_subst_of_closed (j : Nat) (u : SysTTerm) (as : List SysTTerm)
    (hc : ∀ a ∈ as, Closed a) : as.map (subst j u) = as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp [subst_of_closed j u (hc a (mem_cons_head a as)),
        ih (fun x hx => hc x (mem_cons_tail hx))]

private theorem hasType_naryLams_nil {n : Nat} {b : SysTTerm}
    (h : HasType (List.replicate n SysTTy.nat) b .nat) :
    HasType [] (naryLams n b) (naryTy n) :=
  hasType_naryLams (Γ := []) (by simpa using h)

private def tabulate {α : Type} : (n : Nat) → (Fin n → α) → List α
  | 0, _ => []
  | n + 1, f => f 0 :: tabulate n (fun i => f i.succ)

private theorem tabulate_length {α : Type} (n : Nat) (f : Fin n → α) :
    (tabulate n f).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tabulate, ih]

private theorem map_tabulate {α β : Type} {n : Nat} (f : α → β) (g : Fin n → α) :
    (tabulate n g).map f = tabulate n (fun i => f (g i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [tabulate, List.map]
      rw [ih]

private theorem mem_tabulate {α : Type} {n : Nat} {f : Fin n → α} {a : α} :
    a ∈ tabulate n f → ∃ i, a = f i := by
  induction n with
  | zero => intro h; cases h
  | succ n ih =>
      intro h
      simp only [tabulate, List.mem_cons] at h
      cases h with
      | inl h => exact ⟨(0 : Fin (n + 1)), h⟩
      | inr h =>
          obtain ⟨i, hi⟩ := ih h
          exact ⟨i.succ, hi⟩

private theorem numerals_ofFn {n : Nat} (f : Fin n → ℕ) :
    numerals (ofFn f) = tabulate n (fun i => natLit (f i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [ofFn, numerals_cons, tabulate, ih]

private theorem stepStar_apps_tabulate {n : Nat} (t : SysTTerm)
    {f g : Fin n → SysTTerm} (h : ∀ i, StepStar (f i) (g i)) :
    StepStar (apps t (tabulate n f)) (apps t (tabulate n g)) := by
  induction n generalizing t with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
      have h1 : StepStar
          (apps (.app t (f 0)) (tabulate n (fun i => f i.succ)))
          (apps (.app t (g 0)) (tabulate n (fun i => f i.succ))) :=
        stepStar_apps_fn (stepStar_appR t (h 0)) _
      have h2 := ih (.app t (g 0)) (fun i => h i.succ)
      simpa [tabulate, apps] using h1.trans h2

private theorem exists_fin_fn {n : Nat} {P : Fin n → SysTTerm → Prop}
    (h : ∀ i : Fin n, ∃ t, P i t) :
    ∃ ts : Fin n → SysTTerm, ∀ i, P i (ts i) := by
  induction n with
  | zero => exact ⟨Fin.elim0, fun i => nomatch i⟩
  | succ n ih =>
      obtain ⟨t0, h0⟩ := h 0
      obtain ⟨ts, hts⟩ := ih (fun i => h i.succ)
      refine ⟨Fin.cons t0 ts, ?_⟩
      intro i
      cases i using Fin.cases with
      | zero => simpa [Fin.cons_zero] using h0
      | succ i => simpa [Fin.cons_succ] using hts i

/-! ## One representing term per `Primrec'` constructor -/

/--
Proves: the constant `zero` represents the 0-ary zero function.
Does not prove: representation of any positive constant (that uses `succ` and `comp`).
Relation: `StepStar` on `apps`; here both sides are `zero`.
Closure: reflexive.
Strategy: full `Step`.
Trust: kernel-only.
Scope: the unique 0-ary vector.
-/
theorem represents_zero : RepresentsN SysTTerm.zero (fun _ : List.Vector ℕ 0 => 0) := by
  refine ⟨HasType.zero, ?_⟩
  intro v
  exact Relation.ReflTransGen.refl

/--
Proves: `λx. succ x` represents unary successor.
Does not prove: successor in any other arity.
Relation: one `Step.beta`, then definitional equality with `natLit (n+1)`.
Closure: one-step, viewed as `StepStar`.
Strategy: full `Step`.
Trust: kernel-only.
Scope: every 1-vector.
-/
theorem represents_succ :
    RepresentsN (.lam .nat (.succ (.var 0))) (fun v : List.Vector ℕ 1 => Nat.succ (head v)) := by
  refine ⟨HasType.lam (HasType.succ (HasType.var (by decide))), ?_⟩
  intro v
  have happs : apps (.lam .nat (.succ (.var 0))) (numerals v) =
      .app (.lam .nat (.succ (.var 0))) (natLit (head v)) := by
    rw [numerals_head_tail]
    rfl
  rw [happs]
  have hsubst : subst 0 (natLit (head v)) (.succ (.var 0)) = natLit (Nat.succ (head v)) := by
    simp [subst, natLit]
  exact Relation.ReflTransGen.single (hsubst ▸ Step.beta .nat (.succ (.var 0)) (natLit (head v)))

private def getTerm (n : Nat) (i : Fin n) : SysTTerm :=
  naryLams n (.var (n - 1 - i.val))

/--
Proves: the n-ary projection onto index `i` is represented by n nested lambdas
returning de Bruijn index `n-1-i`.
Does not prove: projections of non-numeral arguments.
Relation: `StepStar` through `n` betas, then lookup of the closed numeral.
Closure: reflexive-transitive.
Strategy: full `Step`.
Trust: kernel-only.
Scope: every `n` and every `i : Fin n`.
-/
theorem represents_get {n : Nat} (i : Fin n) :
    RepresentsN (getTerm n i) (fun v => get v i) := by
  refine ⟨?ty, ?red⟩
  · unfold getTerm
    refine hasType_naryLams_nil ?_
    simpa using hasType_replicate_var (n := n) (k := n - 1 - i.val) (by omega)
  · intro v
    have hc : ∀ a ∈ numerals v, Closed a := closed_mem_numerals v
    have hlen : (numerals v).length = n := numerals_length v
    have hred : StepStar (apps (naryLams n (.var (n - 1 - i.val))) (numerals v))
        (instFrom 0 (numerals v) (.var (n - 1 - i.val))) := by
      simpa [hlen] using stepStar_apps_naryLams (numerals v) (.var (n - 1 - i.val)) hc
    have hhit := (instFrom_var_hit_index 0 (numerals v) hc (n - 1 - i.val) i.val
        (Nat.zero_le _) (by omega) (by rw [hlen]; omega))
    have hget := numerals_get v i
    unfold getTerm
    refine hred.trans ?_
    rw [hhit, hget]

private def compTerm {m n : Nat} (F : SysTTerm) (Gs : Fin n → SysTTerm) : SysTTerm :=
  naryLams m (apps F (tabulate n (fun i => apps (Gs i) (boundVars m))))

private theorem closed_of_representsN {n : Nat} {t : SysTTerm} {f : List.Vector ℕ n → ℕ}
    (h : RepresentsN t f) : Closed t :=
  closed_of_hasType_nil h.1

/--
Proves: if `F` represents n-ary `f` and each `Gs i` represents m-ary `g i`, then
`compTerm F Gs` represents `fun a => f (ofFn fun i => g i a)`.
Does not prove: composition of open (non-closed) representatives.
Relation: `StepStar` through m betas, then each inner application, then `F`.
Closure: reflexive-transitive.
Strategy: full `Step`.
Trust: kernel-only.
Scope: every arities `m, n` and every `Primrec'.comp` instance.
-/
theorem represents_comp {m n : Nat}
    {f : List.Vector ℕ n → ℕ} {g : Fin n → List.Vector ℕ m → ℕ}
    {F : SysTTerm} {Gs : Fin n → SysTTerm}
    (hF : RepresentsN F f) (hG : ∀ i, RepresentsN (Gs i) (g i)) :
    RepresentsN (compTerm (m := m) (n := n) F Gs)
      (fun a => f (ofFn fun i => g i a)) := by
  refine ⟨?ty, ?red⟩
  · unfold compTerm
    refine hasType_naryLams_nil ?_
    let Γ := List.replicate m SysTTy.nat
    have hFΓ : HasType Γ F (naryTy n) := hasType_nil_weaken hF.1
    have hlen : (tabulate n (fun i => apps (Gs i) (boundVars m))).length = n :=
      tabulate_length n _
    have ht : HasType Γ F (naryTy (tabulate n (fun i => apps (Gs i) (boundVars m))).length) := by
      simpa [hlen] using hFΓ
    refine hasType_apps ht ?_
    intro a ha
    obtain ⟨i, rfl⟩ := mem_tabulate ha
    have hGi : HasType Γ (Gs i) (naryTy m) := hasType_nil_weaken (hG i).1
    have hlenB : (boundVars m).length = m := boundVars_length m
    have hGi' : HasType Γ (Gs i) (naryTy (boundVars m).length) := by simpa [hlenB] using hGi
    refine hasType_apps hGi' ?_
    exact hasType_boundVars m Γ (fun k hk => getElem?_replicate_nat m k hk)
  · intro v
    have hc : ∀ a ∈ numerals v, Closed a := closed_mem_numerals v
    have hlen : (numerals v).length = m := numerals_length v
    have hFcl : Closed F := closed_of_representsN hF
    have hGcl : ∀ i, Closed (Gs i) := fun i => closed_of_representsN (hG i)
    let body := apps F (tabulate n (fun i => apps (Gs i) (boundVars m)))
    have hred : StepStar (apps (naryLams m body) (numerals v)) (instFrom 0 (numerals v) body) := by
      simpa [hlen] using stepStar_apps_naryLams (numerals v) body hc
    have hinstF : instFrom 0 (numerals v) F = F := instFrom_of_closed 0 (numerals v) hFcl
    have hinstBody : instFrom 0 (numerals v) body =
        apps F (tabulate n (fun i => instFrom 0 (numerals v) (apps (Gs i) (boundVars m)))) := by
      simp only [body]
      rw [instFrom_apps, hinstF, map_tabulate]
    have hbound : (boundVars m).map (instFrom 0 (numerals v)) = numerals v := by
      refine list_eq_getD _ _ SysTTerm.zero ?hlen ?hget
      · simp [boundVars_length, numerals_length]
      · intro j hj
        have hjn : j < m := by simpa [boundVars_length] using hj
        have hmap := getD_map (instFrom 0 (numerals v)) (boundVars m) j .zero .zero
          (by simpa [boundVars_length] using hjn)
        rw [hmap, boundVars_getD m j hjn]
        exact instFrom_var_hit_index 0 (numerals v) hc (m - 1 - j) j
          (Nat.zero_le _) (by omega) (by rw [hlen]; omega)
    have hinstGi : ∀ i,
        instFrom 0 (numerals v) (apps (Gs i) (boundVars m)) = apps (Gs i) (numerals v) := by
      intro i
      rw [instFrom_apps, instFrom_of_closed 0 (numerals v) (hGcl i), hbound]
    unfold compTerm
    refine hred.trans ?_
    rw [hinstBody]
    have hinner : StepStar
        (apps F (tabulate n (fun i => instFrom 0 (numerals v) (apps (Gs i) (boundVars m)))))
        (apps F (tabulate n (fun i => natLit (g i v)))) := by
      have hmap : ∀ i,
          StepStar (instFrom 0 (numerals v) (apps (Gs i) (boundVars m))) (natLit (g i v)) := by
        intro i
        rw [hinstGi]
        exact (hG i).2 v
      exact stepStar_apps_tabulate F hmap
    refine hinner.trans ?_
    have hnum : tabulate n (fun i => natLit (g i v)) = numerals (ofFn fun i => g i v) :=
      (numerals_ofFn (fun i => g i v)).symm
    rw [hnum]
    exact hF.2 (ofFn fun i => g i v)

private def precSuccBody (G : SysTTerm) (paramTerms : List SysTTerm) : SysTTerm :=
  .lam .nat (.lam .nat (apps G (.var 1 :: .var 0 :: paramTerms)))

private def precBody (n : Nat) (F G : SysTTerm) : SysTTerm :=
  .natrec (apps F (boundVars n))
    (precSuccBody G ((boundVars n).map (shift 2 0)))
    (.var n)

private def precTerm (n : Nat) (F G : SysTTerm) : SysTTerm :=
  naryLams (n + 1) (precBody n F G)

private theorem shift_var_ge_zero (d k : Nat) : shift d 0 (.var k) = .var (k + d) := by
  simp [shift]

private theorem map_shift_boundVars_getD (n j : Nat) (hj : j < n) :
    ((boundVars n).map (shift 2 0)).getD j .zero = .var (n - 1 - j + 2) := by
  rw [getD_map (shift 2 0) (boundVars n) j .zero .zero (by simpa [boundVars_length] using hj)]
  rw [boundVars_getD n j hj, shift_var_ge_zero]

private theorem instFrom_boundVars_tail {n : Nat} (v : List.Vector ℕ (n + 1)) :
    (boundVars n).map (instFrom 0 (numerals v)) = numerals (tail v) := by
  refine list_eq_getD _ _ SysTTerm.zero ?hlen ?hget
  · simp [boundVars_length, numerals_length]
  · intro j hj
    have hjn : j < n := by simpa [boundVars_length] using hj
    have hc : ∀ a ∈ numerals v, Closed a := closed_mem_numerals v
    have hlen : (numerals v).length = n + 1 := numerals_length v
    have hmap := getD_map (instFrom 0 (numerals v)) (boundVars n) j .zero .zero
      (by simpa [boundVars_length] using hjn)
    rw [hmap, boundVars_getD n j hjn]
    have hhit := (instFrom_var_hit_index 0 (numerals v) hc (n - 1 - j) (j + 1)
      (Nat.zero_le _) (by omega) (by rw [hlen]; omega))
    have hget : (numerals v).getD (j + 1) .zero = (numerals (tail v)).getD j .zero := by
      rw [numerals, getD_cons_succ]
    exact hhit.trans hget

private theorem instFrom_shifted_boundVars_tail {n : Nat} (v : List.Vector ℕ (n + 1)) :
    ((boundVars n).map (shift 2 0)).map (instFrom 2 (numerals v)) = numerals (tail v) := by
  refine list_eq_getD _ _ SysTTerm.zero ?hlen ?hget
  · simp [boundVars_length, numerals_length]
  · intro j hj
    have hjn : j < n := by simpa [boundVars_length] using hj
    have hc : ∀ a ∈ numerals v, Closed a := closed_mem_numerals v
    have hlen : (numerals v).length = n + 1 := numerals_length v
    have hmap := getD_map (instFrom 2 (numerals v)) ((boundVars n).map (shift 2 0)) j
      .zero .zero (by simpa [boundVars_length] using hjn)
    rw [hmap, map_shift_boundVars_getD n j hjn]
    have hhit := (instFrom_var_hit_index 2 (numerals v) hc (n - 1 - j + 2) (j + 1)
      (by omega) (by omega) (by rw [hlen]; omega))
    have hget : (numerals v).getD (j + 1) .zero = (numerals (tail v)).getD j .zero := by
      rw [numerals, getD_cons_succ]
    exact hhit.trans hget

private theorem instFrom_precSuccBody {n : Nat} (G : SysTTerm) (v : List.Vector ℕ (n + 1))
    (hGcl : Closed G) :
    instFrom 0 (numerals v) (precSuccBody G ((boundVars n).map (shift 2 0))) =
      precSuccBody G (numerals (tail v)) := by
  have hc : ∀ a ∈ numerals v, Closed a := closed_mem_numerals v
  unfold precSuccBody
  rw [instFrom_lam 0 (numerals v) .nat _ hc]
  rw [instFrom_lam 1 (numerals v) .nat _ hc]
  have hG : instFrom 2 (numerals v) G = G := instFrom_of_closed 2 (numerals v) hGcl
  have h1 : instFrom 2 (numerals v) (.var 1) = .var 1 := instFrom_var_lt 2 (numerals v) 1 (by omega)
  have h0 : instFrom 2 (numerals v) (.var 0) = .var 0 := instFrom_var_lt 2 (numerals v) 0 (by omega)
  rw [instFrom_apps, hG]
  apply congrArg (SysTTerm.lam .nat)
  apply congrArg (SysTTerm.lam .nat)
  apply congrArg (apps G)
  simp only [List.map]
  rw [h1, h0]
  refine congrArg (List.cons _) (congrArg (List.cons _) ?_)
  exact instFrom_shifted_boundVars_tail v

private theorem numerals_cons₂ {n : Nat} (y IH : ℕ) (params : List.Vector ℕ n) :
    numerals (y ::ᵥ IH ::ᵥ params) = natLit y :: natLit IH :: numerals params := by
  simp [numerals_cons]

private theorem stepStar_prec_eval {n : Nat}
    {f : List.Vector ℕ n → ℕ} {g : List.Vector ℕ (n + 2) → ℕ}
    (F G : SysTTerm) (params : List.Vector ℕ n)
    (hF : RepresentsN F f) (hG : RepresentsN G g) :
    ∀ k : Nat,
      StepStar
        (.natrec (apps F (numerals params)) (precSuccBody G (numerals params)) (natLit k))
        (natLit (k.rec (f params) fun y IH => g (y ::ᵥ IH ::ᵥ params))) := by
  intro k
  induction k with
  | zero =>
      refine (stepStar_natrec_zero _ _).trans ?_
      exact hF.2 params
  | succ k ih =>
      have hunf := stepStar_natrec_succ (apps F (numerals params))
        (precSuccBody G (numerals params)) k
      have hIH : StepStar
          (.app (.app (precSuccBody G (numerals params)) (natLit k))
            (.natrec (apps F (numerals params)) (precSuccBody G (numerals params)) (natLit k)))
          (.app (.app (precSuccBody G (numerals params)) (natLit k))
            (natLit (k.rec (f params) fun y IH => g (y ::ᵥ IH ::ᵥ params)))) :=
        stepStar_appR _ ih
      let IHVal : ℕ := k.rec (f params) (fun y IHv => g (y ::ᵥ IHv ::ᵥ params))
      have hbeta1 : StepStar
          (.app (precSuccBody G (numerals params)) (natLit k))
          (.lam .nat (subst 1 (natLit k)
            (apps G (.var 1 :: .var 0 :: numerals params)))) := by
        unfold precSuccBody
        have hs : shift 1 0 (natLit k) = natLit k := shift_of_closed 1 0 (closed_natLit k)
        have : subst 0 (natLit k)
            (.lam .nat (apps G (.var 1 :: .var 0 :: numerals params))) =
            .lam .nat (subst 1 (natLit k) (apps G (.var 1 :: .var 0 :: numerals params))) := by
          simp [subst, hs]
        exact Relation.ReflTransGen.single (this ▸
          Step.beta .nat (.lam .nat (apps G (.var 1 :: .var 0 :: numerals params))) (natLit k))
      have hbeta1app : StepStar
          (.app (.app (precSuccBody G (numerals params)) (natLit k)) (natLit IHVal))
          (.app (.lam .nat (subst 1 (natLit k)
            (apps G (.var 1 :: .var 0 :: numerals params)))) (natLit IHVal)) :=
        stepStar_appL _ hbeta1
      have hsubst1 : subst 1 (natLit k) (apps G (.var 1 :: .var 0 :: numerals params)) =
          apps G (natLit k :: .var 0 :: numerals params) := by
        have hGcl : Closed G := closed_of_representsN hG
        have hG : subst 1 (natLit k) G = G := subst_of_closed 1 (natLit k) hGcl
        have hparams : (numerals params).map (subst 1 (natLit k)) = numerals params :=
          map_subst_of_closed 1 (natLit k) (numerals params) (closed_mem_numerals params)
        have hv1 : subst 1 (natLit k) (.var 1) = natLit k := by
          simp [subst]
        have hv0 : subst 1 (natLit k) (.var 0) = .var 0 := by
          simp [subst]
        rw [subst_apps, hG]
        simp only [List.map]
        rw [hv1, hv0, hparams]
      have hbeta2 : StepStar
          (.app (.lam .nat (subst 1 (natLit k)
            (apps G (.var 1 :: .var 0 :: numerals params)))) (natLit IHVal))
          (apps G (natLit k :: natLit IHVal :: numerals params)) := by
        rw [hsubst1]
        have hGcl : Closed G := closed_of_representsN hG
        have hG : subst 0 (natLit IHVal) G = G := subst_of_closed 0 (natLit IHVal) hGcl
        have hk : subst 0 (natLit IHVal) (natLit k) = natLit k :=
          subst_of_closed 0 (natLit IHVal) (closed_natLit k)
        have hparams : (numerals params).map (subst 0 (natLit IHVal)) = numerals params :=
          map_subst_of_closed 0 (natLit IHVal) (numerals params) (closed_mem_numerals params)
        have hbody : subst 0 (natLit IHVal) (apps G (natLit k :: .var 0 :: numerals params)) =
            apps G (natLit k :: natLit IHVal :: numerals params) := by
          have hv0 : subst 0 (natLit IHVal) (.var 0) = natLit IHVal := by
            simp [subst]
          rw [subst_apps, hG]
          simp only [List.map]
          rw [hk, hv0, hparams]
        exact Relation.ReflTransGen.single (hbody ▸
          Step.beta .nat (apps G (natLit k :: .var 0 :: numerals params)) (natLit IHVal))
      have hGred : StepStar (apps G (natLit k :: natLit IHVal :: numerals params))
          (natLit (g (k ::ᵥ IHVal ::ᵥ params))) := by
        have : numerals (k ::ᵥ IHVal ::ᵥ params) = natLit k :: natLit IHVal :: numerals params :=
          numerals_cons₂ k IHVal params
        simpa [this] using hG.2 (k ::ᵥ IHVal ::ᵥ params)
      refine hunf.trans (hIH.trans ?_)
      exact (hbeta1app.trans hbeta2).trans hGred

/--
Proves: if `F` represents the n-ary base and `G` the (n+2)-ary step, then `precTerm n F G`
represents Mathlib's `Primrec'.prec` recursor.
Does not prove: representation of course-of-values recursion, or of partial recursive
functions.
Relation: `StepStar` through `n+1` betas, then `natrec` unfolding on the head numeral.
Closure: reflexive-transitive.
Strategy: full `Step`.
Trust: kernel-only.
Scope: every arity `n` and every `Primrec'.prec` instance.
-/
theorem represents_prec {n : Nat}
    {f : List.Vector ℕ n → ℕ} {g : List.Vector ℕ (n + 2) → ℕ}
    {F G : SysTTerm} (hF : RepresentsN F f) (hG : RepresentsN G g) :
    RepresentsN (precTerm n F G)
      (fun v : List.Vector ℕ (n + 1) =>
        (head v).rec (f (tail v)) fun y IH => g (y ::ᵥ IH ::ᵥ tail v)) := by
  refine ⟨?ty, ?red⟩
  · unfold precTerm precBody
    refine hasType_naryLams_nil ?_
    let Γ := List.replicate (n + 1) SysTTy.nat
    have hFΓ : HasType Γ F (naryTy n) := hasType_nil_weaken hF.1
    have hlenB : (boundVars n).length = n := boundVars_length n
    have hF' : HasType Γ F (naryTy (boundVars n).length) := by simpa [hlenB] using hFΓ
    have hz : HasType Γ (apps F (boundVars n)) .nat :=
      hasType_apps hF' (hasType_boundVars n Γ (fun k hk => getElem?_replicate_nat (n + 1) k (by omega)))
    have hn : HasType Γ (.var n) .nat := hasType_replicate_var (n := n + 1) (k := n) (Nat.lt_succ_self n)
    refine HasType.natrec hz ?_ hn
    unfold precSuccBody
    refine HasType.lam (HasType.lam ?_)
    let Δ := SysTTy.nat :: SysTTy.nat :: Γ
    have hΔ : Δ = List.replicate (n + 3) SysTTy.nat := by
      simp [Δ, Γ, List.replicate]
    have hGΔ : HasType Δ G (naryTy (n + 2)) := hasType_nil_weaken hG.1
    have hargs : ∀ a ∈ (.var 1 :: .var 0 :: (boundVars n).map (shift 2 0)), HasType Δ a .nat := by
      intro a ha
      rw [hΔ]
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hasType_replicate_var (n := n + 3) (k := 1) (by omega)
      · rcases ha with rfl | ha
        · exact hasType_replicate_var (n := n + 3) (k := 0) (by omega)
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
          obtain ⟨k, hk, rfl⟩ := mem_boundVars hu
          rw [shift_var_ge_zero]
          exact hasType_replicate_var (n := n + 3) (k := k + 2) (by omega)
    have hlenA : (.var 1 :: .var 0 :: (boundVars n).map (shift 2 0)).length = n + 2 := by
      simp [boundVars_length]
    have hG' : HasType Δ G (naryTy (.var 1 :: .var 0 :: (boundVars n).map (shift 2 0)).length) := by
      simpa [hlenA] using hGΔ
    exact hasType_apps (Γ := Δ) hG' hargs
  · intro v
    have hc : ∀ a ∈ numerals v, Closed a := closed_mem_numerals v
    have hlen : (numerals v).length = n + 1 := numerals_length v
    have hFcl : Closed F := closed_of_representsN hF
    have hGcl : Closed G := closed_of_representsN hG
    have hred : StepStar (apps (naryLams (n + 1) (precBody n F G)) (numerals v))
        (instFrom 0 (numerals v) (precBody n F G)) := by
      simpa [hlen] using stepStar_apps_naryLams (numerals v) (precBody n F G) hc
    have hinst : instFrom 0 (numerals v) (precBody n F G) =
        .natrec (apps F (numerals (tail v)))
          (precSuccBody G (numerals (tail v))) (natLit (head v)) := by
      unfold precBody
      rw [instFrom_natrec]
      have hZ : instFrom 0 (numerals v) (apps F (boundVars n)) = apps F (numerals (tail v)) := by
        rw [instFrom_apps, instFrom_of_closed 0 (numerals v) hFcl, instFrom_boundVars_tail]
      have hS := instFrom_precSuccBody (n := n) G v hGcl
      have hN : instFrom 0 (numerals v) (.var n) = natLit (head v) := by
        have hhit := (instFrom_var_hit_index 0 (numerals v) hc n 0
          (Nat.zero_le _) (by omega) (by rw [hlen]; omega))
        have hget : (numerals v).getD 0 .zero = natLit (head v) := by
          rw [numerals, getD_cons_zero]
        exact hhit.trans hget
      rw [hZ, hS, hN]
    unfold precTerm
    refine hred.trans ?_
    rw [hinst]
    exact stepStar_prec_eval F G (tail v) hF hG (head v)

/-! ## Induction on `Nat.Primrec'` -/

/--
Proves: every pairing-free primitive recursive function is represented by some closed
well-typed System T term of type `naryTy n`.
Does not prove: a canonical choice of representative, or representation of
`Nat.Partrec` functions.
Relation: `RepresentsN`, i.e. `HasType []` and `StepStar` on numeral spines.
Closure: reflexive-transitive.
Strategy: full `Step`.
Trust: kernel-only plus Mathlib `Nat.Primrec'`.
Scope: every arity and every `Nat.Primrec'` derivation.
-/
theorem primrec'_representable {n : Nat} {f : List.Vector ℕ n → ℕ} (hf : Nat.Primrec' f) :
    ∃ t, RepresentsN t f := by
  induction hf with
  | zero => exact ⟨.zero, represents_zero⟩
  | succ => exact ⟨.lam .nat (.succ (.var 0)), represents_succ⟩
  | get i => exact ⟨getTerm _ i, represents_get i⟩
  | @comp m n f g hf hg ihf ihg =>
      obtain ⟨F, hF⟩ := ihf
      obtain ⟨Gs, hGs⟩ := exists_fin_fn ihg
      exact ⟨compTerm (m := m) (n := n) F Gs, represents_comp hF hGs⟩
  | @prec n f g hf hg ihf ihg =>
      obtain ⟨F, hF⟩ := ihf
      obtain ⟨G, hG⟩ := ihg
      exact ⟨precTerm n F G, represents_prec hF hG⟩

/-! ## Unary corollary consumed by lane L7a -/

/--
Proves: the unary representation predicate (same proposition as L7a's `Represents`).
Does not prove: that this definition is definitionally the L7a name (the supervisor
bridges the two namespaces).
Relation: `HasType [] t (nat → nat)` and `StepStar (app t (natLit n)) (natLit (f n))`.
Closure: reflexive-transitive.
Strategy: full `Step`.
Trust: kernel-only.
Scope: unary functions `ℕ → ℕ`.
-/
def Represents (t : SysTTerm) (f : ℕ → ℕ) : Prop :=
  HasType [] t (.arrow .nat .nat) ∧ ∀ n : ℕ, StepStar (.app t (natLit n)) (natLit (f n))

/--
Proves: every unary `Nat.Primrec` function is represented by a closed System T term of
type `nat → nat`.
Does not prove: undecidability of System T equality (L7a), or representation of
non-primitive-recursive total functions.
Relation: `Represents` on `StepStar` of unary application.
Closure: reflexive-transitive.
Strategy: full `Step`.
Trust: kernel-only plus `Primrec.nat_iff`, `Nat.Primrec'.prim_iff₁`, `Nat.Primrec'.of_prim`.
Scope: every `f : ℕ → ℕ` with `Nat.Primrec f`.
-/
theorem primrecRepresentation : ∀ f : ℕ → ℕ, Nat.Primrec f → ∃ t, Represents t f := by
  intro f hf
  have hP : Primrec f := (Primrec.nat_iff (f := f)).mpr hf
  have h' : Nat.Primrec' (fun v : List.Vector ℕ 1 => f (head v)) :=
    (Nat.Primrec'.prim_iff₁ (f := f)).mpr hP
  have hOf : Nat.Primrec' (fun v : List.Vector ℕ 1 => f (head v)) :=
    Nat.Primrec'.of_prim (hP.comp Primrec.vector_head)
  obtain ⟨t, ⟨hty, hred⟩⟩ := primrec'_representable hOf
  have _used_prim_iff₁ : Nat.Primrec' (fun v : List.Vector ℕ 1 => f (head v)) := h'
  refine ⟨t, ⟨?_, ?_⟩⟩
  · simpa [naryTy] using hty
  · intro k
    have hv := hred (cons k nil)
    simpa [numerals, apps, head_cons] using hv

/-! ## Non-vacuity: addition -/

/-- Gödel's recursor for addition: `λa. λb. natrec b (λy ih. succ ih) a`. -/
def addTerm : SysTTerm :=
  .lam .nat (.lam .nat (.natrec (.var 0) (.lam .nat (.lam .nat (.succ (.var 0)))) (.var 1)))

/--
Proves: Mathlib's 2-ary addition is `Nat.Primrec'`.
Does not prove: that `addTerm` is the representative produced by `primrec'_representable`.
Relation: not a rewrite relation.
Closure: not applicable.
Strategy: not applicable.
Trust: Mathlib `Nat.Primrec'.add`.
Scope: 2-ary addition `v.head + v.tail.head`.
-/
theorem add_is_primrec' : Nat.Primrec' fun v : List.Vector ℕ 2 => head v + head (tail v) :=
  Nat.Primrec'.add

/--
Proves: `addTerm` represents binary addition on numeral spines.
Does not prove: that `primrec'_representable` returns this same term.
Relation: `RepresentsN` via `StepStar` of `natrec` unfolding.
Closure: reflexive-transitive.
Strategy: full `Step`.
Trust: kernel-only.
Scope: 2-ary addition `head v + head (tail v)`.
-/
theorem represents_add :
    RepresentsN addTerm (fun v : List.Vector ℕ 2 => head v + head (tail v)) := by
  refine ⟨?ty, ?red⟩
  · unfold addTerm
    refine HasType.lam (HasType.lam ?_)
    refine HasType.natrec (HasType.var (by decide)) ?_ (HasType.var (by decide))
    exact HasType.lam (HasType.lam (HasType.succ (HasType.var (by decide))))
  · intro v
    have hc : ∀ a ∈ numerals v, Closed a := closed_mem_numerals v
    -- `addTerm = naryLams 2 (natrec (var 0) (λy ih. succ ih) (var 1))`
    have hadd : addTerm = naryLams 2
        (.natrec (.var 0) (.lam .nat (.lam .nat (.succ (.var 0)))) (.var 1)) := rfl
    rw [hadd]
    have hred : StepStar
        (apps (naryLams 2 (.natrec (.var 0) (.lam .nat (.lam .nat (.succ (.var 0)))) (.var 1)))
          (numerals v))
        (instFrom 0 (numerals v)
          (.natrec (.var 0) (.lam .nat (.lam .nat (.succ (.var 0)))) (.var 1))) := by
      have hlen : (numerals v).length = 2 := numerals_length v
      simpa [hlen] using
        stepStar_apps_naryLams (numerals v)
          (.natrec (.var 0) (.lam .nat (.lam .nat (.succ (.var 0)))) (.var 1)) hc
    refine hred.trans ?_
    have hinst : instFrom 0 (numerals v)
        (.natrec (.var 0) (.lam .nat (.lam .nat (.succ (.var 0)))) (.var 1)) =
        .natrec (natLit (head (tail v)))
          (.lam .nat (.lam .nat (.succ (.var 0)))) (natLit (head v)) := by
      rw [instFrom_natrec]
      have hlen : (numerals v).length = 2 := numerals_length v
      have h0 : instFrom 0 (numerals v) (.var 0) = natLit (head (tail v)) := by
        have h2 : 0 < 0 + (numerals v).length := by rw [hlen]; exact Nat.succ_pos 1
        have hidx : 0 + (numerals v).length - 1 - 0 = 1 := by rw [hlen]
        exact (instFrom_var_hit_index 0 (numerals v) hc 0 1 (Nat.zero_le 0) h2 hidx).trans
          ((numerals_getD_succ v 0).trans (numerals_getD_zero (tail v)))
      have h1 : instFrom 0 (numerals v) (.var 1) = natLit (head v) := by
        have h2 : 1 < 0 + (numerals v).length := by rw [hlen]; exact Nat.lt_succ_self 1
        have hidx : 0 + (numerals v).length - 1 - 1 = 0 := by rw [hlen]
        exact (instFrom_var_hit_index 0 (numerals v) hc 1 0 (Nat.zero_le 1) h2 hidx).trans
          (numerals_getD_zero v)
      have hS : instFrom 0 (numerals v) (.lam .nat (.lam .nat (.succ (.var 0)))) =
          .lam .nat (.lam .nat (.succ (.var 0))) :=
        instFrom_of_closed 0 (numerals v) (by
          simp [Closed, ClosedBelow])
      rw [h0, h1, hS]
    rw [hinst]
    -- Unfold `natrec b (λy ih. succ ih) a` to `a + b`.
    have hloop : ∀ a b : ℕ,
        StepStar (.natrec (natLit b) (.lam .nat (.lam .nat (.succ (.var 0)))) (natLit a))
          (natLit (a + b)) := by
      intro a b
      induction a with
      | zero =>
          simpa [Nat.zero_add] using
            stepStar_natrec_zero (natLit b) (.lam .nat (.lam .nat (.succ (.var 0))))
      | succ a ih =>
          have hunf := stepStar_natrec_succ (natLit b)
            (.lam .nat (.lam .nat (.succ (.var 0)))) a
          have hIH := stepStar_appR
            (.app (.lam .nat (.lam .nat (.succ (.var 0)))) (natLit a)) ih
          have hbeta1 : StepStar
              (.app (.lam .nat (.lam .nat (.succ (.var 0)))) (natLit a))
              (.lam .nat (.succ (.var 0))) := by
            have hs : shift 1 0 (natLit a) = natLit a := shift_of_closed 1 0 (closed_natLit a)
            have : subst 0 (natLit a) (.lam .nat (.succ (.var 0))) = .lam .nat (.succ (.var 0)) := by
              simp [subst]
            exact Relation.ReflTransGen.single (this ▸
              Step.beta .nat (.lam .nat (.succ (.var 0))) (natLit a))
          have hbeta1app := stepStar_appL (natLit (a + b)) hbeta1
          have hbeta2 : StepStar
              (.app (.lam .nat (.succ (.var 0))) (natLit (a + b)))
              (natLit ((a + 1) + b)) := by
            have : subst 0 (natLit (a + b)) (.succ (.var 0)) = natLit ((a + 1) + b) := by
              simp [subst, natLit, Nat.succ_add]
            exact Relation.ReflTransGen.single (this ▸
              Step.beta .nat (.succ (.var 0)) (natLit (a + b)))
          refine hunf.trans (hIH.trans (hbeta1app.trans hbeta2))
    have : head v + head (tail v) = head v + head (tail v) := rfl
    simpa [Nat.add_comm] using hloop (head v) (head (tail v))

/--
Proves: `2 + 3` as represented by `addTerm` reduces to `5`.
Does not prove: a cost bound, or that `normalizeFuel` is complete for every representing term.
Relation: `StepStar`.
Closure: reflexive-transitive.
Strategy: full `Step`.
Trust: kernel-only; the same claim is also `decide`-checked via `normalizeFuel` below.
Scope: the closed instance `apps addTerm [natLit 2, natLit 3]`.
-/
theorem stepStar_add_two_three :
    StepStar (apps addTerm [natLit 2, natLit 3]) (natLit 5) := by
  have h := represents_add.2 (cons 2 (cons 3 nil))
  have hnum : numerals (cons 2 (cons 3 (nil : List.Vector ℕ 0))) = [natLit 2, natLit 3] := by
    decide
  simpa [hnum] using h

/-- Computational replay of the same instance through the carrier normalizer. -/
theorem normalizeFuel_add_two_three :
    normalizeFuel 100 (apps addTerm [natLit 2, natLit 3]) = some (natLit 5, 9) := by
  decide

/--
Proves: the general `primrec'_representable` theorem applies to addition.
Does not prove: that the chosen witness equals `addTerm`.
Relation: `RepresentsN` existence.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only plus Mathlib `Nat.Primrec'.add`.
Scope: 2-ary addition.
-/
theorem primrec'_representable_add :
    ∃ t, RepresentsN t (fun v : List.Vector ℕ 2 => head v + head (tail v)) :=
  primrec'_representable Nat.Primrec'.add

end OperatorKO7.HigherOrderRewritingPrimrecRepresentation
