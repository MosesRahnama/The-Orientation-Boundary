import OperatorKO7.Meta.Rewriting.Rewrite
import OperatorKO7.Meta.Methods.OrientationClosure.SchemaCore
import OperatorKO7.Meta.Methods.OrientationClosure.FreePolynomialTermination
import OperatorKO7.Meta.OrdinalHierarchy
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Multiset.UnionInter
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Tactic

/-!
# Path-order method rows of the Orientation Boundary closeout

Rows: `acRPO`, `rpoModuloPermutation`, `popStarFamily`, `simpleTerminationOrderType`,
`cichonSlowGrowing`.

Terms are the generic first-order terms `OperatorKO7.Meta.Rewriting.Term σ ν` over an arbitrary
signature `σ`. The free recursor schema of `SchemaCore` is the instance.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders

open OperatorKO7.Meta.Rewriting

/-! ## 1. List lemmas -/

section ListLemmas

variable {α : Type*}

theorem getElem_append_cons_of_ne (pre post : List α) (a b : α) (j : Nat)
    (h₁ : j < (pre ++ a :: post).length) (h₂ : j < (pre ++ b :: post).length)
    (hne : j ≠ pre.length) :
    (pre ++ a :: post)[j] = (pre ++ b :: post)[j] := by
  simp only [List.getElem_append]
  split_ifs with hj
  · rfl
  · have hpos : j - pre.length ≠ 0 := by omega
    simp only [List.getElem_cons, hpos, dite_false]

theorem getElem_append_cons_self (pre post : List α) (a : α) (j : Nat)
    (h : j < (pre ++ a :: post).length) (hj : j = pre.length) :
    (pre ++ a :: post)[j] = a := by
  subst hj
  simp

theorem coe_append_cons (pre post : List α) (a : α) :
    ((pre ++ a :: post : List α) : Multiset α) = ((pre ++ post : List α) : Multiset α) + {a} := by
  rw [Multiset.coe_eq_coe.2 List.perm_middle, ← Multiset.cons_coe, ← Multiset.singleton_add,
    add_comm]

end ListLemmas

/-! ## 2. Dershowitz–Manna extension -/

section DMExt

variable {α : Type*}

/-- Dershowitz–Manna multiset extension (Dershowitz and Manna 1979): `M` lies above `N` when
`N` arises from `M` by replacing a nonempty submultiset `Z` by a multiset `Y` each of whose
elements lies below some element of `Z`. -/
def DM (R : α → α → Prop) (M N : Multiset α) : Prop :=
  ∃ X Y Z : Multiset α, Z ≠ 0 ∧ M = X + Z ∧ N = X + Y ∧ ∀ y ∈ Y, ∃ z ∈ Z, R z y

/-- Transitivity of the Dershowitz–Manna extension, needing transitivity of the base relation
only on triples drawn from the three multisets in order. -/
theorem DM.trans_local {R : α → α → Prop} {M N P : Multiset α}
    (htr : ∀ a ∈ M, ∀ b ∈ N, ∀ c ∈ P, R a b → R b c → R a c)
    (h₁ : DM R M N) (h₂ : DM R N P) : DM R M P := by
  classical
  obtain ⟨X₁, Y₁, Z₁, hZ₁, hM, hN₁, hYZ₁⟩ := h₁
  obtain ⟨X₂, Y₂, Z₂, _, hN₂, hP, hYZ₂⟩ := h₂
  have hN : X₁ + Y₁ = X₂ + Z₂ := hN₁.symm.trans hN₂
  refine ⟨X₂ ∩ X₁, Y₂ + (Y₁ - Z₂), Z₁ + (Z₂ - Y₁), ?_, ?_, ?_, ?_⟩
  · intro h
    exact hZ₁ (le_antisymm ((Multiset.le_add_right _ _).trans h.le) (Multiset.zero_le _))
  · rw [hM]
    ext a
    have hc := congrArg (Multiset.count a) hN
    simp only [Multiset.count_add] at hc
    simp only [Multiset.count_add, Multiset.count_inter, Multiset.count_sub]
    rw [min_def]
    split_ifs <;> omega
  · rw [hP]
    ext a
    have hc := congrArg (Multiset.count a) hN
    simp only [Multiset.count_add] at hc
    simp only [Multiset.count_add, Multiset.count_inter, Multiset.count_sub]
    rw [min_def]
    split_ifs <;> omega
  · intro y hy
    rcases Multiset.mem_add.1 hy with hy2 | hy1
    · obtain ⟨z, hz, hzy⟩ := hYZ₂ y hy2
      by_cases hzY : z ∈ Y₁
      · obtain ⟨w, hw, hwz⟩ := hYZ₁ z hzY
        refine ⟨w, Multiset.mem_add.2 (Or.inl hw), htr w ?_ z ?_ y ?_ hwz hzy⟩
        · rw [hM]; exact Multiset.mem_add.2 (Or.inr hw)
        · rw [hN₂]; exact Multiset.mem_add.2 (Or.inr hz)
        · rw [hP]; exact Multiset.mem_add.2 (Or.inr hy2)
      · refine ⟨z, Multiset.mem_add.2 (Or.inr ?_), hzy⟩
        rwa [Multiset.mem_sub, Multiset.count_eq_zero_of_notMem hzY, Multiset.count_pos]
    · have hy1' : y ∈ Y₁ := Multiset.mem_of_le (Multiset.sub_le_self _ _) hy1
      obtain ⟨w, hw, hwy⟩ := hYZ₁ y hy1'
      exact ⟨w, Multiset.mem_add.2 (Or.inl hw), hwy⟩

/-- Adding a common part preserves the extension. -/
theorem DM.add_left {R : α → α → Prop} {M N : Multiset α} (W : Multiset α) (h : DM R M N) :
    DM R (W + M) (W + N) := by
  obtain ⟨X, Y, Z, hZ, rfl, rfl, hYZ⟩ := h
  exact ⟨W + X, Y, Z, hZ, (add_assoc _ _ _).symm, (add_assoc _ _ _).symm, hYZ⟩

end DMExt

/-! ## 3. The recursive path order with status

Dershowitz 1987 (J. Symbolic Computation 3, pp. 69–115), Definition 18 (recursive path ordering,
after Dershowitz 1982), combined with the status of p. 98: each symbol compares its arguments as
a multiset, or lexicographically in a fixed order of positions (Kamin–Lévy, Definition 19). The
lexicographic order of positions is a permutation of the argument positions. This section is
the syntactic generator; the order modulo permutative congruence is `RPOm` in section 6. -/

/-- Argument status: multiset, or lexicographic in the order of positions given by a
permutation for each arity. -/
inductive ArgStatus where
  | mul : ArgStatus
  | lex (π : (n : Nat) → Equiv.Perm (Fin n)) : ArgStatus

theorem ArgStatus.lex_inj {π π' : (n : Nat) → Equiv.Perm (Fin n)}
    (h : ArgStatus.lex π = ArgStatus.lex π') : π = π' := by
  cases h
  rfl

section Core

variable {σ ν : Type}

/-- The recursive path order with status. `pr g f` means that `g` lies below `f` in the
precedence. -/
inductive RPO (pr : σ → σ → Prop) (st : σ → ArgStatus) : Term σ ν → Term σ ν → Prop
  | subEq {f : σ} {args : List (Term σ ν)} {t : Term σ ν} (ht : t ∈ args) :
      RPO pr st (.app f args) t
  | subGt {f : σ} {args : List (Term σ ν)} {t : Term σ ν} (a : Term σ ν) (ha : a ∈ args)
      (h : RPO pr st a t) : RPO pr st (.app f args) t
  | prec {f g : σ} {args targs : List (Term σ ν)} (hfg : pr g f)
      (h : ∀ u ∈ targs, RPO pr st (.app f args) u) : RPO pr st (.app f args) (.app g targs)
  | mul {f : σ} {args targs : List (Term σ ν)} (hst : st f = .mul)
      (X Y Z : Multiset (Term σ ν)) (φ : Term σ ν → Term σ ν) (hZ : Z ≠ 0)
      (hs : (args : Multiset (Term σ ν)) = X + Z) (ht : (targs : Multiset (Term σ ν)) = X + Y)
      (hφZ : ∀ y ∈ Y, φ y ∈ Z) (hφ : ∀ y ∈ Y, RPO pr st (φ y) y) :
      RPO pr st (.app f args) (.app f targs)
  | lex {f : σ} {args targs : List (Term σ ν)} (π : (n : Nat) → Equiv.Perm (Fin n))
      (hst : st f = .lex π) (n : Nat) (hn : args.length = n) (hn' : targs.length = n)
      (k : Fin n)
      (hpre : ∀ i : Fin n, i < k →
        args[(π n i).1]'(lt_of_lt_of_eq (π n i).2 hn.symm) =
          targs[(π n i).1]'(lt_of_lt_of_eq (π n i).2 hn'.symm))
      (hcut : RPO pr st (args[(π n k).1]'(lt_of_lt_of_eq (π n k).2 hn.symm))
        (targs[(π n k).1]'(lt_of_lt_of_eq (π n k).2 hn'.symm)))
      (hdom : ∀ u ∈ targs, RPO pr st (.app f args) u) :
      RPO pr st (.app f args) (.app f targs)

/-- Reverse order: `u` lies below `t`. -/
def RPORev (pr : σ → σ → Prop) (st : σ → ArgStatus) (u t : Term σ ν) : Prop := RPO pr st t u

/-- The head part of a comparison between two applications: precedence, or equal heads with
the status comparison of the arguments, measured by the relation `R`. -/
def HeadGt (pr : σ → σ → Prop) (st : σ → ArgStatus) (R : Term σ ν → Term σ ν → Prop)
    (f : σ) (args : List (Term σ ν)) (g : σ) (targs : List (Term σ ν)) : Prop :=
  pr g f ∨ (g = f ∧ st f = .mul ∧ DM R (args : Multiset (Term σ ν)) (targs : Multiset (Term σ ν))) ∨
    (g = f ∧ ∃ π : (n : Nat) → Equiv.Perm (Fin n), st f = .lex π ∧
      ∃ (n : Nat) (hn : args.length = n) (hn' : targs.length = n) (k : Fin n),
        (∀ i : Fin n, i < k →
          args[(π n i).1]'(lt_of_lt_of_eq (π n i).2 hn.symm) =
            targs[(π n i).1]'(lt_of_lt_of_eq (π n i).2 hn'.symm)) ∧
        R (args[(π n k).1]'(lt_of_lt_of_eq (π n k).2 hn.symm))
          (targs[(π n k).1]'(lt_of_lt_of_eq (π n k).2 hn'.symm)))

variable {pr : σ → σ → Prop} {st : σ → ArgStatus}

theorem RPO.not_var_left {x : ν} {t : Term σ ν} : ¬ RPO pr st (.var x) t := by
  intro h
  cases h

/-- Applications dominate every argument of a term they dominate. -/
theorem RPO.dom {s : Term σ ν} {g : σ} {targs : List (Term σ ν)}
    (h : RPO pr st s (.app g targs)) : ∀ u ∈ targs, RPO pr st s u := by
  generalize ht : (Term.app g targs : Term σ ν) = t at h
  induction h generalizing g targs with
  | subEq hmem =>
      subst ht
      exact fun u hu => .subGt _ hmem (.subEq hu)
  | subGt a ha _ ih => exact fun u hu => .subGt a ha (ih ht u hu)
  | prec _ hdom _ =>
      cases ht
      exact hdom
  | mul _ X Y Z φ _ hs ht' hφZ hφ _ =>
      cases ht
      intro u hu
      have hu' : u ∈ X + Y := by rw [← ht']; exact Multiset.mem_coe.2 hu
      rcases Multiset.mem_add.1 hu' with hX | hY
      · exact .subEq (Multiset.mem_coe.1 (by rw [hs]; exact Multiset.mem_add.2 (Or.inl hX)))
      · exact .subGt (φ u)
          (Multiset.mem_coe.1 (by rw [hs]; exact Multiset.mem_add.2 (Or.inr (hφZ u hY))))
          (hφ u hY)
  | lex _ _ _ _ _ _ _ _ hdom _ _ =>
      cases ht
      exact hdom

/-- A multiset comparison of the arguments gives the multiset clause. -/
theorem RPO.of_DM {f : σ} {args targs : List (Term σ ν)} (hst : st f = .mul)
    (h : DM (RPO pr st) (args : Multiset (Term σ ν)) (targs : Multiset (Term σ ν))) :
    RPO pr st (.app f args) (.app f targs) := by
  classical
  obtain ⟨X, Y, Z, hZ, hs, ht, hdom⟩ := h
  refine .mul hst X Y Z (fun y => if hy : y ∈ Y then (hdom y hy).choose else y) hZ hs ht ?_ ?_
  · intro y hy
    simp only [dif_pos hy]
    exact (hdom y hy).choose_spec.1
  · intro y hy
    simp only [dif_pos hy]
    exact (hdom y hy).choose_spec.2

/-- Characterization of comparisons from an application: a subterm clause, or a head clause
together with domination of every argument of the right-hand side. -/
theorem RPO.app_iff {f : σ} {args : List (Term σ ν)} {t : Term σ ν} :
    RPO pr st (.app f args) t ↔
      (∃ a ∈ args, a = t ∨ RPO pr st a t) ∨
        (∃ g targs, t = .app g targs ∧ HeadGt pr st (RPO pr st) f args g targs ∧
          ∀ u ∈ targs, RPO pr st (.app f args) u) := by
  constructor
  · intro h
    cases h with
    | subEq ht => exact Or.inl ⟨t, ht, Or.inl rfl⟩
    | subGt a ha h => exact Or.inl ⟨a, ha, Or.inr h⟩
    | @prec _ g _ targs hfg hdom => exact Or.inr ⟨g, targs, rfl, Or.inl hfg, hdom⟩
    | @mul _ _ targs hst X Y Z φ hZ hs ht hφZ hφ =>
        refine Or.inr ⟨f, targs, rfl, Or.inr (Or.inl ⟨rfl, hst, X, Y, Z, hZ, hs, ht, ?_⟩), ?_⟩
        · exact fun y hy => ⟨φ y, hφZ y hy, hφ y hy⟩
        · exact RPO.dom (.mul hst X Y Z φ hZ hs ht hφZ hφ)
    | @lex _ _ targs π hst n hn hn' k hpre hcut hdom =>
        exact Or.inr ⟨f, targs, rfl, Or.inr (Or.inr ⟨rfl, π, hst, n, hn, hn', k, hpre, hcut⟩),
          hdom⟩
  · rintro (⟨a, ha, rfl | h⟩ | ⟨g, targs, rfl, hhead, hdom⟩)
    · exact .subEq ha
    · exact .subGt a ha h
    · rcases hhead with hfg | ⟨rfl, hst, hdm⟩ | ⟨rfl, π, hst, n, hn, hn', k, hpre, hcut⟩
      · exact .prec hfg hdom
      · exact RPO.of_DM hst hdm
      · exact .lex π hst n hn hn' k hpre hcut hdom

/-- Transitivity of head clauses, given transitivity of the argument comparison on triples. -/
theorem HeadGt.trans (hpr : ∀ a b c : σ, pr a b → pr b c → pr a c)
    {R : Term σ ν → Term σ ν → Prop} {f g h : σ} {args targs uargs : List (Term σ ν)}
    (htr : ∀ a ∈ args, ∀ b ∈ targs, ∀ c ∈ uargs, R a b → R b c → R a c)
    (h₁ : HeadGt pr st R f args g targs) (h₂ : HeadGt pr st R g targs h uargs) :
    HeadGt pr st R f args h uargs := by
  rcases h₁ with hgf | ⟨rfl, hst₁, hdm₁⟩ | ⟨rfl, π₁, hst₁, n₁, hn₁, hn₁', k₁, hpre₁, hcut₁⟩
  · rcases h₂ with hhg | ⟨rfl, _, _⟩ | ⟨rfl, _⟩
    · exact Or.inl (hpr _ _ _ hhg hgf)
    · exact Or.inl hgf
    · exact Or.inl hgf
  · rcases h₂ with hhg | ⟨rfl, _, hdm₂⟩ | ⟨rfl, π₂, hst₂, _⟩
    · exact Or.inl hhg
    · refine Or.inr (Or.inl ⟨rfl, hst₁, DM.trans_local ?_ hdm₁ hdm₂⟩)
      intro a ha b hb c hc hab hbc
      exact htr a (Multiset.mem_coe.1 ha) b (Multiset.mem_coe.1 hb) c (Multiset.mem_coe.1 hc)
        hab hbc
    · rw [hst₁] at hst₂
      cases hst₂
  · rcases h₂ with hhg | ⟨rfl, hst₂, _⟩ | ⟨rfl, π₂, hst₂, n₂, hn₂, hn₂', k₂, hpre₂, hcut₂⟩
    · exact Or.inl hhg
    · rw [hst₁] at hst₂
      cases hst₂
    · have hπ : π₂ = π₁ := ArgStatus.lex_inj (hst₂.symm.trans hst₁)
      subst hπ
      have hnn : n₂ = n₁ := hn₂.symm.trans hn₁'
      subst hnn
      refine Or.inr (Or.inr ⟨rfl, π₂, hst₁, n₂, hn₁, hn₂', ?_⟩)
      rcases lt_trichotomy k₁ k₂ with hk | hk | hk
      · refine ⟨k₁, ?_, ?_⟩
        · intro i hi
          exact (hpre₁ i hi).trans (hpre₂ i (hi.trans hk))
        · have := hpre₂ k₁ hk
          rw [← this]
          exact hcut₁
      · subst hk
        refine ⟨k₁, ?_, ?_⟩
        · intro i hi
          exact (hpre₁ i hi).trans (hpre₂ i hi)
        · exact htr _ (List.getElem_mem _) _ (List.getElem_mem _) _ (List.getElem_mem _)
            hcut₁ hcut₂
      · refine ⟨k₂, ?_, ?_⟩
        · intro i hi
          exact (hpre₁ i (hi.trans hk)).trans (hpre₂ i hi)
        · have := hpre₁ k₂ hk
          rw [this]
          exact hcut₂

theorem RPO.trans_aux (hpr : ∀ a b c : σ, pr a b → pr b c → pr a c) :
    ∀ n : Nat, ∀ s t u : Term σ ν, s.size + t.size + u.size ≤ n →
      RPO pr st s t → RPO pr st t u → RPO pr st s u := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s t u hsz h₁ h₂
  cases s with
  | var x => exact absurd h₁ RPO.not_var_left
  | app f args =>
  rcases RPO.app_iff.1 h₁ with ⟨a, ha, rfl | hat⟩ | ⟨g, targs, rfl, hhead₁, hdom₁⟩
  · exact .subGt a ha h₂
  · have := Term.size_lt_of_mem (f := f) ha
    exact .subGt a ha (ih _ (by omega) a t u le_rfl hat h₂)
  · rcases RPO.app_iff.1 h₂ with ⟨b, hb, rfl | hbu⟩ | ⟨h, uargs, rfl, hhead₂, hdom₂⟩
    · exact hdom₁ b hb
    · have := Term.size_lt_of_mem (f := g) hb
      exact ih _ (by omega) _ b u le_rfl (hdom₁ b hb) hbu
    · have hsu : ∀ w ∈ uargs, RPO pr st (.app f args) w := by
        intro w hw
        have := Term.size_lt_of_mem (f := h) hw
        exact ih _ (by omega) _ _ w le_rfl h₁ (hdom₂ w hw)
      refine RPO.app_iff.2 (Or.inr ⟨h, uargs, rfl, HeadGt.trans hpr ?_ hhead₁ hhead₂, hsu⟩)
      intro a ha b hb c hc hab hbc
      have h1 := Term.size_lt_of_mem (f := f) ha
      have h2 := Term.size_lt_of_mem (f := g) hb
      have h3 := Term.size_lt_of_mem (f := h) hc
      exact ih _ (by omega) a b c le_rfl hab hbc

/-- **Transitivity** of the recursive path order with status. -/
theorem RPO.trans (hpr : ∀ a b c : σ, pr a b → pr b c → pr a c) {s t u : Term σ ν}
    (h₁ : RPO pr st s t) (h₂ : RPO pr st t u) : RPO pr st s u :=
  RPO.trans_aux hpr _ s t u le_rfl h₁ h₂

end Core

/-! ## 4. Accessibility of the Dershowitz–Manna and lexicographic extensions -/

section DMAcc

variable {α : Type*} {R : α → α → Prop}

/-- One Dershowitz–Manna move: one element `a` is replaced by elements below it. -/
def DMOne (R : α → α → Prop) (M N : Multiset α) : Prop :=
  ∃ (X Y : Multiset α) (a : α), M = X + {a} ∧ N = X + Y ∧ ∀ y ∈ Y, R a y

theorem dmOne_cons_inv {a : α} {M N : Multiset α} (h : DMOne R (a ::ₘ M) N) :
    ∃ M', (N = a ::ₘ M' ∧ DMOne R M M') ∨ (N = M + M' ∧ ∀ x ∈ M', R a x) := by
  classical
  obtain ⟨X, Y, b, h0, rfl, h2⟩ := h
  obtain rfl | hab := eq_or_ne a b
  · refine ⟨Y, Or.inr ⟨?_, h2⟩⟩
    rw [← Multiset.singleton_add, add_comm] at h0
    rw [add_right_cancel h0]
  · refine ⟨Y + (M - {b}), Or.inl ⟨?_, M - {b}, Y, b, ?_, add_comm _ _, h2⟩⟩
    · rw [← Multiset.singleton_add, add_comm] at h0
      rw [tsub_eq_tsub_of_add_eq_add h0, add_comm Y, ← Multiset.singleton_add, ← add_assoc,
        add_tsub_cancel_of_le]
      have : a ∈ X + {b} := by rw [← h0]; simp
      simpa [hab] using this
    · rw [tsub_add_cancel_of_le]
      have : b ∈ a ::ₘ M := by rw [h0]; simp
      simpa [hab.symm] using this

theorem acc_dmOne_cons {a : α} (ha : Acc (flip R) a) :
    ∀ {M : Multiset α}, Acc (fun N M => DMOne R M N) M →
      Acc (fun N M => DMOne R M N) (a ::ₘ M) := by
  induction ha with
  | intro a _ iha =>
  intro M hM
  induction hM with
  | intro M hM ihM =>
  refine Acc.intro _ (fun N hNM => ?_)
  obtain ⟨M', ⟨rfl, hM'⟩ | ⟨rfl, hN⟩⟩ := dmOne_cons_inv hNM
  · exact ihM _ hM'
  · clear hNM
    induction M' using Multiset.induction with
    | empty => simpa using Acc.intro M hM
    | @cons b N ihN =>
        simp only [Multiset.mem_cons, forall_eq_or_imp, Multiset.add_cons] at hN ⊢
        obtain ⟨hba, hN⟩ := hN
        exact iha b hba (ihN hN)

theorem acc_dmOne {M : Multiset α} (hM : ∀ x ∈ M, Acc (flip R) x) :
    Acc (fun N M => DMOne R M N) M := by
  induction M using Multiset.induction_on with
  | empty =>
      refine Acc.intro _ (fun N hN => ?_)
      obtain ⟨X, Y, a, h, -, -⟩ := hN
      exact absurd h.symm (by simp)
  | cons a M ih =>
      exact acc_dmOne_cons (hM a (Multiset.mem_cons_self a M))
        (ih fun x hx => hM x (Multiset.mem_cons_of_mem hx))

theorem transGen_dmOne_aux (Z : Multiset α) :
    ∀ X Y : Multiset α, Z ≠ 0 → (∀ y ∈ Y, ∃ z ∈ Z, R z y) →
      Relation.TransGen (fun N M => DMOne R M N) (X + Y) (X + Z) := by
  classical
  induction Z using Multiset.induction_on with
  | empty =>
      intro X Y hZ
      exact absurd rfl hZ
  | cons z Z ih =>
    intro X Y _ hYZ
    by_cases hZ' : Z = 0
    · subst hZ'
      refine .single ⟨X, Y, z, rfl, rfl, fun y hy => ?_⟩
      obtain ⟨z', hz', hz'y⟩ := hYZ y hy
      have : z' = z := by simpa using hz'
      subst this
      exact hz'y
    · let Y' : Multiset α := Y.filter (fun y => R z y)
      have h1 : Relation.TransGen (fun N M => DMOne R M N) ((X + Y') + (Y - Y'))
          ((X + Y') + Z) := by
        refine ih (X + Y') (Y - Y') hZ' ?_
        intro y hy
        simp only [Y', Multiset.sub_filter_eq_filter_not, Multiset.mem_filter] at hy
        obtain ⟨z', hz', hz'y⟩ := hYZ y hy.1
        rcases Multiset.mem_cons.1 hz' with rfl | hz'Z
        · exact absurd hz'y hy.2
        · exact ⟨z', hz'Z, hz'y⟩
      have heq : (X + Y') + (Y - Y') = X + Y := by
        rw [add_assoc, add_tsub_cancel_of_le (Multiset.filter_le _ _)]
      rw [heq] at h1
      refine .tail h1 ⟨X + Z, Y', z, ?_, add_right_comm _ _ _, ?_⟩
      · rw [Multiset.add_cons, ← Multiset.singleton_add, add_comm]
      · intro y hy
        exact (Multiset.mem_filter.1 hy).2

theorem transGen_dmOne_of_dm {M N : Multiset α} (h : DM R M N) :
    Relation.TransGen (fun N M => DMOne R M N) N M := by
  obtain ⟨X, Y, Z, hZ, rfl, rfl, hYZ⟩ := h
  exact transGen_dmOne_aux Z X Y hZ hYZ

/-- A multiset whose elements are accessible is accessible for the Dershowitz–Manna
extension. -/
theorem acc_dm {M : Multiset α} (hM : ∀ x ∈ M, Acc (flip R) x) :
    Acc (fun N M => DM R M N) M :=
  Subrelation.accessible (fun {_ _} h => transGen_dmOne_of_dm h) (acc_dmOne hM).transGen

end DMAcc

section LexAcc

variable {α : Type*} (R : α → α → Prop)

/-- Lexicographic descent on tuples: the prefix before `k` agrees and position `k` drops. -/
def ArgLex {n : Nat} (w v : Fin n → α) : Prop :=
  ∃ k : Fin n, (∀ i : Fin n, i.val < k.val → w i = v i) ∧ R (v k) (w k)

/-- Lexicographic descent restricted to tuples with accessible entries. -/
def ArgLexAcc {n : Nat} (w v : Fin n → α) : Prop :=
  (∀ i : Fin n, Acc (flip R) (w i)) ∧ ArgLex R w v

/-- Prepend an entry to a tuple. -/
def consTup {n : Nat} (x : α) (p : Fin n → α) : Fin (n + 1) → α := fun i => i.cases x p

/-- Drop the first entry of a tuple. -/
def tailTup {n : Nat} (v : Fin (n + 1) → α) : Fin n → α := fun i => v i.succ

theorem consTup_self_tail {n : Nat} (v : Fin (n + 1) → α) : consTup (v 0) (tailTup v) = v := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

theorem acc_argLexAcc_cons {n : Nat}
    (ih : ∀ p : Fin n → α, (∀ i, Acc (flip R) (p i)) → Acc (ArgLexAcc R) p)
    {x : α} (hx : Acc (flip R) x) :
    ∀ {p : Fin n → α}, Acc (ArgLexAcc R) p → Acc (ArgLexAcc R) (consTup x p) := by
  induction hx with
  | intro x _ ihx =>
    intro p hp
    induction hp with
    | intro p _ ihp =>
      refine Acc.intro (consTup x p) fun w hw => ?_
      obtain ⟨hwAcc, k, hpref, hlt⟩ := hw
      cases k using Fin.cases with
      | zero =>
          have hR : flip R (w 0) x := by
            change R x (w 0)
            simpa [consTup] using hlt
          have hTail : Acc (ArgLexAcc R) (tailTup w) := ih (tailTup w) (fun i => hwAcc i.succ)
          have hAcc := ihx (w 0) hR hTail
          simpa [consTup_self_tail] using hAcc
      | succ k =>
          have hxw : w 0 = x := by
            simpa [consTup] using hpref 0 (Nat.succ_pos k.val)
          have htailStep : ArgLexAcc R (tailTup w) p := by
            refine ⟨fun i => hwAcc i.succ, k, ?_, ?_⟩
            · intro i hi
              have : i.succ.val < k.succ.val := by
                simpa [Fin.val_succ] using Nat.succ_lt_succ hi
              simpa [tailTup, consTup] using hpref i.succ this
            · simpa [consTup, tailTup] using hlt
          have hAcc := ihp (tailTup w) htailStep
          have hwEq : w = consTup x (tailTup w) :=
            (consTup_self_tail w).symm.trans (congrArg (fun h => consTup h (tailTup w)) hxw)
          exact hwEq ▸ hAcc

/-- A tuple with accessible entries is accessible for the lexicographic descent. -/
theorem acc_argLexAcc :
    ∀ (n : Nat) (v : Fin n → α), (∀ i, Acc (flip R) (v i)) → Acc (ArgLexAcc R) v := by
  intro n
  induction n with
  | zero =>
      intro v _
      refine Acc.intro _ fun w hw => ?_
      obtain ⟨-, k, -, -⟩ := hw
      exact k.elim0
  | succ n ih =>
      intro v hv
      have hcons := acc_argLexAcc_cons R ih (hv 0) (ih (tailTup v) (fun i => hv i.succ))
      simpa [consTup_self_tail] using hcons

end LexAcc

/-! ## 5. Well-foundedness, stability, monotonicity and soundness of the RPO -/

section CoreProps

variable {σ ν : Type} {pr : σ → σ → Prop} {st : σ → ArgStatus}

theorem RPO.acc_rhs {f : σ} {args : List (Term σ ν)}
    (hargs : ∀ a ∈ args, Acc (RPORev pr st) a)
    (hLower : ∀ (g : σ) (targs : List (Term σ ν)), pr g f →
      (∀ a ∈ targs, Acc (RPORev pr st) a) → Acc (RPORev pr st) (.app g targs))
    (hSame : ∀ targs : List (Term σ ν), (∀ a ∈ targs, Acc (RPORev pr st) a) →
      HeadGt pr st (RPO pr st) f args f targs → Acc (RPORev pr st) (.app f targs)) :
    ∀ (n : Nat) (t : Term σ ν), t.size ≤ n → RPO pr st (.app f args) t →
      Acc (RPORev pr st) t := by
  intro n
  induction n with
  | zero =>
      intro t hle _
      have := Term.one_le_size t
      omega
  | succ n ih =>
      intro t hle ht
      rcases RPO.app_iff.1 ht with ⟨a, ha, rfl | hat⟩ | ⟨g, targs, rfl, hhead, hdom⟩
      · exact hargs a ha
      · exact Acc.inv (hargs a ha) hat
      · have hacc : ∀ u ∈ targs, Acc (RPORev pr st) u := by
          intro u hu
          have := Term.size_lt_of_mem (f := g) hu
          exact ih u (by omega) (hdom u hu)
        rcases hhead with hgf | ⟨rfl, hrest⟩ | ⟨rfl, hrest⟩
        · exact hLower g targs hgf hacc
        · exact hSame targs hacc (Or.inr (Or.inl ⟨rfl, hrest⟩))
        · exact hSame targs hacc (Or.inr (Or.inr ⟨rfl, hrest⟩))

theorem RPO.acc_app_of_lower (f : σ)
    (hLower : ∀ (g : σ) (targs : List (Term σ ν)), pr g f →
      (∀ a ∈ targs, Acc (RPORev pr st) a) → Acc (RPORev pr st) (.app g targs)) :
    ∀ args : List (Term σ ν), (∀ a ∈ args, Acc (RPORev pr st) a) →
      Acc (RPORev pr st) (.app f args) := by
  cases hst : st f with
  | mul =>
      suffices H : ∀ M : Multiset (Term σ ν), Acc (fun N M => DM (RPO pr st) M N) M →
          ∀ args : List (Term σ ν), (args : Multiset (Term σ ν)) = M →
            (∀ a ∈ args, Acc (RPORev pr st) a) → Acc (RPORev pr st) (.app f args) from
        fun args hargs =>
          H _ (acc_dm (fun x hx => hargs x (Multiset.mem_coe.1 hx))) args rfl hargs
      intro M hM
      induction hM with
      | intro M _ ihM =>
      intro args hargsM hargs
      refine Acc.intro _ (fun t ht => RPO.acc_rhs hargs hLower ?_ _ t le_rfl ht)
      intro targs htargs hhead
      rcases hhead with hff | ⟨_, _, hdm⟩ | ⟨_, π, hst', _⟩
      · exact hLower f targs hff htargs
      · exact ihM _ (hargsM ▸ hdm) targs rfl htargs
      · rw [hst] at hst'
        cases hst'
  | lex π =>
      intro args hargs
      obtain ⟨n, hn⟩ : ∃ n, args.length = n := ⟨_, rfl⟩
      suffices H : ∀ v : Fin n → Term σ ν, Acc (ArgLexAcc (RPO pr st)) v →
          ∀ (args' : List (Term σ ν)) (hn' : args'.length = n),
            (fun i : Fin n => args'[(π n i).1]'(lt_of_lt_of_eq (π n i).2 hn'.symm)) = v →
            (∀ a ∈ args', Acc (RPORev pr st) a) → Acc (RPORev pr st) (.app f args') from
        H _ (acc_argLexAcc (RPO pr st) n _ (fun i => hargs _ (List.getElem_mem _)))
          args hn rfl hargs
      intro v hv
      induction hv with
      | intro v _ ihv =>
      intro args' hn' hv' hargs'
      refine Acc.intro _ (fun t ht => RPO.acc_rhs hargs' hLower ?_ _ t le_rfl ht)
      intro targs htargs hhead
      rcases hhead with hff | ⟨_, hst', _⟩ | ⟨_, π', hst', n', hn₁, hn₂, k, hpre, hcut⟩
      · exact hLower f targs hff htargs
      · rw [hst] at hst'
        cases hst'
      · have hπ : π' = π := ArgStatus.lex_inj (hst'.symm.trans hst)
        subst hπ
        have hnn : n' = n := hn₁.symm.trans hn'
        subst hnn
        refine ihv _ ⟨fun i => htargs _ (List.getElem_mem _), k, ?_, ?_⟩ targs hn₂ rfl htargs
        · intro i hi
          rw [← hv']
          exact (hpre i hi).symm
        · rw [← hv']
          exact hcut

theorem RPO.acc_app (hwf : WellFounded pr) (f : σ) :
    ∀ args : List (Term σ ν), (∀ a ∈ args, Acc (RPORev pr st) a) →
      Acc (RPORev pr st) (.app f args) := by
  refine WellFounded.induction hwf f (C := fun f => ∀ args : List (Term σ ν),
    (∀ a ∈ args, Acc (RPORev pr st) a) → Acc (RPORev pr st) (.app f args)) ?_
  intro f ihf
  exact RPO.acc_app_of_lower f (fun g targs hg htargs => ihf g hg targs htargs)

theorem RPO.acc_term (hwf : WellFounded pr) (t : Term σ ν) : Acc (RPORev pr st) t := by
  induction t using Term.rec' with
  | hvar x => exact Acc.intro _ (fun u h => absurd h RPO.not_var_left)
  | happ f args ih => exact RPO.acc_app hwf f args ih

/-- **Well-foundedness** of the recursive path order with status for a well-founded
precedence (Dershowitz 1987, Theorems 23 and 24). The proof is nested accessibility; Kruskal's
theorem is not used, so the signature may be infinite. -/
theorem RPO.wf (hwf : WellFounded pr) : WellFounded (RPORev (ν := ν) pr st) :=
  ⟨RPO.acc_term hwf⟩

/-- **Irreflexivity**. -/
theorem RPO.irrefl (hwf : WellFounded pr) (t : Term σ ν) : ¬ RPO pr st t t := fun h =>
  (RPO.wf (ν := ν) (st := st) hwf).isIrrefl.irrefl t h

end CoreProps

section Bind

variable {σ : Type}

mutual
/-- Substitution of terms over `W` for the variables `V`. -/
def tbind {V W : Type} (θ : V → Term σ W) : Term σ V → Term σ W
  | .var x => θ x
  | .app f args => .app f (tbindList θ args)
/-- `tbind` on argument lists. -/
def tbindList {V W : Type} (θ : V → Term σ W) : List (Term σ V) → List (Term σ W)
  | [] => []
  | a :: as => tbind θ a :: tbindList θ as
end

theorem tbindList_eq_map {V W : Type} (θ : V → Term σ W) (l : List (Term σ V)) :
    tbindList θ l = l.map (tbind θ) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [tbindList, ih]

@[simp] theorem tbind_var {V W : Type} (θ : V → Term σ W) (x : V) :
    tbind θ (.var x) = θ x := by
  simp [tbind]

@[simp] theorem tbind_app {V W : Type} (θ : V → Term σ W) (f : σ) (args : List (Term σ V)) :
    tbind θ (.app f args) = .app f (args.map (tbind θ)) := by
  simp [tbind, tbindList_eq_map]

/-- On one variable type, `tbind` is the substitution of the rewriting library. -/
theorem tbind_eq_apply {ν : Type} (θ : Subst σ ν) (t : Term σ ν) :
    tbind θ t = Subst.apply θ t := by
  induction t using Term.rec' with
  | hvar x => simp
  | happ f args ih =>
      rw [tbind_app, Subst.apply_app, Subst.applyList_eq_map]
      congr 1
      exact List.map_congr_left ih

/-- **Stability under substitution.** -/
theorem RPO.bind {pr : σ → σ → Prop} {st : σ → ArgStatus} {V W : Type} (θ : V → Term σ W)
    {s t : Term σ V} (h : RPO pr st s t) : RPO pr st (tbind θ s) (tbind θ t) := by
  classical
  induction h with
  | subEq hmem =>
      rw [tbind_app]
      exact .subEq (List.mem_map_of_mem hmem)
  | subGt a ha _ ih =>
      rw [tbind_app]
      exact .subGt _ (List.mem_map_of_mem ha) ih
  | prec hfg _ ih =>
      rw [tbind_app, tbind_app]
      refine .prec hfg ?_
      intro u hu
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
      simpa [tbind_app] using ih w hw
  | mul hst X Y Z φ hZ hs ht hφZ _ ih =>
      rw [tbind_app, tbind_app]
      refine RPO.of_DM hst ⟨X.map (tbind θ), Y.map (tbind θ), Z.map (tbind θ), ?_, ?_, ?_, ?_⟩
      · simpa using hZ
      · rw [← Multiset.map_coe, hs, Multiset.map_add]
      · rw [← Multiset.map_coe, ht, Multiset.map_add]
      · intro y' hy'
        obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hy'
        exact ⟨tbind θ (φ y), Multiset.mem_map_of_mem _ (hφZ y hy), ih y hy⟩
  | lex π hst n hn hn' k hpre _ _ ihcut ihdom =>
      rw [tbind_app, tbind_app]
      refine .lex π hst n (by simpa using hn) (by simpa using hn') k ?_ ?_ ?_
      · intro i hi
        simp only [List.getElem_map]
        rw [hpre i hi]
      · simp only [List.getElem_map]
        exact ihcut
      · intro u hu
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu
        simpa [tbind_app] using ihdom w hw

/-- **Closure under one-hole argument contexts.** -/
theorem RPO.mono_arg {pr : σ → σ → Prop} {st : σ → ArgStatus} {ν : Type} (f : σ)
    (pre post : List (Term σ ν)) {a b : Term σ ν} (h : RPO pr st a b) :
    RPO pr st (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post)) := by
  have hdom : ∀ u ∈ pre ++ b :: post, RPO pr st (.app f (pre ++ a :: post)) u := by
    intro u hu
    rcases List.mem_append.1 hu with hpre | hbpost
    · exact .subEq (by simp [hpre])
    · rcases List.mem_cons.1 hbpost with rfl | hpost
      · exact .subGt a (by simp) h
      · exact .subEq (by simp [hpost])
  cases hst : st f with
  | mul =>
      refine .mul hst ((pre ++ post : List (Term σ ν)) : Multiset (Term σ ν)) {b} {a}
        (fun _ => a) (Multiset.singleton_ne_zero a) (coe_append_cons pre post a)
        (coe_append_cons pre post b) ?_ ?_
      · intro y _
        exact Multiset.mem_singleton_self a
      · intro y hy
        rw [Multiset.mem_singleton.1 hy]
        exact h
  | lex π =>
      set n := (pre ++ a :: post).length with hn
      have hn' : (pre ++ b :: post).length = n := by simp [hn]
      have hp : pre.length < n := by simp [hn]
      let k : Fin n := (π n).symm ⟨pre.length, hp⟩
      have hk : π n k = ⟨pre.length, hp⟩ := by simp [k]
      refine .lex π hst n hn.symm hn' k ?_ ?_ hdom
      · intro i hi
        have hne : (π n i).1 ≠ pre.length := by
          intro heq
          have hik : π n i = π n k := by rw [hk]; exact Fin.ext heq
          exact (ne_of_lt hi) ((π n).injective hik)
        exact getElem_append_cons_of_ne pre post a b _ _ _ hne
      · rw [getElem_append_cons_self pre post a (π n k).1 (lt_of_lt_of_eq (π n k).2 hn)
            (by rw [hk]),
          getElem_append_cons_self pre post b (π n k).1 (lt_of_lt_of_eq (π n k).2 hn'.symm)
            (by rw [hk])]
        exact h

/-- Occurrence of a variable. -/
inductive Occurs {ν : Type} (x : ν) : Term σ ν → Prop
  | here : Occurs x (.var x)
  | arg {f : σ} {args : List (Term σ ν)} {a : Term σ ν} (ha : a ∈ args) (h : Occurs x a) :
      Occurs x (.app f args)

/-- **Variable condition**: the right-hand side of a comparison has no variable that the
left-hand side lacks. -/
theorem RPO.occurs {pr : σ → σ → Prop} {st : σ → ArgStatus} {ν : Type} {x : ν}
    {s t : Term σ ν} (h : RPO pr st s t) : Occurs x t → Occurs x s := by
  induction h with
  | subEq hmem => exact fun hx => .arg hmem hx
  | subGt a ha _ ih => exact fun hx => .arg ha (ih hx)
  | prec _ _ ih =>
      intro hx
      cases hx with
      | arg hu hxu => exact ih _ hu hxu
  | mul _ X Y Z φ _ hs ht hφZ _ ih =>
      intro hx
      cases hx with
      | @arg _ _ u hu hxu =>
        have hu' : u ∈ X + Y := by rw [← ht]; exact Multiset.mem_coe.2 hu
        rcases Multiset.mem_add.1 hu' with hX | hY
        · have hmem : u ∈ X + Z := Multiset.mem_add.2 (Or.inl hX)
          rw [← hs] at hmem
          exact .arg (Multiset.mem_coe.1 hmem) hxu
        · have hmem : φ u ∈ X + Z := Multiset.mem_add.2 (Or.inr (hφZ u hY))
          rw [← hs] at hmem
          exact .arg (Multiset.mem_coe.1 hmem) (ih u hY hxu)
  | lex _ _ _ _ _ _ _ _ _ _ ihdom =>
      intro hx
      cases hx with
      | arg hu hxu => exact ihdom _ hu hxu

/-- Rewrite steps of a system whose rules are oriented decrease in the order. -/
theorem RPO.of_step {pr : σ → σ → Prop} {st : σ → ArgStatus} {ν : Type} {R : TRS σ ν}
    (hR : ∀ rule ∈ R, RPO pr st rule.lhs rule.rhs) {s t : Term σ ν} (h : Step R s t) :
    RPO pr st s t := by
  induction h with
  | root hroot =>
      obtain ⟨rule, hrule, θ, rfl, rfl⟩ := hroot
      have := RPO.bind θ (hR rule hrule)
      simpa [tbind_eq_apply] using this
  | arg f pre post _ ih => exact RPO.mono_arg f pre post ih

/-- **Soundness** (Dershowitz 1987, Theorems 8 and 23): a system whose rules decrease in the
recursive path order over a well-founded precedence terminates. Relation: `Rewriting.Step`,
full context closure, full rewriting. -/
theorem RPO.step_wf {pr : σ → σ → Prop} {st : σ → ArgStatus} {ν : Type}
    (hwf : WellFounded pr) {R : TRS σ ν} (hR : ∀ rule ∈ R, RPO pr st rule.lhs rule.rhs) :
    WellFounded (fun u t : Term σ ν => Step R t u) :=
  Subrelation.wf (fun {_ _} h => RPO.of_step hR h) (RPO.wf hwf)

/-- The substitution sending each variable to itself is the identity. -/
theorem tbind_var_self {V : Type} (t : Term σ V) : tbind (fun x => (.var x : Term σ V)) t = t := by
  induction t using Term.rec' with
  | hvar x => simp
  | happ f args ih =>
      rw [tbind_app]
      congr 1
      conv_rhs => rw [← List.map_id args]
      exact List.map_congr_left ih

end Bind

/-! ## 6. The order modulo permutative congruence

Dershowitz 1987, Definition 18: terms are compared up to permutative congruence, the congruence
that permutes the arguments of multiset-status symbols. Each congruence class is represented by
the term whose multiset-status argument lists are sorted by a fixed well-ordering of terms. That
well-ordering picks the representative and takes part in no comparison. -/

section Canon

variable {σ ν : Type}

/-- A well-ordering of terms used only to choose a representative argument list. -/
noncomputable def termLinearOrder (σ ν : Type) : LinearOrder (Term σ ν) :=
  IsWellOrder.linearOrder WellOrderingRel

/-- The sorted representative list of a multiset of terms. -/
noncomputable def sortTerms (M : Multiset (Term σ ν)) : List (Term σ ν) :=
  letI := termLinearOrder σ ν
  Multiset.sort (· ≤ ·) M

theorem coe_sortTerms (M : Multiset (Term σ ν)) :
    (sortTerms M : Multiset (Term σ ν)) = M := by
  letI := termLinearOrder σ ν
  unfold sortTerms
  exact Multiset.sort_eq (· ≤ ·) M

/-- Representative argument list: sorted for multiset status, unchanged for lexicographic
status. -/
noncomputable def canonArgs (st : σ → ArgStatus) (f : σ) (l : List (Term σ ν)) :
    List (Term σ ν) :=
  match st f with
  | .mul => sortTerms (l : Multiset (Term σ ν))
  | .lex _ => l

theorem canonArgs_of_mul {st : σ → ArgStatus} {f : σ} (hst : st f = .mul)
    (l : List (Term σ ν)) : canonArgs st f l = sortTerms (l : Multiset (Term σ ν)) := by
  simp [canonArgs, hst]

theorem canonArgs_of_lex {st : σ → ArgStatus} {f : σ} {π : (n : Nat) → Equiv.Perm (Fin n)}
    (hst : st f = .lex π) (l : List (Term σ ν)) : canonArgs st f l = l := by
  simp [canonArgs, hst]

theorem canonArgs_coe (st : σ → ArgStatus) (f : σ) (l : List (Term σ ν)) :
    (canonArgs st f l : Multiset (Term σ ν)) = l := by
  cases hst : st f with
  | mul => rw [canonArgs_of_mul hst, coe_sortTerms]
  | lex π => rw [canonArgs_of_lex hst]

theorem canonArgs_mem (st : σ → ArgStatus) (f : σ) (l : List (Term σ ν)) (x : Term σ ν) :
    x ∈ canonArgs st f l ↔ x ∈ l := by
  rw [← Multiset.mem_coe, canonArgs_coe, Multiset.mem_coe]

theorem canonArgs_map (st : σ → ArgStatus) (f : σ) {V W : Type} (l : List (Term σ V))
    (g : Term σ V → Term σ W) :
    canonArgs st f ((canonArgs st f l).map g) = canonArgs st f (l.map g) := by
  cases hst : st f with
  | mul =>
      simp only [canonArgs_of_mul hst]
      congr 1
      rw [← Multiset.map_coe, coe_sortTerms, Multiset.map_coe]
  | lex π => simp only [canonArgs_of_lex hst]

mutual
/-- Permutation-canonical representative of a term. -/
noncomputable def kappa (st : σ → ArgStatus) : Term σ ν → Term σ ν
  | .var x => .var x
  | .app f args => .app f (canonArgs st f (kappaList st args))
/-- `kappa` on argument lists. -/
noncomputable def kappaList (st : σ → ArgStatus) : List (Term σ ν) → List (Term σ ν)
  | [] => []
  | a :: as => kappa st a :: kappaList st as
end

theorem kappaList_eq_map (st : σ → ArgStatus) (l : List (Term σ ν)) :
    kappaList st l = l.map (kappa st) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [kappaList, ih]

@[simp] theorem kappa_var (st : σ → ArgStatus) (x : ν) :
    kappa (σ := σ) st (.var x) = .var x := by
  simp [kappa]

theorem kappa_app (st : σ → ArgStatus) (f : σ) (args : List (Term σ ν)) :
    kappa st (.app f args) = .app f (canonArgs st f (args.map (kappa st))) := by
  simp [kappa, kappaList_eq_map]

/-- Representatives commute with substitution up to re-sorting. -/
theorem kappa_bind (st : σ → ArgStatus) {V W : Type} (θ : V → Term σ W) (t : Term σ V) :
    kappa st (tbind θ (kappa st t)) = kappa st (tbind θ t) := by
  induction t using Term.rec' with
  | hvar x => simp
  | happ f args ih =>
      simp only [kappa_app, tbind_app, List.map_map]
      rw [canonArgs_map st f (args.map (kappa st)) (kappa st ∘ tbind θ), List.map_map]
      congr 2
      apply List.map_congr_left
      intro a ha
      simpa using ih a ha

theorem kappa_idem (st : σ → ArgStatus) (t : Term σ ν) : kappa st (kappa st t) = kappa st t := by
  have := kappa_bind st (fun x => (.var x : Term σ ν)) t
  simpa [tbind_var_self] using this

/-- The RPO transported along `kappa ∘ tbind θ`. -/
theorem RPO.kappa_bind {pr : σ → σ → Prop} {st : σ → ArgStatus} {V W : Type}
    (θ : V → Term σ W) {a b : Term σ V} (h : RPO pr st a b) :
    RPO pr st (kappa st (tbind θ a)) (kappa st (tbind θ b)) := by
  classical
  induction h with
  | subEq hmem =>
      simp only [tbind_app, kappa_app]
      exact .subEq ((canonArgs_mem _ _ _ _).2
        (List.mem_map_of_mem (List.mem_map_of_mem hmem)))
  | subGt a ha _ ih =>
      simp only [tbind_app, kappa_app] at ih ⊢
      exact .subGt _ ((canonArgs_mem _ _ _ _).2
        (List.mem_map_of_mem (List.mem_map_of_mem ha))) ih
  | prec hfg _ ih =>
      simp only [tbind_app, kappa_app] at ih ⊢
      refine .prec hfg ?_
      intro u' hu'
      rw [canonArgs_mem, List.map_map] at hu'
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hu'
      exact ih u hu
  | mul hst X Y Z φ hZ hs ht hφZ _ ih =>
      simp only [tbind_app, kappa_app]
      refine RPO.of_DM hst ?_
      rw [canonArgs_coe, canonArgs_coe, List.map_map, List.map_map, ← Multiset.map_coe,
        ← Multiset.map_coe, hs, ht, Multiset.map_add, Multiset.map_add]
      refine ⟨X.map (kappa st ∘ tbind θ), Y.map (kappa st ∘ tbind θ),
        Z.map (kappa st ∘ tbind θ), by simpa using hZ, rfl, rfl, ?_⟩
      intro y' hy'
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hy'
      exact ⟨(kappa st ∘ tbind θ) (φ y), Multiset.mem_map_of_mem _ (hφZ y hy), ih y hy⟩
  | lex π hst n hn hn' k hpre _ _ ihcut ihdom =>
      simp only [tbind_app, kappa_app, canonArgs_of_lex hst, List.map_map] at ihdom ⊢
      refine .lex π hst n (by simpa using hn) (by simpa using hn') k ?_ ?_ ?_
      · intro i hi
        simp only [List.getElem_map, Function.comp_apply]
        rw [hpre i hi]
      · simp only [List.getElem_map, Function.comp_apply]
        exact ihcut
      · intro u' hu'
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hu'
        exact ihdom u hu

/-- **The recursive path order with status modulo permutative congruence** (Dershowitz 1987,
J. Symbolic Comput. 3, Definition 18, with the status of p. 98). -/
def RPOm (pr : σ → σ → Prop) (st : σ → ArgStatus) (s t : Term σ ν) : Prop :=
  RPO pr st (kappa st s) (kappa st t)

/-- Permutative congruence: equal representatives. -/
def PermEq (st : σ → ArgStatus) (s t : Term σ ν) : Prop := kappa st s = kappa st t

/-- One permutation of the arguments of a multiset-status symbol, in any context. -/
inductive PermStep (st : σ → ArgStatus) : Term σ ν → Term σ ν → Prop
  | root {f : σ} {args args' : List (Term σ ν)} (hst : st f = .mul) (hp : args.Perm args') :
      PermStep st (.app f args) (.app f args')
  | arg (f : σ) (pre post : List (Term σ ν)) {a b : Term σ ν} (h : PermStep st a b) :
      PermStep st (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post))

variable {pr : σ → σ → Prop} {st : σ → ArgStatus}

theorem kappa_app_arg (st : σ → ArgStatus) (f : σ) (pre post : List (Term σ ν))
    {a b : Term σ ν} (h : kappa st a = kappa st b) :
    kappa st (.app f (pre ++ a :: post)) = kappa st (.app f (pre ++ b :: post)) := by
  simp [kappa_app, h]

theorem permEq_of_permStep {s t : Term σ ν} (h : PermStep st s t) : PermEq st s t := by
  induction h with
  | root hst hp =>
      unfold PermEq
      rw [kappa_app, kappa_app, canonArgs_of_mul hst, canonArgs_of_mul hst]
      congr 2
      exact Multiset.coe_eq_coe.2 (hp.map _)
  | arg f pre post _ ih => exact kappa_app_arg st f pre post ih

theorem eqvGen_permStep_app (f : σ) :
    ∀ (pre l l' : List (Term σ ν)), List.Forall₂ (Relation.EqvGen (PermStep st)) l l' →
      Relation.EqvGen (PermStep st) (.app f (pre ++ l)) (.app f (pre ++ l')) := by
  intro pre l l' h
  induction h generalizing pre with
  | nil => exact .refl _
  | @cons a b l l' hab _ ih =>
      have hstep : Relation.EqvGen (PermStep st) (.app f (pre ++ a :: l))
          (.app f (pre ++ b :: l)) := by
        clear ih
        induction hab with
        | rel x y hxy => exact .rel _ _ (.arg f pre l hxy)
        | refl x => exact .refl _
        | symm x y _ ih' => exact .symm _ _ ih'
        | trans x y z _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
      have := ih (pre ++ [b])
      simp only [List.append_assoc, List.singleton_append] at this
      exact .trans _ _ _ hstep this

theorem eqvGen_permStep_kappa (t : Term σ ν) : Relation.EqvGen (PermStep st) t (kappa st t) := by
  induction t using Term.rec' with
  | hvar x => simpa using Relation.EqvGen.refl (Term.var x)
  | happ f args ih =>
      have h1 : Relation.EqvGen (PermStep st) (.app f args) (.app f (args.map (kappa st))) := by
        have := eqvGen_permStep_app (st := st) f [] args (args.map (kappa st)) ?_
        · simpa using this
        · rw [List.forall₂_map_right_iff]
          exact List.forall₂_same.2 ih
      rw [kappa_app]
      refine .trans _ _ _ h1 ?_
      cases hst : st f with
      | mul =>
          rw [canonArgs_of_mul hst]
          exact .rel _ _ (.root hst (Multiset.coe_eq_coe.1 (coe_sortTerms _)).symm)
      | lex π =>
          rw [canonArgs_of_lex hst]
          exact .refl _

/-- **The congruence is permutative congruence.** Two terms have equal representatives iff
they are connected by permutations of multiset-status arguments. -/
theorem permEq_iff_eqvGen (s t : Term σ ν) :
    PermEq st s t ↔ Relation.EqvGen (PermStep st) s t := by
  constructor
  · intro h
    have h1 := eqvGen_permStep_kappa (st := st) s
    have h2 := eqvGen_permStep_kappa (st := st) t
    unfold PermEq at h
    rw [h] at h1
    exact .trans _ _ _ h1 (.symm _ _ h2)
  · intro h
    induction h with
    | rel x y hxy => exact permEq_of_permStep hxy
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem RPOm.compat {s s' t t' : Term σ ν} (hs : PermEq st s s') (ht : PermEq st t t')
    (h : RPOm pr st s t) : RPOm pr st s' t' := by
  unfold RPOm PermEq at *
  rw [← hs, ← ht]
  exact h

theorem RPOm.wf (hwf : WellFounded pr) : WellFounded (fun u t : Term σ ν => RPOm pr st t u) :=
  Subrelation.wf (fun {_ _} h => h) (InvImage.wf (kappa st) (RPO.wf (ν := ν) (st := st) hwf))

theorem RPOm.irrefl (hwf : WellFounded pr) (t : Term σ ν) : ¬ RPOm pr st t t :=
  RPO.irrefl hwf (kappa st t)

theorem RPOm.trans (hpr : ∀ a b c : σ, pr a b → pr b c → pr a c) {s t u : Term σ ν}
    (h₁ : RPOm pr st s t) (h₂ : RPOm pr st t u) : RPOm pr st s u :=
  RPO.trans hpr h₁ h₂

theorem RPOm.bind {V W : Type} (θ : V → Term σ W) {s t : Term σ V} (h : RPOm pr st s t) :
    RPOm pr st (tbind θ s) (tbind θ t) := by
  unfold RPOm at *
  rw [← kappa_bind st θ s, ← kappa_bind st θ t]
  exact RPO.kappa_bind θ h

theorem RPOm.mono_arg (f : σ) (pre post : List (Term σ ν)) {a b : Term σ ν}
    (h : RPOm pr st a b) :
    RPOm pr st (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post)) := by
  unfold RPOm at *
  simp only [kappa_app, List.map_append, List.map_cons]
  cases hst : st f with
  | mul =>
      rw [canonArgs_of_mul hst, canonArgs_of_mul hst]
      refine RPO.of_DM hst ?_
      rw [coe_sortTerms, coe_sortTerms, coe_append_cons, coe_append_cons]
      exact ⟨_, {kappa st b}, {kappa st a}, Multiset.singleton_ne_zero _, rfl, rfl,
        fun y hy => ⟨kappa st a, Multiset.mem_singleton_self _, by
          rw [Multiset.mem_singleton.1 hy]; exact h⟩⟩
  | lex π =>
      rw [canonArgs_of_lex hst, canonArgs_of_lex hst]
      exact RPO.mono_arg f _ _ h

theorem RPOm.sub {f : σ} {args : List (Term σ ν)} {a : Term σ ν} (ha : a ∈ args) :
    RPOm pr st (.app f args) a := by
  unfold RPOm
  rw [kappa_app]
  exact .subEq ((canonArgs_mem _ _ _ _).2 (List.mem_map_of_mem ha))

theorem RPOm.subGt {f : σ} {args : List (Term σ ν)} {a t : Term σ ν} (ha : a ∈ args)
    (h : RPOm pr st a t) : RPOm pr st (.app f args) t := by
  unfold RPOm at *
  rw [kappa_app]
  exact .subGt _ ((canonArgs_mem _ _ _ _).2 (List.mem_map_of_mem ha)) h

theorem RPOm.prec {f g : σ} {args targs : List (Term σ ν)} (hfg : pr g f)
    (h : ∀ u ∈ targs, RPOm pr st (.app f args) u) : RPOm pr st (.app f args) (.app g targs) := by
  unfold RPOm at *
  have hx : ∀ u' ∈ canonArgs st g (targs.map (kappa st)),
      RPO pr st (kappa st (.app f args)) u' := by
    intro u' hu'
    rw [canonArgs_mem] at hu'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hu'
    exact h u hu
  rw [kappa_app st g targs]
  rw [kappa_app st f args] at hx ⊢
  exact .prec hfg hx

theorem RPOm.mul {f : σ} {args targs : List (Term σ ν)} (hst : st f = .mul)
    (h : DM (RPO pr st) (args.map (kappa st) : Multiset (Term σ ν))
      (targs.map (kappa st) : Multiset (Term σ ν))) :
    RPOm pr st (.app f args) (.app f targs) := by
  unfold RPOm
  rw [kappa_app, kappa_app]
  refine RPO.of_DM hst ?_
  rwa [canonArgs_coe, canonArgs_coe]

theorem RPOm.lex {f : σ} {args targs : List (Term σ ν)} (π : (n : Nat) → Equiv.Perm (Fin n))
    (hst : st f = .lex π) (n : Nat) (hn : args.length = n) (hn' : targs.length = n)
    (k : Fin n)
    (hpre : ∀ i : Fin n, i < k →
      PermEq st (args[(π n i).1]'(lt_of_lt_of_eq (π n i).2 hn.symm))
        (targs[(π n i).1]'(lt_of_lt_of_eq (π n i).2 hn'.symm)))
    (hcut : RPOm pr st (args[(π n k).1]'(lt_of_lt_of_eq (π n k).2 hn.symm))
      (targs[(π n k).1]'(lt_of_lt_of_eq (π n k).2 hn'.symm)))
    (hdom : ∀ u ∈ targs, RPOm pr st (.app f args) u) :
    RPOm pr st (.app f args) (.app f targs) := by
  unfold RPOm PermEq at *
  simp only [kappa_app, canonArgs_of_lex hst] at hdom ⊢
  refine .lex π hst n (by simpa using hn) (by simpa using hn') k ?_ ?_ ?_
  · intro i hi
    simp only [List.getElem_map]
    exact hpre i hi
  · simp only [List.getElem_map]
    exact hcut
  · intro u' hu'
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hu'
    exact hdom u hu

theorem RPOm.of_step {R : TRS σ ν} (hR : ∀ rule ∈ R, RPOm pr st rule.lhs rule.rhs)
    {s t : Term σ ν} (h : Step R s t) : RPOm pr st s t := by
  induction h with
  | root hroot =>
      obtain ⟨rule, hrule, θ, rfl, rfl⟩ := hroot
      have := RPOm.bind θ (hR rule hrule)
      simpa [tbind_eq_apply] using this
  | arg f pre post _ ih => exact RPOm.mono_arg f pre post ih

/-- **Soundness** for the order modulo permutative congruence. -/
theorem RPOm.step_wf (hwf : WellFounded pr) {R : TRS σ ν}
    (hR : ∀ rule ∈ R, RPOm pr st rule.lhs rule.rhs) :
    WellFounded (fun u t : Term σ ν => Step R t u) :=
  Subrelation.wf (fun {_ _} h => RPOm.of_step hR h) (RPOm.wf hwf)

end Canon

/-! ## 7. The free recursor schema as a first-order system -/

/-- The four symbols of the free schema. -/
inductive Sym where
  | zero | succ | wrap | recur
  deriving DecidableEq, Repr, Fintype

open OperatorKO7.Methods.OrientationClosure.SchemaCore

/-- Adapter from the free schema to first-order terms over `Sym`. -/
def toTerm {ν : Type} : FreeTerm ν → Term Sym ν
  | .var x => .var x
  | .zero => .app .zero []
  | .succ t => .app .succ [toTerm t]
  | .wrap s t => .app .wrap [toTerm s, toTerm t]
  | .recur b s n => .app .recur [toTerm b, toTerm s, toTerm n]

/-- Variables of the two rule schemas. -/
inductive RuleVar where
  | b | s | n
  deriving DecidableEq, Repr

/-- Left-hand side of `recur b s zero → b`. -/
def ruleLhsZero : Term Sym RuleVar := .app .recur [.var .b, .var .s, .app .zero []]
/-- Right-hand side of `recur b s zero → b`. -/
def ruleRhsZero : Term Sym RuleVar := .var .b
/-- Left-hand side of the duplicating rule `recur b s (succ n) → wrap s (recur b s n)`. -/
def ruleLhsSucc : Term Sym RuleVar := .app .recur [.var .b, .var .s, .app .succ [.var .n]]
/-- Right-hand side of the duplicating rule. -/
def ruleRhsSucc : Term Sym RuleVar :=
  .app .wrap [.var .s, .app .recur [.var .b, .var .s, .var .n]]

/-- Instantiation of the rule variables by translated free terms. -/
def ruleInst {ν : Type} (b s n : FreeTerm ν) : RuleVar → Term Sym ν
  | .b => toTerm b
  | .s => toTerm s
  | .n => toTerm n

theorem ruleInst_zero {ν : Type} (b s : FreeTerm ν) :
    tbind (ruleInst b s .zero) ruleLhsZero = toTerm (.recur b s .zero) ∧
      tbind (ruleInst b s .zero) ruleRhsZero = toTerm b := by
  constructor <;> simp [ruleLhsZero, ruleRhsZero, ruleInst, toTerm]

theorem ruleInst_succ {ν : Type} (b s n : FreeTerm ν) :
    tbind (ruleInst b s n) ruleLhsSucc = toTerm (.recur b s (.succ n)) ∧
      tbind (ruleInst b s n) ruleRhsSucc = toTerm (.wrap s (.recur b s n)) := by
  constructor <;> simp [ruleLhsSucc, ruleRhsSucc, ruleInst, toTerm]

/-- An order closed under argument contexts that orients the root rules orients every
contextual step of the free schema. -/
theorem toTerm_contextStep {ν : Type} (O : Term Sym ν → Term Sym ν → Prop)
    (hmono : ∀ (f : Sym) (pre post : List (Term Sym ν)) {a b : Term Sym ν}, O a b →
      O (.app f (pre ++ a :: post)) (.app f (pre ++ b :: post)))
    (hroot : ∀ {t u : FreeTerm ν}, RootStep t u → O (toTerm t) (toTerm u))
    {t u : FreeTerm ν} (h : ContextStep t u) : O (toTerm t) (toTerm u) := by
  cases h with
  | lift C hr =>
    induction C with
    | hole => exact hroot hr
    | succ C ih => exact hmono .succ [] [] ih
    | wrapLeft C r ih => exact hmono .wrap [] [toTerm r] ih
    | wrapRight l C ih => exact hmono .wrap [toTerm l] [] ih
    | recurBase C s n ih => exact hmono .recur [] [toTerm s, toTerm n] ih
    | recurStep b C n ih => exact hmono .recur [toTerm b] [toTerm n] ih
    | recurCounter b s C ih => exact hmono .recur [toTerm b, toTerm s] [] ih

theorem freeContext_wf_of {ν : Type} (O : Term Sym ν → Term Sym ν → Prop)
    (hwf : WellFounded (fun u t => O t u))
    (hstep : ∀ {t u : FreeTerm ν}, ContextStep t u → O (toTerm t) (toTerm u)) :
    WellFounded (fun u t : FreeTerm ν => ContextStep t u) :=
  Subrelation.wf (fun {_ _} h => hstep h) (InvImage.wf toTerm hwf)

theorem rpom_rootStep {ν : Type} {pr : Sym → Sym → Prop} {st : Sym → ArgStatus}
    (hZ : RPOm pr st ruleLhsZero ruleRhsZero) (hS : RPOm pr st ruleLhsSucc ruleRhsSucc) :
    ∀ {t u : FreeTerm ν}, RootStep t u → RPOm pr st (toTerm t) (toTerm u)
  | _, _, .recurZero b s => by
      have := RPOm.bind (ruleInst b s .zero) hZ
      rwa [(ruleInst_zero b s).1, (ruleInst_zero b s).2] at this
  | _, _, .recurSucc b s n => by
      have := RPOm.bind (ruleInst b s n) hS
      rwa [(ruleInst_succ b s n).1, (ruleInst_succ b s n).2] at this

theorem rpom_contextStep {ν : Type} {pr : Sym → Sym → Prop} {st : Sym → ArgStatus}
    (hZ : RPOm pr st ruleLhsZero ruleRhsZero) (hS : RPOm pr st ruleLhsSucc ruleRhsSucc)
    {t u : FreeTerm ν} (h : ContextStep t u) : RPOm pr st (toTerm t) (toTerm u) :=
  toTerm_contextStep (RPOm pr st) (fun f pre post _ _ hab => RPOm.mono_arg f pre post hab)
    (rpom_rootStep hZ hS) h

theorem rpom_zero_rule (pr : Sym → Sym → Prop) (st : Sym → ArgStatus) :
    RPOm pr st ruleLhsZero ruleRhsZero :=
  RPOm.sub (by simp [ruleRhsZero])

/-- Orientation of the duplicating rule by any status once `wrap` lies below `recur`. -/
theorem rpom_succ_rule {pr : Sym → Sym → Prop} {st : Sym → ArgStatus}
    (hprec : pr .wrap .recur) : RPOm pr st ruleLhsSucc ruleRhsSucc := by
  refine RPOm.prec hprec ?_
  intro u hu
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with rfl | rfl
  · exact RPOm.sub (by simp)
  · exact RPOm.mono_arg (st := st) Sym.recur
      [(Term.var RuleVar.b : Term Sym RuleVar), Term.var RuleVar.s] []
      (RPOm.sub (f := Sym.succ) (args := [Term.var RuleVar.n]) (List.mem_singleton_self _))

/-- The precedence `wrap < recur` is necessary: the variable condition excludes every other
clause. -/
theorem rpom_succ_rule_prec {pr : Sym → Sym → Prop} {st : Sym → ArgStatus}
    (h : RPOm pr st ruleLhsSucc ruleRhsSucc) : pr .wrap .recur := by
  unfold RPOm ruleLhsSucc ruleRhsSucc at h
  rw [kappa_app, kappa_app] at h
  rcases RPO.app_iff.1 h with ⟨a, ha, hEq | hat⟩ | ⟨g, targs, hgt, hhead, _⟩
  · rw [canonArgs_mem] at ha
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false,
      kappa_var] at ha
    rcases ha with rfl | rfl | rfl
    · cases hEq
    · cases hEq
    · rw [kappa_app] at hEq
      cases hEq
  · have hocc : Occurs RuleVar.s (Term.app Sym.wrap (canonArgs st .wrap
        ([Term.var RuleVar.s, Term.app Sym.recur [.var .b, .var .s, .var .n]].map (kappa st)))) :=
      .arg ((canonArgs_mem _ _ _ _).2 (by simp)) .here
    have hs := RPO.occurs hat hocc
    rw [canonArgs_mem] at ha
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false,
      kappa_var] at ha
    rcases ha with rfl | rfl | rfl
    · cases hs
    · exact absurd hat RPO.not_var_left
    · rw [kappa_app] at hs
      cases hs with
      | arg hu hxu =>
          rw [canonArgs_mem] at hu
          simp only [List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false,
            kappa_var] at hu
          subst hu
          cases hxu
  · cases hgt
    rcases hhead with hp | ⟨hgf, _⟩ | ⟨hgf, _⟩
    · exact hp
    · cases hgf
    · cases hgf

theorem rpom_succ_rule_iff {pr : Sym → Sym → Prop} {st : Sym → ArgStatus} :
    RPOm pr st ruleLhsSucc ruleRhsSucc ↔ pr .wrap .recur :=
  ⟨rpom_succ_rule_prec, rpom_succ_rule⟩

/-! ## 8. Row `rpoModuloPermutation` -/

/-- Native data: a precedence and an argument status (multiset, or lexicographic in a
permutation of the positions) for each symbol of the free signature. -/
structure rpoModuloPermutationData : Type where
  prec : Sym → Sym → Prop
  status : Sym → ArgStatus

/-- Admissibility: Dershowitz 1987 (J. Symbolic Comput. 3, pp. 69–115), Definition 18 with the
status combination of p. 98 and Theorem 23. The precedence is a transitive, well-founded strict
order; every status is admissible. -/
def rpoModuloPermutationLaws (M : rpoModuloPermutationData) : Prop :=
  (∀ a b c, M.prec a b → M.prec b c → M.prec a c) ∧ WellFounded M.prec

/-- The method's own acceptance of the free two-rule system: both rule schemas decrease in the
order modulo permutative congruence. Adapter: `toTerm`, rule variables `RuleVar`. -/
def rpoModuloPermutationAccepts (M : rpoModuloPermutationData) : Prop :=
  RPOm M.prec M.status ruleLhsZero ruleRhsZero ∧ RPOm M.prec M.status ruleLhsSucc ruleRhsSucc

/-- Verdict: escape. The method accepts the free two-rule system, and its soundness theorem
yields termination of the contextual relation `SchemaCore.ContextStep` over every variable
type. -/
def rpoModuloPermutationResult (M : rpoModuloPermutationData) : Prop :=
  rpoModuloPermutationAccepts M ∧
    ∀ ν : Type, WellFounded (fun u t : FreeTerm ν => ContextStep t u)

/-- **Soundness** of the method on the free system: acceptance and admissibility give
termination of `ContextStep`. The proof uses stability under substitution, closure under
argument contexts and well-foundedness of the order. -/
theorem rpoModuloPermutation_sound : ∀ M : rpoModuloPermutationData,
    rpoModuloPermutationLaws M → rpoModuloPermutationAccepts M →
      ∀ ν : Type, WellFounded (fun u t : FreeTerm ν => ContextStep t u) := by
  intro M hL hA ν
  exact freeContext_wf_of (RPOm M.prec M.status) (RPOm.wf hL.2)
    (fun h => rpom_contextStep hA.1 hA.2 h)

/-- Rank of the witness precedence `zero < succ < wrap < recur`. -/
def symRank : Sym → Nat
  | .zero => 0
  | .succ => 1
  | .wrap => 2
  | .recur => 3

/-- Witness status: `recur` compares its arguments lexicographically from the last position
(the counter) to the first; the other symbols use multiset status. -/
def revStatus : Sym → ArgStatus
  | .recur => .lex (fun _ => Fin.revPerm)
  | _ => .mul

def rpoModuloPermutationWitness : rpoModuloPermutationData where
  prec := fun a b => symRank a < symRank b
  status := revStatus

theorem rpoModuloPermutationWitness_laws :
    rpoModuloPermutationLaws rpoModuloPermutationWitness :=
  ⟨fun _ _ _ h₁ h₂ => lt_trans h₁ h₂, InvImage.wf symRank Nat.lt_wfRel.wf⟩

theorem rpoModuloPermutationWitness_accepts :
    rpoModuloPermutationAccepts rpoModuloPermutationWitness :=
  ⟨rpom_zero_rule _ _, rpom_succ_rule (show symRank Sym.wrap < symRank Sym.recur by decide)⟩

theorem rpoModuloPermutationWitness_result :
    rpoModuloPermutationResult rpoModuloPermutationWitness :=
  ⟨rpoModuloPermutationWitness_accepts,
    rpoModuloPermutation_sound _ rpoModuloPermutationWitness_laws
      rpoModuloPermutationWitness_accepts⟩

/-- Two ground recursor terms that the counter-first permutation and the identity permutation
order in opposite directions. -/
def permProbeA : Term Sym RuleVar :=
  .app .recur [.app .zero [], .app .zero [], .app .succ [.app .zero []]]
def permProbeB : Term Sym RuleVar :=
  .app .recur [.app .succ [.app .zero []], .app .zero [], .app .zero []]

/-- The witness with the identity permutation for `recur`. -/
def idStatus : Sym → ArgStatus
  | .recur => .lex (fun n => Equiv.refl (Fin n))
  | _ => .mul

/-- **Defining feature.** The status permutation acts on the recursive argument comparison:
with the counter-first permutation `permProbeA` lies above `permProbeB`, the reverse comparison
fails, and with the identity permutation `permProbeB` lies above `permProbeA`. The permutation
is not the identity. Compatibility: arguments of the multiset-status symbol `wrap` commute up to
permutative congruence, and the order does not separate congruent terms. -/
theorem rpoModuloPermutationWitness_feature :
    RPOm rpoModuloPermutationWitness.prec rpoModuloPermutationWitness.status permProbeA
        permProbeB ∧
      ¬ RPOm rpoModuloPermutationWitness.prec rpoModuloPermutationWitness.status permProbeB
        permProbeA ∧
      RPOm rpoModuloPermutationWitness.prec idStatus permProbeB permProbeA ∧
      (Fin.revPerm : Equiv.Perm (Fin 3)) ≠ Equiv.refl (Fin 3) ∧
      PermEq revStatus (Term.app Sym.wrap [permProbeA, permProbeB])
        (Term.app Sym.wrap [permProbeB, permProbeA]) := by
  have hAB : RPOm rpoModuloPermutationWitness.prec rpoModuloPermutationWitness.status
      permProbeA permProbeB := by
    refine RPOm.lex (fun _ => Fin.revPerm) rfl 3 rfl rfl 0 ?_ ?_ ?_
    · intro i hi
      exact absurd hi (Fin.not_lt_zero i)
    · exact RPOm.sub (by simp)
    · intro u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> exact RPOm.sub (by simp)
  refine ⟨hAB, ?_, ?_, ?_, ?_⟩
  · intro hBA
    exact RPOm.irrefl rpoModuloPermutationWitness_laws.2 _
      (RPOm.trans rpoModuloPermutationWitness_laws.1 hAB hBA)
  · refine RPOm.lex (fun n => Equiv.refl (Fin n)) rfl 3 rfl rfl 0 ?_ ?_ ?_
    · intro i hi
      exact absurd hi (Fin.not_lt_zero i)
    · exact RPOm.sub (by simp)
    · intro u hu
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
      rcases hu with rfl | rfl | rfl <;> exact RPOm.sub (by simp)
  · intro h
    have := congrArg (fun e : Equiv.Perm (Fin 3) => (e 0 : Nat)) h
    simp at this
  · exact permEq_of_permStep (.root rfl (List.Perm.swap _ _ []))

/-- **Mutation.** Placing `wrap` above `recur` in the precedence, everything else fixed, makes
the method reject the duplicating rule. -/
theorem rpoModuloPermutation_mutation :
    ¬ rpoModuloPermutationAccepts
      { rpoModuloPermutationWitness with prec := fun a b => symRank b < symRank a } := by
  intro h
  have := rpom_succ_rule_prec h.2
  simp [symRank] at this

/-! ## 9. The polynomial path order POP* over an arbitrary signature

Avanzini and Moser, *Polynomial path orders*, Logical Methods in Computer Science 9(4:9), 2013:
Definition 3.1 (safe mapping; constructors have only safe positions), Definition 3.2 (safe
equivalence), Definition 3.3 (admissible precedence), Definition 3.4 (auxiliary order `>pop`),
Definition 3.5 (polynomial path order `>pop*`), Definition 3.6 (predicative recursive constructor
TRS), Theorem 3.11 (the innermost derivation height of basic terms is polynomial in the depth of
the normal arguments). As in the convention after Definition 3.2, the normal positions of a
symbol come first and `nrm f` is their number. The precedence is strict, so its equivalence is
equality of symbols and Definition 3.3 holds for every precedence. Safe equivalence is realized
by sorting the normal block and the safe block of every argument list. -/

section PopStar

variable {σ ν : Type}

theorem sortTerms_zero : sortTerms (0 : Multiset (Term σ ν)) = [] := by
  letI := termLinearOrder σ ν
  unfold sortTerms
  exact Multiset.sort_zero (· ≤ ·)

theorem sortTerms_singleton (a : Term σ ν) : sortTerms ({a} : Multiset (Term σ ν)) = [a] := by
  letI := termLinearOrder σ ν
  unfold sortTerms
  exact Multiset.sort_singleton (· ≤ ·) a

/-- POP* data on a signature: strict precedence, defined symbols, number of normal
positions. -/
structure PopData (σ : Type) where
  prec : σ → σ → Prop
  isDef : σ → Prop
  nrm : σ → Nat

/-- Representative argument list under safe equivalence. -/
noncomputable def canonPop (D : PopData σ) (f : σ) (l : List (Term σ ν)) : List (Term σ ν) :=
  sortTerms ((l.take (D.nrm f) : List (Term σ ν)) : Multiset (Term σ ν)) ++
    sortTerms ((l.drop (D.nrm f) : List (Term σ ν)) : Multiset (Term σ ν))

theorem canonPop_coe (D : PopData σ) (f : σ) (l : List (Term σ ν)) :
    (canonPop D f l : Multiset (Term σ ν)) = l := by
  unfold canonPop
  rw [← Multiset.coe_add, coe_sortTerms, coe_sortTerms, Multiset.coe_add, List.take_append_drop]

theorem canonPop_mem (D : PopData σ) (f : σ) (l : List (Term σ ν)) (x : Term σ ν) :
    x ∈ canonPop D f l ↔ x ∈ l := by
  rw [← Multiset.mem_coe, canonPop_coe, Multiset.mem_coe]

theorem canonPop_singleton (D : PopData σ) (f : σ) (a : Term σ ν) : canonPop D f [a] = [a] := by
  unfold canonPop
  cases D.nrm f with
  | zero => simp [sortTerms_zero, sortTerms_singleton]
  | succ k => simp [sortTerms_zero, sortTerms_singleton]

mutual
/-- Safe-equivalence representative of a term. -/
noncomputable def kappaP (D : PopData σ) : Term σ ν → Term σ ν
  | .var x => .var x
  | .app f args => .app f (canonPop D f (kappaPList D args))
/-- `kappaP` on argument lists. -/
noncomputable def kappaPList (D : PopData σ) : List (Term σ ν) → List (Term σ ν)
  | [] => []
  | a :: as => kappaP D a :: kappaPList D as
end

theorem kappaPList_eq_map (D : PopData σ) (l : List (Term σ ν)) :
    kappaPList D l = l.map (kappaP D) := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [kappaPList, ih]

@[simp] theorem kappaP_var (D : PopData σ) (x : ν) :
    kappaP (σ := σ) D (.var x) = .var x := by
  simp [kappaP]

theorem kappaP_app (D : PopData σ) (f : σ) (args : List (Term σ ν)) :
    kappaP D (.app f args) = .app f (canonPop D f (args.map (kappaP D))) := by
  simp [kappaP, kappaPList_eq_map]

/-- Multiset status for every symbol: the multiset path order. -/
def mulSt : σ → ArgStatus := fun _ => .mul

theorem kappaM_kappaP (D : PopData σ) (t : Term σ ν) :
    kappa mulSt (kappaP D t) = kappa mulSt t := by
  induction t using Term.rec' with
  | hvar x => simp
  | happ f args ih =>
      rw [kappaP_app, kappa_app, kappa_app, canonArgs_of_mul (st := mulSt) (f := f) rfl,
        canonArgs_of_mul (st := mulSt) (f := f) rfl]
      congr 1
      rw [← Multiset.map_coe, canonPop_coe, Multiset.map_coe, List.map_map]
      congr 2
      exact List.map_congr_left ih

/-- `BelowF prec f t`: every symbol of `t` lies below `f` (the set `T(F≺f, V)`). -/
inductive BelowF (prec : σ → σ → Prop) (f : σ) : Term σ ν → Prop
  | var (x : ν) : BelowF prec f (.var x)
  | app {g : σ} {args : List (Term σ ν)} (hg : prec g f) (h : ∀ a ∈ args, BelowF prec f a) :
      BelowF prec f (.app g args)

/-- The auxiliary order `>pop` (Definition 3.4). Equality in `⩾pop` is safe equivalence. -/
inductive PopAux (D : PopData σ) : Term σ ν → Term σ ν → Prop
  | subEq {f : σ} {args : List (Term σ ν)} {t : Term σ ν} (a : Term σ ν) (ha : a ∈ args)
      (hpos : D.isDef f → a ∈ args.take (D.nrm f)) (heq : kappaP D a = kappaP D t) :
      PopAux D (.app f args) t
  | subGt {f : σ} {args : List (Term σ ν)} {t : Term σ ν} (a : Term σ ν) (ha : a ∈ args)
      (hpos : D.isDef f → a ∈ args.take (D.nrm f)) (h : PopAux D a t) :
      PopAux D (.app f args) t
  | prec {f g : σ} {args targs : List (Term σ ν)} (hD : D.isDef f) (hfg : D.prec g f)
      (h : ∀ u ∈ targs, PopAux D (.app f args) u) : PopAux D (.app f args) (.app g targs)

/-- The polynomial path order `>pop*` (Definition 3.5). The multiset comparisons of clause (3)
are taken modulo safe equivalence, on representatives. -/
inductive Pop (D : PopData σ) : Term σ ν → Term σ ν → Prop
  | subEq {f : σ} {args : List (Term σ ν)} {t : Term σ ν} (a : Term σ ν) (ha : a ∈ args)
      (heq : kappaP D a = kappaP D t) : Pop D (.app f args) t
  | subGt {f : σ} {args : List (Term σ ν)} {t : Term σ ν} (a : Term σ ν) (ha : a ∈ args)
      (h : Pop D a t) : Pop D (.app f args) t
  | comp {f g : σ} {args targs : List (Term σ ν)} (hD : D.isDef f) (hfg : D.prec g f)
      (hnrm : ∀ u ∈ targs.take (D.nrm g), PopAux D (.app f args) u)
      (hsafe : ∀ u ∈ targs.drop (D.nrm g), Pop D (.app f args) u)
      (hone : (targs.drop (D.nrm g)).Pairwise
        (fun u w => BelowF D.prec f u ∨ BelowF D.prec f w)) :
      Pop D (.app f args) (.app g targs)
  | eqHead {f : σ} {args targs : List (Term σ ν)} (hD : D.isDef f)
      (X Y Z : Multiset (Term σ ν)) (φ : Term σ ν → Term σ ν) (hZ : Z ≠ 0)
      (hs : (((args.take (D.nrm f)).map (kappaP D) : List (Term σ ν)) : Multiset (Term σ ν)) =
        X + Z)
      (ht : (((targs.take (D.nrm f)).map (kappaP D) : List (Term σ ν)) : Multiset (Term σ ν)) =
        X + Y)
      (hφZ : ∀ y ∈ Y, φ y ∈ Z) (hφ : ∀ y ∈ Y, Pop D (φ y) y)
      (X' Y' Z' : Multiset (Term σ ν)) (φ' : Term σ ν → Term σ ν)
      (hs' : (((args.drop (D.nrm f)).map (kappaP D) : List (Term σ ν)) : Multiset (Term σ ν)) =
        X' + Z')
      (ht' : (((targs.drop (D.nrm f)).map (kappaP D) : List (Term σ ν)) : Multiset (Term σ ν)) =
        X' + Y')
      (hφZ' : ∀ y ∈ Y', φ' y ∈ Z') (hφ' : ∀ y ∈ Y', Pop D (φ' y) y) :
      Pop D (.app f args) (.app f targs)

theorem permEq_mul_of_kappaP {D : PopData σ} {a t : Term σ ν}
    (h : kappaP D a = kappaP D t) : PermEq mulSt a t := by
  unfold PermEq
  rw [← kappaM_kappaP D a, h, kappaM_kappaP]

/-- `>pop` is contained in the multiset path order modulo permutation. -/
theorem PopAux.toMPO {D : PopData σ} {s t : Term σ ν} (h : PopAux D s t) :
    RPOm D.prec mulSt s t := by
  induction h with
  | subEq a ha _ heq => exact RPOm.compat rfl (permEq_mul_of_kappaP heq) (RPOm.sub ha)
  | subGt a ha _ _ ih => exact RPOm.subGt ha ih
  | prec _ hfg _ ih => exact RPOm.prec hfg ih

/-- **`>pop*` is a restriction of the multiset path order** (the remark after
Definition 3.5). -/
theorem Pop.toMPO {D : PopData σ} {s t : Term σ ν} (h : Pop D s t) :
    RPOm D.prec mulSt s t := by
  classical
  induction h with
  | subEq a ha heq => exact RPOm.compat rfl (permEq_mul_of_kappaP heq) (RPOm.sub ha)
  | subGt a ha _ ih => exact RPOm.subGt ha ih
  | @comp f g args targs _ hfg hnrm _ _ ih =>
      refine RPOm.prec hfg ?_
      intro u hu
      rw [← List.take_append_drop (D.nrm g) targs] at hu
      rcases List.mem_append.1 hu with hu1 | hu2
      · exact (hnrm u hu1).toMPO
      · exact ih u hu2
  | @eqHead f args targs _ X Y Z φ hZ hs ht hφZ _ X' Y' Z' φ' hs' ht' hφZ' _ ih ih' =>
      refine RPOm.mul rfl ?_
      have hcomp : ∀ l : List (Term σ ν),
          (l.map (kappaP D)).map (kappa mulSt) = l.map (kappa mulSt) := by
        intro l
        rw [List.map_map]
        exact List.map_congr_left (fun a _ => kappaM_kappaP D a)
      have hsplit : ∀ l : List (Term σ ν),
          ((l.map (kappa mulSt) : List (Term σ ν)) : Multiset (Term σ ν)) =
            Multiset.map (kappa mulSt)
                (((l.take (D.nrm f)).map (kappaP D) : List (Term σ ν)) : Multiset (Term σ ν)) +
              Multiset.map (kappa mulSt)
                (((l.drop (D.nrm f)).map (kappaP D) : List (Term σ ν)) : Multiset (Term σ ν)) := by
        intro l
        rw [Multiset.map_coe, Multiset.map_coe, hcomp, hcomp, Multiset.coe_add, ← List.map_append,
          List.take_append_drop]
      rw [hsplit args, hsplit targs, hs, ht, hs', ht']
      refine ⟨Multiset.map (kappa mulSt) X + Multiset.map (kappa mulSt) X',
        Multiset.map (kappa mulSt) Y + Multiset.map (kappa mulSt) Y',
        Multiset.map (kappa mulSt) Z + Multiset.map (kappa mulSt) Z', ?_, ?_, ?_, ?_⟩
      · intro h0
        apply hZ
        have hle : Multiset.map (kappa mulSt) Z ≤ 0 :=
          (Multiset.le_add_right _ _).trans h0.le
        exact Multiset.map_eq_zero.1 (le_antisymm hle (Multiset.zero_le _))
      · rw [Multiset.map_add, Multiset.map_add, add_add_add_comm]
      · rw [Multiset.map_add, Multiset.map_add, add_add_add_comm]
      · intro y hy
        rcases Multiset.mem_add.1 hy with hy1 | hy2
        · obtain ⟨y₀, hy₀, rfl⟩ := Multiset.mem_map.1 hy1
          exact ⟨kappa mulSt (φ y₀),
            Multiset.mem_add.2 (Or.inl (Multiset.mem_map_of_mem _ (hφZ y₀ hy₀))), ih y₀ hy₀⟩
        · obtain ⟨y₀, hy₀, rfl⟩ := Multiset.mem_map.1 hy2
          exact ⟨kappa mulSt (φ' y₀),
            Multiset.mem_add.2 (Or.inr (Multiset.mem_map_of_mem _ (hφZ' y₀ hy₀))), ih' y₀ hy₀⟩

/-- **Irreflexivity** of `>pop*` for a well-founded precedence. -/
theorem Pop.irrefl {D : PopData σ} (hwf : WellFounded D.prec) (t : Term σ ν) : ¬ Pop D t t :=
  fun h => RPOm.irrefl hwf t h.toMPO

/-- **Well-foundedness** of `>pop*` for a well-founded precedence. -/
theorem Pop.wf {D : PopData σ} (hwf : WellFounded D.prec) :
    WellFounded (fun u t : Term σ ν => Pop D t u) :=
  Subrelation.wf (fun {_ _} h => h.toMPO) (RPOm.wf hwf)

/-- **Termination** of every system contained in `>pop*` (POP* is a restriction of MPO and thus
a termination order; Avanzini–Moser 2013, remark after Definition 3.5). -/
theorem Pop.step_wf {D : PopData σ} (hwf : WellFounded D.prec) {R : TRS σ ν}
    (hR : ∀ rule ∈ R, Pop D rule.lhs rule.rhs) :
    WellFounded (fun u t : Term σ ν => Step R t u) :=
  RPOm.step_wf hwf (fun rule hrule => (hR rule hrule).toMPO)

theorem occurs_app_iff {x : ν} {f : σ} {args : List (Term σ ν)} :
    Occurs x (.app f args) ↔ ∃ a ∈ args, Occurs x a := by
  constructor
  · intro h
    cases h with
    | arg ha h => exact ⟨_, ha, h⟩
  · rintro ⟨a, ha, h⟩
    exact .arg ha h

theorem occurs_kappa (st : σ → ArgStatus) (x : ν) (t : Term σ ν) :
    Occurs x (kappa st t) ↔ Occurs x t := by
  induction t using Term.rec' with
  | hvar y => simp
  | happ f args ih =>
      rw [kappa_app, occurs_app_iff, occurs_app_iff]
      constructor
      · rintro ⟨a', ha', hx⟩
        rw [canonArgs_mem] at ha'
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 ha'
        exact ⟨a, ha, (ih a ha).1 hx⟩
      · rintro ⟨a, ha, hx⟩
        exact ⟨kappa st a, (canonArgs_mem _ _ _ _).2 (List.mem_map_of_mem ha), (ih a ha).2 hx⟩

/-- Variable condition for the order modulo permutation. -/
theorem RPOm.occurs {pr : σ → σ → Prop} {st : σ → ArgStatus} {x : ν} {s t : Term σ ν}
    (h : RPOm pr st s t) (hx : Occurs x t) : Occurs x s :=
  (occurs_kappa st x s).1 (RPO.occurs h ((occurs_kappa st x t).2 hx))

end PopStar

/-! ## 10. Row `popStarFamily` -/

/-- Native data of `popStarFamily` on the free signature: the precedence and the safe positions
of the defined symbol `recur`. The constructors `zero`, `succ`, `wrap` have only safe positions
(Definition 3.1). -/
structure popStarFamilyData : Type where
  prec : Sym → Sym → Prop
  safeB : Bool
  safeS : Bool
  safeN : Bool

/-- Normal arguments of `recur`, in the order base, step, counter. -/
def recurNormals {α : Type} (sb ss sn : Bool) (b s n : α) : List α :=
  (if sb then [] else [b]) ++ (if ss then [] else [s]) ++ (if sn then [] else [n])

/-- Safe arguments of `recur`, in the order base, step, counter. -/
def recurSafes {α : Type} (sb ss sn : Bool) (b s n : α) : List α :=
  (if sb then [b] else []) ++ (if ss then [s] else []) ++ (if sn then [n] else [])

/-- Normal-first presentation of the arguments of `recur`. -/
def recurArgs {α : Type} (sb ss sn : Bool) (b s n : α) : List α :=
  recurNormals sb ss sn b s n ++ recurSafes sb ss sn b s n

/-- Number of normal positions of `recur`. -/
def recurNrm (sb ss sn : Bool) : Nat :=
  (if sb then 0 else 1) + (if ss then 0 else 1) + (if sn then 0 else 1)

theorem length_recurNormals {α : Type} (sb ss sn : Bool) (b s n : α) :
    (recurNormals sb ss sn b s n).length = recurNrm sb ss sn := by
  cases sb <;> cases ss <;> cases sn <;> rfl

theorem take_recurArgs {α : Type} (sb ss sn : Bool) (b s n : α) :
    (recurArgs sb ss sn b s n).take (recurNrm sb ss sn) = recurNormals sb ss sn b s n :=
  List.take_left' (length_recurNormals sb ss sn b s n)

theorem drop_recurArgs {α : Type} (sb ss sn : Bool) (b s n : α) :
    (recurArgs sb ss sn b s n).drop (recurNrm sb ss sn) = recurSafes sb ss sn b s n :=
  List.drop_left' (length_recurNormals sb ss sn b s n)

theorem recurArgs_perm {α : Type} (sb ss sn : Bool) (b s n : α) :
    (recurArgs sb ss sn b s n).Perm [b, s, n] := by
  cases sb <;> cases ss <;> cases sn <;>
    simp only [recurArgs, recurNormals, recurSafes, Bool.false_eq_true, if_false, if_true,
      List.nil_append, List.append_nil, List.cons_append]
  all_goals first
    | exact List.Perm.refl _
    | exact List.Perm.cons _ (List.Perm.swap _ _ _)
    | exact List.Perm.swap _ _ _
    | exact List.perm_append_comm (l₁ := [_, _]) (l₂ := [_])
    | exact List.perm_append_comm (l₁ := [_]) (l₂ := [_, _])

theorem mem_recurArgs {α : Type} (sb ss sn : Bool) (b s n x : α) :
    x ∈ recurArgs sb ss sn b s n ↔ x = b ∨ x = s ∨ x = n := by
  rw [(recurArgs_perm sb ss sn b s n).mem_iff]
  simp

theorem mem_recurNormals_true {α : Type} (sb ss : Bool) {b s n x : α}
    (h : x ∈ recurNormals sb ss true b s n) : x = b ∨ x = s := by
  cases sb <;> cases ss <;> simp [recurNormals] at h <;> tauto

theorem recurNormals_false {α : Type} (sb ss : Bool) (b s n : α) :
    recurNormals sb ss false b s n = recurNormals sb ss true b s n ++ [n] := by
  simp [recurNormals]

theorem recurNormals_true_indep {α : Type} (sb ss : Bool) (b s n n' : α) :
    recurNormals sb ss true b s n = recurNormals sb ss true b s n' := by
  simp [recurNormals]

theorem recurSafes_false {α : Type} (sb ss : Bool) (b s n n' : α) :
    recurSafes sb ss false b s n = recurSafes sb ss false b s n' := by
  simp [recurSafes]

/-- POP* data of the free signature: `recur` is the only defined symbol. -/
def popDataOf (M : popStarFamilyData) : PopData Sym where
  prec := M.prec
  isDef := fun f => f = .recur
  nrm := fun f => match f with
    | .recur => recurNrm M.safeB M.safeS M.safeN
    | _ => 0

/-- POP* presentation of `recur b s zero`. -/
def popLhsZero (M : popStarFamilyData) : Term Sym RuleVar :=
  .app .recur (recurArgs M.safeB M.safeS M.safeN (.var .b) (.var .s) (.app .zero []))
/-- POP* presentation of `recur b s (succ n)`. -/
def popLhsSucc (M : popStarFamilyData) : Term Sym RuleVar :=
  .app .recur (recurArgs M.safeB M.safeS M.safeN (.var .b) (.var .s) (.app .succ [.var .n]))
/-- The recursive call `recur b s n` in POP* presentation. -/
def popRecCall (M : popStarFamilyData) : Term Sym RuleVar :=
  .app .recur (recurArgs M.safeB M.safeS M.safeN (.var .b) (.var .s) (.var .n))
/-- POP* presentation of `wrap s (recur b s n)`. -/
def popRhsSucc (M : popStarFamilyData) : Term Sym RuleVar :=
  .app .wrap [.var .s, popRecCall M]

theorem kappaM_recurArgs {ν : Type} (sb ss sn : Bool) (b s n : Term Sym ν) :
    kappa mulSt (Term.app Sym.recur (recurArgs sb ss sn b s n)) =
      kappa mulSt (Term.app Sym.recur [b, s, n]) := by
  rw [kappa_app, kappa_app, canonArgs_of_mul (st := mulSt) (f := Sym.recur) rfl,
    canonArgs_of_mul (st := mulSt) (f := Sym.recur) rfl]
  congr 2
  exact Multiset.coe_eq_coe.2 ((recurArgs_perm sb ss sn b s n).map _)

/-- Admissibility (Avanzini–Moser 2013, Definitions 3.1, 3.3 and 3.6): the precedence is a
strict partial order on the finite signature. -/
def popStarFamilyLaws (M : popStarFamilyData) : Prop :=
  (∀ a, ¬ M.prec a a) ∧ (∀ a b c, M.prec a b → M.prec b c → M.prec a c)

theorem popStarFamily_prec_wf {M : popStarFamilyData} (hL : popStarFamilyLaws M) :
    WellFounded M.prec :=
  @Finite.wellFounded_of_trans_of_irrefl Sym _ M.prec ⟨fun a b c => hL.2 a b c⟩ ⟨hL.1⟩

/-- The method's own acceptance of the free two-rule system: both rules decrease in `>pop*`
(Definition 3.6, predicative recursive). Adapter: the normal-first presentation of `recur`. -/
def popStarFamilyAccepts (M : popStarFamilyData) : Prop :=
  Pop (popDataOf M) (popLhsZero M) (.var .b) ∧ Pop (popDataOf M) (popLhsSucc M) (popRhsSucc M)

/-- Verdict: escape. POP* accepts the free two-rule system for a precedence with `wrap` below
`recur` and the counter in a normal position; termination of `SchemaCore.ContextStep` follows
because POP* is contained in the multiset path order. The complexity statement of Theorem 3.11
concerns innermost derivations from basic terms; its instance is
`popStarFamily_complexity_scope`. -/
def popStarFamilyResult (M : popStarFamilyData) : Prop :=
  popStarFamilyAccepts M ∧ ∀ ν : Type, WellFounded (fun u t : FreeTerm ν => ContextStep t u)

/-- **Soundness** on the free system: acceptance by POP* gives acceptance by the multiset path
order modulo permutation, whose soundness gives termination of `ContextStep`. -/
theorem popStarFamily_sound : ∀ M : popStarFamilyData, popStarFamilyLaws M →
    popStarFamilyAccepts M → ∀ ν : Type, WellFounded (fun u t : FreeTerm ν => ContextStep t u) := by
  intro M hL hA ν
  have hwf := popStarFamily_prec_wf hL
  have hZ : RPOm M.prec mulSt ruleLhsZero ruleRhsZero := by
    have h := hA.1.toMPO
    refine RPOm.compat ?_ rfl h
    exact kappaM_recurArgs _ _ _ _ _ _
  have hS : RPOm M.prec mulSt ruleLhsSucc ruleRhsSucc := by
    have h := hA.2.toMPO
    refine RPOm.compat ?_ ?_ h
    · exact kappaM_recurArgs _ _ _ _ _ _
    · exact kappa_app_arg mulSt Sym.wrap [Term.var RuleVar.s] [] (kappaM_recurArgs _ _ _ _ _ _)
  exact freeContext_wf_of (RPOm M.prec mulSt) (RPOm.wf hwf) (fun h => rpom_contextStep hZ hS h)

/-- The successor argument `succ n` dominates no term containing another variable. -/
theorem pop_succ_not {M : popStarFamilyData} {x : RuleVar} {t : Term Sym RuleVar}
    (hx : x ≠ .n) (hocc : Occurs x t) :
    ¬ Pop (popDataOf M) (.app .succ [.var .n]) t := by
  intro hp
  have h := RPOm.occurs hp.toMPO hocc
  rw [occurs_app_iff] at h
  obtain ⟨a, ha, hxa⟩ := h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
  subst ha
  cases hxa
  exact hx rfl

/-- The recursive call is `>pop*`-below the left-hand side only if the counter is normal. -/
theorem pop_recCall_forces {M : popStarFamilyData} (hirr : ∀ a, ¬ M.prec a a)
    (h : Pop (popDataOf M) (popLhsSucc M) (popRecCall M)) : M.safeN = false := by
  simp only [popRecCall] at h
  cases h with
  | subEq a ha heq =>
      rcases (mem_recurArgs _ _ _ _ _ _ a).1 ha with rfl | rfl | rfl
      · simp [kappaP_app] at heq
      · simp [kappaP_app] at heq
      · rw [kappaP_app, kappaP_app] at heq
        cases heq
  | subGt a ha hp =>
      rcases (mem_recurArgs _ _ _ _ _ _ a).1 ha with rfl | rfl | rfl
      · cases hp
      · cases hp
      · exact absurd hp (pop_succ_not (x := .b) (by decide)
          (occurs_app_iff.2 ⟨.var .b, (mem_recurArgs _ _ _ _ _ _ _).2 (Or.inl rfl), .here⟩))
  | comp _ hrr _ _ _ => exact absurd hrr (hirr _)
  | eqHead _ X Y Z φ hZ hs ht hφZ hφ X' Y' Z' φ' hs' ht' hφZ' hφ' =>
      by_contra hN
      have hN' : M.safeN = true := by simpa using hN
      have hnrm : (popDataOf M).nrm Sym.recur = recurNrm M.safeB M.safeS M.safeN := rfl
      rw [hnrm, take_recurArgs] at hs ht
      rw [hN'] at hs ht
      have hXZ : X + Z = X + Y := by
        rw [← hs, ← ht]
        simp [recurNormals]
      have hZY : Z = Y := add_left_cancel hXZ
      obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero (hZY ▸ hZ)
      have hz : φ y ∈ X + Z := Multiset.mem_add.2 (Or.inr (hφZ y hy))
      rw [← hs, Multiset.mem_coe] at hz
      obtain ⟨a, ha, haz⟩ := List.mem_map.1 hz
      rcases mem_recurNormals_true _ _ ha with rfl | rfl
      · have := hφ y hy
        rw [← haz, kappaP_var] at this
        cases this
      · have := hφ y hy
        rw [← haz, kappaP_var] at this
        cases this

/-- **Safe and normal positions derived from the rules.** Under the admissibility laws, POP*
accepts the free two-rule system iff `wrap` lies below `recur` and the counter is a normal
position of `recur`; the positions of the base and of the duplicated step argument are free. -/
theorem popStarFamily_accepts_iff (M : popStarFamilyData) (hL : popStarFamilyLaws M) :
    popStarFamilyAccepts M ↔ M.prec .wrap .recur ∧ M.safeN = false := by
  constructor
  · rintro ⟨-, h⟩
    simp only [popRhsSucc] at h
    cases h with
    | subEq a ha heq =>
        rcases (mem_recurArgs _ _ _ _ _ _ a).1 ha with rfl | rfl | rfl
        · simp [kappaP_app] at heq
        · simp [kappaP_app] at heq
        · rw [kappaP_app, kappaP_app] at heq
          cases heq
    | subGt a ha hp =>
        rcases (mem_recurArgs _ _ _ _ _ _ a).1 ha with rfl | rfl | rfl
        · cases hp
        · cases hp
        · exact absurd hp (pop_succ_not (x := .s) (by decide)
            (occurs_app_iff.2 ⟨.var .s, by simp, .here⟩))
    | comp _ hfg _ hsafe _ =>
        refine ⟨hfg, pop_recCall_forces hL.1 (hsafe _ ?_)⟩
        show popRecCall M ∈ ([Term.var RuleVar.s, popRecCall M] : List (Term Sym RuleVar)).drop 0
        simp
  · rintro ⟨hprec, hN⟩
    refine ⟨Pop.subEq (.var .b) ((mem_recurArgs _ _ _ _ _ _ _).2 (Or.inl rfl)) rfl, ?_⟩
    refine Pop.comp rfl hprec ?_ ?_ ?_
    · intro u hu
      simp [popDataOf] at hu
    · intro u hu
      have hu' : u = .var .s ∨ u = popRecCall M := by
        simpa [popDataOf] using hu
      rcases hu' with rfl | rfl
      · exact Pop.subEq (.var .s) ((mem_recurArgs _ _ _ _ _ _ _).2 (Or.inr (Or.inl rfl))) rfl
      · simp only [popRecCall]
        have hnrm : (popDataOf M).nrm Sym.recur = recurNrm M.safeB M.safeS M.safeN := rfl
        refine Pop.eqHead rfl
          (((recurNormals M.safeB M.safeS true (Term.var RuleVar.b) (Term.var RuleVar.s)
            (Term.var RuleVar.n)).map (kappaP (popDataOf M)) : List (Term Sym RuleVar)) :
              Multiset (Term Sym RuleVar))
          {Term.var RuleVar.n} {kappaP (popDataOf M) (.app .succ [.var .n])}
          (fun _ => kappaP (popDataOf M) (.app .succ [.var .n])) (Multiset.singleton_ne_zero _)
          ?_ ?_ ?_ ?_
          (((recurSafes M.safeB M.safeS false (Term.var RuleVar.b) (Term.var RuleVar.s)
            (Term.var RuleVar.n)).map (kappaP (popDataOf M)) : List (Term Sym RuleVar)) :
              Multiset (Term Sym RuleVar)) 0 0 id ?_ ?_ ?_ ?_
        · rw [hnrm, take_recurArgs, hN, recurNormals_false, List.map_append, List.map_cons,
            List.map_nil,
            recurNormals_true_indep M.safeB M.safeS (Term.var RuleVar.b) (Term.var RuleVar.s)
              (Term.app Sym.succ [Term.var RuleVar.n]) (Term.var RuleVar.n),
            ← Multiset.coe_add, Multiset.coe_singleton]
        · rw [hnrm, take_recurArgs, hN, recurNormals_false, List.map_append, List.map_cons,
            List.map_nil, kappaP_var, ← Multiset.coe_add, Multiset.coe_singleton]
        · intro y _
          exact Multiset.mem_singleton_self _
        · intro y hy
          rw [Multiset.mem_singleton] at hy
          subst hy
          simp only [kappaP_app, List.map_cons, List.map_nil, kappaP_var, canonPop_singleton]
          exact Pop.subEq (.var .n) (by simp) rfl
        · rw [hnrm, drop_recurArgs, hN, recurSafes_false _ _ _ _ _ (Term.var RuleVar.n)]
          simp
        · rw [hnrm, drop_recurArgs, hN]
          simp
        · intro y hy
          simp at hy
        · intro y hy
          simp at hy
    · simp only [popDataOf, List.drop_zero]
      refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
      intro w _
      exact Or.inl (BelowF.var _)

/-- Witness: precedence `zero < succ < wrap < recur`; the counter is normal, the base and the
duplicated step argument are safe. -/
def popStarFamilyWitness : popStarFamilyData where
  prec := fun a b => symRank a < symRank b
  safeB := true
  safeS := true
  safeN := false

theorem popStarFamilyWitness_laws : popStarFamilyLaws popStarFamilyWitness :=
  ⟨fun a => lt_irrefl (symRank a), fun _ _ _ h₁ h₂ => lt_trans h₁ h₂⟩

theorem popStarFamilyWitness_accepts : popStarFamilyAccepts popStarFamilyWitness :=
  (popStarFamily_accepts_iff _ popStarFamilyWitness_laws).2
    ⟨show symRank Sym.wrap < symRank Sym.recur by decide, rfl⟩

theorem popStarFamilyWitness_result : popStarFamilyResult popStarFamilyWitness :=
  ⟨popStarFamilyWitness_accepts,
    popStarFamily_sound _ popStarFamilyWitness_laws popStarFamilyWitness_accepts⟩

/-- **Defining feature.** The accepted recursive rule duplicates safe data: the step argument
`s` sits in a safe position of `recur` and occurs both under `wrap` and in the safe block of the
recursive call. The restriction to one recursive call per right-hand side (the third condition
of clause (2) of Definition 3.5) rejects the rule whose right-hand side carries two recursive
calls. -/
theorem popStarFamilyWitness_feature :
    popStarFamilyWitness.safeS = true ∧
      (Term.var RuleVar.s : Term Sym RuleVar) ∈
        recurSafes popStarFamilyWitness.safeB popStarFamilyWitness.safeS
          popStarFamilyWitness.safeN (Term.var RuleVar.b) (Term.var RuleVar.s)
          (Term.var RuleVar.n) ∧
      Pop (popDataOf popStarFamilyWitness) (popLhsSucc popStarFamilyWitness)
        (popRhsSucc popStarFamilyWitness) ∧
      ¬ Pop (popDataOf popStarFamilyWitness) (popLhsSucc popStarFamilyWitness)
        (.app .wrap [popRecCall popStarFamilyWitness, popRecCall popStarFamilyWitness]) := by
  refine ⟨rfl, by simp [recurSafes, popStarFamilyWitness], popStarFamilyWitness_accepts.2, ?_⟩
  intro h
  cases h with
  | subEq a ha heq =>
      rcases (mem_recurArgs _ _ _ _ _ _ a).1 ha with rfl | rfl | rfl
      · simp [kappaP_app] at heq
      · simp [kappaP_app] at heq
      · rw [kappaP_app, kappaP_app] at heq
        cases heq
  | subGt a ha hp =>
      rcases (mem_recurArgs _ _ _ _ _ _ a).1 ha with rfl | rfl | rfl
      · cases hp
      · cases hp
      · refine absurd hp (pop_succ_not (x := .b) (by decide) ?_)
        refine occurs_app_iff.2 ⟨popRecCall popStarFamilyWitness, by simp, ?_⟩
        exact occurs_app_iff.2 ⟨.var .b, (mem_recurArgs _ _ _ _ _ _ _).2 (Or.inl rfl), .here⟩
  | comp _ _ _ _ hone =>
      simp only [popDataOf, List.drop_zero, List.pairwise_cons, List.mem_cons, List.mem_nil_iff,
        or_false, forall_eq] at hone
      rcases hone with hb | hb <;>
      · cases hb with
        | app hg _ => exact absurd hg (lt_irrefl _)

/-- **Mutation.** Making the counter a safe position of `recur`, everything else fixed, makes
POP* reject the duplicating rule. -/
theorem popStarFamily_mutation :
    ¬ popStarFamilyAccepts { popStarFamilyWitness with safeN := true } := by
  intro h
  have := ((popStarFamily_accepts_iff _
    ⟨fun a => lt_irrefl (symRank a), fun _ _ _ h₁ h₂ => lt_trans h₁ h₂⟩).1 h).2
  simp at this

/-! ## 11. Derivation lengths of the free system -/

section Derivations

variable {ν : Type}

/-- `n` contextual steps of the free system. -/
inductive CtxPow : Nat → FreeTerm ν → FreeTerm ν → Prop
  | refl (t : FreeTerm ν) : CtxPow 0 t t
  | step {n : Nat} {t u v : FreeTerm ν} (h : ContextStep t u) (hr : CtxPow n u v) :
      CtxPow (n + 1) t v

theorem CtxPow.trans : ∀ {m n : Nat} {a b c : FreeTerm ν},
    CtxPow m a b → CtxPow n b c → CtxPow (n + m) a c
  | _, _, _, _, _, .refl _, h₂ => h₂
  | _, _, _, _, _, .step h hr, h₂ => .step h (CtxPow.trans hr h₂)

theorem CtxPow.plug (C : FreeContext ν) : ∀ {n : Nat} {t u : FreeTerm ν},
    CtxPow n t u → CtxPow n (C.plug t) (C.plug u)
  | _, _, _, .refl _ => .refl _
  | _, _, _, .step h hr => .step (h.outer C) (CtxPow.plug C hr)

/-- The coupled polynomial interpretation (`α = 1`, `β = 2`) of
`FreePolynomialTermination`. -/
def wVal (t : FreeTerm ν) : Nat :=
  (FreePolynomialTermination.coupledInterpretation 1 2).eval (fun _ => 0) t

theorem wVal_step {t u : FreeTerm ν} (h : ContextStep t u) : wVal u < wVal t :=
  FreePolynomialTermination.coupled_contextStep_decreases (by decide) (by decide) _ h

/-- **Upper bound on derivation height**: every derivation from `t` has at most `wVal t`
steps. -/
theorem ctxPow_le_wVal : ∀ {n : Nat} {t u : FreeTerm ν}, CtxPow n t u → n + wVal u ≤ wVal t
  | _, _, _, .refl _ => by simp
  | _, _, _, .step h hr => by
      have h₁ := ctxPow_le_wVal hr
      have h₂ := wVal_step h
      omega

/-- No `recur` node. -/
def recurFree : FreeTerm ν → Prop
  | .var _ => True
  | .zero => True
  | .succ t => recurFree t
  | .wrap s t => recurFree s ∧ recurFree t
  | .recur _ _ _ => False

/-- Every `recur` node has `recur`-free arguments. -/
def tame : FreeTerm ν → Prop
  | .var _ => True
  | .zero => True
  | .succ t => tame t
  | .wrap s t => tame s ∧ tame t
  | .recur b s n => recurFree b ∧ recurFree s ∧ recurFree n

/-- Number of leading successors. -/
def succDepth : FreeTerm ν → Nat
  | .succ t => succDepth t + 1
  | _ => 0

/-- Remaining steps of every `recur` node of a tame term. -/
def pot : FreeTerm ν → Nat
  | .var _ => 0
  | .zero => 0
  | .succ t => pot t
  | .wrap s t => pot s + pot t
  | .recur _ _ n => succDepth n + 1

theorem recurFree_tame : ∀ {t : FreeTerm ν}, recurFree t → tame t ∧ pot t = 0
  | .var _, _ => ⟨trivial, rfl⟩
  | .zero, _ => ⟨trivial, rfl⟩
  | .succ t, h => recurFree_tame (t := t) h
  | .wrap s t, h => by
      obtain ⟨h₁, h₂⟩ := recurFree_tame (t := s) h.1
      obtain ⟨h₃, h₄⟩ := recurFree_tame (t := t) h.2
      exact ⟨⟨h₁, h₃⟩, by simp [pot, h₂, h₄]⟩
  | .recur _ _ _, h => h.elim

theorem recurFree_plug : ∀ (C : FreeContext ν) {t : FreeTerm ν},
    recurFree (C.plug t) → recurFree t
  | .hole, _, h => h
  | .succ C, _, h => recurFree_plug C h
  | .wrapLeft C _, _, h => recurFree_plug C h.1
  | .wrapRight _ C, _, h => recurFree_plug C h.2
  | .recurBase _ _ _, _, h => h.elim
  | .recurStep _ _ _, _, h => h.elim
  | .recurCounter _ _ _, _, h => h.elim

theorem rootStep_tame {t u : FreeTerm ν} (ht : tame t) (h : RootStep t u) :
    tame u ∧ pot u + 1 = pot t := by
  cases h with
  | recurZero b s =>
      obtain ⟨hb, -⟩ := recurFree_tame ht.1
      refine ⟨hb, ?_⟩
      simp [pot, succDepth, (recurFree_tame ht.1).2]
  | recurSucc b s n =>
      obtain ⟨hs, hs0⟩ := recurFree_tame ht.2.1
      refine ⟨⟨hs, ht.1, ht.2.1, ht.2.2⟩, ?_⟩
      simp [pot, succDepth, hs0]

theorem plug_tame {t u : FreeTerm ν} (hr : RootStep t u) : ∀ (C : FreeContext ν),
    tame (C.plug t) → tame (C.plug u) ∧ pot (C.plug u) + 1 = pot (C.plug t)
  | .hole, h => rootStep_tame h hr
  | .succ C, h => plug_tame hr C h
  | .wrapLeft C r, h => by
      obtain ⟨h₁, h₂⟩ := plug_tame hr C h.1
      refine ⟨⟨h₁, h.2⟩, ?_⟩
      simp only [FreeContext.plug, pot]
      omega
  | .wrapRight l C, h => by
      obtain ⟨h₁, h₂⟩ := plug_tame hr C h.2
      refine ⟨⟨h.1, h₁⟩, ?_⟩
      simp only [FreeContext.plug, pot]
      omega
  | .recurBase C _ _, h => by
      have := recurFree_plug C h.1
      cases hr <;> exact this.elim
  | .recurStep _ C _, h => by
      have := recurFree_plug C h.2.1
      cases hr <;> exact this.elim
  | .recurCounter _ _ C, h => by
      have := recurFree_plug C h.2.2
      cases hr <;> exact this.elim

theorem ctxPow_tame_bound : ∀ {n : Nat} {t u : FreeTerm ν}, tame t → CtxPow n t u → n ≤ pot t
  | _, _, _, _, .refl _ => Nat.zero_le _
  | _, _, _, ht, .step h hrest => by
      cases h with
      | lift C hr =>
        obtain ⟨hu, hp⟩ := plug_tame hr C ht
        have := ctxPow_tame_bound hu hrest
        omega

/-- An explicit family with exponentially long derivations. -/
def expFam : Nat → FreeTerm ν
  | 0 => .zero
  | k + 1 => .recur .zero (expFam k) (.succ (.succ .zero))

/-- Length of the derivation built for `expFam k`. -/
def expLen : Nat → Nat
  | 0 => 0
  | k + 1 => 2 * expLen k + 3

theorem expFam_deriv : ∀ k : Nat, ∃ u : FreeTerm ν, CtxPow (expLen k) (expFam k) u
  | 0 => ⟨_, .refl _⟩
  | k + 1 => by
      obtain ⟨u, hu⟩ := expFam_deriv k
      set t : FreeTerm ν := expFam k with ht
      have s₁ : ContextStep (FreeTerm.recur .zero t (.succ (.succ .zero)))
          (FreeTerm.wrap t (.recur .zero t (.succ .zero))) :=
        rootStep_contextStep (.recurSucc _ _ _)
      have s₂ : ContextStep (FreeTerm.wrap t (.recur .zero t (.succ .zero)))
          (FreeTerm.wrap t (.wrap t (.recur .zero t .zero))) :=
        ContextStep.lift (.wrapRight t .hole) (.recurSucc _ _ _)
      have s₃ : ContextStep (FreeTerm.wrap t (.wrap t (.recur .zero t .zero)))
          (FreeTerm.wrap t (.wrap t .zero)) :=
        ContextStep.lift (.wrapRight t (.wrapRight t .hole)) (.recurZero _ _)
      have p₁ : CtxPow (expLen k) (FreeTerm.wrap t (.wrap t .zero))
          (FreeTerm.wrap u (.wrap t .zero)) :=
        CtxPow.plug (.wrapLeft .hole (.wrap t .zero)) hu
      have p₂ : CtxPow (expLen k) (FreeTerm.wrap u (.wrap t .zero))
          (FreeTerm.wrap u (.wrap u .zero)) :=
        CtxPow.plug (.wrapRight u (.wrapLeft .hole .zero)) hu
      refine ⟨FreeTerm.wrap u (.wrap u .zero), ?_⟩
      have hlen : expLen (k + 1) = (expLen k + expLen k) + 1 + 1 + 1 := by
        simp only [expLen]
        omega
      rw [hlen]
      exact .step s₁ (.step s₂ (.step s₃ (CtxPow.trans p₁ p₂)))

theorem expLen_ge (k : Nat) : 2 ^ k ≤ expLen k + 1 := by
  induction k with
  | zero => simp [expLen]
  | succ k ih =>
      simp only [expLen, pow_succ]
      omega

/-- Structural size of a free term. -/
def freeSize : FreeTerm ν → Nat
  | .var _ => 1
  | .zero => 1
  | .succ t => freeSize t + 1
  | .wrap s t => freeSize s + freeSize t + 1
  | .recur b s n => freeSize b + freeSize s + freeSize n + 1

theorem freeSize_expFam (k : Nat) : freeSize (expFam (ν := ν) k) = 5 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [expFam, freeSize, ih]
      omega

end Derivations

/-- **Complexity scope of POP*** (instance of Avanzini–Moser 2013, Theorem 3.11). From a basic
term `recur b s n` with constructor arguments, every derivation of the contextual relation (hence
every innermost derivation) has at most `succDepth n + 1` steps: linear in the depth of the
normal argument. Theorem 3.11 itself is an external result and is not re-proved here. -/
theorem popStarFamily_complexity_scope {ν : Type} (b s n : FreeTerm ν) (hb : recurFree b)
    (hs : recurFree s) (hn : recurFree n) {k : Nat} {u : FreeTerm ν}
    (h : CtxPow k (.recur b s n) u) : k ≤ succDepth n + 1 :=
  ctxPow_tame_bound (t := FreeTerm.recur b s n) ⟨hb, hs, hn⟩ h

/-- The complexity statement of POP* does not extend to derivational complexity: starting
terms of size `5k + 1` have derivations of length at least `2^k - 1`. -/
theorem popStarFamily_derivational_outside_scope {ν : Type} (k : Nat) :
    ∃ u : FreeTerm ν, ∃ m : Nat, CtxPow m (expFam k) u ∧ 2 ^ k ≤ m + 1 ∧
      freeSize (expFam (ν := ν) k) = 5 * k + 1 := by
  obtain ⟨u, hu⟩ := expFam_deriv (ν := ν) k
  exact ⟨u, expLen k, hu, expLen_ge k, freeSize_expFam k⟩

/-! ## 12. Order laws of POP* that fail

POP* is irreflexive and well founded (section 9). It is not transitive, and it is closed neither
under contexts nor under substitutions; Avanzini and Moser note after Definition 3.5 that closure
under contexts fails. The three failures are proved below on one admissible signature. -/

/-- Signature for the counterexamples: `F`, `G`, `H` defined with one normal position, `S` and
`C` constructors. -/
inductive PSym where
  | F | G | H | S | C
  deriving DecidableEq, Repr

inductive PVar where
  | x | y | z | w
  deriving DecidableEq, Repr

/-- Precedence `H < F` and `C < F`, nothing else. -/
def pPrec (a b : PSym) : Prop := (a = .H ∧ b = .F) ∨ (a = .C ∧ b = .F)

def pData : PopData PSym where
  prec := pPrec
  isDef := fun f => f = .F ∨ f = .G ∨ f = .H
  nrm := fun f => match f with
    | .F => 1
    | .G => 1
    | .H => 1
    | _ => 0

def pRank : PSym → Nat
  | .F => 1
  | _ => 0

theorem pPrec_wf : WellFounded pPrec :=
  Subrelation.wf (fun {a b} h => by
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> show pRank _ < pRank _ <;> decide)
    (InvImage.wf pRank Nat.lt_wfRel.wf)

theorem pPrec_irrefl (a : PSym) : ¬ pPrec a a := by
  rintro (⟨rfl, h⟩ | ⟨rfl, h⟩) <;> cases h

theorem pPrec_trans (a b c : PSym) (h₁ : pPrec a b) (h₂ : pPrec b c) : pPrec a c := by
  rcases h₁ with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rcases h₂ with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h

theorem pop_var_left {D : PopData PSym} {v : PVar} {t : Term PSym PVar} :
    ¬ Pop D (.var v) t := by
  intro h
  cases h

theorem popAux_var_left {D : PopData PSym} {v : PVar} {t : Term PSym PVar} :
    ¬ PopAux D (.var v) t := by
  intro h
  cases h

/-- The terms of the transitivity counterexample. -/
def cxS : Term PSym PVar := .app .F [.app .G [.app .S [.var .y]]]
def cxT : Term PSym PVar := .app .H [.app .G [.app .S [.var .y]]]
def cxU : Term PSym PVar := .app .H [.app .G [.var .y]]

theorem kappaP_unary (f g : PSym) (v : PVar) :
    kappaP pData (Term.app f [Term.app g [Term.var v]]) = .app f [.app g [.var v]] := by
  simp [kappaP_app, canonPop_singleton]

theorem pop_cxS_cxT : Pop pData cxS cxT := by
  refine Pop.comp (Or.inl rfl) (Or.inl ⟨rfl, rfl⟩) ?_ ?_ ?_
  · intro u hu
    simp only [pData, List.take_succ_cons, List.take_zero, List.mem_cons, List.mem_nil_iff,
      or_false] at hu
    subst hu
    exact PopAux.subEq _ (by simp) (fun _ => by simp [pData]) rfl
  · intro u hu
    simp [pData] at hu
  · simp [pData]

theorem pop_cxT_cxU : Pop pData cxT cxU := by
  refine Pop.eqHead (Or.inr (Or.inr rfl)) 0
    {kappaP pData (.app .G [.var .y])} {kappaP pData (.app .G [.app .S [.var .y]])}
    (fun _ => kappaP pData (.app .G [.app .S [.var .y]])) (Multiset.singleton_ne_zero _)
    (by simp [pData]) (by simp [pData]) (fun _ _ => Multiset.mem_singleton_self _) ?_
    0 0 0 id (by simp [pData]) (by simp [pData]) (fun _ h => by simp at h)
    (fun _ h => by simp at h)
  intro y hy
  rw [Multiset.mem_singleton] at hy
  subst hy
  rw [kappaP_unary, kappaP_app, List.map_cons, List.map_nil, kappaP_var, canonPop_singleton]
  refine Pop.eqHead (Or.inr (Or.inl rfl)) 0 {Term.var PVar.y} {Term.app PSym.S [Term.var PVar.y]}
    (fun _ => Term.app PSym.S [Term.var PVar.y]) (Multiset.singleton_ne_zero _) ?_ ?_
    (fun _ _ => Multiset.mem_singleton_self _) ?_ 0 0 0 id (by simp [pData]) (by simp [pData])
    (fun _ h => by simp at h) (fun _ h => by simp at h)
  · simp [pData, kappaP_app, canonPop_singleton]
  · simp [pData]
  · intro y hy
    rw [Multiset.mem_singleton] at hy
    subst hy
    exact Pop.subEq (.var .y) (by simp) rfl

theorem not_pop_GSy_HGy :
    ¬ Pop pData (Term.app PSym.G [Term.app PSym.S [Term.var PVar.y]]) cxU := by
  intro h
  unfold cxU at h
  cases h with
  | subEq a ha heq =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      subst ha
      rw [kappaP_app, kappaP_app] at heq
      cases heq
  | subGt a ha hp =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      subst ha
      cases hp with
      | subEq a' ha' heq' =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha'
          subst ha'
          rw [kappaP_var, kappaP_app] at heq'
          cases heq'
      | subGt a' ha' hp' =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha'
          subst ha'
          exact pop_var_left hp'
      | comp hD _ _ _ _ => simp [pData] at hD
  | comp _ hfg _ _ _ => simp [pData, pPrec] at hfg

theorem not_popAux_cxS_Gy : ¬ PopAux pData cxS (Term.app PSym.G [Term.var PVar.y]) := by
  intro h
  unfold cxS at h
  cases h with
  | subEq a ha _ heq =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      subst ha
      rw [kappaP_unary, kappaP_app] at heq
      simp [canonPop_singleton] at heq
  | subGt a ha _ hp =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      subst ha
      cases hp with
      | subEq a' ha' _ heq' =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha'
          subst ha'
          rw [kappaP_app, kappaP_app] at heq'
          cases heq'
      | subGt a' ha' _ hp' =>
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha'
          subst ha'
          cases hp' with
          | subEq a'' ha'' _ heq'' =>
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha''
              subst ha''
              rw [kappaP_var, kappaP_app] at heq''
              cases heq''
          | subGt a'' ha'' _ hp'' =>
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha''
              subst ha''
              exact popAux_var_left hp''
          | prec hD _ _ => simp [pData] at hD
      | prec _ hfg _ => exact pPrec_irrefl _ hfg
  | prec _ hfg _ => simp [pData, pPrec] at hfg

theorem not_pop_cxS_cxU : ¬ Pop pData cxS cxU := by
  intro h
  have hS := h
  unfold cxS at h
  cases h with
  | subEq a ha heq =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      subst ha
      unfold cxU at heq
      rw [kappaP_app, kappaP_app] at heq
      cases heq
  | subGt a ha hp =>
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      subst ha
      exact not_pop_GSy_HGy hp
  | comp _ _ hnrm _ _ =>
      exact not_popAux_cxS_Gy (hnrm _ (by simp [pData]))

/-- **POP* is not transitive.** -/
theorem popStar_not_transitive :
    ∃ s t u : Term PSym PVar, Pop pData s t ∧ Pop pData t u ∧ ¬ Pop pData s u :=
  ⟨cxS, cxT, cxU, pop_cxS_cxT, pop_cxT_cxU, not_pop_cxS_cxU⟩

/-- **POP* is not closed under contexts**: the safe position of a defined symbol. -/
theorem popStar_not_context_closed :
    Pop pData (Term.app PSym.S [Term.var PVar.z]) (Term.var PVar.z) ∧
      ¬ Pop pData (Term.app PSym.F ([Term.var PVar.x] ++ Term.app PSym.S [Term.var PVar.z] :: []))
        (Term.app PSym.F ([Term.var PVar.x] ++ Term.var PVar.z :: [])) := by
  refine ⟨Pop.subEq (.var .z) (by simp) rfl, ?_⟩
  intro h
  cases h with
  | subEq a ha heq =>
      simp only [List.singleton_append, List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl
      · rw [kappaP_var, kappaP_app] at heq
        cases heq
      · rw [kappaP_app, kappaP_app] at heq
        cases heq
  | subGt a ha hp =>
      simp only [List.singleton_append, List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl
      · exact pop_var_left hp
      · cases hp with
        | subEq a' ha' heq' =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha'
            subst ha'
            rw [kappaP_var, kappaP_app] at heq'
            cases heq'
        | subGt a' ha' hp' =>
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha'
            subst ha'
            exact pop_var_left hp'
        | comp hD _ _ _ _ => simp [pData] at hD
  | comp _ hfg _ _ _ => exact pPrec_irrefl _ hfg
  | eqHead _ X Y Z φ hZ hs ht hφZ hφ _ _ _ _ _ _ _ _ =>
      have hs' : X + Z = {Term.var PVar.x} := by rw [← hs]; simp [pData]
      have ht' : X + Y = {Term.var PVar.x} := by rw [← ht]; simp [pData]
      have hZY : Z = Y := add_left_cancel (hs'.trans ht'.symm)
      obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero (hZY ▸ hZ)
      have hz : φ y ∈ X + Z := Multiset.mem_add.2 (Or.inr (hφZ y hy))
      rw [hs', Multiset.mem_singleton] at hz
      have := hφ y hy
      rw [hz] at this
      exact pop_var_left this

/-- The substitution of the substitution counterexample. -/
def cxSubst : PVar → Term PSym PVar
  | .y => .app .F [.var .z, .var .w]
  | v => .var v

/-- **POP* is not closed under substitutions.** -/
theorem popStar_not_subst_closed :
    Pop pData (Term.app PSym.F [Term.app PSym.S [Term.var PVar.x], Term.var PVar.y])
        (Term.app PSym.C [Term.var PVar.y, Term.app PSym.F [Term.var PVar.x, Term.var PVar.y]]) ∧
      ¬ Pop pData
        (tbind cxSubst (Term.app PSym.F [Term.app PSym.S [Term.var PVar.x], Term.var PVar.y]))
        (tbind cxSubst (Term.app PSym.C [Term.var PVar.y,
          Term.app PSym.F [Term.var PVar.x, Term.var PVar.y]])) := by
  constructor
  · refine Pop.comp (Or.inl rfl) (Or.inr ⟨rfl, rfl⟩) ?_ ?_ ?_
    · intro u hu
      simp [pData] at hu
    · intro u hu
      simp only [pData, List.drop_zero, List.mem_cons, List.mem_nil_iff, or_false] at hu
      rcases hu with rfl | rfl
      · exact Pop.subEq (.var .y) (by simp) rfl
      · refine Pop.eqHead (Or.inl rfl) 0 {Term.var PVar.x}
          {kappaP pData (Term.app PSym.S [Term.var PVar.x])}
          (fun _ => kappaP pData (Term.app PSym.S [Term.var PVar.x]))
          (Multiset.singleton_ne_zero _) (by simp [pData]) (by simp [pData])
          (fun _ _ => Multiset.mem_singleton_self _) ?_ {Term.var PVar.y} 0 0 id
          (by simp [pData]) (by simp [pData]) (fun _ h => by simp at h) (fun _ h => by simp at h)
        intro y hy
        rw [Multiset.mem_singleton] at hy
        subst hy
        rw [kappaP_app, List.map_cons, List.map_nil, kappaP_var, canonPop_singleton]
        exact Pop.subEq (.var .x) (by simp) rfl
    · simp only [pData, List.drop_zero]
      refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
      intro w _
      exact Or.inl (BelowF.var _)
  · intro h
    simp only [tbind_app, List.map_cons, List.map_nil, tbind_var, cxSubst] at h
    cases h with
    | subEq a ha heq =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
        rcases ha with rfl | rfl
        · rw [kappaP_app, kappaP_app] at heq
          cases heq
        · rw [kappaP_app, kappaP_app] at heq
          cases heq
    | subGt a ha hp =>
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
        rcases ha with rfl | rfl
        · cases hp with
          | subEq a' ha' heq' =>
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha'
              subst ha'
              rw [kappaP_var, kappaP_app] at heq'
              cases heq'
          | subGt a' ha' hp' =>
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha'
              subst ha'
              exact pop_var_left hp'
          | comp hD _ _ _ _ => simp [pData] at hD
        · cases hp with
          | subEq a' ha' heq' =>
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha'
              rcases ha' with rfl | rfl <;>
              · rw [kappaP_var, kappaP_app] at heq'
                cases heq'
          | subGt a' ha' hp' =>
              simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha'
              rcases ha' with rfl | rfl <;> exact pop_var_left hp'
          | comp _ _ _ hsafe _ =>
              exact Pop.irrefl pPrec_wf _ (hsafe _ (by simp [pData]))
    | comp _ _ _ _ hone =>
        simp only [pData, List.drop_zero, List.pairwise_cons, List.mem_cons, List.mem_nil_iff,
          or_false, forall_eq] at hone
        rcases hone.1 with hb | hb <;>
        · cases hb with
          | app hg _ => exact pPrec_irrefl _ hg

/-! ## 13. Row `acRPO` -/

/-- Native data of the AC-RPO row: a precedence, an argument status and the
associative-commutative symbols. -/
structure acRPOData : Type where
  prec : Sym → Sym → Prop
  status : Sym → ArgStatus
  ac : Sym → Bool

/-- Admissibility: the AC-RPO clauses of Rubio and Nieuwenhuis 1995 (Theoretical Computer
Science 142, "A total AC-compatible ordering based on RPO", the flattened same-head clause on
AC symbols) restricted to the four schema symbols, in the pinned row form of
`PathOrderRows.ACRPORowClaim` (2026) and `RDRSPathOrderDichotomy.acRPOBarrierUnlessHeadPrecedence`
(2026): the precedence is a transitive, well-founded strict order and every AC symbol carries
multiset status, so its same-head clause compares the flattened argument multiset. -/
def acRPOLaws (M : acRPOData) : Prop :=
  (∀ a b c, M.prec a b → M.prec b c → M.prec a c) ∧
    WellFounded M.prec ∧
    (∀ f, M.ac f = true → M.status f = .mul)

mutual
  /-- AC flattening of a term: the argument list of every symbol is passed through
  `acRPOFlatArgs`. -/
  def acRPOFlat (ac : Sym → Bool) {ν : Type} : Term Sym ν → Term Sym ν
    | .var x => .var x
    | .app f args => .app f (acRPOFlatArgs ac f args)
  /-- Flattening of an argument list at the head symbol `f`. -/
  def acRPOFlatArgs (ac : Sym → Bool) (f : Sym) {ν : Type} :
      List (Term Sym ν) → List (Term Sym ν)
    | [] => []
    | a :: as =>
      match acRPOFlat ac a with
      | .app g args' =>
        if g = f && ac f then args' ++ acRPOFlatArgs ac f as
        else acRPOFlat ac a :: acRPOFlatArgs ac f as
      | t => t :: acRPOFlatArgs ac f as
end

/-- Flattening is the identity on the first rule left-hand side, for every AC symbol set. -/
theorem acRPOFlat_ruleLhsZero (ac : Sym → Bool) :
    acRPOFlat ac (ν := RuleVar) ruleLhsZero = ruleLhsZero := by
  simp [acRPOFlat, acRPOFlatArgs, ruleLhsZero]

/-- Flattening is the identity on the first rule right-hand side, for every AC symbol set. -/
theorem acRPOFlat_ruleRhsZero (ac : Sym → Bool) :
    acRPOFlat ac (ν := RuleVar) ruleRhsZero = ruleRhsZero := by
  simp [acRPOFlat, ruleRhsZero]

/-- Flattening is the identity on the duplicating rule left-hand side. -/
theorem acRPOFlat_ruleLhsSucc (ac : Sym → Bool) :
    acRPOFlat ac (ν := RuleVar) ruleLhsSucc = ruleLhsSucc := by
  simp [acRPOFlat, acRPOFlatArgs, ruleLhsSucc]

/-- Flattening is the identity on the duplicating rule right-hand side. -/
theorem acRPOFlat_ruleRhsSucc (ac : Sym → Bool) :
    acRPOFlat ac (ν := RuleVar) ruleRhsSucc = ruleRhsSucc := by
  simp [acRPOFlat, acRPOFlatArgs, ruleRhsSucc]

/-- The AC-RPO comparison: the recursive path order with status on the flattened AC
representatives of the two terms. -/
def acRPO (M : acRPOData) {ν : Type} (s t : Term Sym ν) : Prop :=
  RPO M.prec M.status (acRPOFlat M.ac s) (acRPOFlat M.ac t)

/-- **Well-foundedness of AC-RPO**: flattening transports the recursive path order, so the
AC-RPO comparison is well founded over any signature once the precedence is. -/
theorem acRPO_wf {M : acRPOData} {ν : Type} (hwf : WellFounded M.prec) :
    WellFounded (fun u t : Term Sym ν => acRPO M t u) :=
  InvImage.wf (fun t => acRPOFlat M.ac t) (RPO.wf (ν := ν) hwf)

/-- The zero rule decreases in the recursive path order for every precedence and status. -/
theorem rpo_zero_rule (pr : Sym → Sym → Prop) (st : Sym → ArgStatus) :
    RPO pr st ruleLhsZero ruleRhsZero :=
  RPO.subEq (f := Sym.recur)
    (args := [Term.var RuleVar.b, Term.var RuleVar.s, Term.app Sym.zero []])
    (by simp [ruleRhsZero])

/-- The duplicating rule decreases in the recursive path order once `wrap` lies below `recur`. -/
theorem rpo_succ_rule {pr : Sym → Sym → Prop} {st : Sym → ArgStatus}
    (hprec : pr .wrap .recur) : RPO pr st ruleLhsSucc ruleRhsSucc := by
  refine RPO.prec (f := Sym.recur) (g := Sym.wrap)
    (args := [Term.var RuleVar.b, Term.var RuleVar.s, Term.app Sym.succ [Term.var RuleVar.n]])
    (targs := [Term.var RuleVar.s, Term.app Sym.recur [.var .b, .var .s, .var .n]]) hprec ?_
  intro u hu
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with rfl | rfl
  · exact RPO.subEq (by simp)
  · exact RPO.mono_arg Sym.recur [Term.var RuleVar.b, Term.var RuleVar.s] []
      (RPO.subEq (f := Sym.succ) (args := [Term.var RuleVar.n]) (by simp))

/-- The only variable occurring in the successor term is the counter. -/
theorem occurs_succ_var {x : RuleVar} :
    Occurs x (Term.app Sym.succ [Term.var RuleVar.n]) ↔ x = RuleVar.n := by
  constructor
  · intro h
    rw [occurs_app_iff] at h
    obtain ⟨a, ha, hxa⟩ := h
    simp only [List.mem_singleton] at ha
    subst ha
    cases hxa with
    | here => rfl
  · intro h
    subst h
    exact Occurs.arg (by simp) Occurs.here

/-- The precedence `wrap < recur` is necessary for the duplicating rule: the variable
condition excludes every other recursive path clause. -/
theorem rpo_succ_rule_prec {pr : Sym → Sym → Prop} {st : Sym → ArgStatus}
    (h : RPO pr st ruleLhsSucc ruleRhsSucc) : pr .wrap .recur := by
  rcases RPO.app_iff.1 h with ⟨a, ha, hEq | hat⟩ | ⟨g, targs, hgt, hhead, _⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · unfold ruleRhsSucc at hEq
      cases hEq
    · unfold ruleRhsSucc at hEq
      cases hEq
    · unfold ruleRhsSucc at hEq
      cases hEq
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact absurd hat RPO.not_var_left
    · exact absurd hat RPO.not_var_left
    · have hocc : Occurs RuleVar.s ruleRhsSucc :=
        Occurs.arg (by simp) Occurs.here
      have hs := RPO.occurs hat hocc
      exact absurd ((occurs_succ_var (x := RuleVar.s)).1 hs) (by decide)
  · unfold ruleRhsSucc at hgt
    injection hgt with hg htargs
    subst hg
    subst htargs
    rcases hhead with hp | ⟨hgf, _⟩ | ⟨hgf, _⟩
    · exact hp
    · cases hgf
    · cases hgf

/-- Root steps of the free schema decrease in the recursive path order. -/
theorem rpo_rootStep {ν : Type} {pr : Sym → Sym → Prop} {st : Sym → ArgStatus}
    (hZ : RPO pr st ruleLhsZero ruleRhsZero) (hS : RPO pr st ruleLhsSucc ruleRhsSucc) :
    ∀ {t u : FreeTerm ν}, RootStep t u → RPO pr st (toTerm t) (toTerm u)
  | _, _, .recurZero b s => by
      have := RPO.bind (ruleInst b s .zero) hZ
      rwa [(ruleInst_zero b s).1, (ruleInst_zero b s).2] at this
  | _, _, .recurSucc b s n => by
      have := RPO.bind (ruleInst b s n) hS
      rwa [(ruleInst_succ b s n).1, (ruleInst_succ b s n).2] at this

/-- The method's own acceptance of the free two-rule system: both rule schemas decrease in the
AC-RPO comparison on flattened representatives. Adapter: `toTerm`, rule variables `RuleVar`. -/
def acRPOAccepts (M : acRPOData) : Prop :=
  acRPO M ruleLhsZero ruleRhsZero ∧ acRPO M ruleLhsSucc ruleRhsSucc

/-- The method accepts the free two-rule system with the flattened multiset comparison, and
its soundness theorem yields termination of the contextual relation `SchemaCore.ContextStep`
over every variable type.
Verdict: escape. -/
def acRPOResult (M : acRPOData) : Prop :=
  acRPOAccepts M ∧
    ∀ ν : Type, WellFounded (fun u t : FreeTerm ν => ContextStep t u)

/-- **Soundness** of AC-RPO on the free system: acceptance and admissibility give termination
of `ContextStep`. The flattened comparisons reduce to recursive path comparisons on the rule
schemas, and the recursive path order is stable under substitution, closed under argument
contexts and well founded. -/
theorem acRPO_sound : ∀ M : acRPOData, acRPOLaws M → acRPOAccepts M →
    ∀ ν : Type, WellFounded (fun u t : FreeTerm ν => ContextStep t u) := by
  intro M hL hA ν
  have hZ : RPO M.prec M.status ruleLhsZero ruleRhsZero := by
    have h := hA.1
    simpa [acRPO, acRPOFlat_ruleLhsZero, acRPOFlat_ruleRhsZero] using h
  have hS : RPO M.prec M.status ruleLhsSucc ruleRhsSucc := by
    have h := hA.2
    simpa [acRPO, acRPOFlat_ruleLhsSucc, acRPOFlat_ruleRhsSucc] using h
  exact freeContext_wf_of (RPO M.prec M.status) (RPO.wf hL.2.1)
    (fun h => toTerm_contextStep (RPO M.prec M.status)
      (fun f pre post _ _ hab => RPO.mono_arg f pre post hab)
      (rpo_rootStep hZ hS) h)

/-- **Acceptance characterization**: the duplicating rule is accepted exactly when `wrap` lies
below `recur`; flattening does not change the two rule schemas, so the AC clauses act on the
argument multisets and the head precedence decides the row. -/
theorem acRPO_accepts_iff (M : acRPOData) :
    acRPOAccepts M ↔ M.prec .wrap .recur := by
  constructor
  · intro hA
    have hS : RPO M.prec M.status ruleLhsSucc ruleRhsSucc := by
      have h := hA.2
      simpa [acRPO, acRPOFlat_ruleLhsSucc, acRPOFlat_ruleRhsSucc] using h
    exact rpo_succ_rule_prec hS
  · intro hprec
    refine ⟨?_, ?_⟩
    · have h := rpo_zero_rule M.prec M.status
      simpa [acRPO, acRPOFlat_ruleLhsZero, acRPOFlat_ruleRhsZero] using h
    · have h := rpo_succ_rule (pr := M.prec) (st := M.status) hprec
      simpa [acRPO, acRPOFlat_ruleLhsSucc, acRPOFlat_ruleRhsSucc] using h

/-- Witness data: the rank precedence `zero < succ < wrap < recur`, multiset status everywhere
and `wrap` as the only associative-commutative symbol. -/
def acRPOWitness : acRPOData where
  prec := fun a b => symRank a < symRank b
  status := fun _ => .mul
  ac := fun f => f == .wrap

theorem acRPOWitness_laws : acRPOLaws acRPOWitness := by
  refine ⟨fun _ _ _ h₁ h₂ => lt_trans h₁ h₂, InvImage.wf symRank Nat.lt_wfRel.wf, ?_⟩
  intro f _
  rfl

theorem acRPOWitness_accepts : acRPOAccepts acRPOWitness := by
  constructor
  · have h := rpo_zero_rule acRPOWitness.prec acRPOWitness.status
    simpa [acRPO, acRPOFlat_ruleLhsZero, acRPOFlat_ruleRhsZero] using h
  · have h := rpo_succ_rule (pr := acRPOWitness.prec) (st := acRPOWitness.status)
      (show symRank .wrap < symRank .recur by decide)
    simpa [acRPO, acRPOFlat_ruleLhsSucc, acRPOFlat_ruleRhsSucc] using h

theorem acRPOWitness_result : acRPOResult acRPOWitness :=
  ⟨acRPOWitness_accepts, acRPO_sound _ acRPOWitness_laws acRPOWitness_accepts⟩

/-- A non-AC symbol distributes through the argument map: its arguments are flattened
individually because no splicing applies. -/
theorem acRPOFlatArgs_eq_map_of_not_ac {ac : Sym → Bool} {f : Sym} {ν : Type} (hf : ac f = false) :
    ∀ l : List (Term Sym ν), acRPOFlatArgs ac f l = l.map (acRPOFlat ac) := by
  intro l
  induction l with
  | nil => rfl
  | cons a as ih =>
      rw [acRPOFlatArgs, ih, List.map_cons]
      cases h : acRPOFlat ac a with
      | app g args' => simp [hf]
      | var x => simp

/-- Flattening commutes with a context at a symbol that is not associative-commutative. -/
theorem acRPOFlat_app_of_not_ac {ac : Sym → Bool} {f : Sym} {ν : Type} (hf : ac f = false)
    (l : List (Term Sym ν)) :
    acRPOFlat ac (.app f l) = .app f (l.map (acRPOFlat ac)) := by
  simp only [acRPOFlat]
  congr 1
  exact acRPOFlatArgs_eq_map_of_not_ac hf l

/-- The AC-RPO comparison is closed under the successor context, a context whose symbol is
not associative-commutative. -/
theorem acRPO_context_succ {M : acRPOData} (hsucc : M.ac .succ = false) {ν : Type}
    {a b : Term Sym ν} (h : acRPO M a b) :
    acRPO M (.app .succ [a]) (.app .succ [b]) := by
  have ha := acRPOFlat_app_of_not_ac (ac := M.ac) hsucc [a]
  have hb := acRPOFlat_app_of_not_ac (ac := M.ac) hsucc [b]
  show RPO M.prec M.status (acRPOFlat M.ac (.app .succ [a]))
    (acRPOFlat M.ac (.app .succ [b]))
  rw [ha, hb]
  exact RPO.mono_arg .succ [] [] h

/-- **Defining feature.** The flattened multiset comparison of AC-RPO: the associative
rearrangement has one flattened representative, the commutative rearrangement has the same
argument multiset, the duplicating rule is accepted, and the comparison is transported into
the successor context. -/
theorem acRPOWitness_feature :
    acRPOAccepts acRPOWitness ∧
      acRPOFlat acRPOWitness.ac (ν := RuleVar)
          (.app .wrap [.app .wrap [.var .b, .var .s], .var .n]) =
        acRPOFlat acRPOWitness.ac (ν := RuleVar)
          (.app .wrap [.var .b, .app .wrap [.var .s, .var .n]]) ∧
      (acRPOFlatArgs acRPOWitness.ac .wrap (ν := RuleVar) [.var .b, .var .s] :
          Multiset (Term Sym RuleVar)) =
        acRPOFlatArgs acRPOWitness.ac .wrap (ν := RuleVar) [.var .s, .var .b] ∧
      acRPO acRPOWitness (.app .succ [ruleLhsSucc]) (.app .succ [ruleRhsSucc]) := by
  refine ⟨acRPOWitness_accepts, ?_, ?_, ?_⟩
  · simp [acRPOFlat, acRPOFlatArgs, acRPOWitness]
  · rw [Multiset.coe_eq_coe]
    simp only [acRPOFlat, acRPOFlatArgs]
    exact List.Perm.swap _ _ _
  · exact acRPO_context_succ (by decide) acRPOWitness_accepts.2

/-- **Mutation.** Placing `wrap` above `recur` in the precedence, everything else fixed,
makes the method reject the duplicating rule. -/
theorem acRPO_mutation :
    ¬ acRPOAccepts { acRPOWitness with prec := fun a b => symRank b < symRank a } := by
  intro h
  have hS : RPO (fun a b => symRank b < symRank a) acRPOWitness.status
      ruleLhsSucc ruleRhsSucc := by
    have h2 := h.2
    simpa [acRPO, acRPOFlat_ruleLhsSucc, acRPOFlat_ruleRhsSucc] using h2
  have hprec := rpo_succ_rule_prec hS
  exact absurd hprec (by decide)

/-! ## 14. Row `simpleTerminationOrderType`

Simple termination (Middeldorp and Zantema, "Simple termination revisited", Theoretical
Computer Science 175, 1997: a system is simply terminating iff it is compatible with a
simplification order, equivalently iff the system with the embedding rules added terminates)
and the order type of the simplification order used. The landed row restricted the data to an
affine rank image, whose barrier is the affine barrier of the ground restriction and not a
property of the method. The native object is the recursive path order of section 5, a
simplification order: it contains the embedding (subterm) relation, is stable under
substitution, is closed under argument contexts and is well founded for a well-founded
precedence. The free recursor is compatible with it. -/

/-- Native data of the row: a precedence and an argument status for each of the four symbols of
the free signature. The method's order is the recursive path order `RPO M.prec M.status` of
section 5. -/
structure simpleTerminationOrderTypeData : Type where
  prec : Sym → Sym → Prop
  status : Sym → ArgStatus

/-- Admissibility of the pinned primary definition: Middeldorp and Zantema, "Simple termination
revisited", Theoretical Computer Science 175, 1997, Definition 1 and Theorem 1, together with the
recursive path order of Dershowitz 1987 (J. Symbolic Computation 3, Definition 18 and Theorem 23).
The recursive path order is a simplification order exactly when its precedence is a transitive,
well-founded strict order: the embedding clause contains the subterm relation, and the
precedence, multiset and lexicographic clauses give stability and context closure. -/
def simpleTerminationOrderTypeLaws (M : simpleTerminationOrderTypeData) : Prop :=
  (∀ a b c : Sym, M.prec a b → M.prec b c → M.prec a c) ∧ WellFounded M.prec

/-- The method's own acceptance of the free two-rule system: both rule schemas decrease in the
simplification order. Adapter: `toTerm`, rule variables `RuleVar`. -/
def simpleTerminationOrderTypeAccepts (M : simpleTerminationOrderTypeData) : Prop :=
  RPO M.prec M.status ruleLhsZero ruleRhsZero ∧
    RPO M.prec M.status ruleLhsSucc ruleRhsSucc

/-- Verdict: escape. The simplification order accepts the free two-rule system, and the method's
soundness theorem yields termination of the contextual relation `SchemaCore.ContextStep` over
every variable type. -/
def simpleTerminationOrderTypeResult (M : simpleTerminationOrderTypeData) : Prop :=
  simpleTerminationOrderTypeAccepts M ∧
    ∀ μ : Type, WellFounded (fun u t : FreeTerm μ => ContextStep t u)

/-- **Soundness** of the method on the free system: acceptance and a well-founded precedence give
termination of `ContextStep`. The proof uses the embedding clause, stability under substitution,
closure under argument contexts and well-foundedness of the recursive path order. -/
theorem simpleTerminationOrderType_sound : ∀ M : simpleTerminationOrderTypeData,
    simpleTerminationOrderTypeLaws M → simpleTerminationOrderTypeAccepts M →
      simpleTerminationOrderTypeResult M := by
  intro M hL hA
  exact ⟨hA, fun μ => freeContext_wf_of (RPO M.prec M.status) (RPO.wf hL.2)
    (fun h => toTerm_contextStep (RPO M.prec M.status)
      (fun f pre post _ _ hab => RPO.mono_arg f pre post hab)
      (rpo_rootStep hA.1 hA.2) h)⟩

/-- Witness: the rank precedence `zero < succ < wrap < recur` and multiset status everywhere. -/
def simpleTerminationOrderTypeWitness : simpleTerminationOrderTypeData where
  prec := fun a b => symRank a < symRank b
  status := fun _ => .mul

theorem simpleTerminationOrderTypeWitness_laws :
    simpleTerminationOrderTypeLaws simpleTerminationOrderTypeWitness :=
  ⟨fun _ _ _ h₁ h₂ => lt_trans h₁ h₂, InvImage.wf symRank Nat.lt_wfRel.wf⟩

theorem simpleTerminationOrderTypeWitness_accepts :
    simpleTerminationOrderTypeAccepts simpleTerminationOrderTypeWitness :=
  ⟨rpo_zero_rule _ _, rpo_succ_rule (show symRank Sym.wrap < symRank Sym.recur by decide)⟩

theorem simpleTerminationOrderTypeWitness_result :
    simpleTerminationOrderTypeResult simpleTerminationOrderTypeWitness :=
  simpleTerminationOrderType_sound _ simpleTerminationOrderTypeWitness_laws
    simpleTerminationOrderTypeWitness_accepts

/-- **Defining feature.** Simple termination: the order is a simplification order that contains
the embedding relation on every application (the embedding rules added to the system), it orients
both free rules, and the derivation length of the free system on tame terms is bounded by the
remaining recursor count `pot` of section 11, independently of the order type. -/
theorem simpleTerminationOrderTypeWitness_feature :
    simpleTerminationOrderTypeAccepts simpleTerminationOrderTypeWitness ∧
    (∀ (f : Sym) (args : List (Term Sym RuleVar)) (a : Term Sym RuleVar), a ∈ args →
      RPO simpleTerminationOrderTypeWitness.prec simpleTerminationOrderTypeWitness.status
        (.app f args) a) ∧
    (∀ {μ : Type} (n : Nat) (t u : FreeTerm μ), tame t → CtxPow n t u → n ≤ pot t) :=
  ⟨simpleTerminationOrderTypeWitness_accepts,
    fun _ _ _ ha => RPO.subEq ha,
    fun _ _ _ ht h => ctxPow_tame_bound ht h⟩

/-- **Mutation.** Placing `wrap` above `recur` in the precedence, everything else fixed, makes
the method reject the duplicating rule. -/
theorem simpleTerminationOrderType_mutation :
    ¬ simpleTerminationOrderTypeAccepts
      { simpleTerminationOrderTypeWitness with prec := fun a b => symRank b < symRank a } := by
  intro h
  have := rpo_succ_rule_prec h.2
  simp [symRank] at this

/-- General simple-termination statement for an arbitrary first-order TRS: an RPO instance with
a well-founded precedence that orients every rule terminates under full rewriting. -/
def simpleTerminationOrderType_scope : Prop :=
  ∀ {σ ν : Type} (R : TRS σ ν),
    (∃ (pr : σ → σ → Prop) (st : σ → ArgStatus),
      (∀ a b c : σ, pr a b → pr b c → pr a c) ∧ WellFounded pr ∧
        ∀ rule ∈ R, RPO pr st rule.lhs rule.rhs) →
      WellFounded (fun u t : Term σ ν => Step R t u)

/-- The general scope is discharged by the native RPO soundness theorem. The transitivity field
is retained because it belongs to the usual simplification-order presentation, although
`RPO.step_wf` derives the required termination from well-founded precedence and rule orientation. -/
theorem simpleTerminationOrderType_scope_proven : simpleTerminationOrderType_scope := by
  intro σ ν R h
  rcases h with ⟨pr, st, _htrans, hwf, hR⟩
  exact RPO.step_wf hwf hR

/-- Exact method-identity certificate: the row's comparison is the recursive path order, its
free-system witness orients both rules, and the same soundness theorem applies to every TRS over
every signature and variable type. -/
theorem simpleTerminationOrderType_methodIdentity :
    simpleTerminationOrderType_scope ∧
      simpleTerminationOrderTypeLaws simpleTerminationOrderTypeWitness ∧
      simpleTerminationOrderTypeAccepts simpleTerminationOrderTypeWitness :=
  ⟨simpleTerminationOrderType_scope_proven,
    simpleTerminationOrderTypeWitness_laws,
    simpleTerminationOrderTypeWitness_accepts⟩

/-! ## 15. Row `cichonSlowGrowing` -/

/-- Fundamental sequences of the numeral notations step down by one. -/
theorem ordinalFundamentalSequence_ofNat_succ (n : Nat) :
    ONote.fundamentalSequence (ONote.ofNat n.succ) = Sum.inl (some (ONote.ofNat n)) := by
  cases n with
  | zero => rfl
  | succ k => rfl

/-- The slow-growing hierarchy takes the value `n` at the numeral notation `ofNat n`. -/
theorem ordinalSlowGrowing_ofNat (n : Nat) :
    OperatorKO7.OrdinalHierarchy.slowGrowing (ONote.ofNat n) = fun _ => n := by
  induction n with
  | zero => exact OperatorKO7.OrdinalHierarchy.slowGrowing_zero
  | succ n ih =>
      rw [@OperatorKO7.OrdinalHierarchy.slowGrowing_succ (ONote.ofNat n.succ) (ONote.ofNat n)
        (ordinalFundamentalSequence_ofNat_succ n)]
      funext i
      rw [ih]

/-- Native data of the Cichon slow-growing row: an ordinal notation for each term and a
numerical bound. -/
structure cichonSlowGrowingData : Type 1 where
  note : ∀ {ν : Type}, FreeTerm ν → ONote
  bound : ∀ {ν : Type}, FreeTerm ν → Nat

/-- Admissibility of the pinned primary definition: the controlled ordinal descent of the
compiled Cichon receipt, in the row form pinned by `SafeStepCtx_Complexity_Cichon` (2026,
`ctxExpNote`, `ctxExpCichonBound`, `safeStepCtx_length_le_ctxExpCichonBound`) with the
hierarchy of `OrdinalHierarchy.slowGrowing` (2026, after Cichon 1983, Proceedings of the
American Mathematical Society 87). The bound is positive and strictly decreases along every
contextual step of the free two-rule system. -/
def cichonSlowGrowingLaws (M : cichonSlowGrowingData) : Prop :=
  (∀ {ν : Type} (t : FreeTerm ν), 1 ≤ M.bound t) ∧
    (∀ {ν : Type} {t u : FreeTerm ν}, ContextStep t u → M.bound u < M.bound t)

/-- The method's own acceptance: the ordinal notation stays below `ω` and the slow-growing
value of the notation at the term's structural size is dominated by the bound. Adapter: the
free schema and its structural size `freeSize`. -/
def cichonSlowGrowingAccepts (M : cichonSlowGrowingData) : Prop :=
  (∀ {ν : Type} (t : FreeTerm ν), ONote.repr (M.note t) < Ordinal.omega0) ∧
    (∀ {ν : Type} (t : FreeTerm ν),
      OperatorKO7.OrdinalHierarchy.slowGrowing (M.note t) (freeSize t) ≤ M.bound t)

/-- The method accepts the free two-rule system, and its soundness theorem yields the
numerical bound `n + 1 ≤ bound t` on every `n`-step contextual derivation from `t`, over
every variable type.
Verdict: escape. -/
def cichonSlowGrowingResult (M : cichonSlowGrowingData) : Prop :=
  cichonSlowGrowingAccepts M ∧
    (∀ {ν : Type} {n : Nat} {t u : FreeTerm ν}, CtxPow n t u → n + 1 ≤ M.bound t)

/-- **Soundness** of the slow-growing bound on the free system: a positive bound that strictly
decreases along every contextual step bounds every derivation length. -/
theorem cichonSlowGrowing_sound : ∀ M : cichonSlowGrowingData,
    cichonSlowGrowingLaws M → cichonSlowGrowingAccepts M →
      ∀ {ν : Type} {n : Nat} {t u : FreeTerm ν}, CtxPow n t u → n + 1 ≤ M.bound t := by
  intro M hL _ ν n t u h
  induction h with
  | refl t => exact hL.1 t
  | step hstep _ ih =>
      have := hL.2 hstep
      omega

/-- Witness: the notation is the finite numeral of the coupled polynomial weight, and the
bound is that weight plus one. -/
def cichonSlowGrowingWitness : cichonSlowGrowingData where
  note := fun {ν : Type} (t : FreeTerm ν) => ONote.ofNat (wVal t)
  bound := fun {ν : Type} (t : FreeTerm ν) => wVal t + 1

theorem cichonSlowGrowingWitness_laws : cichonSlowGrowingLaws cichonSlowGrowingWitness := by
  constructor
  · intro ν t
    show (1 : Nat) ≤ wVal t + 1
    exact Nat.le_add_left 1 (wVal t)
  · intro ν t u h
    have hw := wVal_step h
    show wVal u + 1 < wVal t + 1
    omega

theorem cichonSlowGrowingWitness_accepts :
    cichonSlowGrowingAccepts cichonSlowGrowingWitness := by
  constructor
  · intro ν t
    show ONote.repr (ONote.ofNat (wVal t)) < Ordinal.omega0
    rw [ONote.repr_ofNat]
    exact Ordinal.nat_lt_omega0 (wVal t)
  · intro ν t
    show OperatorKO7.OrdinalHierarchy.slowGrowing (ONote.ofNat (wVal t)) (freeSize t) ≤
      wVal t + 1
    rw [ordinalSlowGrowing_ofNat]
    simp

theorem cichonSlowGrowingWitness_result : cichonSlowGrowingResult cichonSlowGrowingWitness :=
  ⟨cichonSlowGrowingWitness_accepts,
    cichonSlowGrowing_sound _ cichonSlowGrowingWitness_laws cichonSlowGrowingWitness_accepts⟩

/-- **Defining feature.** Ordinal notation, norm and controlled descent connect to the actual
slow-growing bound: the note is the finite numeral of the polynomial weight, the
slow-growing value at the structural norm is that weight, the zero rule already supplies the
strict descent with its numerical bound, and an unrelated constant bound satisfies positivity
but not descent. -/
theorem cichonSlowGrowingWitness_feature :
    (∀ {ν : Type} (t : FreeTerm ν),
      ONote.repr (cichonSlowGrowingWitness.note t) = (wVal t : Ordinal)) ∧
      (∀ {ν : Type} (t : FreeTerm ν),
        OperatorKO7.OrdinalHierarchy.slowGrowing (cichonSlowGrowingWitness.note t)
          (freeSize t) = wVal t) ∧
      (∀ {ν : Type} (b s : FreeTerm ν),
        1 + 1 ≤ cichonSlowGrowingWitness.bound (FreeTerm.recur b s FreeTerm.zero)) ∧
      ¬ (∀ {ν : Type} {t u : FreeTerm ν}, ContextStep t u →
        (fun {ν : Type} (_ : FreeTerm ν) => 1) u <
          (fun {ν : Type} (_ : FreeTerm ν) => 1) t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ν t
    show ONote.repr (ONote.ofNat (wVal t)) = (wVal t : Ordinal)
    exact ONote.repr_ofNat (wVal t)
  · intro ν t
    show OperatorKO7.OrdinalHierarchy.slowGrowing (ONote.ofNat (wVal t)) (freeSize t) = wVal t
    rw [ordinalSlowGrowing_ofNat]
  · intro ν b s
    have h := wVal_step (rootStep_contextStep (RootStep.recurZero b s))
    show (1 : Nat) + 1 ≤ wVal (FreeTerm.recur b s FreeTerm.zero) + 1
    omega
  · intro h
    exact absurd (h (rootStep_contextStep
      (RootStep.recurZero (FreeTerm.zero : FreeTerm Unit) FreeTerm.zero))) (Nat.lt_irrefl 1)

/-- **Mutation.** Replacing the note by an unrelated notation function that is not calibrated
to the bound, everything else fixed, makes the method reject the free two-rule system. -/
theorem cichonSlowGrowing_mutation :
    ¬ cichonSlowGrowingAccepts
      { cichonSlowGrowingWitness with
          note := fun {ν : Type} (t : FreeTerm ν) => ONote.ofNat (1000 + freeSize t) } := by
  intro h
  have hc := h.2 (FreeTerm.zero : FreeTerm Empty)
  rw [ordinalSlowGrowing_ofNat] at hc
  simp only [freeSize] at hc
  have hb : ({ cichonSlowGrowingWitness with
      note := fun {ν : Type} (t : FreeTerm ν) => ONote.ofNat (1000 + freeSize t) }).bound
        (FreeTerm.zero : FreeTerm Empty) = 1 := by
    show wVal (FreeTerm.zero : FreeTerm Empty) + 1 = 1
    simp [wVal, FreePolynomialTermination.coupledInterpretation]
  rw [hb] at hc
  omega
end OperatorKO7.Methods.OrientationClosure.MethodRowsPathOrders
