import OperatorKO7.Meta.Rewriting.Term

/-!
This module defines positions, subterm lookup, replacement, valid positions, and
parallel-position commutation for first-order terms. The proofs use structural recursion over
terms and argument lists.















-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Rewriting

universe u v

/-- Abbreviation for the displayed type.
-/
abbrev Pos := List Nat

namespace Term

variable {sigma : Type u} {nu : Type v}

/-- Definition with formal content given by the displayed type and body.


-/
def subtermAt : Term sigma nu → Pos → Option (Term sigma nu)
  | t, [] => some t
  | .var _, _ :: _ => none
  | .app _ args, i :: p =>
      match args[i]? with
      | none => none
      | some a => subtermAt a p

@[simp] theorem subtermAt_nil (t : Term sigma nu) : subtermAt t [] = some t := by
  cases t <;> rfl

@[simp] theorem subtermAt_var_cons (x : nu) (i : Nat) (p : Pos) :
    subtermAt (Term.var (sigma := sigma) x) (i :: p) = none := rfl

theorem subtermAt_app_cons (f : sigma) (args : List (Term sigma nu)) (i : Nat) (p : Pos) :
    subtermAt (Term.app f args) (i :: p) =
      match args[i]? with
      | none => none
      | some a => subtermAt a p := rfl

mutual
/-- Definition with formal content given by the displayed type and body.


-/
def replaceAt : Term sigma nu → Pos → Term sigma nu → Term sigma nu
  | _, [], s => s
  | .var x, _ :: _, _ => .var x
  | .app f args, i :: p, s => .app f (replaceAtList args i p s)
/-- Definition with formal content given by the displayed type and body. -/
def replaceAtList : List (Term sigma nu) → Nat → Pos → Term sigma nu → List (Term sigma nu)
  | [], _, _, _ => []
  | a :: as, 0, p, s => replaceAt a p s :: as
  | a :: as, i + 1, p, s => a :: replaceAtList as i p s
end

@[simp] theorem replaceAt_nil (t s : Term sigma nu) : replaceAt t [] s = s := by
  cases t <;> rfl

@[simp] theorem replaceAt_var_cons (x : nu) (i : Nat) (p : Pos) (s : Term sigma nu) :
    replaceAt (Term.var (sigma := sigma) x) (i :: p) s = .var x := rfl

@[simp] theorem replaceAt_app_cons (f : sigma) (args : List (Term sigma nu))
    (i : Nat) (p : Pos) (s : Term sigma nu) :
    replaceAt (Term.app f args) (i :: p) s = .app f (replaceAtList args i p s) := rfl

@[simp] theorem replaceAtList_nil (i : Nat) (p : Pos) (s : Term sigma nu) :
    replaceAtList ([] : List (Term sigma nu)) i p s = [] := rfl

@[simp] theorem replaceAtList_cons_zero (a : Term sigma nu) (as : List (Term sigma nu))
    (p : Pos) (s : Term sigma nu) :
    replaceAtList (a :: as) 0 p s = replaceAt a p s :: as := rfl

@[simp] theorem replaceAtList_cons_succ (a : Term sigma nu) (as : List (Term sigma nu))
    (i : Nat) (p : Pos) (s : Term sigma nu) :
    replaceAtList (a :: as) (i + 1) p s = a :: replaceAtList as i p s := rfl

/-- The displayed proposition follows from the stated hypotheses. -/
theorem length_replaceAtList (args : List (Term sigma nu)) (i : Nat) (p : Pos)
    (s : Term sigma nu) : (replaceAtList args i p s).length = args.length := by
  induction args generalizing i with
  | nil => simp
  | cons a as ih =>
      cases i with
      | zero => simp
      | succ i => simp [ih]

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem getElem?_replaceAtList_self (args : List (Term sigma nu)) (i : Nat) (p : Pos)
    (s : Term sigma nu) (hi : i < args.length) :
    (replaceAtList args i p s)[i]? = some (replaceAt args[i] p s) := by
  induction args generalizing i with
  | nil => simp at hi
  | cons a as ih =>
      cases i with
      | zero => simp
      | succ i =>
          simp only [replaceAtList_cons_succ, List.getElem?_cons_succ]
          have hi' : i < as.length := by simpa using hi
          rw [ih i hi']
          simp

/-- The displayed proposition follows from the stated hypotheses. -/
theorem getElem?_replaceAtList_ne (args : List (Term sigma nu)) (i j : Nat) (p : Pos)
    (s : Term sigma nu) (hij : i ≠ j) :
    (replaceAtList args i p s)[j]? = args[j]? := by
  induction args generalizing i j with
  | nil => simp
  | cons a as ih =>
      cases i with
      | zero =>
          cases j with
          | zero => exact absurd rfl hij
          | succ j => simp
      | succ i =>
          cases j with
          | zero => simp
          | succ j =>
              simp only [replaceAtList_cons_succ, List.getElem?_cons_succ]
              exact ih i j (by omega)

/-! Declarations for the section below. -/

/-- Definition with formal content given by the displayed type and body. -/
def ValidPos (t : Term sigma nu) (p : Pos) : Prop := (subtermAt t p).isSome

theorem validPos_nil (t : Term sigma nu) : ValidPos t [] := by
  simp [ValidPos]

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem subtermAt_replaceAt_same :
    ∀ (t : Term sigma nu) (p : Pos) (s : Term sigma nu),
      ValidPos t p → subtermAt (replaceAt t p s) p = some s := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
      intro p s hp
      cases p with
      | nil => simp
      | cons i p => simp [ValidPos] at hp
  | happ f args ih =>
      intro p s hp
      cases p with
      | nil => simp
      | cons i p =>
          simp only [ValidPos, subtermAt_app_cons] at hp
          --
          rw [replaceAt_app_cons, subtermAt_app_cons]
          cases hgi : args[i]? with
          | none => rw [hgi] at hp; simp at hp
          | some a =>
              have hi : i < args.length := by
                rw [List.getElem?_eq_some_iff] at hgi; exact hgi.1
              rw [getElem?_replaceAtList_self args i p s hi]
              have hai : args[i] = a := by
                rw [List.getElem?_eq_some_iff] at hgi
                obtain ⟨_, ha⟩ := hgi; exact ha
              rw [hai]
              have hmem : a ∈ args := hai ▸ List.getElem_mem hi
              rw [hgi] at hp
              exact ih a hmem p s (by simpa [ValidPos] using hp)

/-! ## Parallel positions and commutation -/

/-- One position is a prefix of another when it is an initial segment. -/
def Pos.IsPrefix (p q : Pos) : Prop := ∃ r, q = p ++ r

/-- Definition with formal content given by the displayed type and body.

-/
def Pos.parallel (p q : Pos) : Prop := ¬ Pos.IsPrefix p q ∧ ¬ Pos.IsPrefix q p

theorem Pos.parallel_comm {p q : Pos} (h : Pos.parallel p q) : Pos.parallel q p :=
  ⟨h.2, h.1⟩

/-- The displayed proposition follows from the stated hypotheses.


-/
theorem parallel_cons_cases {p q : Pos} (h : Pos.parallel p q) :
    ∃ i j p' q', p = i :: p' ∧ q = j :: q' ∧
      (i ≠ j ∨ (i = j ∧ Pos.parallel p' q')) := by
  cases p with
  | nil => exact absurd ⟨q, by simp⟩ h.1
  | cons i p' =>
      cases q with
      | nil => exact absurd ⟨i :: p', by simp⟩ h.2
      | cons j q' =>
          refine ⟨i, j, p', q', rfl, rfl, ?_⟩
          by_cases hij : i = j
          · subst hij
            refine Or.inr ⟨rfl, ?_, ?_⟩
            · rintro ⟨r, hr⟩
              exact h.1 ⟨r, by simp [hr]⟩
            · rintro ⟨r, hr⟩
              exact h.2 ⟨r, by simp [hr]⟩
          · exact Or.inl hij

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem replaceAtList_comm_ne (args : List (Term sigma nu)) :
    ∀ (i j : Nat) (p' q' : Pos) (a b : Term sigma nu), i ≠ j →
      replaceAtList (replaceAtList args i p' a) j q' b
        = replaceAtList (replaceAtList args j q' b) i p' a := by
  induction args with
  | nil => intro i j p' q' a b _; simp
  | cons c cs ih =>
      intro i j p' q' a b hij
      cases i with
      | zero =>
          cases j with
          | zero => exact absurd rfl hij
          | succ j => simp
      | succ i =>
          cases j with
          | zero => simp
          | succ j =>
              simp only [replaceAtList_cons_succ]
              rw [ih i j p' q' a b (by omega)]

/-- The displayed proposition follows from the stated hypotheses.

-/
theorem replaceAtList_comm_eq (args : List (Term sigma nu)) (p' q' : Pos)
    (hcomm : ∀ a ∈ args, ∀ (x y : Term sigma nu),
      replaceAt (replaceAt a p' x) q' y = replaceAt (replaceAt a q' y) p' x) :
    ∀ (i : Nat) (a b : Term sigma nu),
      replaceAtList (replaceAtList args i p' a) i q' b
        = replaceAtList (replaceAtList args i q' b) i p' a := by
  induction args with
  | nil => intro i a b; simp
  | cons c cs ih =>
      intro i a b
      cases i with
      | zero =>
          simp only [replaceAtList_cons_zero]
          rw [hcomm c (by simp) a b]
      | succ i =>
          simp only [replaceAtList_cons_succ]
          rw [ih (fun d hd => hcomm d (by simp [hd])) i a b]

/-- Replacements at parallel positions commute. -/
theorem replaceAt_parallel_comm :
    ∀ (t : Term sigma nu) (p q : Pos) (a b : Term sigma nu),
      Pos.parallel p q →
      replaceAt (replaceAt t p a) q b = replaceAt (replaceAt t q b) p a := by
  intro t
  induction t using Term.rec' with
  | hvar x =>
      intro p q a b hpq
      obtain ⟨i, j, p', q', hp, hq, _⟩ := parallel_cons_cases hpq
      subst hp; subst hq; simp
  | happ f args ih =>
      intro p q a b hpq
      obtain ⟨i, j, p', q', hp, hq, hcase⟩ := parallel_cons_cases hpq
      subst hp; subst hq
      rw [replaceAt_app_cons, replaceAt_app_cons, replaceAt_app_cons, replaceAt_app_cons]
      congr 1
      rcases hcase with hij | ⟨hij, hpar⟩
      · exact replaceAtList_comm_ne args i j p' q' a b hij
      · subst hij
        exact replaceAtList_comm_eq args p' q'
          (fun d hd x y => ih d hd p' q' x y hpar) i a b

end Term

end OperatorKO7.Meta.Rewriting

/-! Declarations for the section below. -/

#print axioms OperatorKO7.Meta.Rewriting.Term.subtermAt
#print axioms OperatorKO7.Meta.Rewriting.Term.replaceAt
#print axioms OperatorKO7.Meta.Rewriting.Term.subtermAt_replaceAt_same
#print axioms OperatorKO7.Meta.Rewriting.Term.replaceAt_parallel_comm
