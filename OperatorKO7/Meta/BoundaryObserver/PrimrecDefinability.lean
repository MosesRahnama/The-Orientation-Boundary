import OperatorKO7.Meta.DistinctionBoundary.GodelArithmetization
import Mathlib.Computability.Primrec

/-!
# Arithmetic definitions of primitive recursive functions

Manuscript: the appeal to Proposition VII of Gödel in Theorem `thm:godel-equality-repair`.

Every `Nat.Primrec` function `f` has, for every input variable `a` and output variable `b` at least
`53`, a formula `φ` of the checker's language with `evalForm env φ ↔ f (env a) = env b` for every
environment. The proof follows the generation of `Nat.Primrec`: zero and successor are equations,
the two projections of the Cantor pairing are read through the pairing equation, pairing and
composition introduce fresh variables, and primitive recursion quantifies over a finite sequence
coded by Gödel's `β` function, whose existence is `beta_exists`. Variables below `53` are avoided
because the order and remainder formulas bind `50`, `51` and `52`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.PrimrecDefinability

open OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-- `φ` defines `f` with input variable `a` and output variable `b`. -/
def DefinesAt (f : ℕ → ℕ) (φ : Formula) (a b : ℕ) : Prop :=
  ∀ env : ℕ → ℕ, evalForm env φ ↔ f (env a) = env b

/-- `f` has a defining formula at every pair of variables at least `53`. -/
def Definable (f : ℕ → ℕ) : Prop :=
  ∀ a b : ℕ, 53 ≤ a → 53 ≤ b → ∃ φ, DefinesAt f φ a b

/-! ## Fresh variables and environment updates -/

/-- Fresh variables above `a`, `b` and the bound variables of the order formulas. -/
def vr (a b j : ℕ) : ℕ := a + b + 53 + j

@[simp] theorem vr_ge (a b j : ℕ) : 53 ≤ vr a b j := by unfold vr; omega
@[simp] theorem left_ne_vr (a b j : ℕ) : a ≠ vr a b j := by unfold vr; omega
@[simp] theorem right_ne_vr (a b j : ℕ) : b ≠ vr a b j := by unfold vr; omega
@[simp] theorem vr_inj (a b i j : ℕ) : vr a b i = vr a b j ↔ i = j := by unfold vr; omega
@[simp] theorem vr_ne_51 (a b j : ℕ) : vr a b j ≠ 51 := by unfold vr; omega
@[simp] theorem vr_ne_52 (a b j : ℕ) : vr a b j ≠ 52 := by unfold vr; omega

/-- Environment update. -/
def upd (env : ℕ → ℕ) (x n : ℕ) : ℕ → ℕ := fun y => if y = x then n else env y

@[simp] theorem upd_same (env : ℕ → ℕ) (x n : ℕ) : upd env x n x = n := if_pos rfl

theorem upd_ne (env : ℕ → ℕ) {x y : ℕ} (n : ℕ) (h : y ≠ x) : upd env x n y = env y := if_neg h

theorem eval_ex (env : ℕ → ℕ) (x : ℕ) (φ : Formula) :
    evalForm env (existsF x φ) ↔ ∃ n, evalForm (upd env x n) φ :=
  eval_existsF env x φ

theorem eval_all (env : ℕ → ℕ) (x : ℕ) (φ : Formula) :
    evalForm env (Formula.all x φ) ↔ ∀ n, evalForm (upd env x n) φ :=
  Iff.rfl

theorem eval_imp (env : ℕ → ℕ) (φ ψ : Formula) :
    evalForm env (Formula.imp φ ψ) ↔ (evalForm env φ → evalForm env ψ) :=
  Iff.rfl

theorem eval_eqv (env : ℕ → ℕ) (s t : Term) :
    evalForm env (Formula.eq s t) ↔ evalTerm env s = evalTerm env t :=
  Iff.rfl

theorem eval_not (env : ℕ → ℕ) (φ : Formula) :
    evalForm env (Formula.not φ) ↔ ¬ evalForm env φ :=
  Iff.rfl

theorem termHasVar_var_ne {k x : ℕ} (h : x ≠ k) : termHasVar k (Term.var x) = false := by
  simp [termHasVar, h]

/-! ## Order, pairing and the `β` function on variables -/

theorem eval_ltV (env : ℕ → ℕ) {x y : ℕ} (hx : x ≠ 51) (hy : y ≠ 51) :
    evalForm env (ltF (Term.var x) (Term.var y)) ↔ env x < env y := by
  simpa [evalTerm] using eval_ltF env (Term.var x) (Term.var y) (termHasVar_var_ne hx)
    (termHasVar_var_ne hy)

/-- The Cantor pairing equation `n = pair x y` on variables. -/
def PairF (x y n : ℕ) : Formula :=
  orF (andF (ltF (Term.var x) (Term.var y))
        (Formula.eq (Term.var n) (Term.add (Term.mul (Term.var y) (Term.var y)) (Term.var x))))
      (andF (Formula.not (ltF (Term.var x) (Term.var y)))
        (Formula.eq (Term.var n)
          (Term.add (Term.add (Term.mul (Term.var x) (Term.var x)) (Term.var x)) (Term.var y))))

theorem eval_PairF (env : ℕ → ℕ) {x y n : ℕ} (hx : x ≠ 51) (hy : y ≠ 51) :
    evalForm env (PairF x y n) ↔ env n = Nat.pair (env x) (env y) := by
  have hlt := eval_ltV env hx hy
  simp only [PairF, eval_orF, eval_andF, eval_not, eval_eqv, hlt, evalTerm, Nat.pair]
  by_cases h : env x < env y <;> simp [h]

theorem eval_betaT (env : ℕ → ℕ) {c d w : ℕ} (i : Term) (hc : c ≠ 52) (hd1 : d ≠ 51)
    (hd2 : d ≠ 52) (hw1 : w ≠ 51) (hw2 : w ≠ 52) (hi1 : termHasVar 51 i = false)
    (hi2 : termHasVar 52 i = false) :
    evalForm env (betaF (Term.var c) (Term.var d) i (Term.var w)) ↔
      env w = beta (env c) (env d) (evalTerm env i) := by
  simpa [evalTerm] using eval_betaF env (Term.var c) (Term.var d) i (Term.var w) hi1
    (termHasVar_var_ne hd1) (termHasVar_var_ne hw1) (termHasVar_var_ne hc) hi2
    (termHasVar_var_ne hd2) (termHasVar_var_ne hw2)

theorem eval_betaV (env : ℕ → ℕ) {c d i w : ℕ} (hc : c ≠ 52) (hd1 : d ≠ 51) (hd2 : d ≠ 52)
    (hi1 : i ≠ 51) (hi2 : i ≠ 52) (hw1 : w ≠ 51) (hw2 : w ≠ 52) :
    evalForm env (betaF (Term.var c) (Term.var d) (Term.var i) (Term.var w)) ↔
      env w = beta (env c) (env d) (env i) :=
  eval_betaT env (Term.var i) hc hd1 hd2 hw1 hw2 (termHasVar_var_ne hi1) (termHasVar_var_ne hi2)

theorem eval_betaZ (env : ℕ → ℕ) {c d w : ℕ} (hc : c ≠ 52) (hd1 : d ≠ 51) (hd2 : d ≠ 52)
    (hw1 : w ≠ 51) (hw2 : w ≠ 52) :
    evalForm env (betaF (Term.var c) (Term.var d) Term.zero (Term.var w)) ↔
      env w = beta (env c) (env d) 0 :=
  eval_betaT env Term.zero hc hd1 hd2 hw1 hw2 rfl rfl

theorem eval_betaS (env : ℕ → ℕ) {c d i w : ℕ} (hc : c ≠ 52) (hd1 : d ≠ 51) (hd2 : d ≠ 52)
    (hi1 : i ≠ 51) (hi2 : i ≠ 52) (hw1 : w ≠ 51) (hw2 : w ≠ 52) :
    evalForm env (betaF (Term.var c) (Term.var d) (Term.succ (Term.var i)) (Term.var w)) ↔
      env w = beta (env c) (env d) (env i + 1) :=
  eval_betaT env (Term.succ (Term.var i)) hc hd1 hd2 hw1 hw2 (termHasVar_var_ne hi1)
    (termHasVar_var_ne hi2)

/-! ## Primitive recursion -/

/-- The sequence computed by `Nat.Primrec.prec` at the parameter `z`. -/
def precSeq (f g : ℕ → ℕ) (z : ℕ) : ℕ → ℕ
  | 0 => f z
  | i + 1 => g (Nat.pair z (Nat.pair i (precSeq f g z i)))

theorem rec_eq_precSeq (f g : ℕ → ℕ) (z : ℕ) :
    ∀ n : ℕ, Nat.rec (motive := fun _ => ℕ) (f z) (fun y IH => g (Nat.pair z (Nat.pair y IH))) n =
      precSeq f g z n
  | 0 => rfl
  | n + 1 => by
      show g (Nat.pair z (Nat.pair n (Nat.rec (motive := fun _ => ℕ) (f z)
        (fun y IH => g (Nat.pair z (Nat.pair y IH))) n))) =
        g (Nat.pair z (Nat.pair n (precSeq f g z n)))
      rw [rec_eq_precSeq f g z n]

/-- The defining formula of a primitive recursion, with `φF` defining the base function at
variables `vr a b 0`, `vr a b 4` and `φG` the step function at `vr a b 8`, `vr a b 9`. -/
def precForm (φF φG : Formula) (a b : ℕ) : Formula :=
  existsF (vr a b 0) (existsF (vr a b 1) (andF (PairF (vr a b 0) (vr a b 1) a)
    (existsF (vr a b 2) (existsF (vr a b 3) (andF
      (existsF (vr a b 4) (andF
        (betaF (Term.var (vr a b 2)) (Term.var (vr a b 3)) Term.zero (Term.var (vr a b 4))) φF))
      (andF
        (Formula.all (vr a b 5) (Formula.imp (ltF (Term.var (vr a b 5)) (Term.var (vr a b 1)))
          (existsF (vr a b 6) (existsF (vr a b 7) (existsF (vr a b 8) (existsF (vr a b 9) (andF
            (betaF (Term.var (vr a b 2)) (Term.var (vr a b 3)) (Term.var (vr a b 5))
              (Term.var (vr a b 6)))
            (andF (PairF (vr a b 5) (vr a b 6) (vr a b 7))
              (andF (PairF (vr a b 0) (vr a b 7) (vr a b 8))
                (andF (betaF (Term.var (vr a b 2)) (Term.var (vr a b 3))
                  (Term.succ (Term.var (vr a b 5))) (Term.var (vr a b 9))) φG))))))))))
        (betaF (Term.var (vr a b 2)) (Term.var (vr a b 3)) (Term.var (vr a b 1)) (Term.var b))))))))

theorem precForm_defines {f g : ℕ → ℕ} {φF φG : Formula} {a b : ℕ} (ha : 53 ≤ a) (hb : 53 ≤ b)
    (hF : ∀ e, evalForm e φF ↔ f (e (vr a b 0)) = e (vr a b 4))
    (hG : ∀ e, evalForm e φG ↔ g (e (vr a b 8)) = e (vr a b 9)) (env : ℕ → ℕ) :
    evalForm env (precForm φF φG a b) ↔ precSeq f g (env a).unpair.1 (env a).unpair.2 = env b := by
  have ha51 : a ≠ 51 := by omega
  have hb51 : b ≠ 51 := by omega
  have hb52 : b ≠ 52 := by omega
  simp only [precForm, eval_ex, eval_all, eval_imp, eval_andF, hF, hG,
    eval_PairF _ (vr_ne_51 _ _ _) (vr_ne_51 _ _ _), eval_PairF _ (vr_ne_51 _ _ _) ha51,
    eval_betaZ _ (vr_ne_52 _ _ _) (vr_ne_51 _ _ _) (vr_ne_52 _ _ _) (vr_ne_51 _ _ _) (vr_ne_52 _ _ _),
    eval_betaV _ (vr_ne_52 _ _ _) (vr_ne_51 _ _ _) (vr_ne_52 _ _ _) (vr_ne_51 _ _ _)
      (vr_ne_52 _ _ _) (vr_ne_51 _ _ _) (vr_ne_52 _ _ _),
    eval_betaV _ (vr_ne_52 _ _ _) (vr_ne_51 _ _ _) (vr_ne_52 _ _ _) (vr_ne_51 _ _ _)
      (vr_ne_52 _ _ _) hb51 hb52,
    eval_betaS _ (vr_ne_52 _ _ _) (vr_ne_51 _ _ _) (vr_ne_52 _ _ _) (vr_ne_51 _ _ _)
      (vr_ne_52 _ _ _) (vr_ne_51 _ _ _) (vr_ne_52 _ _ _),
    eval_ltV _ (vr_ne_51 _ _ _) (vr_ne_51 _ _ _)]
  simp only [upd_same, ne_eq, upd_ne _ _ (left_ne_vr a b _), upd_ne _ _ (right_ne_vr a b _)]
  simp (disch := simp) only [upd_ne, upd_same, vr_inj, OfNat.ofNat_ne_zero, not_false_eq_true]
  constructor
  · rintro ⟨zv, yv, hpair, cv, dv, ⟨wv, hw, hfw⟩, hstep, hfin⟩
    have hseq : ∀ k, k ≤ yv → beta cv dv k = precSeq f g zv k := by
      intro k
      induction k with
      | zero => intro _; rw [← hw, ← hfw]; rfl
      | succ k ih =>
        intro hk
        obtain ⟨w1v, p1v, p2v, w2v, h1, h2, h3, h4, h5⟩ := hstep k hk
        rw [← h4, ← h5, h3, h2, h1, ih (Nat.le_of_succ_le hk)]
        rfl
    rw [hpair, Nat.unpair_pair, hfin, hseq yv le_rfl]
  · intro h
    obtain ⟨cv, dv, hcd⟩ := beta_exists (env a).unpair.2 (precSeq f g (env a).unpair.1)
    refine ⟨(env a).unpair.1, (env a).unpair.2, (Nat.pair_unpair (env a)).symm, cv, dv,
      ⟨beta cv dv 0, rfl, ?_⟩, ?_, ?_⟩
    · rw [hcd 0 (Nat.zero_le _)]
      rfl
    · intro iv hiv
      refine ⟨beta cv dv iv, Nat.pair iv (beta cv dv iv),
        Nat.pair (env a).unpair.1 (Nat.pair iv (beta cv dv iv)), beta cv dv (iv + 1),
        rfl, rfl, rfl, rfl, ?_⟩
      rw [hcd iv (Nat.le_of_lt hiv), hcd (iv + 1) hiv]
      rfl
    · rw [hcd _ le_rfl, h]

/-! ## Proposition VII -/

/-- **Proposition VII.** Every primitive recursive function has an arithmetic definition. -/
theorem definable_of_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) : Definable f := by
  induction hf with
  | zero =>
    intro a b _ _
    exact ⟨Formula.eq (Term.var b) Term.zero, fun env => by
      simp only [eval_eqv, evalTerm]
      exact eq_comm⟩
  | succ =>
    intro a b _ _
    exact ⟨Formula.eq (Term.var b) (Term.succ (Term.var a)), fun env => by
      simp only [eval_eqv, evalTerm]
      exact eq_comm⟩
  | left =>
    intro a b ha hb
    refine ⟨existsF (vr a b 0) (PairF b (vr a b 0) a), fun env => ?_⟩
    have hb51 : b ≠ 51 := by omega
    simp only [eval_ex, eval_PairF _ hb51 (vr_ne_51 a b 0), upd_same,
      upd_ne _ _ (left_ne_vr a b 0), upd_ne _ _ (right_ne_vr a b 0)]
    constructor
    · rintro ⟨k, hk⟩
      rw [hk, Nat.unpair_pair]
    · intro h
      exact ⟨(env a).unpair.2, by rw [← h, Nat.pair_unpair]⟩
  | right =>
    intro a b ha hb
    refine ⟨existsF (vr a b 0) (PairF (vr a b 0) b a), fun env => ?_⟩
    have hb51 : b ≠ 51 := by omega
    simp only [eval_ex, eval_PairF _ (vr_ne_51 a b 0) hb51, upd_same,
      upd_ne _ _ (left_ne_vr a b 0), upd_ne _ _ (right_ne_vr a b 0)]
    constructor
    · rintro ⟨k, hk⟩
      rw [hk, Nat.unpair_pair]
    · intro h
      exact ⟨(env a).unpair.1, by rw [← h, Nat.pair_unpair]⟩
  | @pair f g _ _ ihf ihg =>
    intro a b ha hb
    obtain ⟨φF, hF⟩ := ihf a (vr a b 0) ha (vr_ge a b 0)
    obtain ⟨φG, hG⟩ := ihg a (vr a b 1) ha (vr_ge a b 1)
    have hF' : ∀ e, evalForm e φF ↔ f (e a) = e (vr a b 0) := hF
    have hG' : ∀ e, evalForm e φG ↔ g (e a) = e (vr a b 1) := hG
    refine ⟨existsF (vr a b 0) (existsF (vr a b 1)
      (andF φF (andF φG (PairF (vr a b 0) (vr a b 1) b)))), fun env => ?_⟩
    simp only [eval_ex, eval_andF, hF', hG', eval_PairF _ (vr_ne_51 a b 0) (vr_ne_51 a b 1)]
    simp (disch := simp) only [upd_ne, upd_same, vr_inj, left_ne_vr, right_ne_vr,
      OfNat.ofNat_ne_zero, not_false_eq_true, ne_eq]
    constructor
    · rintro ⟨x, y, rfl, rfl, h⟩
      exact h.symm
    · intro h
      exact ⟨_, _, rfl, rfl, h.symm⟩
  | @comp f g _ _ ihf ihg =>
    intro a b ha hb
    obtain ⟨φG, hG⟩ := ihg a (vr a b 0) ha (vr_ge a b 0)
    obtain ⟨φF, hF⟩ := ihf (vr a b 0) b (vr_ge a b 0) hb
    have hG' : ∀ e, evalForm e φG ↔ g (e a) = e (vr a b 0) := hG
    have hF' : ∀ e, evalForm e φF ↔ f (e (vr a b 0)) = e b := hF
    refine ⟨existsF (vr a b 0) (andF φG φF), fun env => ?_⟩
    simp only [eval_ex, eval_andF, hF', hG', upd_same, upd_ne _ _ (left_ne_vr a b 0),
      upd_ne _ _ (right_ne_vr a b 0)]
    constructor
    · rintro ⟨n, rfl, h⟩
      exact h
    · intro h
      exact ⟨_, rfl, h⟩
  | @prec f g _ _ ihf ihg =>
    intro a b ha hb
    obtain ⟨φF, hF⟩ := ihf (vr a b 0) (vr a b 4) (vr_ge a b 0) (vr_ge a b 4)
    obtain ⟨φG, hG⟩ := ihg (vr a b 8) (vr a b 9) (vr_ge a b 8) (vr_ge a b 9)
    refine ⟨precForm φF φG a b, fun env => (precForm_defines ha hb hF hG env).trans ?_⟩
    exact iff_of_eq (congrArg (· = env b) (rec_eq_precSeq f g _ _).symm)

end OperatorKO7.Meta.BoundaryObserver.PrimrecDefinability
