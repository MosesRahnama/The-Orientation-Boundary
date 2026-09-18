import OperatorKO7.Meta.Methods.OrientationClosure.PolynomialOrientationDecision
import OperatorKO7.Meta.Methods.OrientationClosure.CouplingTheorem
import OperatorKO7.Meta.Methods.OrientationClosure.MethodRowsDependencyPairs
import Mathlib.Tactic

/-!
# The orientation boundary in a certificate language

Certificates for termination of the free recursor come in four kinds, as in the certification
format of termination tools: a natural-coefficient polynomial interpretation with successor
`n ↦ n + a`, a matrix interpretation of any dimension, a Knuth-Bendix order, and dependency pairs
with the subterm criterion for a projection. `check` is an executable checker.

* Polynomial certificates. The checker is the decision procedure of T-DEC-1 together with a test
  for positive linear monomials in every argument. An accepted certificate proves termination of
  the contextual relation (`checkPoly_sound`); on certificates that pass the monomial test, the
  checker accepts if and only if the interpretation orients both root rules
  (`checkPoly_complete`), so its rejections are complete for this class.
* No certificate of a direct class is accepted: retentive affine polynomial certificates, by the
  coupling inequality of P3.1 on the value schema (`affine_certificate_rejected`); matrix
  certificates, by the same inequality on the top-left entries (`matrix_certificate_rejected`);
  Knuth-Bendix certificates, by the variable condition (`kbo_certificate_rejected`).
* The dependency-pair checker accepts a projection if and only if the subterm criterion holds for
  it, which happens if and only if it selects the counter (`checkDP_iff`); the counter projection
  is accepted and proves termination (`checkDP_sound`).
* The coupled polynomial certificate `(n + 1)(s + b + 2)` with wrapper `s + y + 1` is accepted
  (`region_certificate_accepted`).
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.CertificateLanguage

open OperatorKO7.Meta.Rewriting
open OperatorKO7.StepDuplicating
open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.InterpretationLaws
open OperatorKO7.Methods.OrientationClosure.PolynomialOrientationDecision
open OperatorKO7.Methods.OrientationClosure.CouplingTheorem
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness
open OperatorKO7.Methods.OrientationClosure.MethodRowsDependencyPairs

/-! ## Certificates -/

/-- A matrix interpretation of dimension `d + 1`: a constant vector and one matrix per argument
position for every free symbol. -/
structure MatrixCert (d : Nat) where
  const : FreeSym → Fin (d + 1) → Nat
  mat : FreeSym → Nat → Matrix (Fin (d + 1)) (Fin (d + 1)) Nat

/-- A Knuth-Bendix certificate: symbol weights, the variable weight and a precedence. -/
structure KBOCert where
  weight : FreeSym → Nat
  varWeight : Nat
  prec : FreeSym → Nat

/-- Certificates for termination of the free recursor. -/
inductive Certificate where
  | poly (z a : Nat) (W : List WMono) (R : List RMono)
  | matrix (d : Nat) (M : MatrixCert d)
  | kbo (K : KBOCert)
  | dpSubterm (proj : FreeSym → Nat)

/-! ## Polynomial certificates -/

/-- The wrapper has positive linear monomials in `s` and in `y`; the recursor has positive linear
monomials in `b`, in `s` and in `n`. -/
def linearMonomials (W : List WMono) (R : List RMono) : Bool :=
  W.any (fun m => decide (1 ≤ m.coeff) && m.sDeg == 1 && m.yDeg == 0) &&
    W.any (fun m => decide (1 ≤ m.coeff) && m.sDeg == 0 && m.yDeg == 1) &&
    R.any (fun m => decide (1 ≤ m.coeff) && m.bDeg == 1 && m.sDeg == 0 && m.nDeg == 0) &&
    R.any (fun m => decide (1 ≤ m.coeff) && m.bDeg == 0 && m.sDeg == 1 && m.nDeg == 0) &&
    R.any (fun m => decide (1 ≤ m.coeff) && m.bDeg == 0 && m.sDeg == 0 && m.nDeg == 1)

/-- The polynomial checker: the T-DEC-1 decision of both root rules and the monomial test. -/
def checkPoly (z a : Nat) (W : List WMono) (R : List RMono) : Bool :=
  decideRootUnit z a W R && linearMonomials W R

theorem wEval_mono (W : List WMono) {s s' y y' : Nat} (hs : s ≤ s') (hy : y ≤ y') :
    wEval W s y ≤ wEval W s' y' := by
  induction W with
  | nil => simp [wEval]
  | cons m p ih =>
    simp only [wEval]
    exact Nat.add_le_add
      (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs _)) (Nat.pow_le_pow_left hy _)) ih

theorem wEval_strict_s (W : List WMono) {s s' : Nat} (y : Nat) (hs : s < s')
    (hW : ∃ m ∈ W, 1 ≤ m.coeff ∧ m.sDeg = 1 ∧ m.yDeg = 0) : wEval W s y < wEval W s' y := by
  induction W with
  | nil =>
    obtain ⟨m, hm, -⟩ := hW
    simp at hm
  | cons m p ih =>
    simp only [wEval]
    obtain ⟨m', hm', hc, hsd, hyd⟩ := hW
    rcases List.mem_cons.1 hm' with heq | hp
    · rw [heq] at hc hsd hyd
      have h1 : m.coeff * s ^ m.sDeg * y ^ m.yDeg < m.coeff * s' ^ m.sDeg * y ^ m.yDeg := by
        rw [hsd, hyd, pow_one, pow_zero, mul_one, mul_one]
        nlinarith
      exact Nat.add_lt_add_of_lt_of_le h1 (wEval_mono p hs.le le_rfl)
    · have h1 : m.coeff * s ^ m.sDeg * y ^ m.yDeg ≤ m.coeff * s' ^ m.sDeg * y ^ m.yDeg :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs.le _))
      exact Nat.add_lt_add_of_le_of_lt h1 (ih ⟨m', hp, hc, hsd, hyd⟩)

theorem wEval_strict_y (W : List WMono) (s : Nat) {y y' : Nat} (hy : y < y')
    (hW : ∃ m ∈ W, 1 ≤ m.coeff ∧ m.sDeg = 0 ∧ m.yDeg = 1) : wEval W s y < wEval W s y' := by
  induction W with
  | nil =>
    obtain ⟨m, hm, -⟩ := hW
    simp at hm
  | cons m p ih =>
    simp only [wEval]
    obtain ⟨m', hm', hc, hsd, hyd⟩ := hW
    rcases List.mem_cons.1 hm' with heq | hp
    · rw [heq] at hc hsd hyd
      have h1 : m.coeff * s ^ m.sDeg * y ^ m.yDeg < m.coeff * s ^ m.sDeg * y' ^ m.yDeg := by
        rw [hsd, hyd, pow_one, pow_zero, mul_one]
        nlinarith
      exact Nat.add_lt_add_of_lt_of_le h1 (wEval_mono p le_rfl hy.le)
    · have h1 : m.coeff * s ^ m.sDeg * y ^ m.yDeg ≤ m.coeff * s ^ m.sDeg * y' ^ m.yDeg :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hy.le _)
      exact Nat.add_lt_add_of_le_of_lt h1 (ih ⟨m', hp, hc, hsd, hyd⟩)

theorem rEval_strict_b (R : List RMono) {b b' : Nat} (s n : Nat) (hb : b < b')
    (hR : ∃ m ∈ R, 1 ≤ m.coeff ∧ m.bDeg = 1 ∧ m.sDeg = 0 ∧ m.nDeg = 0) :
    rEval R b s n < rEval R b' s n := by
  induction R with
  | nil =>
    obtain ⟨m, hm, -⟩ := hR
    simp at hm
  | cons m p ih =>
    simp only [rEval]
    obtain ⟨m', hm', hc, hbd, hsd, hnd⟩ := hR
    rcases List.mem_cons.1 hm' with heq | hp
    · rw [heq] at hc hbd hsd hnd
      have h1 : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg <
          m.coeff * b' ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg := by
        rw [hbd, hsd, hnd, pow_one, pow_zero, pow_zero, mul_one, mul_one]
        nlinarith
      exact Nat.add_lt_add_of_lt_of_le h1 (rEval_mono p hb.le le_rfl le_rfl)
    · have h1 : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg ≤
          m.coeff * b' ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb.le _)))
      exact Nat.add_lt_add_of_le_of_lt h1 (ih ⟨m', hp, hc, hbd, hsd, hnd⟩)

theorem rEval_strict_s (R : List RMono) (b : Nat) {s s' : Nat} (n : Nat) (hs : s < s')
    (hR : ∃ m ∈ R, 1 ≤ m.coeff ∧ m.bDeg = 0 ∧ m.sDeg = 1 ∧ m.nDeg = 0) :
    rEval R b s n < rEval R b s' n := by
  induction R with
  | nil =>
    obtain ⟨m, hm, -⟩ := hR
    simp at hm
  | cons m p ih =>
    simp only [rEval]
    obtain ⟨m', hm', hc, hbd, hsd, hnd⟩ := hR
    rcases List.mem_cons.1 hm' with heq | hp
    · rw [heq] at hc hbd hsd hnd
      have h1 : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg <
          m.coeff * b ^ m.bDeg * s' ^ m.sDeg * n ^ m.nDeg := by
        rw [hbd, hsd, hnd, pow_one, pow_zero, pow_zero, mul_one, mul_one]
        nlinarith
      exact Nat.add_lt_add_of_lt_of_le h1 (rEval_mono p le_rfl hs.le le_rfl)
    · have h1 : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg ≤
          m.coeff * b ^ m.bDeg * s' ^ m.sDeg * n ^ m.nDeg :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs.le _))
      exact Nat.add_lt_add_of_le_of_lt h1 (ih ⟨m', hp, hc, hbd, hsd, hnd⟩)

theorem rEval_strict_n (R : List RMono) (b s : Nat) {n n' : Nat} (hn : n < n')
    (hR : ∃ m ∈ R, 1 ≤ m.coeff ∧ m.bDeg = 0 ∧ m.sDeg = 0 ∧ m.nDeg = 1) :
    rEval R b s n < rEval R b s n' := by
  induction R with
  | nil =>
    obtain ⟨m, hm, -⟩ := hR
    simp at hm
  | cons m p ih =>
    simp only [rEval]
    obtain ⟨m', hm', hc, hbd, hsd, hnd⟩ := hR
    rcases List.mem_cons.1 hm' with heq | hp
    · rw [heq] at hc hbd hsd hnd
      have h1 : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg <
          m.coeff * b ^ m.bDeg * s ^ m.sDeg * n' ^ m.nDeg := by
        rw [hbd, hsd, hnd, pow_one, pow_zero, pow_zero, mul_one, mul_one]
        nlinarith
      exact Nat.add_lt_add_of_lt_of_le h1 (rEval_mono p le_rfl le_rfl hn.le)
    · have h1 : m.coeff * b ^ m.bDeg * s ^ m.sDeg * n ^ m.nDeg ≤
          m.coeff * b ^ m.bDeg * s ^ m.sDeg * n' ^ m.nDeg :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn.le _)
      exact Nat.add_lt_add_of_le_of_lt h1 (ih ⟨m', hp, hc, hbd, hsd, hnd⟩)

/-- The monomial test gives strict monotonicity in every argument. -/
theorem poly_strictContextLaws {z a : Nat} {W : List WMono} {R : List RMono}
    (h : linearMonomials W R = true) :
    StrictContextLaws (polyInterpretation z 1 a W R) (· < ·) := by
  simp only [linearMonomials, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨m1, hm1, ⟨hc1, hs1⟩, hy1⟩, ⟨m2, hm2, ⟨hc2, hs2⟩, hy2⟩⟩, ⟨m3, hm3, ⟨⟨hc3, hb3⟩, hs3⟩, hn3⟩⟩,
    ⟨m4, hm4, ⟨⟨hc4, hb4⟩, hs4⟩, hn4⟩⟩, ⟨m5, hm5, ⟨⟨hc5, hb5⟩, hs5⟩, hn5⟩⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    show 1 * x + a < 1 * y + a
    omega
  · intro x y w hxy
    exact wEval_strict_s W w hxy ⟨m1, hm1, hc1, hs1, hy1⟩
  · intro w x y hxy
    exact wEval_strict_y W w hxy ⟨m2, hm2, hc2, hs2, hy2⟩
  · intro x y s n hxy
    exact rEval_strict_b R s n hxy ⟨m3, hm3, hc3, hb3, hs3, hn3⟩
  · intro b x y n hxy
    exact rEval_strict_s R b n hxy ⟨m4, hm4, hc4, hb4, hs4, hn4⟩
  · intro b s x y hxy
    exact rEval_strict_n R b s hxy ⟨m5, hm5, hc5, hb5, hs5, hn5⟩

/-- Soundness: an accepted polynomial certificate proves termination of the contextual relation. -/
theorem checkPoly_sound {z a : Nat} {W : List WMono} {R : List RMono}
    (h : checkPoly z a W R = true) (ν : Type) :
    WellFounded (fun u t : FreeTerm ν => ContextStep t u) := by
  simp only [checkPoly, Bool.and_eq_true] at h
  exact contextStep_reverse_wellFounded ((decideRootUnit_iff z a W R).1 h.1)
    (poly_strictContextLaws h.2) Nat.lt_wfRel.wf (fun _ => 0)

/-- Completeness: on certificates that pass the monomial test, the checker accepts exactly the
interpretations that orient both root rules. -/
theorem checkPoly_complete {z a : Nat} {W : List WMono} {R : List RMono}
    (hm : linearMonomials W R = true) :
    checkPoly z a W R = true ↔ RootRuleOrients (polyInterpretation z 1 a W R) (· < ·) := by
  rw [checkPoly, hm, Bool.and_true, decideRootUnit_iff]

/-- The value schema of a unit-successor polynomial interpretation. -/
abbrev valueSchema (z a : Nat) (W : List WMono) (R : List RMono) : StepDuplicatingSchema where
  T := Nat
  base := z
  succ n := 1 * n + a
  wrap := wEval W
  recur := rEval R

/-- Retentive affine polynomial certificates are rejected, by the coupling inequality on the value
schema: retention of the wrapper arguments forces the counter gain above every payload value, and
an affine recursor has a gain independent of the payload. -/
theorem affine_certificate_rejected (z a α βw γ r0 rb rs rn : Nat) (hβw : 1 ≤ βw) (hγ : 1 ≤ γ) :
    checkPoly z a (affineW α βw γ) (multilinearR r0 rb rs rn 0 0 0 0) = false := by
  cases h : checkPoly z a (affineW α βw γ) (multilinearR r0 rb rs rn 0 0 0 0) with
  | false => rfl
  | true =>
    exfalso
    simp only [checkPoly, Bool.and_eq_true] at h
    have hroot := (decideRootUnit_iff z a _ _).1 h.1
    have hret : ∀ x y : Nat, α + x + y ≤ wEval (affineW α βw γ) x y := by
      intro x y
      simp [affineW, wEval]
      nlinarith
    have hc := retained_wrapper_forces_payload_coupled_gain
      (S := valueSchema z a (affineW α βw γ) (multilinearR r0 rb rs rn 0 0 0 0)) id α
      (fun x y => hret x y) (fun b s n => hroot.recurSucc b s n)
    have key := hc 0 (rn * a) 0
    simp only [counterGainZ, id] at key
    simp only [rEval_multilinearR] at key
    have hα0 : (0 : Int) ≤ (α : Int) := by positivity
    push_cast at key
    ring_nf at key
    linarith

/-- The coupled certificate of the P2.4 region is accepted. -/
theorem region_certificate_accepted : checkPoly 0 1 regionW (regionR 1 2) = true := by
  rw [checkPoly, (region_decides 1 2).2 ⟨le_rfl, le_rfl⟩, Bool.true_and]
  decide

/-! ## Matrix certificates -/

/-- Entrywise comparison `B ≤ A` of natural matrices. -/
def matGe {k : Nat} (A B : Matrix (Fin k) (Fin k) Nat) : Bool := decide (∀ i j, B i j ≤ A i j)

/-- The matrix checker (Endrullis, Waldmann and Zantema 2008): positive top-left entries of the
argument matrices, the coefficient conditions of the successor rule for `b`, `s` and `n`, and the
strict condition on the first entry of the constant vectors. -/
def checkMatrix (d : Nat) (M : MatrixCert d) : Bool :=
  decide (1 ≤ M.mat .succ 0 0 0) && decide (1 ≤ M.mat .wrap 0 0 0) &&
    decide (1 ≤ M.mat .wrap 1 0 0) && decide (1 ≤ M.mat .recur 0 0 0) &&
    decide (1 ≤ M.mat .recur 1 0 0) && decide (1 ≤ M.mat .recur 2 0 0) &&
    matGe (M.mat .recur 0) (M.mat .wrap 1 * M.mat .recur 0) &&
    matGe (M.mat .recur 1) (M.mat .wrap 0 + M.mat .wrap 1 * M.mat .recur 1) &&
    matGe (M.mat .recur 2 * M.mat .succ 0) (M.mat .wrap 1 * M.mat .recur 2) &&
    decide (M.const .wrap 0 + (M.mat .wrap 1).mulVec (M.const .recur) 0 <
      M.const .recur 0 + (M.mat .recur 2).mulVec (M.const .succ) 0)

/-- No matrix certificate is accepted: at the top-left entry the step argument occurs once on the
left and twice on the right, and positive entries make the right side larger. -/
theorem matrix_certificate_rejected (d : Nat) (M : MatrixCert d) : checkMatrix d M = false := by
  cases h : checkMatrix d M with
  | false => rfl
  | true =>
    exfalso
    simp only [checkMatrix, matGe, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hw0⟩, hw1⟩, -⟩, -⟩, -⟩, -⟩, hs⟩, -⟩, -⟩ := h
    have key := hs 0 0
    rw [Matrix.add_apply, Matrix.mul_apply] at key
    have hsum : M.mat .wrap 1 0 0 * M.mat .recur 1 0 0 ≤
        ∑ j, M.mat .wrap 1 0 j * M.mat .recur 1 j 0 :=
      Finset.single_le_sum (f := fun j => M.mat .wrap 1 0 j * M.mat .recur 1 j 0)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ 0)
    have h3 := Nat.mul_le_mul_right (M.mat .recur 1 0 0) hw1
    linarith

/-! ## Knuth-Bendix certificates -/

mutual
/-- Occurrences of the variable `x`. -/
def varCount (x : Nat) : Term FreeSym Nat → Nat
  | .var y => if y = x then 1 else 0
  | .app _ args => varCountList x args
/-- Occurrences of the variable `x` in a list of terms. -/
def varCountList (x : Nat) : List (Term FreeSym Nat) → Nat
  | [] => 0
  | t :: ts => varCount x t + varCountList x ts
end

/-- The variable condition: no listed variable occurs more often on the right than on the left. -/
def varCondition (r : Rule FreeSym Nat) (xs : List Nat) : Bool :=
  xs.all fun x => decide (varCount x r.rhs ≤ varCount x r.lhs)

/-- The Knuth-Bendix checker (Knuth and Bendix 1970): the variable condition of both rules and the
admissibility of the weights. The comparison of the two sides is evaluated only after these
conditions, and for the free recursor the variable condition of the successor rule already
fails. -/
def checkKBO (K : KBOCert) : Bool :=
  varCondition zeroRule [0, 1] && varCondition succRule [0, 1, 2] &&
    decide (1 ≤ K.varWeight) && decide (K.varWeight ≤ K.weight .zero)

theorem succRule_varCondition_fails : varCondition succRule [0, 1, 2] = false := by
  decide

/-- No Knuth-Bendix certificate is accepted: the step argument occurs once on the left of the
successor rule and twice on the right. -/
theorem kbo_certificate_rejected (K : KBOCert) : checkKBO K = false := by
  simp [checkKBO, succRule_varCondition_fails]

/-! ## Dependency-pair certificates -/

/-- The dependency-pair checker: the subterm criterion of the unique dependency pair
`recur(b, s, succ n) → recur(b, s, n)` at the projection `proj`. -/
def checkDP (proj : FreeSym → Nat) : Bool := proj .recur == 2

theorem subtermCriterion_of_proj {proj : FreeSym → Nat} (hproj : proj .recur = 2) :
    SubtermCriterion freeRecursorTRS proj := by
  intro rule hrule f largs hl g targs hsub hdef
  rw [freeRecursorTRS_defined_iff] at hdef
  subst hdef
  simp only [freeRecursorTRS, List.mem_cons, List.not_mem_nil, or_false] at hrule
  rcases hrule with rfl | rfl
  · simp only [zeroRule] at hsub
    exact absurd hsub not_isSubterm_app_var
  · have ht := succRule_rhs_recur_subterm hsub
    subst ht
    simp only [succRule, Term.app.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    rw [hproj]
    exact ⟨Term.app FreeSym.succ [Term.var 2], Term.var 2, rfl, rfl,
      ProperSubterm.arg FreeSym.succ [Term.var 2] List.mem_cons_self (IsSubterm.refl _)⟩

/-- The checker accepts a projection if and only if the subterm criterion holds for it. -/
theorem checkDP_iff (proj : FreeSym → Nat) :
    checkDP proj = true ↔ SubtermCriterion freeRecursorTRS proj := by
  constructor
  · intro h
    exact subtermCriterion_of_proj (by simpa [checkDP] using h)
  · intro hsc
    have hsub : IsSubterm (Term.app FreeSym.recur [Term.var 0, Term.var 1, Term.var 2])
        succRule.rhs :=
      IsSubterm.arg FreeSym.wrap _ (by simp) (IsSubterm.refl _)
    obtain ⟨l0, t0, hl0, ht0, hprop⟩ := hsc succRule (by simp [freeRecursorTRS]) FreeSym.recur
      [Term.var 0, Term.var 1, Term.app FreeSym.succ [Term.var 2]] rfl FreeSym.recur
      [Term.var 0, Term.var 1, Term.var 2] hsub ((freeRecursorTRS_defined_iff _).2 rfl)
    simp only [checkDP, beq_iff_eq]
    generalize proj FreeSym.recur = k at hl0 ht0
    match k, hl0, ht0 with
    | 0, hl0, ht0 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hl0 ht0
      subst hl0
      subst ht0
      cases hprop
    | 1, hl0, ht0 =>
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hl0 ht0
      subst hl0
      subst ht0
      cases hprop
    | 2, _, _ => rfl
    | k + 3, hl0, _ => simp at hl0

/-- Soundness: an accepted dependency-pair certificate proves termination of the free recursor. -/
theorem checkDP_sound {proj : FreeSym → Nat} (h : checkDP proj = true) : FreeTerminates :=
  terminating_of_subtermCriterion freeRecursorTRS freeRecursorTRS_vars ((checkDP_iff proj).1 h)

theorem counter_certificate_accepted : checkDP freeProj = true := rfl

/-! ## The checker and the boundary -/

/-- The executable checker. -/
def check : Certificate → Bool
  | .poly z a W R => checkPoly z a W R
  | .matrix d M => checkMatrix d M
  | .kbo K => checkKBO K
  | .dpSubterm proj => checkDP proj

/-- What an accepted certificate proves: termination of the free recursor, in the term encoding of
its method (constructor terms for interpretations and orders, first-order rewrite terms for
dependency pairs). -/
def Proves : Certificate → Prop
  | .poly .. => WellFounded (fun u t : FreeTerm Nat => ContextStep t u)
  | .matrix .. => WellFounded (fun u t : FreeTerm Nat => ContextStep t u)
  | .kbo .. => WellFounded (fun u t : FreeTerm Nat => ContextStep t u)
  | .dpSubterm _ => FreeTerminates

theorem check_sound : ∀ c : Certificate, check c = true → Proves c
  | .poly _ _ _ _, h => checkPoly_sound h Nat
  | .matrix d M, h => by
    simp [check, matrix_certificate_rejected] at h
  | .kbo K, h => by
    simp [check, kbo_certificate_rejected] at h
  | .dpSubterm _, h => checkDP_sound h

/-- The orientation boundary in the certificate language. No retentive affine polynomial, matrix
or Knuth-Bendix certificate is accepted; the counter-projection dependency-pair certificate and the
coupled polynomial certificate are accepted; every accepted certificate proves termination; on
certificates that pass the monomial test the polynomial checker accepts exactly the orienting
interpretations. -/
theorem certificate_boundary :
    (∀ z a α βw γ r0 rb rs rn : Nat, 1 ≤ βw → 1 ≤ γ →
        check (.poly z a (affineW α βw γ) (multilinearR r0 rb rs rn 0 0 0 0)) = false) ∧
      (∀ (d : Nat) (M : MatrixCert d), check (.matrix d M) = false) ∧
      (∀ K : KBOCert, check (.kbo K) = false) ∧
      check (.dpSubterm freeProj) = true ∧
      check (.poly 0 1 regionW (regionR 1 2)) = true ∧
      (∀ c : Certificate, check c = true → Proves c) ∧
      (∀ (z a : Nat) (W : List WMono) (R : List RMono), linearMonomials W R = true →
        (check (.poly z a W R) = true ↔ RootRuleOrients (polyInterpretation z 1 a W R) (· < ·))) :=
  ⟨fun z a α βw γ r0 rb rs rn hβw hγ => affine_certificate_rejected z a α βw γ r0 rb rs rn hβw hγ,
    fun d M => matrix_certificate_rejected d M, fun K => kbo_certificate_rejected K,
    counter_certificate_accepted, region_certificate_accepted, check_sound,
    fun _ _ _ _ hm => checkPoly_complete hm⟩

end OperatorKO7.Methods.OrientationClosure.CertificateLanguage
