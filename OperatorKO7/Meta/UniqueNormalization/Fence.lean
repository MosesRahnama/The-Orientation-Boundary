import OperatorKO7.Meta.UniqueNormalization.CommonGeneralisation

/-!
# The KO7 fence: the RTA #79 hypothesis is required

Campaign: `Roadmaps\klop\ROADMAP.md`, WP-K1a. Exactly four clauses, and no fifth.

| Clause | Statement | Anchor |
|---|---|---|
| 1 | the `eqW` rule pair overlaps **finitely**, so KO7 lies outside `NonOverlapping` and outside `NonOmegaOverlapping` | `not_nonOmegaOverlapping` |
| 2 | KO7 fails UN= | `not_UNconv` |
| 3 | the `eqW` diagonal peak is a one-step non-joinable peak of KO7, and `FenceKernelBridge` identifies its three-state kernel image with the initial `Fork3` atom | `diagonal_peak_not_joinable`; `kernel_diagonal_contains_initial_fork3` |
| 4 | packaged as necessity of a sufficient hypothesis, by explicit counterexample | `hypothesis_required` |

**Not claimed.** This file does not assert that every UN= failure contains a
non-joinable one-step peak. The four clauses below need only the explicit KO7
witness; no converse, iff, or characterization of arbitrary UN= failure is used
or established here. The Huet and Klop systems in `Examples.lean` are separate
controls and are not invoked as a classification theorem.

## Fidelity block: the encoding of `OperatorKO7.Kernel`

`Trace` has seven constructors and `Step` has eight unconditional root rules,
with no congruence constructors. The eight rules are transcribed below.
`FenceKernelBridge.lean` carries the encoding `enc : Trace -> Term Nat Nat` and
proves that it simulates every kernel step; that file is separate because
`OperatorKO7.Kernel` also declares `Step` and `StepStar`, and importing it here
would shadow the rewriting library's names of the same spelling.

| `Trace` constructor | symbol | arity |
|---|---|---|
| `void` | `0` | 0 |
| `delta` | `1` | 1 |
| `integrate` | `2` | 1 |
| `merge` | `3` | 2 |
| `app` | `4` | 2 |
| `recD` | `5` | 3 |
| `eqW` | `6` | 2 |

| `Step` constructor | rule | Lean |
|---|---|---|
| `R_int_delta` | `integrate(delta x) -> void` | `rIntDelta` |
| `R_merge_void_left` | `merge(void, x) -> x` | `rMergeVL` |
| `R_merge_void_right` | `merge(x, void) -> x` | `rMergeVR` |
| `R_merge_cancel` | `merge(x, x) -> x` | `rMergeCancel` |
| `R_rec_zero` | `recD(b, s, void) -> b` | `rRecZero` |
| `R_rec_succ` | `recD(b, s, delta n) -> app(s, recD(b, s, n))` | `rRecSucc` |
| `R_eq_refl` | `eqW(x, x) -> void` | `rEqRefl` |
| `R_eq_diff` | `eqW(x, y) -> integrate(merge(x, y))` | `rEqDiff` |

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

namespace KO7Fence

/-! ## The eight rules -/

/-- `integrate(delta x) -> void`. -/
def rIntDelta : Rule Nat Nat where
  lhs := .app 2 [.app 1 [.var 0]]; rhs := .app 0 []; lhs_isApp := rfl
/-- `merge(void, x) -> x`. -/
def rMergeVL : Rule Nat Nat where
  lhs := .app 3 [.app 0 [], .var 0]; rhs := .var 0; lhs_isApp := rfl
/-- `merge(x, void) -> x`. -/
def rMergeVR : Rule Nat Nat where
  lhs := .app 3 [.var 0, .app 0 []]; rhs := .var 0; lhs_isApp := rfl
/-- `merge(x, x) -> x`. -/
def rMergeCancel : Rule Nat Nat where
  lhs := .app 3 [.var 0, .var 0]; rhs := .var 0; lhs_isApp := rfl
/-- `recD(b, s, void) -> b`. -/
def rRecZero : Rule Nat Nat where
  lhs := .app 5 [.var 0, .var 1, .app 0 []]; rhs := .var 0; lhs_isApp := rfl
/-- `recD(b, s, delta n) -> app(s, recD(b, s, n))`. -/
def rRecSucc : Rule Nat Nat where
  lhs := .app 5 [.var 0, .var 1, .app 1 [.var 2]]
  rhs := .app 4 [.var 1, .app 5 [.var 0, .var 1, .var 2]]
  lhs_isApp := rfl
/-- `eqW(x, x) -> void`, the reflexive branch of the diagonal. -/
def rEqRefl : Rule Nat Nat where
  lhs := .app 6 [.var 0, .var 0]; rhs := .app 0 []; lhs_isApp := rfl
/-- `eqW(x, y) -> integrate(merge(x, y))`, the difference branch. -/
def rEqDiff : Rule Nat Nat where
  lhs := .app 6 [.var 0, .var 1]; rhs := .app 2 [.app 3 [.var 0, .var 1]]
  lhs_isApp := rfl

/-- The encoded KO7 kernel. -/
def ko7TRS : TRS Nat Nat :=
  [rIntDelta, rMergeVL, rMergeVR, rMergeCancel, rRecZero, rRecSucc, rEqRefl, rEqDiff]

theorem mem_ko7TRS {rule : Rule Nat Nat} (h : rule ∈ ko7TRS) :
    rule = rIntDelta ∨ rule = rMergeVL ∨ rule = rMergeVR ∨ rule = rMergeCancel ∨
      rule = rRecZero ∨ rule = rRecSucc ∨ rule = rEqRefl ∨ rule = rEqDiff := by
  simpa [ko7TRS] using h

-- The local simp set unfolds every rule and every named term of this file.
attribute [local simp] rIntDelta rMergeVL rMergeVR rMergeCancel rRecZero rRecSucc
  rEqRefl rEqDiff

/-! ## Clause 1: KO7 is outside the class, already finitely -/

/-- A substitution sending every variable to `t`. -/
def constSub (t : Term Nat Nat) : Subst Nat Nat := fun _ => t

/-- The two `eqW` rules are distinct. -/
theorem rEqRefl_ne_rEqDiff : rEqRefl ≠ rEqDiff := by
  intro h
  have := congrArg Rule.rhs h
  simp at this

/-- The two `eqW` left-hand sides unify: send every variable to `void`. -/
theorem eqW_unifiable : Unifiable rEqRefl.lhs rEqDiff.lhs :=
  ⟨constSub (.app 0 []), constSub (.app 0 []), rfl⟩

/-- Hence they omega-unify. -/
theorem eqW_omegaUnifiable : OmegaUnifiable rEqRefl.lhs rEqDiff.lhs :=
  OmegaUnifiable.of_unifiable eqW_unifiable

/-- **Clause 1.** KO7 is not non-overlapping: the reflexive and difference
branches of `eqW` unify at the root, with two different rules. -/
theorem not_nonOverlapping : ¬ NonOverlapping ko7TRS := by
  intro hno
  obtain ⟨heq, -⟩ :=
    hno rEqRefl (by simp [ko7TRS]) rEqDiff (by simp [ko7TRS]) rEqRefl.lhs
      (Subterm.refl _) rEqRefl.lhs_isApp eqW_unifiable
  exact rEqRefl_ne_rEqDiff heq

/-- **Clause 1, omega form.** KO7 is not non-omega-overlapping. Finite overlap
already puts it outside, so the hypothesis of RTA open problem #79 fails on KO7
for the simplest possible reason. -/
theorem not_nonOmegaOverlapping : ¬ NonOmegaOverlapping ko7TRS :=
  fun h => not_nonOverlapping (NonOverlapping.of_nonOmegaOverlapping h)

/-! ## Named terms -/

/-- `void`. -/
def tVoid : Term Nat Nat := .app 0 []
/-- `integrate(void)`. -/
def tIntVoid : Term Nat Nat := .app 2 [.app 0 []]
/-- `merge(void, void)`. -/
def tMergeVV : Term Nat Nat := .app 3 [.app 0 [], .app 0 []]
/-- `integrate(merge(void, void))`. -/
def tIntMergeVV : Term Nat Nat := .app 2 [.app 3 [.app 0 [], .app 0 []]]
/-- `eqW(void, void)`, the diagonal. -/
def tEqVV : Term Nat Nat := .app 6 [.app 0 [], .app 0 []]

attribute [local simp] tVoid tIntVoid tMergeVV tIntMergeVV tEqVV

/-! ## Normal forms -/

/-- `void` is a normal form: its symbol heads no left-hand side and it has no
argument positions. -/
theorem tVoid_normalForm : NormalForm ko7TRS tVoid := by
  intro u hstep
  rcases Step.app_inv hstep with hroot | ⟨pre, post, a, b, hargs, -, -⟩
  · obtain ⟨rule, hmem, sb, hsrc, -⟩ := hroot
    rcases mem_ko7TRS hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp at hsrc
  · exact absurd hargs.symm (by simp)

/-- `integrate(void)` is a normal form: the only rule rooted at `integrate`
demands a `delta` argument, and its argument `void` is a normal form. -/
theorem tIntVoid_normalForm : NormalForm ko7TRS tIntVoid := by
  intro u hstep
  rcases Step.app_inv hstep with hroot | ⟨pre, post, a, b, hargs, -, hab⟩
  · obtain ⟨rule, hmem, sb, hsrc, -⟩ := hroot
    rcases mem_ko7TRS hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp at hsrc
  · cases pre with
    | cons c cs => simp at hargs
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at hargs
        obtain ⟨ha, -⟩ := hargs
        subst ha
        exact tVoid_normalForm b hab

/-! ## Clause 2: KO7 fails UN= -/

/-- The diagonal contracts to `void` by the reflexive rule. -/
theorem step_diag_void : Step ko7TRS tEqVV tVoid :=
  Step.root ⟨rEqRefl, by simp [ko7TRS], constSub (.app 0 []), rfl, rfl⟩

/-- The same diagonal contracts to `integrate(merge(void, void))` by the
difference rule. This is the eqW diagonal fork. -/
theorem step_diag_int : Step ko7TRS tEqVV tIntMergeVV :=
  Step.root ⟨rEqDiff, by simp [ko7TRS], constSub (.app 0 []), rfl, rfl⟩

/-- `merge(void, void)` contracts to `void`. -/
theorem step_mergeVV_void : Step ko7TRS tMergeVV tVoid :=
  Step.root ⟨rMergeCancel, by simp [ko7TRS], constSub (.app 0 []), rfl, rfl⟩

/-- Hence `integrate(merge(void, void))` reduces to the normal form
`integrate(void)`. -/
theorem step_intMergeVV_intVoid : Step ko7TRS tIntMergeVV tIntVoid :=
  Step.arg 2 [] [] step_mergeVV_void

/-- `void` and `integrate(void)` are convertible, through the diagonal. -/
theorem conv_void_intVoid : conv ko7TRS tVoid tIntVoid :=
  conv.trans (conv.symm (conv.of_step step_diag_void))
    (conv.trans (conv.of_step step_diag_int) (conv.of_step step_intMergeVV_intVoid))

/-- **Clause 2.** KO7 fails UN=: `void` and `integrate(void)` are two distinct
normal forms joined by a conversion through the `eqW` diagonal. -/
theorem not_UNconv : ¬ UNconv ko7TRS := by
  intro hun
  have := hun tVoid tIntVoid tVoid_normalForm tIntVoid_normalForm conv_void_intVoid
  simp at this

/-- KO7 also fails UN->, from the same diagonal. -/
theorem not_UNred : ¬ UNred ko7TRS := by
  intro hun
  have := hun tEqVV tVoid tIntVoid tVoid_normalForm tIntVoid_normalForm
    (StepStar.single step_diag_void)
    (StepStar.trans (StepStar.single step_diag_int)
      (StepStar.single step_intMergeVV_intVoid))
  simp at this

/-! ## Clause 3: the diagonal peak is a non-joinable one-step peak -/

/-- In a two-element argument list of identical entries, any `pre ++ a :: post`
split has `a` equal to that entry. -/
theorem eq_of_pair_split {v a : Term Nat Nat} {pre post : List (Term Nat Nat)}
    (h : [v, v] = pre ++ a :: post) : a = v := by
  cases pre with
  | nil => simpa using (List.cons.injEq _ _ _ _ ▸ h).1.symm
  | cons c cs =>
      cases cs with
      | nil =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
          exact h.2.1.symm
      | cons d ds => simp at h

/-- `merge(void, void)` steps only to `void`. -/
theorem step_mergeVV_eq {w : Term Nat Nat} (h : Step ko7TRS tMergeVV w) : w = tVoid := by
  rcases Step.app_inv h with hroot | ⟨pre, post, a, b, hargs, -, hab⟩
  · obtain ⟨rule, hmem, sb, hsrc, htgt⟩ := hroot
    rcases mem_ko7TRS hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all
  · have ha : a = Term.app (sigma := Nat) (nu := Nat) 0 [] :=
      eq_of_pair_split (by simpa using hargs)
    subst ha
    exact absurd hab (tVoid_normalForm b)

/-- The two terms reachable from `integrate(merge(void, void))`. -/
def afterInt (w : Term Nat Nat) : Prop := w = tIntMergeVV ∨ w = tIntVoid

/-- The reachable set is closed under stepping. -/
theorem afterInt_step {w w' : Term Nat Nat} (hw : afterInt w) (h : Step ko7TRS w w') :
    afterInt w' := by
  rcases hw with rfl | rfl
  · rcases Step.app_inv h with hroot | ⟨pre, post, a, b, hargs, htgt, hab⟩
    · obtain ⟨rule, hmem, sb, hsrc, -⟩ := hroot
      rcases mem_ko7TRS hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp at hsrc
    · cases pre with
      | cons c cs => simp at hargs
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at hargs
          obtain ⟨ha, hp⟩ := hargs
          subst ha
          subst hp
          have hb : b = tVoid := step_mergeVV_eq hab
          right
          rw [htgt, hb]
          simp
  · exact absurd h (tIntVoid_normalForm w')

/-- Every reduct of `integrate(merge(void, void))` stays in the two-element set,
so `void` is never reached. -/
theorem afterInt_stepStar {w : Term Nat Nat} (h : StepStar ko7TRS tIntMergeVV w) :
    afterInt w := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hlast ih => exact afterInt_step ih hlast

/-- **Clause 3.** The `eqW` diagonal peak is a one-step peak whose two results
have no common reduct. `FenceKernelBridge.kernel_diagonal_contains_initial_fork3` separately
proves that the corresponding three-state kernel image contains the initial `Fork3` atom. -/
theorem diagonal_peak_not_joinable :
    Step ko7TRS tEqVV tVoid ∧ Step ko7TRS tEqVV tIntMergeVV ∧
      ¬ joinable ko7TRS tVoid tIntMergeVV := by
  refine ⟨step_diag_void, step_diag_int, ?_⟩
  rintro ⟨w, hvw, hiw⟩
  have hwv : w = tVoid := (tVoid_normalForm.eq_of_stepStar hvw).symm
  subst hwv
  rcases afterInt_stepStar hiw with h | h <;> simp at h

/-! ## Clause 4: necessity of the hypothesis, packaged -/

/-- KO7 satisfies the right-hand-side variable condition, so its UN= failure is
not the `FreshRhs` phenomenon of `CommonGeneralisation.lean`. -/
theorem rhsDetermined : TRS.RhsDetermined ko7TRS := by
  intro rule hmem
  rcases mem_ko7TRS hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact Term.determinedBy_of_vars_subset (by decide)

/-- **Clause 4. The sufficient hypothesis is required, by explicit
counterexample.** KO7 satisfies the variable condition, lies outside
`NonOmegaOverlapping` (already outside `NonOverlapping`), and fails UN= and
UN->, with a named non-joinable one-step peak as the atom of the failure.

Dropping the hypothesis of RTA open problem #79 therefore admits a system that
loses unique normal forms. No converse is claimed. -/
theorem hypothesis_required :
    TRS.RhsDetermined ko7TRS ∧
      ¬ NonOverlapping ko7TRS ∧ ¬ NonOmegaOverlapping ko7TRS ∧
      ¬ UNconv ko7TRS ∧ ¬ UNred ko7TRS ∧
      ¬ joinable ko7TRS tVoid tIntMergeVV :=
  ⟨rhsDetermined, not_nonOverlapping, not_nonOmegaOverlapping, not_UNconv, not_UNred,
    diagonal_peak_not_joinable.2.2⟩

end KO7Fence

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.KO7Fence.ko7TRS

#print axioms OperatorKO7.Meta.UniqueNormalization.KO7Fence.not_nonOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.KO7Fence.not_nonOmegaOverlapping
#print axioms OperatorKO7.Meta.UniqueNormalization.KO7Fence.tVoid_normalForm
#print axioms OperatorKO7.Meta.UniqueNormalization.KO7Fence.tIntVoid_normalForm
#print axioms OperatorKO7.Meta.UniqueNormalization.KO7Fence.conv_void_intVoid
#print axioms OperatorKO7.Meta.UniqueNormalization.KO7Fence.not_UNconv
#print axioms OperatorKO7.Meta.UniqueNormalization.KO7Fence.not_UNred
#print axioms OperatorKO7.Meta.UniqueNormalization.KO7Fence.step_mergeVV_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.KO7Fence.diagonal_peak_not_joinable
#print axioms OperatorKO7.Meta.UniqueNormalization.KO7Fence.rhsDetermined
#print axioms OperatorKO7.Meta.UniqueNormalization.KO7Fence.hypothesis_required
