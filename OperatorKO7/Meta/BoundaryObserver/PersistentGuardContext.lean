import OperatorKO7.Meta.DistinctionBoundary.ContextualConfluence
import OperatorKO7.Meta.ContextClosed_SN_Full

/-!
# The persistent difference license on the seven-constructor calculus

Manuscript: clause (v) of `prop:persistent-difference` of the Observation-Boundary
Principle.

The guard `a ≠ b` of the difference rule does not survive reduction inside an operand, and the full
context closure of the guarded relation is not confluent (`eqGuardedStepCtx_not_confluent`). This
module guards the difference rule by the license `DiffLicense a b`: every contextual guarded reduct
of `a` differs from every contextual guarded reduct of `b`.

* B1. The license is the interior of disequality along componentwise contextual guarded reduction,
  survives reduction of either operand, fails on every pair with a common reduct and holds at
  `(void, delta void)`.
* B2. The full context closure of the seven unguarded rules with the licensed difference rule lies
  inside the plain guarded contextual relation and inside `StepCtxFull`, and terminates.
* B3. Every one-step peak of that relation is joinable, so Newman's lemma gives confluence.
* B4. The counterexample term `eqW (merge void void) void` reaches `void`, and `void` is its only
  normal form.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.PersistentGuardContext

open OperatorKO7 Trace
open OperatorKO7.EqGuardedConfluence
open MetaSN_KO7
open OperatorKO7.Meta.DistinctionBoundary.ContextualConfluence

/-! ## Newman's lemma for an arbitrary relation -/

/-- **Newman's lemma.** A terminating, locally confluent relation is confluent. -/
theorem newman_lemma {α : Type*} {r : α → α → Prop} (hwf : WellFounded (fun a b => r b a))
    (hloc : ∀ a b c, r a b → r a c →
      ∃ d, Relation.ReflTransGen r b d ∧ Relation.ReflTransGen r c d) :
    ∀ a b c, Relation.ReflTransGen r a b → Relation.ReflTransGen r a c →
      ∃ d, Relation.ReflTransGen r b d ∧ Relation.ReflTransGen r c d := by
  intro a
  refine hwf.induction (C := fun a => ∀ b c, Relation.ReflTransGen r a b →
    Relation.ReflTransGen r a c → ∃ d, Relation.ReflTransGen r b d ∧ Relation.ReflTransGen r c d)
    a ?_
  intro a ih b c hab hac
  rcases hab.cases_head with rfl | ⟨b1, hab1, hb1b⟩
  · exact ⟨c, hac, Relation.ReflTransGen.refl⟩
  rcases hac.cases_head with rfl | ⟨c1, hac1, hc1c⟩
  · exact ⟨b, Relation.ReflTransGen.refl, Relation.ReflTransGen.head hab1 hb1b⟩
  obtain ⟨e, hb1e, hc1e⟩ := hloc a b1 c1 hab1 hac1
  obtain ⟨f, hbf, hef⟩ := ih b1 hab1 b e hb1b hb1e
  obtain ⟨g, hfg, hcg⟩ := ih c1 hac1 f c (hc1e.trans hef) hc1c
  exact ⟨g, hbf.trans hfg, hcg⟩

/-! ## B1: the license -/

/-- The persistent difference license: every contextual guarded reduct of `a` differs from every
contextual guarded reduct of `b`. -/
def DiffLicense (a b : Trace) : Prop :=
  ∀ a' b', EqGuardedCtxStar a a' → EqGuardedCtxStar b b' → a' ≠ b'

/-- One operand takes a contextual guarded step and the other stays. -/
inductive OperandStep : Trace × Trace → Trace × Trace → Prop
  | left {a a' b : Trace} : EqGuardedStepCtx a a' → OperandStep (a, b) (a', b)
  | right {a b b' : Trace} : EqGuardedStepCtx b b' → OperandStep (a, b) (a, b')

/-- The interior of disequality along `OperandStep`: disequality at every pair reached. -/
def DiffInterior (p : Trace × Trace) : Prop :=
  ∀ q, Relation.ReflTransGen OperandStep p q → q.1 ≠ q.2

theorem operandStar_of {a b a' b' : Trace} (ha : EqGuardedCtxStar a a')
    (hb : EqGuardedCtxStar b b') : Relation.ReflTransGen OperandStep (a, b) (a', b') :=
  (Relation.ReflTransGen.lift (fun x => (x, b)) (fun _ _ h => OperandStep.left h) ha).trans
    (Relation.ReflTransGen.lift (fun y => (a', y)) (fun _ _ h => OperandStep.right h) hb)

theorem components_of_operandStar {p q : Trace × Trace}
    (h : Relation.ReflTransGen OperandStep p q) :
    EqGuardedCtxStar p.1 q.1 ∧ EqGuardedCtxStar p.2 q.2 := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | tail _ hs ih =>
    cases hs with
    | left h => exact ⟨ih.1.tail h, ih.2⟩
    | right h => exact ⟨ih.1, ih.2.tail h⟩

/-- Componentwise reduction of a pair is reduction of each operand. -/
theorem operandStar_iff {a b a' b' : Trace} :
    Relation.ReflTransGen OperandStep (a, b) (a', b') ↔
      EqGuardedCtxStar a a' ∧ EqGuardedCtxStar b b' :=
  ⟨components_of_operandStar, fun h => operandStar_of h.1 h.2⟩

/-- **B1, the interior.** The license is the interior of disequality along componentwise
contextual guarded reduction. -/
theorem diffLicense_iff_interior {a b : Trace} : DiffLicense a b ↔ DiffInterior (a, b) := by
  constructor
  · intro h q hq
    exact h q.1 q.2 (components_of_operandStar hq).1 (components_of_operandStar hq).2
  · intro h a' b' ha hb
    exact h (a', b') (operandStar_of ha hb)

/-- The interior is forward invariant under componentwise reduction. -/
theorem diffInterior_forward {p q : Trace × Trace} (hp : DiffInterior p)
    (hq : Relation.ReflTransGen OperandStep p q) : DiffInterior q :=
  fun r hr => hp r (hq.trans hr)

/-- The interior contains every forward-invariant predicate inside disequality. -/
theorem le_diffInterior {Q : Trace × Trace → Prop} (hQ : ∀ p, Q p → p.1 ≠ p.2)
    (hinv : ∀ p q, Q p → OperandStep p q → Q q) {p : Trace × Trace} (hp : Q p) :
    DiffInterior p := by
  intro q hq
  apply hQ
  induction hq with
  | refl => exact hp
  | tail _ hs ih => exact hinv _ _ ih hs

theorem diffLicense_ne {a b : Trace} (h : DiffLicense a b) : a ≠ b :=
  h a b Relation.ReflTransGen.refl Relation.ReflTransGen.refl

/-- **B1, advance.** The license survives contextual guarded reduction of the first operand. -/
theorem diffLicense_of_starL {a a' b : Trace} (h : DiffLicense a b)
    (ha : EqGuardedCtxStar a a') : DiffLicense a' b :=
  fun a'' b' h1 h2 => h a'' b' (ha.trans h1) h2

/-- **B1, advance.** The license survives contextual guarded reduction of the second operand. -/
theorem diffLicense_of_starR {a b b' : Trace} (h : DiffLicense a b)
    (hb : EqGuardedCtxStar b b') : DiffLicense a b' :=
  fun a' b'' h1 h2 => h a' b'' h1 (hb.trans h2)

/-- **B1, coalescence.** A pair with a common contextual guarded reduct has no license. -/
theorem not_diffLicense_of_join {a b c : Trace} (ha : EqGuardedCtxStar a c)
    (hb : EqGuardedCtxStar b c) : ¬ DiffLicense a b :=
  fun h => h c c ha hb rfl

theorem no_step_from_delta_void (u : Trace) : ¬ EqGuardedStepCtx (delta void) u := by
  intro h
  cases h with
  | root hr => cases hr
  | delta hinner => exact no_step_from_void _ hinner

/-- **B1, the example.** The license holds at `(void, delta void)`. -/
theorem diffLicense_void_delta_void : DiffLicense void (delta void) := by
  intro a' b' ha hb
  rw [star_eq_of_no_step no_step_from_void ha, star_eq_of_no_step no_step_from_delta_void hb]
  intro h
  cases h

/-! ## B2: the repaired relation -/

/-- The root relation with the seven unguarded rules and the difference rule guarded by the
license. -/
inductive PStep : Trace → Trace → Prop
  | R_int_delta (t : Trace) : PStep (integrate (delta t)) void
  | R_merge_void_left (t : Trace) : PStep (merge void t) t
  | R_merge_void_right (t : Trace) : PStep (merge t void) t
  | R_merge_cancel (t : Trace) : PStep (merge t t) t
  | R_rec_zero (b s : Trace) : PStep (recΔ b s void) b
  | R_rec_succ (b s n : Trace) : PStep (recΔ b s (delta n)) (app s (recΔ b s n))
  | R_eq_refl (a : Trace) : PStep (eqW a a) void
  | R_eq_diff (a b : Trace) (h : DiffLicense a b) : PStep (eqW a b) (integrate (merge a b))

/-- The full context closure of `PStep`. -/
inductive PStepCtx : Trace → Trace → Prop
  | root {a b : Trace} : PStep a b → PStepCtx a b
  | delta {t u : Trace} : PStepCtx t u → PStepCtx (delta t) (delta u)
  | integrate {t u : Trace} : PStepCtx t u → PStepCtx (integrate t) (integrate u)
  | mergeL {a a' b : Trace} : PStepCtx a a' → PStepCtx (merge a b) (merge a' b)
  | mergeR {a b b' : Trace} : PStepCtx b b' → PStepCtx (merge a b) (merge a b')
  | appL {a a' b : Trace} : PStepCtx a a' → PStepCtx (app a b) (app a' b)
  | appR {a b b' : Trace} : PStepCtx b b' → PStepCtx (app a b) (app a b')
  | recB {b b' s n : Trace} : PStepCtx b b' → PStepCtx (recΔ b s n) (recΔ b' s n)
  | recS {b s s' n : Trace} : PStepCtx s s' → PStepCtx (recΔ b s n) (recΔ b s' n)
  | recN {b s n n' : Trace} : PStepCtx n n' → PStepCtx (recΔ b s n) (recΔ b s n')
  | eqWL {a a' b : Trace} : PStepCtx a a' → PStepCtx (eqW a b) (eqW a' b)
  | eqWR {a b b' : Trace} : PStepCtx b b' → PStepCtx (eqW a b) (eqW a b')

/-- Reflexive-transitive closure of `PStepCtx`. -/
abbrev PStar : Trace → Trace → Prop := Relation.ReflTransGen PStepCtx

theorem pstep_sub_eqGuarded {a b : Trace} (h : PStep a b) : EqGuardedStep a b := by
  cases h with
  | R_int_delta => exact EqGuardedStep.R_int_delta _
  | R_merge_void_left => exact EqGuardedStep.R_merge_void_left _
  | R_merge_void_right => exact EqGuardedStep.R_merge_void_right _
  | R_merge_cancel => exact EqGuardedStep.R_merge_cancel _
  | R_rec_zero => exact EqGuardedStep.R_rec_zero _ _
  | R_rec_succ => exact EqGuardedStep.R_rec_succ _ _ _
  | R_eq_refl => exact EqGuardedStep.R_eq_refl _
  | R_eq_diff _ _ h => exact EqGuardedStep.R_eq_diff _ _ (diffLicense_ne h)

/-- **B2, inclusion.** The repaired relation lies inside the plain guarded contextual relation. -/
theorem pstepCtx_sub_eqGuardedCtx {a b : Trace} (h : PStepCtx a b) : EqGuardedStepCtx a b := by
  induction h with
  | root hr => exact EqGuardedStepCtx.root (pstep_sub_eqGuarded hr)
  | delta _ ih => exact EqGuardedStepCtx.delta ih
  | integrate _ ih => exact EqGuardedStepCtx.integrate ih
  | mergeL _ ih => exact EqGuardedStepCtx.mergeL ih
  | mergeR _ ih => exact EqGuardedStepCtx.mergeR ih
  | appL _ ih => exact EqGuardedStepCtx.appL ih
  | appR _ ih => exact EqGuardedStepCtx.appR ih
  | recB _ ih => exact EqGuardedStepCtx.recB ih
  | recS _ ih => exact EqGuardedStepCtx.recS ih
  | recN _ ih => exact EqGuardedStepCtx.recN ih
  | eqWL _ ih => exact EqGuardedStepCtx.eqWL ih
  | eqWR _ ih => exact EqGuardedStepCtx.eqWR ih

theorem pstar_sub_eqGuardedStar {a b : Trace} (h : PStar a b) : EqGuardedCtxStar a b :=
  Relation.ReflTransGen.mono (fun _ _ h => pstepCtx_sub_eqGuardedCtx h) h

/-- **B2, inclusion in the kernel.** -/
theorem pstepCtx_sub_stepCtxFull {a b : Trace} (h : PStepCtx a b) : StepCtxFull a b :=
  eqGuardedCtx_sub_stepCtxFull (pstepCtx_sub_eqGuardedCtx h)

/-- **B2, termination.** The repaired contextual relation has no infinite reduction. -/
theorem pstepCtx_wf : WellFounded (fun a b : Trace => PStepCtx b a) := by
  refine Subrelation.wf ?_ (InvImage.wf OperatorKO7.PolyInterpretation.W wellFounded_lt)
  intro a b h
  exact W_orients_stepCtxFull (pstepCtx_sub_stepCtxFull h)

/-- The license survives every repaired reduction of the operands. -/
theorem diffLicense_of_pstarL {a a' b : Trace} (h : DiffLicense a b) (ha : PStar a a') :
    DiffLicense a' b :=
  diffLicense_of_starL h (pstar_sub_eqGuardedStar ha)

theorem diffLicense_of_pstarR {a b b' : Trace} (h : DiffLicense a b) (hb : PStar b b') :
    DiffLicense a b' :=
  diffLicense_of_starR h (pstar_sub_eqGuardedStar hb)

/-! ## B3: local confluence and confluence -/

theorem pstar_single {a b : Trace} (h : PStepCtx a b) : PStar a b :=
  Relation.ReflTransGen.single h

theorem pstar_root {a b : Trace} (h : PStep a b) : PStar a b :=
  Relation.ReflTransGen.single (PStepCtx.root h)

theorem pstar_delta {t u : Trace} (h : PStar t u) : PStar (Trace.delta t) (Trace.delta u) :=
  Relation.ReflTransGen.lift Trace.delta (fun _ _ h => PStepCtx.delta h) h

theorem pstar_integrate {t u : Trace} (h : PStar t u) :
    PStar (Trace.integrate t) (Trace.integrate u) :=
  Relation.ReflTransGen.lift Trace.integrate (fun _ _ h => PStepCtx.integrate h) h

theorem pstar_mergeL {a a' b : Trace} (h : PStar a a') :
    PStar (Trace.merge a b) (Trace.merge a' b) :=
  Relation.ReflTransGen.lift (fun x => Trace.merge x b) (fun _ _ h => PStepCtx.mergeL h) h

theorem pstar_mergeR {a b b' : Trace} (h : PStar b b') :
    PStar (Trace.merge a b) (Trace.merge a b') :=
  Relation.ReflTransGen.lift (fun x => Trace.merge a x) (fun _ _ h => PStepCtx.mergeR h) h

theorem pstar_appL {a a' b : Trace} (h : PStar a a') : PStar (Trace.app a b) (Trace.app a' b) :=
  Relation.ReflTransGen.lift (fun x => Trace.app x b) (fun _ _ h => PStepCtx.appL h) h

theorem pstar_appR {a b b' : Trace} (h : PStar b b') : PStar (Trace.app a b) (Trace.app a b') :=
  Relation.ReflTransGen.lift (fun x => Trace.app a x) (fun _ _ h => PStepCtx.appR h) h

theorem pstar_recB {b b' s n : Trace} (h : PStar b b') :
    PStar (Trace.recΔ b s n) (Trace.recΔ b' s n) :=
  Relation.ReflTransGen.lift (fun x => Trace.recΔ x s n) (fun _ _ h => PStepCtx.recB h) h

theorem pstar_recS {b s s' n : Trace} (h : PStar s s') :
    PStar (Trace.recΔ b s n) (Trace.recΔ b s' n) :=
  Relation.ReflTransGen.lift (fun x => Trace.recΔ b x n) (fun _ _ h => PStepCtx.recS h) h

theorem pstar_recN {b s n n' : Trace} (h : PStar n n') :
    PStar (Trace.recΔ b s n) (Trace.recΔ b s n') :=
  Relation.ReflTransGen.lift (fun x => Trace.recΔ b s x) (fun _ _ h => PStepCtx.recN h) h

theorem pstar_eqWL {a a' b : Trace} (h : PStar a a') : PStar (Trace.eqW a b) (Trace.eqW a' b) :=
  Relation.ReflTransGen.lift (fun x => Trace.eqW x b) (fun _ _ h => PStepCtx.eqWL h) h

theorem pstar_eqWR {a b b' : Trace} (h : PStar b b') : PStar (Trace.eqW a b) (Trace.eqW a b') :=
  Relation.ReflTransGen.lift (fun x => Trace.eqW a x) (fun _ _ h => PStepCtx.eqWR h) h

theorem no_pstep_void (u : Trace) : ¬ PStepCtx void u := by
  intro h
  cases h with
  | root hr => cases hr

theorem join_symm {b c : Trace} (h : ∃ d, PStar b d ∧ PStar c d) : ∃ d, PStar c d ∧ PStar b d :=
  let ⟨d, h1, h2⟩ := h
  ⟨d, h2, h1⟩

/-- Two root steps from one source join. -/
theorem root_root_join {a b c : Trace} (h1 : PStep a b) (h2 : PStep a c) :
    ∃ d, PStar b d ∧ PStar c d := by
  cases h1 <;> cases h2 <;> first
    | exact ⟨_, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    | exact (diffLicense_ne (by assumption) rfl).elim

theorem root_integrate {t u t' : Trace} (hs : PStep (integrate t) u) (h : PStepCtx t t') :
    ∃ d, PStar u d ∧ PStar (integrate t') d := by
  cases hs with
  | R_int_delta =>
    cases h with
    | root hr => cases hr
    | delta _ => exact ⟨void, Relation.ReflTransGen.refl, pstar_root (PStep.R_int_delta _)⟩

theorem root_mergeL {x y u x' : Trace} (hs : PStep (merge x y) u) (h : PStepCtx x x') :
    ∃ d, PStar u d ∧ PStar (merge x' y) d := by
  cases hs with
  | R_merge_void_left => exact absurd h (no_pstep_void _)
  | R_merge_void_right => exact ⟨_, pstar_single h, pstar_root (PStep.R_merge_void_right _)⟩
  | R_merge_cancel =>
    exact ⟨_, pstar_single h,
      (pstar_single (PStepCtx.mergeR h)).trans (pstar_root (PStep.R_merge_cancel _))⟩

theorem root_mergeR {x y u y' : Trace} (hs : PStep (merge x y) u) (h : PStepCtx y y') :
    ∃ d, PStar u d ∧ PStar (merge x y') d := by
  cases hs with
  | R_merge_void_left => exact ⟨_, pstar_single h, pstar_root (PStep.R_merge_void_left _)⟩
  | R_merge_void_right => exact absurd h (no_pstep_void _)
  | R_merge_cancel =>
    exact ⟨_, pstar_single h,
      (pstar_single (PStepCtx.mergeL h)).trans (pstar_root (PStep.R_merge_cancel _))⟩

theorem root_recB {b s n u b' : Trace} (hs : PStep (recΔ b s n) u) (h : PStepCtx b b') :
    ∃ d, PStar u d ∧ PStar (recΔ b' s n) d := by
  cases hs with
  | R_rec_zero => exact ⟨_, pstar_single h, pstar_root (PStep.R_rec_zero _ _)⟩
  | R_rec_succ =>
    exact ⟨_, pstar_single (PStepCtx.appR (PStepCtx.recB h)), pstar_root (PStep.R_rec_succ _ _ _)⟩

theorem root_recS {b s n u s' : Trace} (hs : PStep (recΔ b s n) u) (h : PStepCtx s s') :
    ∃ d, PStar u d ∧ PStar (recΔ b s' n) d := by
  cases hs with
  | R_rec_zero => exact ⟨_, Relation.ReflTransGen.refl, pstar_root (PStep.R_rec_zero _ _)⟩
  | R_rec_succ =>
    exact ⟨_, (pstar_single (PStepCtx.appL h)).trans (pstar_single (PStepCtx.appR (PStepCtx.recS h))),
      pstar_root (PStep.R_rec_succ _ _ _)⟩

theorem root_recN {b s n u n' : Trace} (hs : PStep (recΔ b s n) u) (h : PStepCtx n n') :
    ∃ d, PStar u d ∧ PStar (recΔ b s n') d := by
  cases hs with
  | R_rec_zero => exact absurd h (no_pstep_void _)
  | R_rec_succ =>
    cases h with
    | root hr => cases hr
    | delta h' =>
      exact ⟨_, pstar_single (PStepCtx.appR (PStepCtx.recN h')), pstar_root (PStep.R_rec_succ _ _ _)⟩

theorem root_eqWL {x y u x' : Trace} (hs : PStep (eqW x y) u) (h : PStepCtx x x') :
    ∃ d, PStar u d ∧ PStar (eqW x' y) d := by
  cases hs with
  | R_eq_refl =>
    exact ⟨void, Relation.ReflTransGen.refl,
      (pstar_single (PStepCtx.eqWR h)).trans (pstar_root (PStep.R_eq_refl _))⟩
  | R_eq_diff _ _ hl =>
    exact ⟨_, pstar_single (PStepCtx.integrate (PStepCtx.mergeL h)),
      pstar_root (PStep.R_eq_diff _ _ (diffLicense_of_pstarL hl (pstar_single h)))⟩

theorem root_eqWR {x y u y' : Trace} (hs : PStep (eqW x y) u) (h : PStepCtx y y') :
    ∃ d, PStar u d ∧ PStar (eqW x y') d := by
  cases hs with
  | R_eq_refl =>
    exact ⟨void, Relation.ReflTransGen.refl,
      (pstar_single (PStepCtx.eqWL h)).trans (pstar_root (PStep.R_eq_refl _))⟩
  | R_eq_diff _ _ hl =>
    exact ⟨_, pstar_single (PStepCtx.integrate (PStepCtx.mergeR h)),
      pstar_root (PStep.R_eq_diff _ _ (diffLicense_of_pstarR hl (pstar_single h)))⟩

/-- Local joinability at a source. -/
def PLocalJoin (a : Trace) : Prop :=
  ∀ b c, PStepCtx a b → PStepCtx a c → ∃ d, PStar b d ∧ PStar c d

/-- **B3, local confluence.** Every one-step peak of the repaired contextual relation joins. -/
theorem pLocalJoin_all (a : Trace) : PLocalJoin a := by
  induction a with
  | void =>
    intro b c hb _
    exact absurd hb (no_pstep_void b)
  | delta t iht =>
    intro b c hb hc
    cases hb with
    | root hs => cases hs
    | delta h1 =>
      cases hc with
      | root hs => cases hs
      | delta h2 =>
        obtain ⟨d, h1d, h2d⟩ := iht _ _ h1 h2
        exact ⟨_, pstar_delta h1d, pstar_delta h2d⟩
  | integrate t iht =>
    intro b c hb hc
    cases hb with
    | root hs1 =>
      cases hc with
      | root hs2 => exact root_root_join hs1 hs2
      | integrate h2 => exact root_integrate hs1 h2
    | integrate h1 =>
      cases hc with
      | root hs2 => exact join_symm (root_integrate hs2 h1)
      | integrate h2 =>
        obtain ⟨d, h1d, h2d⟩ := iht _ _ h1 h2
        exact ⟨_, pstar_integrate h1d, pstar_integrate h2d⟩
  | merge x y ihx ihy =>
    intro b c hb hc
    cases hb with
    | root hs1 =>
      cases hc with
      | root hs2 => exact root_root_join hs1 hs2
      | mergeL h2 => exact root_mergeL hs1 h2
      | mergeR h2 => exact root_mergeR hs1 h2
    | mergeL h1 =>
      cases hc with
      | root hs2 => exact join_symm (root_mergeL hs2 h1)
      | mergeL h2 =>
        obtain ⟨d, h1d, h2d⟩ := ihx _ _ h1 h2
        exact ⟨_, pstar_mergeL h1d, pstar_mergeL h2d⟩
      | mergeR h2 =>
        exact ⟨_, pstar_single (PStepCtx.mergeR h2), pstar_single (PStepCtx.mergeL h1)⟩
    | mergeR h1 =>
      cases hc with
      | root hs2 => exact join_symm (root_mergeR hs2 h1)
      | mergeL h2 =>
        exact ⟨_, pstar_single (PStepCtx.mergeL h2), pstar_single (PStepCtx.mergeR h1)⟩
      | mergeR h2 =>
        obtain ⟨d, h1d, h2d⟩ := ihy _ _ h1 h2
        exact ⟨_, pstar_mergeR h1d, pstar_mergeR h2d⟩
  | app x y ihx ihy =>
    intro b c hb hc
    cases hb with
    | root hs => cases hs
    | appL h1 =>
      cases hc with
      | root hs => cases hs
      | appL h2 =>
        obtain ⟨d, h1d, h2d⟩ := ihx _ _ h1 h2
        exact ⟨_, pstar_appL h1d, pstar_appL h2d⟩
      | appR h2 =>
        exact ⟨_, pstar_single (PStepCtx.appR h2), pstar_single (PStepCtx.appL h1)⟩
    | appR h1 =>
      cases hc with
      | root hs => cases hs
      | appL h2 =>
        exact ⟨_, pstar_single (PStepCtx.appL h2), pstar_single (PStepCtx.appR h1)⟩
      | appR h2 =>
        obtain ⟨d, h1d, h2d⟩ := ihy _ _ h1 h2
        exact ⟨_, pstar_appR h1d, pstar_appR h2d⟩
  | recΔ b s n ihb ihs ihn =>
    intro u v hu hv
    cases hu with
    | root hs1 =>
      cases hv with
      | root hs2 => exact root_root_join hs1 hs2
      | recB h2 => exact root_recB hs1 h2
      | recS h2 => exact root_recS hs1 h2
      | recN h2 => exact root_recN hs1 h2
    | recB h1 =>
      cases hv with
      | root hs2 => exact join_symm (root_recB hs2 h1)
      | recB h2 =>
        obtain ⟨d, h1d, h2d⟩ := ihb _ _ h1 h2
        exact ⟨_, pstar_recB h1d, pstar_recB h2d⟩
      | recS h2 =>
        exact ⟨_, pstar_single (PStepCtx.recS h2), pstar_single (PStepCtx.recB h1)⟩
      | recN h2 =>
        exact ⟨_, pstar_single (PStepCtx.recN h2), pstar_single (PStepCtx.recB h1)⟩
    | recS h1 =>
      cases hv with
      | root hs2 => exact join_symm (root_recS hs2 h1)
      | recB h2 =>
        exact ⟨_, pstar_single (PStepCtx.recB h2), pstar_single (PStepCtx.recS h1)⟩
      | recS h2 =>
        obtain ⟨d, h1d, h2d⟩ := ihs _ _ h1 h2
        exact ⟨_, pstar_recS h1d, pstar_recS h2d⟩
      | recN h2 =>
        exact ⟨_, pstar_single (PStepCtx.recN h2), pstar_single (PStepCtx.recS h1)⟩
    | recN h1 =>
      cases hv with
      | root hs2 => exact join_symm (root_recN hs2 h1)
      | recB h2 =>
        exact ⟨_, pstar_single (PStepCtx.recB h2), pstar_single (PStepCtx.recN h1)⟩
      | recS h2 =>
        exact ⟨_, pstar_single (PStepCtx.recS h2), pstar_single (PStepCtx.recN h1)⟩
      | recN h2 =>
        obtain ⟨d, h1d, h2d⟩ := ihn _ _ h1 h2
        exact ⟨_, pstar_recN h1d, pstar_recN h2d⟩
  | eqW x y ihx ihy =>
    intro b c hb hc
    cases hb with
    | root hs1 =>
      cases hc with
      | root hs2 => exact root_root_join hs1 hs2
      | eqWL h2 => exact root_eqWL hs1 h2
      | eqWR h2 => exact root_eqWR hs1 h2
    | eqWL h1 =>
      cases hc with
      | root hs2 => exact join_symm (root_eqWL hs2 h1)
      | eqWL h2 =>
        obtain ⟨d, h1d, h2d⟩ := ihx _ _ h1 h2
        exact ⟨_, pstar_eqWL h1d, pstar_eqWL h2d⟩
      | eqWR h2 =>
        exact ⟨_, pstar_single (PStepCtx.eqWR h2), pstar_single (PStepCtx.eqWL h1)⟩
    | eqWR h1 =>
      cases hc with
      | root hs2 => exact join_symm (root_eqWR hs2 h1)
      | eqWL h2 =>
        exact ⟨_, pstar_single (PStepCtx.eqWL h2), pstar_single (PStepCtx.eqWR h1)⟩
      | eqWR h2 =>
        obtain ⟨d, h1d, h2d⟩ := ihy _ _ h1 h2
        exact ⟨_, pstar_eqWR h1d, pstar_eqWR h2d⟩

/-- **B3, confluence.** The repaired contextual relation is confluent, by Newman's lemma. -/
theorem pstepCtx_confluent :
    ∀ a b c, PStar a b → PStar a c → ∃ d, PStar b d ∧ PStar c d :=
  newman_lemma pstepCtx_wf (fun a b c hb hc => pLocalJoin_all a b c hb hc)

/-- **B2 and B3 together.** The repaired relation terminates and is confluent, while the plain
guarded contextual relation it lies inside is not confluent. -/
theorem repaired_terminates_and_confluent :
    WellFounded (fun a b : Trace => PStepCtx b a) ∧
      (∀ a b c, PStar a b → PStar a c → ∃ d, PStar b d ∧ PStar c d) ∧
      ¬ ConfluentEqGuardedCtx :=
  ⟨pstepCtx_wf, pstepCtx_confluent, eqGuardedStepCtx_not_confluent⟩

/-! ## B4: the counterexample term -/

/-- The difference rule is not licensed at the counterexample term. -/
theorem witness_not_licensed : ¬ DiffLicense (merge void void) void :=
  not_diffLicense_of_join
    (Relation.ReflTransGen.single (EqGuardedStepCtx.root (EqGuardedStep.R_merge_void_left void)))
    Relation.ReflTransGen.refl

theorem witness_reaches_void : PStar witness void :=
  (pstar_single (PStepCtx.eqWL (PStepCtx.root (PStep.R_merge_void_left void)))).trans
    (pstar_root (PStep.R_eq_refl void))

theorem pstar_eq_of_no_step {x d : Trace} (hx : ∀ u, ¬ PStepCtx x u) (h : PStar x d) :
    d = x := by
  induction h with
  | refl => rfl
  | tail _ hlast ih =>
    rw [ih] at hlast
    exact absurd hlast (hx _)

/-- **B4.** The counterexample term `eqW (merge void void) void` of the plain-guard failure reaches
`void`, and every normal form it reaches is `void`. -/
theorem witness_unique_normal_form :
    PStar witness void ∧ ∀ d, PStar witness d → (∀ u, ¬ PStepCtx d u) → d = void := by
  refine ⟨witness_reaches_void, fun d hd hnf => ?_⟩
  obtain ⟨e, hde, hve⟩ := pstepCtx_confluent witness d void hd witness_reaches_void
  rw [← pstar_eq_of_no_step hnf hde, pstar_eq_of_no_step no_pstep_void hve]

end OperatorKO7.Meta.BoundaryObserver.PersistentGuardContext
