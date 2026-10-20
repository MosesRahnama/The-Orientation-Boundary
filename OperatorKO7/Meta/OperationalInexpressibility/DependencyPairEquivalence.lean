import OperatorKO7.Meta.OperationalInexpressibility.FiniteTRSReducts

/-!
# The Arts and Giesl equivalence and the bounded presentation of termination

A finite first-order system whose right-hand sides use only left-hand-side variables terminates
exactly when its minimal dependency-chain relation is well founded, exactly when no infinite
minimal chain exists. A term is strongly normalizing exactly when the lengths of its reductions
are bounded, and the absence of a reduction of a given length is decidable.

Relation: `Step R` and the minimal chain relation `MinChainStep R`.
Property: completeness, the equivalence with the existing soundness, sequence form, bounded runs.
Trust: kernel only; the sequence construction uses choice.
Scope: finite rule lists over signature and variable types with decidable equality.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.DependencyPairEquivalence

open OperatorKO7.Meta.Rewriting
open OperatorKO7.Methods.OrientationClosure.DependencyPairSoundness
open OperatorKO7.Meta.OperationalInexpressibility.FiniteTRSReducts

open scoped Subst

universe u v w

section Chains

variable {sigma : Type u} {nu : Type v}

theorem argSteps_stepStar (R : TRS sigma nu) (f : sigma) {xs ys : List (Term sigma nu)}
    (h : Relation.ReflTransGen (ArgStep R) xs ys) :
    Relation.ReflTransGen (Step R) (.app f xs) (.app f ys) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      obtain ⟨pre, post, a, b, hxs, hys, hab⟩ := hstep
      subst hxs
      subst hys
      exact ih.tail ((step_app_iff R f (pre ++ a :: post) (.app f (pre ++ b :: post))).2
        (Or.inr ⟨pre ++ b :: post, ⟨pre, post, a, b, rfl, rfl, hab⟩, rfl⟩))

/-- A minimal chain step is a reduction followed by passage to a subterm. -/
theorem minChainStep_transGen (R : TRS sigma nu) {c d : sigma × List (Term sigma nu)}
    (h : MinChainStep R c d) :
    Relation.TransGen (StepOrSub R) (Term.app d.1 d.2) (Term.app c.1 c.2) := by
  obtain ⟨-, -, args', hreach, rule, hrule, σ, hl, targs, hsub, -, hd⟩ := h
  have hA : Relation.ReflTransGen (StepOrSub R) (Term.app d.1 d.2)
      (Subst.apply σ rule.rhs) := by
    have hsubst : IsSubterm (Term.app d.1 d.2) (Subst.apply σ rule.rhs) := by
      have h1 := IsSubterm.subst σ hsub
      rwa [Subst.apply_app, ← hd] at h1
    exact IsSubterm.reflTransGen hsubst
  have hB : StepOrSub R (Subst.apply σ rule.rhs) (Subst.apply σ rule.lhs) :=
    Or.inl (Step.root ⟨rule, hrule, σ, rfl, rfl⟩)
  have hC : Relation.ReflTransGen (StepOrSub R) (Subst.apply σ rule.lhs)
      (Term.app c.1 c.2) := by
    rw [← hl]
    exact steps_reflTransGen (argSteps_stepStar R c.1 hreach)
  exact (Relation.TransGen.tail' hA hB).trans_left hC

/-- **Completeness of the dependency-pair method.** -/
theorem minChain_wf_of_terminating (R : TRS sigma nu) (hsn : ∀ t, SN R t) :
    WellFounded (fun d c => MinChainStep R c d) := by
  have hwf : WellFounded (Relation.TransGen (StepOrSub R)) :=
    ⟨fun t => (acc_stepOrSub_of_sn (hsn t)).transGen⟩
  refine Subrelation.wf ?_ (InvImage.wf (fun c : sigma × List (Term sigma nu) =>
    Term.app c.1 c.2) hwf)
  intro d c h
  exact minChainStep_transGen R h

/-- **The Arts and Giesl equivalence.** -/
theorem terminating_iff_minChain_wf [DecidableEq nu] (R : TRS sigma nu)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs) :
    (∀ t, SN R t) ↔ WellFounded (fun d c => MinChainStep R c d) :=
  ⟨minChain_wf_of_terminating R, terminating_of_minChain_wf R hvars⟩

end Chains

section Sequences

variable {α : Type w}

/-- Well-foundedness of the reverse of `r` is the absence of an infinite `r`-sequence. -/
theorem wellFounded_flip_iff_no_infinite_chain (r : α → α → Prop) :
    WellFounded (fun b a => r a b) ↔ ¬ ∃ f : ℕ → α, ∀ n, r (f n) (f (n + 1)) := by
  constructor
  · rintro h ⟨f, hf⟩
    haveI : IsWellFounded α (fun b a => r a b) := ⟨h⟩
    obtain ⟨n, hn⟩ := WellFounded.not_rel_apply_succ (r := fun b a => r a b) (f := f)
    exact hn (hf n)
  · intro h
    by_contra hnwf
    have hex : ∃ a, ¬ Acc (fun b a => r a b) a := by
      by_contra hnone
      exact hnwf ⟨fun a => by
        by_contra ha
        exact hnone ⟨a, ha⟩⟩
    obtain ⟨a, ha⟩ := hex
    have hstep : ∀ a, ¬ Acc (fun b a => r a b) a →
        ∃ b, r a b ∧ ¬ Acc (fun b a => r a b) b := by
      intro a ha
      by_contra hnone
      exact ha (Acc.intro a fun b hba => by
        by_contra hb
        exact hnone ⟨b, hba, hb⟩)
    choose g hg1 hg2 using hstep
    let F : (n : ℕ) → {x : α // ¬ Acc (fun b a => r a b) x} :=
      fun n => Nat.rec ⟨a, ha⟩ (fun _ x => ⟨g x.1 x.2, hg2 x.1 x.2⟩) n
    let f : ℕ → α := fun n => (F n).1
    have hr : ∀ n, r (f n) (f (n + 1)) := by
      intro n
      exact hg1 (F n).1 (F n).2
    exact h ⟨f, hr⟩

end Sequences

theorem terminating_iff_no_infinite_minimalChain {sigma : Type u} {nu : Type v} [DecidableEq nu]
    (R : TRS sigma nu) (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs) :
    (∀ t, SN R t) ↔
      ¬ ∃ f : ℕ → sigma × List (Term sigma nu), ∀ n, MinChainStep R (f n) (f (n + 1)) := by
  rw [terminating_iff_minChain_wf R hvars, wellFounded_flip_iff_no_infinite_chain]

section Bounded

variable {α : Type w}

/-- No run of `r` of length `n` starts at `s`. -/
def NoRunOfLength (r : α → α → Prop) (s : α) (n : ℕ) : Prop :=
  ∀ f : ℕ → α, f 0 = s → ¬ ∀ i, i < n → r (f i) (f (i + 1))

/-- The runs of `r` from `s` have bounded length. -/
def BoundedRunsAt (r : α → α → Prop) (s : α) : Prop := ∃ n, NoRunOfLength r s n

theorem not_noRunOfLength_zero (r : α → α → Prop) (s : α) : ¬ NoRunOfLength r s 0 := by
  intro h
  exact h (fun _ => s) rfl (fun i hi => absurd hi (Nat.not_lt_zero i))

theorem NoRunOfLength.mono {r : α → α → Prop} {s : α} {m m' : ℕ} (h : NoRunOfLength r s m)
    (hm : m ≤ m') : NoRunOfLength r s m' := by
  intro f hf0 hrun
  exact h f hf0 fun i hi => hrun i (lt_of_lt_of_le hi hm)

theorem NoRunOfLength.succ_inv {r : α → α → Prop} {s : α} {n : ℕ} (h : NoRunOfLength r s (n + 1))
    {b : α} (hb : r s b) : NoRunOfLength r b n := by
  intro g hg0 hrun
  apply h (fun i => if i = 0 then s else g (i - 1)) rfl
  intro i hi
  cases i with
  | zero => simpa [hg0] using hb
  | succ j =>
      have hj : j < n := Nat.succ_lt_succ_iff.mp hi
      have h1 : (if (j + 1) = 0 then s else g ((j + 1) - 1)) = g j := by simp
      have h2 : (if (j + 1 + 1) = 0 then s else g ((j + 1 + 1) - 1)) = g (j + 1) := by simp
      rw [h1, h2]
      exact hrun j hj

theorem noRunOfLength_succ_of_forall {r : α → α → Prop} {s : α} {n : ℕ}
    (h : ∀ b, r s b → NoRunOfLength r b n) : NoRunOfLength r s (n + 1) := by
  intro f hf0 hrun
  have h1 : r s (f 1) := by
    have := hrun 0 (Nat.succ_pos n)
    rwa [hf0] at this
  exact h (f 1) h1 (fun i => f (i + 1)) rfl (fun i hi => by
    have := hrun (i + 1) (Nat.succ_lt_succ hi)
    simpa using this)

theorem acc_of_boundedRunsAt (r : α → α → Prop) {s : α} (h : BoundedRunsAt r s) :
    Acc (fun b a => r a b) s := by
  obtain ⟨n, hn⟩ := h
  induction n generalizing s with
  | zero => exact absurd hn (not_noRunOfLength_zero r s)
  | succ n ih =>
      refine Acc.intro s fun b hsb => ih (hn.succ_inv hsb)

theorem boundedRunsAt_of_acc (r : α → α → Prop) (succ : α → Finset α)
    (hsucc : ∀ a b, r a b ↔ b ∈ succ a) {s : α} (h : Acc (fun b a => r a b) s) :
    BoundedRunsAt r s := by
  classical
  induction h with
  | intro s _ ih =>
      have hfib : ∀ b : {b // b ∈ succ s}, ∃ m, NoRunOfLength r b.1 m :=
        fun b => ih b.1 ((hsucc s b.1).2 b.2)
      choose n hn using hfib
      refine ⟨(succ s).attach.sup n + 1, ?_⟩
      apply noRunOfLength_succ_of_forall
      intro b hsb
      have hbmem : b ∈ succ s := (hsucc s b).1 hsb
      exact (hn ⟨b, hbmem⟩).mono
        (Finset.le_sup (f := n) (Finset.mem_attach _ ⟨b, hbmem⟩))

theorem acc_iff_boundedRunsAt (r : α → α → Prop) (succ : α → Finset α)
    (hsucc : ∀ a b, r a b ↔ b ∈ succ a) (s : α) :
    Acc (fun b a => r a b) s ↔ BoundedRunsAt r s :=
  ⟨boundedRunsAt_of_acc r succ hsucc, acc_of_boundedRunsAt r⟩

/-- The matrix `NoRunOfLength` is decidable from a finite successor function. -/
def decidableNoRunOfLength (r : α → α → Prop) (succ : α → Finset α)
    (hsucc : ∀ a b, r a b ↔ b ∈ succ a) : ∀ n s, Decidable (NoRunOfLength r s n)
  | 0, s => isFalse (not_noRunOfLength_zero r s)
  | n + 1, s =>
      haveI : ∀ b, Decidable (NoRunOfLength r b n) := fun b => decidableNoRunOfLength r succ hsucc n b
      decidable_of_iff (∀ b ∈ succ s, NoRunOfLength r b n)
        ⟨fun h => noRunOfLength_succ_of_forall fun b hb => h b ((hsucc s b).1 hb),
          fun h b hb => h.succ_inv ((hsucc s b).2 hb)⟩

end Bounded

section Systems

variable {sigma : Type u} {nu : Type v} [DecidableEq sigma] [DecidableEq nu]

/-- **Bounded presentation of strong normalization.** -/
theorem sn_iff_boundedRunsAt (R : TRS sigma nu)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs) (t : Term sigma nu) :
    SN R t ↔ BoundedRunsAt (Step R) t :=
  acc_iff_boundedRunsAt (Step R) (reducts R) (fun a b => (mem_reducts_iff R hvars a b).symm) t

theorem terminating_iff_boundedRuns (R : TRS sigma nu)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs) :
    (∀ t, SN R t) ↔ ∀ t, ∃ n, NoRunOfLength (Step R) t n := by
  exact forall_congr' fun t => sn_iff_boundedRunsAt R hvars t

/-- The bounded matrix of a finite system is decidable. -/
def decidableNoRunOfLength_step (R : TRS sigma nu)
    (hvars : ∀ rule ∈ R, Term.vars rule.rhs ⊆ Term.vars rule.lhs) (t : Term sigma nu) (n : ℕ) :
    Decidable (NoRunOfLength (Step R) t n) :=
  decidableNoRunOfLength (Step R) (reducts R) (fun a b => (mem_reducts_iff R hvars a b).symm) n t

/-- The free recursor: every reduction has bounded length. -/
theorem freeRecursor_boundedRuns (t : Term FreeSym Nat) : BoundedRunsAt (Step freeRecursorTRS) t :=
  (sn_iff_boundedRunsAt freeRecursorTRS freeRecursorTRS_vars t).1 (freeRecursorTRS_terminating t)

end Systems

end OperatorKO7.Meta.OperationalInexpressibility.DependencyPairEquivalence
