import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Range
import Mathlib.Data.Set.Function
import Mathlib.Tactic
import OperatorKO7.Meta.HigherOrderRewriting_SystemTSyntax
import OperatorKO7.Meta.OperationalInexpressibility.ObserverTargetCore
import OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive

/-!
# L1 type-cost boundary: simple typing does not license leftmost-outermost beta cost

Relation: `stepLO` (leftmost-outermost one-step strategy) and its fuelled iterator
`normalizeFuel`; typing observer `infer`; cost target `betaCost`.
Closure: one `stepLO` step, then the fuelled iteration count to a normal form.
Strategy: leftmost-outermost, not the full `Step` relation.
Trust: kernel-only; `decide` fixtures on closed terms; no axioms beyond the Lean baseline.
Scope: Gödel System T carrier `SysTTerm` / `SysTTy`; Church family `churchApp n`;
the type observer `infer []` and the cost target `betaCost f` on that family.
-/

set_option autoImplicit false

namespace OperatorKO7.HigherOrderRewritingTypeCostBoundary

open OperatorKO7.HigherOrderRewritingSystemT
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive

/-! ## Soundness of type inference -/

/--
Proves: if `infer Γ t = some A` then `HasType Γ t A`.
Does not prove: completeness of `infer`, uniqueness of types, or subject reduction.
Relation: `HasType` (the inductive typing judgment), not a rewrite relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every System T term and every de Bruijn context.
-/
private def inferApp : Option SysTTy → Option SysTTy → Option SysTTy
  | some (.arrow A B), some A' => if A = A' then some B else none
  | _, _ => none

private theorem infer_app_eq (Γ : List SysTTy) (f a : SysTTerm) :
    infer Γ (.app f a) = inferApp (infer Γ f) (infer Γ a) :=
  rfl

private def inferSucc : Option SysTTy → Option SysTTy
  | some .nat => some .nat
  | _ => none

private theorem infer_succ_eq (Γ : List SysTTy) (t : SysTTerm) :
    infer Γ (.succ t) = inferSucc (infer Γ t) :=
  rfl

private def inferNatrec : Option SysTTy → Option SysTTy → Option SysTTy → Option SysTTy
  | some A, some (.arrow .nat (.arrow A' A'')), some .nat =>
      if A = A' then if A = A'' then some A else none else none
  | _, _, _ => none

private theorem infer_natrec_eq (Γ : List SysTTy) (z s n : SysTTerm) :
    infer Γ (.natrec z s n) = inferNatrec (infer Γ z) (infer Γ s) (infer Γ n) :=
  rfl

theorem infer_sound : ∀ (Γ : List SysTTy) (t : SysTTerm) (A : SysTTy),
    infer Γ t = some A → HasType Γ t A := by
  intro Γ t A h
  induction t generalizing Γ A with
  | var n =>
      exact HasType.var h
  | lam B b ih =>
      have hmap : infer Γ (.lam B b) = (infer (B :: Γ) b).map (SysTTy.arrow B) := rfl
      rw [hmap] at h
      obtain ⟨C, hC, hA⟩ := Option.map_eq_some_iff.mp h
      cases hA
      exact HasType.lam (ih (B :: Γ) C hC)
  | app f a ihf iha =>
      rw [infer_app_eq] at h
      cases hf : infer Γ f with
      | none =>
          rw [hf] at h
          simp only [inferApp] at h
          cases h
      | some Tf =>
        cases ha : infer Γ a with
        | none =>
            rw [hf, ha] at h
            cases Tf <;> (simp only [inferApp] at h; cases h)
        | some Ta =>
          rw [hf, ha] at h
          cases Tf with
          | nat =>
              simp only [inferApp] at h
              cases h
          | arrow Aarg Bret =>
              simp only [inferApp] at h
              by_cases hEq : Aarg = Ta
              · rw [if_pos hEq] at h
                cases h
                exact HasType.app (ihf Γ _ hf) (iha Γ Aarg (hEq.symm ▸ ha))
              · rw [if_neg hEq] at h
                cases h
  | zero =>
      cases h
      exact HasType.zero
  | succ t ih =>
      rw [infer_succ_eq] at h
      cases ht : infer Γ t with
      | none =>
          rw [ht] at h
          simp only [inferSucc] at h
          cases h
      | some T =>
          rw [ht] at h
          cases T with
          | nat =>
              simp only [inferSucc] at h
              cases h
              exact HasType.succ (ih Γ .nat ht)
          | arrow _ _ =>
              simp only [inferSucc] at h
              cases h
  | natrec z s n ihz ihs ihn =>
      rw [infer_natrec_eq] at h
      cases hz : infer Γ z with
      | none =>
          rw [hz] at h
          simp only [inferNatrec] at h
          cases h
      | some Az =>
        cases hs : infer Γ s with
        | none =>
            rw [hz, hs] at h
            simp only [inferNatrec] at h
            cases h
        | some Ts =>
          cases hn : infer Γ n with
          | none =>
              rw [hz, hs, hn] at h
              cases Ts with
              | nat =>
                  simp only [inferNatrec] at h
                  cases h
              | arrow Tdom Tcod =>
                cases Tdom with
                | nat =>
                    cases Tcod with
                    | nat =>
                        simp only [inferNatrec] at h
                        cases h
                    | arrow _ _ =>
                        simp only [inferNatrec] at h
                        cases h
                | arrow _ _ =>
                    simp only [inferNatrec] at h
                    cases h
          | some Tn =>
            rw [hz, hs, hn] at h
            cases Ts with
            | nat =>
                cases Tn <;> (simp only [inferNatrec] at h; cases h)
            | arrow Tdom Tcod =>
              cases Tdom with
              | arrow _ _ =>
                  cases Tn <;> (simp only [inferNatrec] at h; cases h)
              | nat =>
                cases Tcod with
                | nat =>
                    cases Tn <;> (simp only [inferNatrec] at h; cases h)
                | arrow A' A'' =>
                  cases Tn with
                  | arrow _ _ =>
                      simp only [inferNatrec] at h
                      cases h
                  | nat =>
                      simp only [inferNatrec] at h
                      by_cases h1 : Az = A'
                      · rw [if_pos h1] at h
                        by_cases h2 : Az = A''
                        · rw [if_pos h2] at h
                          cases h
                          subst h1
                          subst h2
                          exact HasType.natrec (ihz Γ _ hz) (ihs Γ _ hs)
                            (ihn Γ .nat hn)
                        · rw [if_neg h2] at h
                          cases h
                      · rw [if_neg h1] at h
                        cases h

/-! ## Church family typing -/

/--
Proves: the Church body `fⁿ(x)` has type `nat` in the context `x : nat, f : nat → nat`.
Does not prove: typing of the closed Church numeral, nor of `churchApp`.
Relation: `HasType`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem hasType_churchBody :
    ∀ n, HasType [SysTTy.nat, SysTTy.arrow .nat .nat] (churchBody n) .nat
  | 0 => HasType.var rfl
  | n + 1 =>
      HasType.app (HasType.var rfl) (hasType_churchBody n)

private theorem infer_churchCtx_var1 :
    infer [SysTTy.nat, SysTTy.arrow .nat .nat] (.var 1) = some (.arrow .nat .nat) :=
  rfl

private theorem infer_churchBody :
    ∀ n, infer [SysTTy.nat, SysTTy.arrow .nat .nat] (churchBody n) = some .nat
  | 0 => rfl
  | n + 1 => by
      unfold churchBody
      rw [infer_app_eq, infer_churchCtx_var1, infer_churchBody n]
      rfl

private theorem infer_succFn : infer [] succFn = some (.arrow .nat .nat) := rfl

private theorem infer_church (n : Nat) :
    infer [] (church n) =
      some (.arrow (.arrow .nat .nat) (.arrow .nat .nat)) := by
  change
      ((infer [SysTTy.nat, SysTTy.arrow .nat .nat] (churchBody n)).map
          (SysTTy.arrow .nat)).map
        (SysTTy.arrow (.arrow .nat .nat)) =
      some (.arrow (.arrow .nat .nat) (.arrow .nat .nat))
  rw [infer_churchBody n]
  rfl

/--
Proves: `infer [] (churchApp n) = some nat` for every `n`.
Does not prove: that `infer` is complete on all closed terms, or that the cost is `n + 2`.
Relation: `infer` (the type observer).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the Church family `churchApp n` in the empty context.
-/
theorem infer_churchApp : ∀ n, infer [] (churchApp n) = some .nat := by
  intro n
  have hinner : infer [] ((church n).app succFn) = some (.arrow .nat .nat) := by
    rw [infer_app_eq, infer_church n, infer_succFn]
    rfl
  unfold churchApp
  rw [infer_app_eq, hinner]
  rfl

/--
Proves: every Church application `churchApp n` is typed `nat` in the empty context.
Does not prove: uniqueness of this type, or any cost fact.
Relation: `HasType`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: the Church family `churchApp n`.
-/
theorem hasType_churchApp : ∀ n, HasType [] (churchApp n) .nat := fun n =>
  infer_sound [] (churchApp n) .nat (infer_churchApp n)

/-! ## Cost formula on the Church family -/

/-- `succFn` applied `n` times to `x`. -/
def succChain (n : Nat) (x : SysTTerm) : SysTTerm :=
  match n with
  | 0 => x
  | n + 1 => .app succFn (succChain n x)

example (x : SysTTerm) : succChain 0 x = x := rfl
example (n : Nat) (x : SysTTerm) :
    succChain (n + 1) x = .app succFn (succChain n x) := rfl

example : subst 1 succFn (churchBody 0) = succChain 0 (.var 0) := by decide
example : subst 1 succFn (churchBody 1) = succChain 1 (.var 0) := by decide
example : subst 1 succFn (churchBody 2) = succChain 2 (.var 0) := by decide

private theorem shift_succFn (d c : Nat) : shift d c succFn = succFn := by
  have h : 0 < c + 1 := Nat.succ_pos c
  simp [succFn, shift, h]

private theorem subst_succFn (j : Nat) (u : SysTTerm) : subst j u succFn = succFn := by
  have h : 0 < j + 1 := Nat.succ_pos j
  simp [succFn, subst, h]

/--
Proves: substituting successor for `f` in the Church body yields the successor chain on `x`.
Does not prove: the two opening `stepLO` steps of `churchApp`, nor the normal-form cost.
Relation: `subst` (the carrier's single substitution).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; closed instances `n = 0, 1, 2` checked by `decide` first.
Scope: every `n : Nat`.
-/
private theorem subst_var1 (u : SysTTerm) : subst 1 u (.var 1) = u := rfl

theorem subst_churchBody :
    ∀ n, subst 1 succFn (churchBody n) = succChain n (.var 0)
  | 0 => rfl
  | n + 1 => by
      change (subst 1 succFn (.var 1)).app (subst 1 succFn (churchBody n)) =
        succFn.app (succChain n (.var 0))
      rw [subst_var1, subst_churchBody n]

private theorem subst_succChain (j : Nat) (u x : SysTTerm) :
    ∀ n, subst j u (succChain n x) = succChain n (subst j u x)
  | 0 => rfl
  | n + 1 => by
      change (subst j u succFn).app (subst j u (succChain n x)) =
        succFn.app (succChain n (subst j u x))
      rw [subst_succFn, subst_succChain j u x n]

private theorem stepLO_beta (A : SysTTy) (b u : SysTTerm) :
    stepLO (.app (.lam A b) u) = some (subst 0 u b) := rfl

private theorem stepLO_app_app (g u a : SysTTerm) :
    stepLO (.app (.app g u) a) =
      match stepLO (.app g u) with
      | some f' => some (.app f' a)
      | none =>
        match stepLO a with
        | some a' => some (.app (.app g u) a')
        | none => none :=
  rfl

example : stepLO (churchApp 0) =
    some (.app (.lam .nat (succChain 0 (.var 0))) .zero) := by decide
example : stepLO (churchApp 1) =
    some (.app (.lam .nat (succChain 1 (.var 0))) .zero) := by decide

/--
Proves: the first leftmost-outermost step of `churchApp n` fires the outer Church redex.
Does not prove: the second step, or the remaining `n` successor applications.
Relation: `stepLO` (leftmost-outermost one-step strategy).
Closure: one step.
Strategy: leftmost-outermost.
Trust: kernel-only; closed instances `n = 0, 1` checked by `decide` first.
Scope: every `n : Nat`.
-/
theorem stepLO_churchApp_first :
    ∀ n, stepLO (churchApp n) =
      some (.app (.lam .nat (succChain n (.var 0))) .zero) := by
  intro n
  unfold churchApp church
  rw [stepLO_app_app, stepLO_beta]
  simp [subst, shift_succFn, subst_churchBody]

example : stepLO (.app (.lam .nat (succChain 0 (.var 0))) .zero) =
    some (succChain 0 .zero) := by decide
example : stepLO (.app (.lam .nat (succChain 1 (.var 0))) .zero) =
    some (succChain 1 .zero) := by decide

/--
Proves: the second leftmost-outermost step of `churchApp n` substitutes zero for `x`.
Does not prove: the subsequent `n` successor-chain steps, or the total cost `n + 2`.
Relation: `stepLO`.
Closure: one step.
Strategy: leftmost-outermost.
Trust: kernel-only; closed instances `n = 0, 1` checked by `decide` first.
Scope: every `n : Nat`.
-/
theorem stepLO_churchApp_second :
    ∀ n, stepLO (.app (.lam .nat (succChain n (.var 0))) .zero) =
      some (succChain n .zero) := by
  intro n
  rw [stepLO_beta, subst_succChain]
  rfl

/-- `j` successors wrapped around `t`. -/
def natLitPrefix (j : Nat) (t : SysTTerm) : SysTTerm :=
  match j with
  | 0 => t
  | j + 1 => .succ (natLitPrefix j t)

example (t : SysTTerm) : natLitPrefix 0 t = t := rfl
example (j : Nat) (t : SysTTerm) :
    natLitPrefix (j + 1) t = .succ (natLitPrefix j t) := rfl

private theorem natLitPrefix_zero :
    ∀ j, natLitPrefix j .zero = natLit j
  | 0 => rfl
  | j + 1 => congrArg SysTTerm.succ (natLitPrefix_zero j)

private theorem natLitPrefix_succ (t : SysTTerm) :
    ∀ j, natLitPrefix j (.succ t) = .succ (natLitPrefix j t)
  | 0 => rfl
  | j + 1 => congrArg SysTTerm.succ (natLitPrefix_succ t j)

private theorem natLitPrefix_succ_eq (j : Nat) (t : SysTTerm) :
    natLitPrefix j (.succ t) = natLitPrefix (j + 1) t :=
  natLitPrefix_succ t j

private theorem stepLO_natLit :
    ∀ n, stepLO (natLit n) = none
  | 0 => rfl
  | n + 1 => by
      unfold natLit stepLO
      rw [stepLO_natLit n]
      rfl

private theorem stepLO_natLitPrefix (t : SysTTerm) :
    ∀ j, stepLO (natLitPrefix j t) = (stepLO t).map (natLitPrefix j)
  | 0 => by
      simp [natLitPrefix]
  | j + 1 => by
      have ih := stepLO_natLitPrefix t j
      unfold natLitPrefix
      change (stepLO (natLitPrefix j t)).map SysTTerm.succ =
        (stepLO t).map (fun u => .succ (natLitPrefix j u))
      rw [ih, Option.map_map]
      rfl

private theorem subst_succ_var0 (u : SysTTerm) :
    subst 0 u (.succ (.var 0)) = .succ u := rfl

private theorem stepLO_succChain_succ (m : Nat) :
    stepLO (succChain (m + 1) .zero) = some (.succ (succChain m .zero)) := by
  change stepLO (.app succFn (succChain m .zero)) = some (.succ (succChain m .zero))
  unfold succFn
  rw [stepLO_beta, subst_succ_var0]

private theorem stepLO_natLitPrefix_succChain (j m : Nat) :
    stepLO (natLitPrefix j (succChain (m + 1) .zero)) =
      some (natLitPrefix (j + 1) (succChain m .zero)) := by
  rw [stepLO_natLitPrefix, stepLO_succChain_succ]
  simp [natLitPrefix_succ_eq]

private theorem normalizeFuel_of_normal (fuel : Nat) {t : SysTTerm}
    (h : stepLO t = none) : normalizeFuel fuel t = some (t, 0) := by
  cases fuel with
  | zero =>
      unfold normalizeFuel
      rw [h]
  | succ _ =>
      unfold normalizeFuel
      rw [h]

private theorem normalizeFuel_of_step {fuel : Nat} {t t' nf : SysTTerm} {c : Nat}
    (hstep : stepLO t = some t')
    (hnf : normalizeFuel fuel t' = some (nf, c)) :
    normalizeFuel (fuel + 1) t = some (nf, c + 1) := by
  unfold normalizeFuel
  simp [hstep]
  simp [hnf]

example : normalizeFuel (0 + 3) (natLitPrefix 2 (succChain 0 .zero)) =
    some (natLit 2, 0) := by decide
example : normalizeFuel (2 + 1) (natLitPrefix 1 (succChain 2 .zero)) =
    some (natLit 3, 2) := by decide

/--
Proves: leftmost-outermost normalization of `succ^j (succFn^m zero)` takes exactly `m`
steps and yields `natLit (j + m)`, given leftover fuel `f`.
Does not prove: the two opening Church-application steps, or a cost for an arbitrary term.
Relation: `normalizeFuel` iterating `stepLO`.
Closure: `m` leftmost-outermost steps.
Strategy: leftmost-outermost.
Trust: kernel-only; closed instances `(j,m,f) = (2,0,3)` and `(1,2,1)` checked by `decide` first.
Scope: every wrapping depth `j`, chain length `m`, and leftover fuel `f`.
-/
theorem normalizeFuel_succChain :
    ∀ j m f, normalizeFuel (m + f) (natLitPrefix j (succChain m .zero)) =
      some (natLit (j + m), m) := by
  intro j m f
  induction m generalizing j f with
  | zero =>
      rw [Nat.zero_add, Nat.add_zero]
      change normalizeFuel f (natLitPrefix j .zero) = some (natLit j, 0)
      have hstep : stepLO (natLitPrefix j .zero) = none := by
        rw [natLitPrefix_zero, stepLO_natLit]
      rw [normalizeFuel_of_normal f hstep, natLitPrefix_zero]
  | succ m ih =>
      rw [Nat.succ_add]
      have hgo :=
        normalizeFuel_of_step
          (stepLO_natLitPrefix_succChain j m)
          (ih (j + 1) f)
      refine Eq.trans hgo ?_
      congr 2
      rw [Nat.add_assoc, Nat.add_comm 1 m]

/--
Proves: `normalizeFuel (n + 2) (churchApp n) = some (natLit n, n + 2)`.
Does not prove: uniqueness of this normal form under full `Step`, or a cost for other strategies.
Relation: `normalizeFuel` iterating `stepLO`.
Closure: `n + 2` leftmost-outermost steps.
Strategy: leftmost-outermost.
Trust: kernel-only; carrier fixtures already give the instances `n = 2` (cost 4) and `n = 5` (cost 7).
Scope: every Church numeral `n` at exact fuel `n + 2`.
-/
theorem normalizeFuel_churchApp :
    ∀ n, normalizeFuel (n + 2) (churchApp n) = some (natLit n, n + 2) := by
  intro n
  have hchain : normalizeFuel n (succChain n .zero) = some (natLit n, n) := by
    have h := normalizeFuel_succChain 0 n 0
    simpa [natLitPrefix] using h
  have hmid :=
    normalizeFuel_of_step (stepLO_churchApp_second n) hchain
  have hgo :=
    normalizeFuel_of_step (stepLO_churchApp_first n) hmid
  simpa using hgo

private theorem normalizeFuel_add (fuel : Nat) :
    ∀ (extra : Nat) (t : SysTTerm) (p : SysTTerm × Nat),
      normalizeFuel fuel t = some p →
        normalizeFuel (fuel + extra) t = some p := by
  induction fuel with
  | zero =>
      intro extra t p h
      cases ht : stepLO t with
      | none =>
          have hp : p = (t, 0) := by
            change (match stepLO t with
                | none => some (t, 0)
                | some _ => none) = some p at h
            rw [ht] at h
            cases h
            rfl
          rw [hp, Nat.zero_add]
          exact normalizeFuel_of_normal extra ht
      | some _ =>
          change (match stepLO t with
              | none => some (t, 0)
              | some _ => none) = some p at h
          rw [ht] at h
          cases h
  | succ fuel ih =>
      intro extra t p h
      cases ht : stepLO t with
      | none =>
          have hp : p = (t, 0) := by
            change (match stepLO t with
                | none => some (t, 0)
                | some t' =>
                    (normalizeFuel fuel t').map (fun q => (q.1, q.2 + 1))) = some p at h
            rw [ht] at h
            cases h
            rfl
          rw [hp]
          exact normalizeFuel_of_normal (fuel.succ + extra) ht
      | some t' =>
          have hmap :
              (normalizeFuel fuel t').map (fun q => (q.1, q.2 + 1)) = some p := by
            change (match stepLO t with
                | none => some (t, 0)
                | some t'' =>
                    (normalizeFuel fuel t'').map (fun q => (q.1, q.2 + 1))) = some p at h
            rw [ht] at h
            exact h
          obtain ⟨q, hq, hp⟩ := Option.map_eq_some_iff.mp hmap
          rcases q with ⟨nf, c⟩
          cases hp
          have ih' := ih extra t' (nf, c) hq
          rw [Nat.succ_add]
          exact normalizeFuel_of_step ht ih'

/--
Proves: extra fuel does not change a completed leftmost-outermost normal-form result.
Does not prove: that every term normalizes, or that `none` answers remain `none`.
Relation: `normalizeFuel` iterating `stepLO`.
Closure: fuel monotonicity of a completed run.
Strategy: leftmost-outermost.
Trust: kernel-only.
Scope: every fuel pair `f ≤ g` and every term that already normalizes at `f`.
-/
theorem normalizeFuel_mono : ∀ f g t p,
    normalizeFuel f t = some p → f ≤ g → normalizeFuel g t = some p := by
  intro f g t p h hle
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk]
  exact normalizeFuel_add f k t p h

/--
Proves: if `n + 2 ≤ f` then `betaCost f (churchApp n) = some (n + 2)`.
Does not prove: a cost for other terms, other strategies, or fuel below `n + 2`.
Relation: `betaCost` (the `stepLO`-step count extracted from `normalizeFuel`).
Closure: `n + 2` leftmost-outermost steps.
Strategy: leftmost-outermost.
Trust: kernel-only.
Scope: every Church numeral `n` and every sufficient fuel `f`.
-/
theorem betaCost_churchApp : ∀ n f, n + 2 ≤ f → betaCost f (churchApp n) = some (n + 2) := by
  intro n f hle
  unfold betaCost
  have h := normalizeFuel_churchApp n
  have hmono := normalizeFuel_mono (n + 2) f (churchApp n) (natLit n, n + 2) h hle
  rw [hmono]
  rfl

/-! ## Collision, unlicensed cost, TypedBoundary, unbounded fiber -/

/--
Proves: distinct Church numerals are an observer collision of `infer []` against `betaCost f`.
Does not prove: a collision for an arbitrary pair of typed terms, or for fuel below both costs.
Relation: observer-fiber equality of `infer []` versus inequality of `betaCost f`.
Closure: not applicable.
Strategy: leftmost-outermost cost, at fuel `f`.
Trust: kernel-only.
Scope: every `m ≠ n` with `m + 2 ≤ f` and `n + 2 ≤ f`.
-/
theorem type_observer_collides_on_church :
    ∀ f m n, m ≠ n → m + 2 ≤ f → n + 2 ≤ f →
      OperationallyInexpressibleAt (infer []) (betaCost f) (churchApp m) (churchApp n) := by
  intro f m n hne hm hn
  refine ⟨?obs, ?ver⟩
  · rw [infer_churchApp, infer_churchApp]
  · rw [betaCost_churchApp m f hm, betaCost_churchApp n f hn]
    intro h
    exact hne (Nat.add_right_cancel (Option.some_injective _ h))

example : OperationallyInexpressibleAt (infer []) (betaCost 100) (churchApp 2) (churchApp 5) :=
  type_observer_collides_on_church 100 2 5 (by decide) (by decide) (by decide)

/--
Proves: for every fuel `f ≥ 7`, `betaCost f` does not factor through the type observer `infer []`.
Does not prove: the same obstruction at fuel below 7, or for a different observer/target pair.
Relation: `FactorsThrough` on `infer []` versus `betaCost f`.
Closure: not applicable.
Strategy: leftmost-outermost cost.
Trust: kernel-only.
Scope: every fuel `f` with `7 ≤ f`; witness pair `churchApp 2`, `churchApp 5`.
-/
theorem church_type_unlicensed_cost :
    ∀ f, 7 ≤ f → ¬ FactorsThrough (infer []) (betaCost f) := by
  intro f hf
  exact not_factorsThrough_of_collision
    (type_observer_collides_on_church f 2 5 (by decide)
      (Nat.le_trans (by decide : 2 + 2 ≤ 7) hf) hf)

example : ¬ FactorsThrough (infer []) (betaCost 7) :=
  church_type_unlicensed_cost 7 (Nat.le_refl 7)

/--
Proves: the Church pair `(churchApp 2, churchApp 5)` is a `TypedBoundary` with type observer
`infer []` and cost verdict `betaCost 100`.
Does not prove: a boundary at a different fuel, or for an arbitrary typed pair.
Relation: `TypedBoundary` (universal boundary primitive).
Closure: not applicable.
Strategy: leftmost-outermost cost at fuel 100.
Trust: kernel-only; uses the carrier fixtures at 2 and 5.
Scope: states `churchApp 2` and `churchApp 5`.
-/
def churchTypeCostBoundary : TypedBoundary where
  State := SysTTerm
  Obs := Option SysTTy
  Verdict := Option Nat
  observe := infer []
  verdict := betaCost 100
  s₁ := churchApp 2
  s₂ := churchApp 5
  obs_eq := infer_churchApp_two.trans infer_churchApp_five.symm
  verdict_ne := betaCost_churchApp_two_ne_five

/--
Proves: `betaCost 100` is not a function of the cheap type observation `infer []`.
Does not prove: the same at every fuel, or that no licensed channel recovers the cost.
Relation: `TypedBoundary.verdict_not_observation_function` on `churchTypeCostBoundary`.
Closure: not applicable.
Strategy: leftmost-outermost cost at fuel 100.
Trust: kernel-only.
Scope: all `SysTTerm` states under `infer []` and `betaCost 100`.
-/
theorem church_verdict_not_observation_function :
    ¬ ∃ decode : Option SysTTy → Option Nat,
        ∀ s : SysTTerm, betaCost 100 s = decode (infer [] s) :=
  TypedBoundary.verdict_not_observation_function churchTypeCostBoundary

private theorem churchBody_injective : Function.Injective churchBody := by
  intro m n h
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rfl
      | succ _ => cases h
  | succ m ih =>
      cases n with
      | zero => cases h
      | succ n =>
          injection h with _ hbody
          exact congrArg Nat.succ (ih hbody)

private theorem churchApp_injective : Function.Injective churchApp := by
  intro m n h
  injection h with happ _
  injection happ with hchurch _
  injection hchurch with _ hlam
  injection hlam with _ hbody
  exact churchBody_injective hbody

/--
Proves: the `infer []`-fiber over `some nat` contains finite sets of every cardinality whose
`betaCost (k + 2)` values are pairwise distinct.
Does not prove: that the fiber equals the Church family, or a cost formula at fuel below `k + 2`.
Relation: `infer []` (type observer) and `betaCost (k + 2)` (leftmost-outermost cost).
Closure: not applicable.
Strategy: leftmost-outermost cost at fuel `k + 2`.
Trust: kernel-only.
Scope: every `k : Nat`; witness `Finset.image churchApp (Finset.range k)`.
-/
theorem church_fiber_unbounded :
    ∀ k, ∃ S : Finset SysTTerm,
      S.card = k ∧
      (∀ t ∈ S, infer [] t = some .nat) ∧
      (S : Set SysTTerm).InjOn (betaCost (k + 2)) := by
  intro k
  refine ⟨Finset.image churchApp (Finset.range k), ?card, ?ty, ?inj⟩
  · rw [Finset.card_image_of_injective _ churchApp_injective, Finset.card_range]
  · intro t ht
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
    exact infer_churchApp n
  · intro t ht u hu hcost
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hu
    have hm' : m + 2 ≤ k + 2 :=
      Nat.add_le_add_right (Nat.le_of_lt (Finset.mem_range.mp hm)) 2
    have hn' : n + 2 ≤ k + 2 :=
      Nat.add_le_add_right (Nat.le_of_lt (Finset.mem_range.mp hn)) 2
    have hmcost := betaCost_churchApp m (k + 2) hm'
    have hncost := betaCost_churchApp n (k + 2) hn'
    rw [hmcost, hncost] at hcost
    exact congrArg churchApp
      (Nat.add_right_cancel (Option.some_injective _ hcost))

end OperatorKO7.HigherOrderRewritingTypeCostBoundary
