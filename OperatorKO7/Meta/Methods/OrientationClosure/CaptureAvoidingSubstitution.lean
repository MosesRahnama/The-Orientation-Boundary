import OperatorKO7.Meta.HigherOrderRewriting_Syntax
import Mathlib.Tactic

/-!
# Capture-avoiding substitution for the named higher-order syntax

`HigherOrderRewriting_Syntax.substitute` intentionally performs no alpha
renaming.  This module supplies a separate total operation with an explicit
capture-avoidance derivation.  A conflicting binder is renamed to a name larger
than every name in the replacement and the current body before substitution
continues.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.CaptureAvoidingSubstitution

open OperatorKO7.HigherOrderRewritingSyntax
open OperatorKO7.HigherOrderRewritingSyntax.HOTerm

/-- Free variables of a named higher-order term. -/
def freeVars : HOTerm → Finset Nat
  | .var x => {x}
  | .atom => ∅
  | .succ t => freeVars t
  | .app f a => freeVars f ∪ freeVars a
  | .lam x body => (freeVars body).erase x
  | .recur b s n => freeVars b ∪ freeVars s ∪ freeVars n
  | .share s r => freeVars s ∪ freeVars r

/-- All variable and binder names appearing in a term. -/
def allNames : HOTerm → Finset Nat
  | .var x => {x}
  | .atom => ∅
  | .succ t => allNames t
  | .app f a => allNames f ∪ allNames a
  | .lam x body => insert x (allNames body)
  | .recur b s n => allNames b ∪ allNames s ∪ allNames n
  | .share s r => allNames s ∪ allNames r

/-- Maximum numeric name occurring in a term, with zero as the empty default. -/
def maxName : HOTerm → Nat
  | .var x => x
  | .atom => 0
  | .succ t => maxName t
  | .app f a => max (maxName f) (maxName a)
  | .lam x body => max x (maxName body)
  | .recur b s n => max (maxName b) (max (maxName s) (maxName n))
  | .share s r => max (maxName s) (maxName r)

/-- Free variables are among all names. -/
theorem freeVars_subset_allNames (t : HOTerm) : freeVars t ⊆ allNames t := by
  induction t with
  | var x => simp [freeVars, allNames]
  | atom => simp [freeVars, allNames]
  | succ t ih => simpa [freeVars, allNames] using ih
  | app f a ihf iha =>
      intro x hx
      simp [freeVars, allNames] at hx ⊢
      exact hx.elim (fun h => Or.inl (ihf h)) (fun h => Or.inr (iha h))
  | lam x body ih =>
      intro y hy
      have hmem : y ∈ freeVars body := Finset.mem_of_mem_erase hy
      simp [allNames]
      exact Or.inr (ih hmem)
  | recur b s n ihb ihs ihn =>
      intro x hx
      simp [freeVars, allNames] at hx ⊢
      rcases hx with hb | hs | hn
      · exact Or.inl (ihb hb)
      · exact Or.inr (Or.inl (ihs hs))
      · exact Or.inr (Or.inr (ihn hn))
  | share s r ihs ihr =>
      intro x hx
      simp [freeVars, allNames] at hx ⊢
      exact hx.elim (fun h => Or.inl (ihs h)) (fun h => Or.inr (ihr h))

/-- Every occurring name is bounded by `maxName`. -/
theorem mem_allNames_le_maxName {x : Nat} {t : HOTerm} (h : x ∈ allNames t) :
    x ≤ maxName t := by
  induction t generalizing x with
  | var y =>
      simp [allNames] at h
      subst x
      exact le_rfl
  | atom => simp [allNames] at h
  | succ t ih => exact ih h
  | app f a ihf iha =>
      simp [allNames] at h
      rcases h with h | h
      · exact (ihf h).trans (Nat.le_max_left _ _)
      · exact (iha h).trans (Nat.le_max_right _ _)
  | lam y body ih =>
      simp [allNames] at h
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact (ih h).trans (Nat.le_max_right _ _)
  | recur b s n ihb ihs ihn =>
      simp [allNames] at h
      rcases h with hb | hs | hn
      · exact (ihb hb).trans (Nat.le_max_left _ _)
      · exact (ihs hs).trans
          ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
      · exact (ihn hn).trans
          ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  | share s r ihs ihr =>
      simp [allNames] at h
      rcases h with h | h
      · exact (ihs h).trans (Nat.le_max_left _ _)
      · exact (ihr h).trans (Nat.le_max_right _ _)

/-- Maximum constructor depth. -/
def termDepth : HOTerm → Nat
  | .var _ | .atom => 1
  | .succ t => termDepth t + 1
  | .app f a => max (termDepth f) (termDepth a) + 1
  | .lam _ body => termDepth body + 1
  | .recur b s n => max (termDepth b) (max (termDepth s) (termDepth n)) + 1
  | .share s r => max (termDepth s) (termDepth r) + 1

/-- Rename occurrences bound by an enclosing binder named `old`.  A nested
binder with the same name shadows the outer binder and stops renaming below it. -/
def renameBound (old fresh : Nat) : HOTerm → HOTerm
  | .var x => if x = old then .var fresh else .var x
  | .atom => .atom
  | .succ t => .succ (renameBound old fresh t)
  | .app f a => .app (renameBound old fresh f) (renameBound old fresh a)
  | .lam x body =>
      if x = old then .lam x body else .lam x (renameBound old fresh body)
  | .recur b s n =>
      .recur (renameBound old fresh b) (renameBound old fresh s) (renameBound old fresh n)
  | .share s r => .share (renameBound old fresh s) (renameBound old fresh r)

/-- Bound renaming preserves structural depth. -/
theorem renameBound_depth (old fresh : Nat) (t : HOTerm) :
    termDepth (renameBound old fresh t) = termDepth t := by
  induction t with
  | var x =>
      by_cases h : x = old <;> simp [renameBound, termDepth, h]
  | atom => rfl
  | succ t ih => simp [renameBound, termDepth, ih]
  | app f a ihf iha => simp [renameBound, termDepth, ihf, iha]
  | lam x body ih =>
      by_cases h : x = old
      · simp [renameBound, termDepth, h]
      · simp [renameBound, termDepth, h, ih]
  | recur b s n ihb ihs ihn => simp [renameBound, termDepth, ihb, ihs, ihn]
  | share s r ihs ihr => simp [renameBound, termDepth, ihs, ihr]

/-- Name used when alpha-renaming a conflicting binder. -/
def freshName (name : Nat) (replacement body : HOTerm) : Nat :=
  max name (max (maxName replacement) (maxName body)) + 1

/-- The generated name differs from the substituted variable. -/
theorem freshName_ne_target (name : Nat) (replacement body : HOTerm) :
    freshName name replacement body ≠ name := by
  unfold freshName
  omega

/-- The generated name is absent from the replacement's free variables. -/
theorem freshName_not_free_replacement
    (name : Nat) (replacement body : HOTerm) :
    freshName name replacement body ∉ freeVars replacement := by
  intro hmem
  have hall := freeVars_subset_allNames replacement hmem
  have hle := mem_allNames_le_maxName hall
  unfold freshName at *
  omega

/-- The generated name is absent from every name already occurring in the body. -/
theorem freshName_not_in_body
    (name : Nat) (replacement body : HOTerm) :
    freshName name replacement body ∉ allNames body := by
  intro hmem
  have hle := mem_allNames_le_maxName hmem
  unfold freshName at *
  omega

/-- Every higher-order term has positive structural depth. -/
theorem termDepth_pos (t : HOTerm) : 0 < termDepth t := by
  induction t <;> simp [termDepth, *]

/-- Fuel-recursive capture-avoiding substitution.  Fuel decreases independently
of alpha-renaming, while the public wrapper supplies the exact structural depth. -/
def substituteFuel : Nat → Nat → HOTerm → HOTerm → HOTerm
  | 0, _, _, t => t
  | fuel + 1, name, replacement, t =>
      match t with
      | .var x => if x = name then replacement else .var x
      | .atom => .atom
      | .succ body => .succ (substituteFuel fuel name replacement body)
      | .app f a => .app (substituteFuel fuel name replacement f)
          (substituteFuel fuel name replacement a)
      | .lam x body =>
          if x = name then
            .lam x body
          else if x ∈ freeVars replacement then
            let fresh := freshName name replacement body
            .lam fresh (substituteFuel fuel name replacement (renameBound x fresh body))
          else
            .lam x (substituteFuel fuel name replacement body)
      | .recur b s n =>
          .recur (substituteFuel fuel name replacement b)
            (substituteFuel fuel name replacement s)
            (substituteFuel fuel name replacement n)
      | .share s r =>
          .share (substituteFuel fuel name replacement s)
            (substituteFuel fuel name replacement r)

/-- Total capture-avoiding substitution. -/
def substituteCA (name : Nat) (replacement t : HOTerm) : HOTerm :=
  substituteFuel (termDepth t) name replacement t

/-- Proof relation exposing why each binder traversal is capture-safe. -/
inductive CaptureAvoidingDerivation (name : Nat) (replacement : HOTerm) :
    HOTerm → HOTerm → Prop
  | variableHit : CaptureAvoidingDerivation name replacement (.var name) replacement
  | variableMiss {x : Nat} (h : x ≠ name) :
      CaptureAvoidingDerivation name replacement (.var x) (.var x)
  | atom : CaptureAvoidingDerivation name replacement .atom .atom
  | succ {t u} : CaptureAvoidingDerivation name replacement t u →
      CaptureAvoidingDerivation name replacement (.succ t) (.succ u)
  | app {f f' a a'} :
      CaptureAvoidingDerivation name replacement f f' →
      CaptureAvoidingDerivation name replacement a a' →
      CaptureAvoidingDerivation name replacement (.app f a) (.app f' a')
  | lamShadow (body : HOTerm) :
      CaptureAvoidingDerivation name replacement (.lam name body) (.lam name body)
  | lamSafe {x : Nat} {body body' : HOTerm}
      (hne : x ≠ name) (hfree : x ∉ freeVars replacement)
      (hbody : CaptureAvoidingDerivation name replacement body body') :
      CaptureAvoidingDerivation name replacement (.lam x body) (.lam x body')
  | lamRename {x fresh : Nat} {body body' : HOTerm}
      (hne : x ≠ name) (hconflict : x ∈ freeVars replacement)
      (hfreshTarget : fresh ≠ name)
      (hfreshReplacement : fresh ∉ freeVars replacement)
      (hfreshBody : fresh ∉ allNames body)
      (hbody : CaptureAvoidingDerivation name replacement (renameBound x fresh body) body') :
      CaptureAvoidingDerivation name replacement (.lam x body) (.lam fresh body')
  | recur {b b' s s' n n'} :
      CaptureAvoidingDerivation name replacement b b' →
      CaptureAvoidingDerivation name replacement s s' →
      CaptureAvoidingDerivation name replacement n n' →
      CaptureAvoidingDerivation name replacement (.recur b s n) (.recur b' s' n')
  | share {s s' r r'} :
      CaptureAvoidingDerivation name replacement s s' →
      CaptureAvoidingDerivation name replacement r r' →
      CaptureAvoidingDerivation name replacement (.share s r) (.share s' r')

/-- Sufficient fuel always produces a certified capture-avoiding derivation. -/
theorem substituteFuel_sound (name : Nat) (replacement : HOTerm) :
    ∀ fuel t, termDepth t ≤ fuel →
      CaptureAvoidingDerivation name replacement t
        (substituteFuel fuel name replacement t)
  | 0, t, hdepth => by
      have hp := termDepth_pos t
      omega
  | fuel + 1, .var x, _ => by
      by_cases h : x = name
      · subst x
        simpa [substituteFuel] using
          (CaptureAvoidingDerivation.variableHit
            (name := name) (replacement := replacement))
      · simpa [substituteFuel, h] using
          (CaptureAvoidingDerivation.variableMiss
            (name := name) (replacement := replacement) h)
  | fuel + 1, .atom, _ => by
      simpa [substituteFuel] using
        (CaptureAvoidingDerivation.atom (name := name) (replacement := replacement))
  | fuel + 1, .succ t, hdepth => by
      have ht : termDepth t ≤ fuel := by
        simp [termDepth] at hdepth
        omega
      simpa [substituteFuel] using
        (CaptureAvoidingDerivation.succ (substituteFuel_sound name replacement fuel t ht))
  | fuel + 1, .app f a, hdepth => by
      have hf : termDepth f ≤ fuel := by
        simp [termDepth] at hdepth
        omega
      have ha : termDepth a ≤ fuel := by
        simp [termDepth] at hdepth
        omega
      simpa [substituteFuel] using
        (CaptureAvoidingDerivation.app
          (substituteFuel_sound name replacement fuel f hf)
          (substituteFuel_sound name replacement fuel a ha))
  | fuel + 1, .lam x body, hdepth => by
      by_cases hx : x = name
      · subst x
        simpa [substituteFuel] using
          (CaptureAvoidingDerivation.lamShadow
            (name := name) (replacement := replacement) body)
      · by_cases hfree : x ∈ freeVars replacement
        · let fresh := freshName name replacement body
          have hb : termDepth body ≤ fuel := by
            simp [termDepth] at hdepth
            omega
          have hbr : termDepth (renameBound x fresh body) ≤ fuel := by
            rw [renameBound_depth]
            exact hb
          have hbody := substituteFuel_sound name replacement fuel
            (renameBound x fresh body) hbr
          simpa [substituteFuel, hx, hfree, fresh] using
            (CaptureAvoidingDerivation.lamRename
              (name := name) (replacement := replacement)
              hx hfree
              (freshName_ne_target name replacement body)
              (freshName_not_free_replacement name replacement body)
              (freshName_not_in_body name replacement body)
              hbody)
        · have hb : termDepth body ≤ fuel := by
            simp [termDepth] at hdepth
            omega
          simpa [substituteFuel, hx, hfree] using
            (CaptureAvoidingDerivation.lamSafe
              (name := name) (replacement := replacement) hx hfree
              (substituteFuel_sound name replacement fuel body hb))
  | fuel + 1, .recur b s n, hdepth => by
      have hb : termDepth b ≤ fuel := by simp [termDepth] at hdepth; omega
      have hs : termDepth s ≤ fuel := by simp [termDepth] at hdepth; omega
      have hn : termDepth n ≤ fuel := by simp [termDepth] at hdepth; omega
      simpa [substituteFuel] using
        (CaptureAvoidingDerivation.recur
          (substituteFuel_sound name replacement fuel b hb)
          (substituteFuel_sound name replacement fuel s hs)
          (substituteFuel_sound name replacement fuel n hn))
  | fuel + 1, .share s r, hdepth => by
      have hs : termDepth s ≤ fuel := by simp [termDepth] at hdepth; omega
      have hr : termDepth r ≤ fuel := by simp [termDepth] at hdepth; omega
      simpa [substituteFuel] using
        (CaptureAvoidingDerivation.share
          (substituteFuel_sound name replacement fuel s hs)
          (substituteFuel_sound name replacement fuel r hr))

/-- The public substitution always carries a capture-avoidance derivation. -/
theorem substituteCA_sound (name : Nat) (replacement t : HOTerm) :
    CaptureAvoidingDerivation name replacement t (substituteCA name replacement t) := by
  unfold substituteCA
  exact substituteFuel_sound name replacement (termDepth t) t le_rfl

/-- Existing replacement captures variable one in this open example. -/
theorem legacy_substitution_capture_control :
    substitute 0 (.var 1) (.lam 1 (.var 0)) = .lam 1 (.var 1) := by
  rfl

/-- Capture-avoiding substitution alpha-renames the conflicting binder. -/
theorem capture_avoiding_control :
    substituteCA 0 (.var 1) (.lam 1 (.var 0)) = .lam 2 (.var 1) := by
  decide

/-- The inserted variable remains free after the alpha-renaming control. -/
theorem inserted_variable_remains_free :
    1 ∈ freeVars (substituteCA 0 (.var 1) (.lam 1 (.var 0))) := by
  decide

/-- A binder matching the substituted variable shadows substitution exactly. -/
theorem binder_shadow_control :
    substituteCA 0 (.var 1) (.lam 0 (.var 0)) = .lam 0 (.var 0) := by
  decide

/-- A nonconflicting binder is preserved. -/
theorem nonconflicting_binder_control :
    substituteCA 0 (.var 1) (.lam 2 (.var 0)) = .lam 2 (.var 1) := by
  decide

end OperatorKO7.Methods.OrientationClosure.CaptureAvoidingSubstitution
