import OperatorKO7.Meta.UniqueNormalization.HubSplitLinearity

/-!
# RTA #79 route R2: generated hub-condition validity

This module proves the remaining per-rule invariants needed by `LinearizesRule`.
The semantic condition trace follows the same state machine as
`encodeHubOccurrences`: when a variable has already acquired a fixed hub,
a later occurrence emits the pair `(hub, fresh)`.

At the top-level split from an empty seen set, both endpoints of every emitted
condition occur in the transformed LHS, the fresh endpoint collapses to the hub,
and the hub is fixed by collapse. Every transformed variable is either fixed or
collapses to such a fixed hub. A left-linear source emits no conditions.

Trust: kernel checked. No external certificate or new axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u

variable {sigma : Type u}

/-- Semantic trace of hub conditions on an occurrence list. -/
def encodeHubConditions (base : Nat) : Nat → List Nat → List Nat → List (Nat × Nat)
  | _, _, [] => []
  | next, seen, x :: xs =>
      if x ∈ seen then
        (x, hubFresh base x next) ::
          encodeHubConditions base (next + 1) seen xs
      else
        encodeHubConditions base (next + 1) (x :: seen) xs

/-- Convert a variable pair to the term pair stored in a conditional rule. -/
def hubConditionTerms (p : Nat × Nat) : Term sigma Nat × Term sigma Nat :=
  (.var p.1, .var p.2)

/-- Condition trace composes over occurrence-list append. -/
theorem encodeHubConditions_append (base next : Nat) (seen xs ys : List Nat) :
    encodeHubConditions base next seen (xs ++ ys) =
      encodeHubConditions base next seen xs ++
        encodeHubConditions base (next + xs.length) (hubSeenAfter seen xs) ys := by
  induction xs generalizing next seen with
  | nil => rfl
  | cons x xs ih =>
      have hcounter : next + 1 + xs.length = next + (xs.length + 1) := by omega
      by_cases hx : x ∈ seen
      · have hseenStep : hubSeenStep seen x = seen := by simp [hubSeenStep, hx]
        simp only [List.cons_append, encodeHubConditions, if_pos hx,
          List.length_cons, hubSeenAfter, hseenStep]
        rw [ih (next + 1) seen, hcounter]
      · have hseenStep : hubSeenStep seen x = x :: seen := by simp [hubSeenStep, hx]
        simp only [List.cons_append, encodeHubConditions, if_neg hx,
          List.length_cons, hubSeenAfter, hseenStep]
        rw [ih (next + 1) (x :: seen), hcounter]

mutual
/-- Exact condition trace of the executable term splitter. -/
theorem hubSplitTermAux_conds_trace (base next : Nat) (seen : List Nat) :
    ∀ t : Term sigma Nat,
      (hubSplitTermAux base next seen t).conds =
        (encodeHubConditions base next seen (Term.varOccurrences t)).map
          (hubConditionTerms (sigma := sigma))
  | .var x => by
      by_cases hx : x ∈ seen <;>
        simp [hubSplitTermAux, encodeHubConditions, hubConditionTerms,
          Term.varOccurrences, hx]
  | .app f args => by
      simp only [hubSplitTermAux, Term.varOccurrences]
      exact hubSplitListAux_conds_trace base next seen args
/-- Exact condition trace across an argument list. -/
theorem hubSplitListAux_conds_trace (base next : Nat) (seen : List Nat) :
    ∀ args : List (Term sigma Nat),
      (hubSplitListAux base next seen args).conds =
        (encodeHubConditions base next seen
          (args.flatMap Term.varOccurrences)).map
            (hubConditionTerms (sigma := sigma))
  | [] => by simp [hubSplitListAux, encodeHubConditions]
  | t :: ts => by
      simp only [hubSplitListAux, List.flatMap_cons]
      rw [hubSplitTermAux_conds_trace, hubSplitListAux_conds_trace,
        encodeHubConditions_append, hubSplitTermAux_next,
        (hubSplitTermAux_trace base next seen t).1, List.map_append]
end

/-- Zero-based generated-condition trace. -/
theorem hubSplitConditions_trace (base : Nat) (t : Term sigma Nat) :
    hubSplitConditions base t =
      (encodeHubConditions base 0 [] (Term.varOccurrences t)).map
        (hubConditionTerms (sigma := sigma)) :=
  hubSplitTermAux_conds_trace base 0 [] t

/-- Membership in `varOccurrences` implies the structural occurrence relation. -/
theorem VarOccurs.of_mem_varOccurrences {x : Nat} {t : Term sigma Nat}
    (h : x ∈ Term.varOccurrences t) : VarOccurs x t := by
  induction t using Term.rec' with
  | hvar y =>
      simp only [Term.varOccurrences, List.mem_singleton] at h
      subst y
      exact VarOccurs.here
  | happ f args ih =>
      simp only [Term.varOccurrences, List.mem_flatMap] at h
      obtain ⟨a, ha, hx⟩ := h
      exact VarOccurs.arg ha (ih a ha hx)

/-- Strong validity invariant for semantic generated conditions. A condition's
hub is either already represented in the incoming seen set or occurs in this
output suffix; its fresh endpoint occurs in the suffix; and both collapse laws
are exact. -/
theorem encodeHubConditions_valid (base next : Nat) :
    ∀ (seen xs : List Nat),
      AllBelowNat base seen → AllBelowNat base xs →
      ∀ p ∈ encodeHubConditions base next seen xs,
        p.1 < base ∧
        (p.1 ∈ seen ∨ p.1 ∈ encodeHubOccurrences base next seen xs) ∧
        p.2 ∈ encodeHubOccurrences base next seen xs ∧
        hubCollapse base p.2 = p.1 ∧ hubCollapse base p.1 = p.1 := by
  intro seen xs hseen hxs
  induction xs generalizing next seen with
  | nil =>
      simp [encodeHubConditions]
  | cons x xs ih =>
      have hxBelow : x < base := hxs x (List.mem_cons_self ..)
      have htailBelow : AllBelowNat base xs :=
        fun z hz => hxs z (List.mem_cons_of_mem _ hz)
      by_cases hx : x ∈ seen
      · have hseenStep : hubSeenStep seen x = seen := by simp [hubSeenStep, hx]
        have hocc : encodeHubOccurrences base next seen (x :: xs)
            = hubFresh base x next :: encodeHubOccurrences base (next + 1) seen xs := by
          simp [encodeHubOccurrences, hx, hseenStep]
        intro p hp
        simp only [encodeHubConditions, if_pos hx, List.mem_cons] at hp
        rcases hp with rfl | hp
        · refine ⟨hseen x hx, Or.inl hx, ?_, hubCollapse_hubFresh _ _ _,
            hubCollapse_of_lt (hseen x hx)⟩
          rw [hocc]
          exact List.mem_cons_self ..
        · have hrec := ih (next + 1) seen hseen htailBelow p hp
          refine ⟨hrec.1, ?_, ?_, hrec.2.2.2.1, hrec.2.2.2.2⟩
          · rcases hrec.2.1 with hs | ho
            · exact Or.inl hs
            · exact Or.inr (by rw [hocc]; exact List.mem_cons_of_mem _ ho)
          · rw [hocc]
            exact List.mem_cons_of_mem _ hrec.2.2.1
      · have hseenStep : hubSeenStep seen x = x :: seen := by simp [hubSeenStep, hx]
        have hnewBelow : AllBelowNat base (x :: seen) := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hxBelow
          · exact hseen z hz
        have hocc : encodeHubOccurrences base next seen (x :: xs)
            = x :: encodeHubOccurrences base (next + 1) (x :: seen) xs := by
          simp [encodeHubOccurrences, hx, hseenStep]
        intro p hp
        simp only [encodeHubConditions, if_neg hx] at hp
        have hrec := ih (next + 1) (x :: seen) hnewBelow htailBelow p hp
        refine ⟨hrec.1, ?_, ?_, hrec.2.2.2.1, hrec.2.2.2.2⟩
        · rcases hrec.2.1 with hs | ho
          · rcases List.mem_cons.mp hs with rfl | hs
            · exact Or.inr (by rw [hocc]; exact List.mem_cons_self ..)
            · exact Or.inl hs
          · exact Or.inr (by rw [hocc]; exact List.mem_cons_of_mem _ ho)
        · rw [hocc]
          exact List.mem_cons_of_mem _ hrec.2.2.1

/-- At top level every generated condition has both endpoints in the transformed
occurrence list and satisfies the exact hub-collapse equations. -/
theorem encodeHubConditions_valid_top (base : Nat) (xs : List Nat)
    (hxs : AllBelowNat base xs) :
    ∀ p ∈ encodeHubConditions base 0 [] xs,
      p.1 ∈ encodeHubOccurrences base 0 [] xs ∧
      p.2 ∈ encodeHubOccurrences base 0 [] xs ∧
      hubCollapse base p.2 = p.1 ∧ hubCollapse base p.1 = p.1 := by
  intro p hp
  have h := encodeHubConditions_valid base 0 [] xs
    (by simp [AllBelowNat]) hxs p hp
  rcases h.2.1 with hs | ho
  · simp at hs
  · exact ⟨ho, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Semantic generated conditions are exactly the valid hub shape required by
`LinearizesRule`. -/
theorem hubSplitConditions_valid (base : Nat) (t : Term sigma Nat)
    (hbelow : AllBelowNat base (Term.varOccurrences t)) :
    ∀ p ∈ hubSplitConditions base t,
      ∃ x y : Nat,
        p.1 = .var x ∧ p.2 = .var y ∧
        VarOccurs x (hubSplitTerm base t) ∧
        VarOccurs y (hubSplitTerm base t) ∧
        hubCollapse base y = x ∧ hubCollapse base x = x := by
  intro p hp
  rw [hubSplitConditions_trace] at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hv := encodeHubConditions_valid_top base (Term.varOccurrences t)
    hbelow q hq
  refine ⟨q.1, q.2, rfl, rfl, ?_, ?_, hv.2.2.1, hv.2.2.2⟩
  · apply VarOccurs.of_mem_varOccurrences
    rw [hubSplitTerm_varOccurrences]
    exact hv.1
  · apply VarOccurs.of_mem_varOccurrences
    rw [hubSplitTerm_varOccurrences]
    exact hv.2.1

/-- **Every encoded output variable is fixed by collapse, or its own hub pair is
one of the generated conditions.** This is the exact shape of the fourth clause
of `LinearizesRule`, and it is strictly stronger than the fixed-or-hub statement
below: it names the condition, not merely the existence of a fixed hub.

Relation: the hub occurrence encoder and its condition trace.
Closure: one traversal of the occurrence list.
Strategy: not applicable.
Trust: kernel checked.
Scope: `Nat` variables; every incoming hub and every source occurrence below
`base`. -/
theorem encodeHubOccurrences_fixed_or_cond (base next : Nat) :
    ∀ (seen xs : List Nat),
      AllBelowNat base seen → AllBelowNat base xs →
      ∀ v ∈ encodeHubOccurrences base next seen xs,
        hubCollapse base v = v ∨
          (hubCollapse base v, v) ∈ encodeHubConditions base next seen xs := by
  intro seen xs hseen hxs
  induction xs generalizing next seen with
  | nil => simp [encodeHubOccurrences]
  | cons x xs ih =>
      have hxBelow : x < base := hxs x (List.mem_cons_self ..)
      have htailBelow : AllBelowNat base xs :=
        fun z hz => hxs z (List.mem_cons_of_mem _ hz)
      by_cases hx : x ∈ seen
      · have hseenStep : hubSeenStep seen x = seen := by simp [hubSeenStep, hx]
        have hocc : encodeHubOccurrences base next seen (x :: xs)
            = hubFresh base x next :: encodeHubOccurrences base (next + 1) seen xs := by
          simp [encodeHubOccurrences, hx, hseenStep]
        have hcond : encodeHubConditions base next seen (x :: xs)
            = (x, hubFresh base x next) ::
                encodeHubConditions base (next + 1) seen xs := by
          simp [encodeHubConditions, hx]
        intro v hv
        rw [hocc] at hv
        rcases List.mem_cons.mp hv with rfl | hv
        · refine Or.inr ?_
          rw [hcond, hubCollapse_hubFresh]
          exact List.mem_cons_self ..
        · rcases ih (next + 1) seen hseen htailBelow v hv with hfix | hc
          · exact Or.inl hfix
          · exact Or.inr (by rw [hcond]; exact List.mem_cons_of_mem _ hc)
      · have hseenStep : hubSeenStep seen x = x :: seen := by simp [hubSeenStep, hx]
        have hnewBelow : AllBelowNat base (x :: seen) := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hxBelow
          · exact hseen z hz
        have hocc : encodeHubOccurrences base next seen (x :: xs)
            = x :: encodeHubOccurrences base (next + 1) (x :: seen) xs := by
          simp [encodeHubOccurrences, hx, hseenStep]
        have hcond : encodeHubConditions base next seen (x :: xs)
            = encodeHubConditions base (next + 1) (x :: seen) xs := by
          simp [encodeHubConditions, hx]
        intro v hv
        rw [hocc] at hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact Or.inl (hubCollapse_of_lt hxBelow)
        · rcases ih (next + 1) (x :: seen) hnewBelow htailBelow v hv with hfix | hc
          · exact Or.inl hfix
          · exact Or.inr (by rw [hcond]; exact hc)

/-- Every encoded output variable is fixed by collapse or collapses to a fixed
hub variable. Corollary of `encodeHubOccurrences_fixed_or_cond`. -/
theorem encodeHubOccurrences_fixedOrHub (base next : Nat) :
    ∀ (seen xs : List Nat),
      AllBelowNat base seen → AllBelowNat base xs →
      ∀ v ∈ encodeHubOccurrences base next seen xs,
        hubCollapse base v = v ∨
          ∃ x, hubCollapse base v = x ∧ hubCollapse base x = x := by
  intro seen xs hseen hxs v hv
  rcases encodeHubOccurrences_fixed_or_cond base next seen xs hseen hxs v hv with
    hfix | hc
  · exact Or.inl hfix
  · refine Or.inr ⟨hubCollapse base v, rfl, ?_⟩
    exact (encodeHubConditions_valid base next seen xs hseen hxs _ hc).2.2.2.2

/-- Zero-based fixed-or-condition invariant. -/
theorem encodeHubOccurrences_fixed_or_cond_top (base : Nat) (xs : List Nat)
    (hxs : AllBelowNat base xs) :
    ∀ v ∈ encodeHubOccurrences base 0 [] xs,
      hubCollapse base v = v ∨
        (hubCollapse base v, v) ∈ encodeHubConditions base 0 [] xs :=
  encodeHubOccurrences_fixed_or_cond base 0 [] xs (by simp [AllBelowNat]) hxs

/-- **Term-level fourth clause of `LinearizesRule`.** Every variable of the split
left-hand side is fixed by the rule collapse, or its hub pair is one of the
generated conditions. -/
theorem hubSplitTerm_fixed_or_cond (base : Nat) (t : Term sigma Nat)
    (hbelow : AllBelowNat base (Term.varOccurrences t))
    {v : Nat} (hv : VarOccurs v (hubSplitTerm base t)) :
    hubCollapse base v = v ∨
      ((Term.var (hubCollapse base v) : Term sigma Nat), (Term.var v : Term sigma Nat))
        ∈ hubSplitConditions base t := by
  have hmem : v ∈ encodeHubOccurrences base 0 [] (Term.varOccurrences t) := by
    rw [← hubSplitTerm_varOccurrences]
    exact hv.mem_varOccurrences
  rcases encodeHubOccurrences_fixed_or_cond_top base (Term.varOccurrences t)
    hbelow v hmem with hfix | hc
  · exact Or.inl hfix
  · refine Or.inr ?_
    rw [hubSplitConditions_trace]
    have hmap := List.mem_map_of_mem (f := hubConditionTerms (sigma := sigma)) hc
    simpa [hubConditionTerms] using hmap

/-- Term-level fixed-or-hub invariant. -/
theorem hubSplitTerm_fixedOrHub (base : Nat) (t : Term sigma Nat)
    (hbelow : AllBelowNat base (Term.varOccurrences t))
    {v : Nat} (hv : VarOccurs v (hubSplitTerm base t)) :
    hubCollapse base v = v ∨
      ∃ x, hubCollapse base v = x ∧ hubCollapse base x = x := by
  apply encodeHubOccurrences_fixedOrHub base 0 [] (Term.varOccurrences t)
    (by simp [AllBelowNat]) hbelow v
  rw [← hubSplitTerm_varOccurrences]
  exact hv.mem_varOccurrences

/-- No source variable from `xs` has already appeared in `seen`. -/
def NoSeen (seen xs : List Nat) : Prop :=
  ∀ x ∈ xs, x ∉ seen

/-- The generated list is empty exactly when every source occurrence is new. -/
theorem encodeHubConditions_eq_nil_iff (base next : Nat) (seen xs : List Nat) :
    encodeHubConditions base next seen xs = [] ↔ xs.Nodup ∧ NoSeen seen xs := by
  induction xs generalizing next seen with
  | nil => simp [encodeHubConditions, NoSeen]
  | cons x xs ih =>
      constructor
      · intro hnil
        have hx : x ∉ seen := by
          intro hmem
          simp [encodeHubConditions, hmem] at hnil
        have htail : encodeHubConditions base (next + 1) (x :: seen) xs = [] := by
          simpa only [encodeHubConditions, if_neg hx] using hnil
        obtain ⟨htailNodup, htailNoSeen⟩ := (ih (next + 1) (x :: seen)).1 htail
        have hxTail : x ∉ xs := by
          intro hmem
          exact htailNoSeen x hmem (List.mem_cons_self ..)
        refine ⟨List.nodup_cons.mpr ⟨hxTail, htailNodup⟩, ?_⟩
        intro y hy hyseen
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hx hyseen
        · exact htailNoSeen y hy (List.mem_cons_of_mem _ hyseen)
      · rintro ⟨hnodup, hnone⟩
        have hx : x ∉ seen := hnone x (List.mem_cons_self ..)
        obtain ⟨hxTail, htailNodup⟩ := List.nodup_cons.mp hnodup
        have htailNoSeen : NoSeen (x :: seen) xs := by
          intro y hy hyseen
          rcases List.mem_cons.mp hyseen with rfl | hyseen
          · exact hxTail hy
          · exact hnone y (List.mem_cons_of_mem _ hy) hyseen
        simp only [encodeHubConditions, if_neg hx]
        exact (ih (next + 1) (x :: seen)).2 ⟨htailNodup, htailNoSeen⟩

/-- Each occurrence adds either one condition or one previously unseen hub. -/
theorem encodeHubConditions_length_balance (base next : Nat) (seen xs : List Nat) :
    (encodeHubConditions base next seen xs).length + (hubSeenAfter seen xs).length =
      xs.length + seen.length := by
  induction xs generalizing next seen with
  | nil => simp [encodeHubConditions, hubSeenAfter]
  | cons x xs ih =>
      by_cases hx : x ∈ seen
      · have hrec := ih (next + 1) seen
        simp only [encodeHubConditions, if_pos hx, List.length_cons,
          hubSeenAfter, hubSeenStep]
        omega
      · have hrec := ih (next + 1) (x :: seen)
        simp only [encodeHubConditions, if_neg hx, List.length_cons,
          hubSeenAfter, hubSeenStep]
        simp only [List.length_cons] at hrec
        omega

/-- A duplicate-free occurrence list emits no conditions when no occurrence is
already present in the incoming seen set. -/
theorem encodeHubConditions_eq_nil_of_nodup (base next : Nat) :
    ∀ (seen xs : List Nat),
      seen.Nodup → xs.Nodup → NoSeen seen xs →
      encodeHubConditions base next seen xs = [] := by
  intro seen xs _ hnodup hnone
  exact (encodeHubConditions_eq_nil_iff base next seen xs).2 ⟨hnodup, hnone⟩

/-- Generated equality conditions vanish exactly on left-linear source terms. -/
theorem hubSplitConditions_eq_nil_iff_leftLinear (base : Nat) (t : Term sigma Nat) :
    hubSplitConditions base t = [] ↔ Term.LeftLinear t := by
  rw [hubSplitConditions_trace, List.map_eq_nil_iff, encodeHubConditions_eq_nil_iff]
  simp [Term.LeftLinear, NoSeen]

/-- The number of generated conditions plus the final hub count is the number
of source variable occurrences. -/
theorem hubSplitConditions_length_balance (base : Nat) (t : Term sigma Nat) :
    (hubSplitConditions base t).length +
        (hubSeenAfter [] (Term.varOccurrences t)).length = (Term.varOccurrences t).length := by
  rw [hubSplitConditions_trace, List.length_map]
  simpa using encodeHubConditions_length_balance base 0 [] (Term.varOccurrences t)

/-- Repeated incoming hubs do not impose an additional precondition. -/
theorem duplicate_seen_without_conditions (base next : Nat) :
    encodeHubConditions base next [0, 0] [1, 2] = [] := by
  apply (encodeHubConditions_eq_nil_iff base next [0, 0] [1, 2]).2
  simp [NoSeen]

/-- A repeated source variable emits its actual hub-to-fresh equality. -/
theorem repeated_variable_one_condition (base next : Nat) :
    encodeHubConditions base next [] [0, 0] = [(0, hubFresh base 0 (next + 1))] := by
  simp [encodeHubConditions]

/-- A left-linear source term emits no hub conditions. -/
theorem hubSplitConditions_eq_nil_of_leftLinear (base : Nat) (t : Term sigma Nat)
    (hlin : Term.LeftLinear t) : hubSplitConditions base t = [] := by
  rw [hubSplitConditions_trace]
  have hsem : encodeHubConditions base 0 [] (Term.varOccurrences t) = [] :=
    encodeHubConditions_eq_nil_of_nodup base 0 [] (Term.varOccurrences t)
      (by simp) hlin (by simp [NoSeen])
  rw [hsem]
  rfl

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.encodeHubConditions
#check @OperatorKO7.Meta.UniqueNormalization.hubConditionTerms
#check @OperatorKO7.Meta.UniqueNormalization.encodeHubConditions_append
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitTermAux_conds_trace
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitListAux_conds_trace
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitConditions_trace
#check @OperatorKO7.Meta.UniqueNormalization.VarOccurs.of_mem_varOccurrences
#check @OperatorKO7.Meta.UniqueNormalization.encodeHubConditions_valid
#check @OperatorKO7.Meta.UniqueNormalization.encodeHubConditions_valid_top
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitConditions_valid
#check @OperatorKO7.Meta.UniqueNormalization.encodeHubOccurrences_fixedOrHub
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitTerm_fixedOrHub
#check @OperatorKO7.Meta.UniqueNormalization.NoSeen
#check @OperatorKO7.Meta.UniqueNormalization.encodeHubConditions_eq_nil_of_nodup
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitConditions_eq_nil_of_leftLinear

#print axioms OperatorKO7.Meta.UniqueNormalization.encodeHubConditions_append
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitTermAux_conds_trace
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitListAux_conds_trace
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitConditions_trace
#print axioms OperatorKO7.Meta.UniqueNormalization.VarOccurs.of_mem_varOccurrences
#print axioms OperatorKO7.Meta.UniqueNormalization.encodeHubConditions_valid
#print axioms OperatorKO7.Meta.UniqueNormalization.encodeHubConditions_valid_top
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitConditions_valid
#print axioms OperatorKO7.Meta.UniqueNormalization.encodeHubOccurrences_fixedOrHub
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitTerm_fixedOrHub
#print axioms OperatorKO7.Meta.UniqueNormalization.encodeHubConditions_eq_nil_of_nodup
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitConditions_eq_nil_of_leftLinear
