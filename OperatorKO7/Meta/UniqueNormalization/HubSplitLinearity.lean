import OperatorKO7.Meta.UniqueNormalization.HubSplitCore

/-!
# RTA #79 route R2: left-linearity of the representative-hub split

`encodeHubOccurrences` is the variable-list semantics of the stateful term
splitter. An unseen source variable is emitted unchanged and added to `seen`; a
seen source variable is emitted as a fresh code at the current global occurrence
index.

Under the rule fresh-base invariant, encoded outputs are duplicate-free and are
disjoint from every hub already in the initial `seen` set. The exact trace
between the term splitter and this list encoder then yields left-linearity of the
transformed rule LHS.

Trust: kernel checked. No external certificate or new axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u

variable {sigma : Type u}

/-- Update the represented-hub set after one source occurrence. -/
def hubSeenStep (seen : List Nat) (x : Nat) : List Nat :=
  if x ∈ seen then seen else x :: seen

/-- Hub set after processing an occurrence list. -/
def hubSeenAfter : List Nat → List Nat → List Nat
  | seen, [] => seen
  | seen, x :: xs => hubSeenAfter (hubSeenStep seen x) xs

/-- Output variable list of the representative-hub occurrence encoding. -/
def encodeHubOccurrences (base : Nat) : Nat → List Nat → List Nat → List Nat
  | _, _, [] => []
  | next, seen, x :: xs =>
      let out := if x ∈ seen then hubFresh base x next else x
      out :: encodeHubOccurrences base (next + 1) (hubSeenStep seen x) xs

/-- Seen-state composition over append. -/
theorem hubSeenAfter_append (seen xs ys : List Nat) :
    hubSeenAfter seen (xs ++ ys) = hubSeenAfter (hubSeenAfter seen xs) ys := by
  induction xs generalizing seen with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, hubSeenAfter]
      exact ih (hubSeenStep seen x)

/-- Encoding an append composes the stateful traversals and shifts the global
counter by the prefix occurrence count. -/
theorem encodeHubOccurrences_append (base next : Nat) (seen xs ys : List Nat) :
    encodeHubOccurrences base next seen (xs ++ ys) =
      encodeHubOccurrences base next seen xs ++
        encodeHubOccurrences base (next + xs.length) (hubSeenAfter seen xs) ys := by
  induction xs generalizing next seen with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.cons_append, encodeHubOccurrences, List.length_cons]
      rw [ih]
      have hcounter : next + 1 + xs.length = next + (xs.length + 1) := by omega
      rw [hcounter]
      rfl

/-- Every member of a list lies below a bound. -/
def AllBelowNat (base : Nat) (xs : List Nat) : Prop :=
  ∀ x ∈ xs, x < base

/-- A fresh code at an earlier global index cannot appear in a later encoded
suffix. Original hub outputs are below the base; later fresh outputs have a
different occurrence index. -/
theorem hubFresh_not_mem_encodeHubOccurrences_of_lt
    {base x k start : Nat} (hks : k < start) :
    ∀ (seen xs : List Nat), AllBelowNat base xs →
      hubFresh base x k ∉ encodeHubOccurrences base start seen xs
  | _, [], _ => by simp [encodeHubOccurrences]
  | seen, y :: ys, hbelow => by
      simp only [encodeHubOccurrences, List.mem_cons]
      intro hmem
      rcases hmem with hEq | htail
      · by_cases hy : y ∈ seen
        · have hEq' : hubFresh base x k = hubFresh base y start := by
            simpa [hy] using hEq
          have hk : k = start := (hubFresh_injective hEq').2
          exact (Nat.ne_of_lt hks) hk
        · have hEq' : hubFresh base x k = y := by
            simpa [hy] using hEq
          have hyb : y < base := hbelow y (List.mem_cons_self ..)
          exact (hubFresh_ne_of_lt_base hyb) hEq'
      · exact hubFresh_not_mem_encodeHubOccurrences_of_lt
          (Nat.lt_succ_of_lt hks) (hubSeenStep seen y) ys
          (fun z hz => hbelow z (List.mem_cons_of_mem _ hz)) htail

/-- If all seen hubs and all source occurrences lie below the fresh base, the
encoding is duplicate-free and no output collides with an initially seen hub. -/
theorem encodeHubOccurrences_nodup_disjoint (base next : Nat) :
    ∀ (seen xs : List Nat),
      seen.Nodup → AllBelowNat base seen → AllBelowNat base xs →
      (encodeHubOccurrences base next seen xs).Nodup ∧
        ∀ v ∈ encodeHubOccurrences base next seen xs, v ∉ seen
  | seen, [], _, _, _ => by simp [encodeHubOccurrences]
  | seen, x :: xs, hseenNodup, hseenBelow, hxsBelow => by
      have hxBelow : x < base := hxsBelow x (List.mem_cons_self ..)
      have htailBelow : AllBelowNat base xs :=
        fun z hz => hxsBelow z (List.mem_cons_of_mem _ hz)
      by_cases hx : x ∈ seen
      · have hseenStep : hubSeenStep seen x = seen := by simp [hubSeenStep, hx]
        have ih := encodeHubOccurrences_nodup_disjoint base (next + 1)
          seen xs hseenNodup hseenBelow htailBelow
        have hfreshNotTail :
            hubFresh base x next ∉
              encodeHubOccurrences base (next + 1) seen xs :=
          hubFresh_not_mem_encodeHubOccurrences_of_lt
            (Nat.lt_succ_self next) seen xs htailBelow
        have hfreshNotSeen : hubFresh base x next ∉ seen := by
          intro hfresh
          have hb := hseenBelow _ hfresh
          exact (not_hubFresh_lt base x next) hb
        simp only [encodeHubOccurrences, hx, if_pos, hseenStep, List.nodup_cons]
        exact ⟨⟨hfreshNotTail, ih.1⟩, fun v hv => by
          rcases List.mem_cons.mp hv with rfl | hv
          · exact hfreshNotSeen
          · exact ih.2 v hv⟩
      · have hseenStep : hubSeenStep seen x = x :: seen := by simp [hubSeenStep, hx]
        have hnewNodup : (x :: seen).Nodup := by simp [hx, hseenNodup]
        have hnewBelow : AllBelowNat base (x :: seen) := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hxBelow
          · exact hseenBelow z hz
        have ih := encodeHubOccurrences_nodup_disjoint base (next + 1)
          (x :: seen) xs hnewNodup hnewBelow htailBelow
        have hxNotTail : x ∉ encodeHubOccurrences base (next + 1) (x :: seen) xs :=
          fun hmem => ih.2 x hmem (List.mem_cons_self ..)
        simp only [encodeHubOccurrences, hx, hseenStep, List.nodup_cons]
        exact ⟨⟨hxNotTail, ih.1⟩, fun v hv => by
          rcases List.mem_cons.mp hv with rfl | hv
          · exact hx
          · intro hvSeen
            exact ih.2 v hv (List.mem_cons_of_mem _ hvSeen)⟩

mutual
/-- Exact occurrence-list trace of the term splitter, including its seen state. -/
theorem hubSplitTermAux_trace (base next : Nat) (seen : List Nat) :
    ∀ t : Term sigma Nat,
      (hubSplitTermAux base next seen t).seen =
          hubSeenAfter seen (Term.varOccurrences t) ∧
      Term.varOccurrences (hubSplitTermAux base next seen t).term =
          encodeHubOccurrences base next seen (Term.varOccurrences t)
  | .var x => by
      by_cases hx : x ∈ seen <;>
        simp [hubSplitTermAux, hubSeenAfter, hubSeenStep,
          encodeHubOccurrences, Term.varOccurrences, hx]
  | .app f args => by
      simp only [hubSplitTermAux, Term.varOccurrences]
      exact hubSplitListAux_trace base next seen args
/-- List-level exact occurrence trace. -/
theorem hubSplitListAux_trace (base next : Nat) (seen : List Nat) :
    ∀ args : List (Term sigma Nat),
      (hubSplitListAux base next seen args).seen =
          hubSeenAfter seen (args.flatMap Term.varOccurrences) ∧
      (hubSplitListAux base next seen args).terms.flatMap Term.varOccurrences =
          encodeHubOccurrences base next seen (args.flatMap Term.varOccurrences)
  | [] => by simp [hubSplitListAux, hubSeenAfter, encodeHubOccurrences]
  | t :: ts => by
      have ht := hubSplitTermAux_trace base next seen t
      have hs := hubSplitListAux_trace base
        (hubSplitTermAux base next seen t).next
        (hubSplitTermAux base next seen t).seen ts
      constructor
      · simp only [hubSplitListAux, List.flatMap_cons]
        rw [hs.1, ht.1, hubSeenAfter_append]
      · simp only [hubSplitListAux, List.flatMap_cons]
        rw [ht.2, hs.2, encodeHubOccurrences_append,
          ht.1, hubSplitTermAux_next]
end

/-- Zero-based occurrence trace. -/
theorem hubSplitTerm_varOccurrences (base : Nat) (t : Term sigma Nat) :
    Term.varOccurrences (hubSplitTerm base t) =
      encodeHubOccurrences base 0 [] (Term.varOccurrences t) :=
  (hubSplitTermAux_trace base 0 [] t).2

/-- A split term is left-linear whenever every original occurrence lies below
the fresh base. -/
theorem hubSplitTerm_leftLinear_of_below (base : Nat) (t : Term sigma Nat)
    (hbelow : AllBelowNat base (Term.varOccurrences t)) :
    Term.LeftLinear (hubSplitTerm base t) := by
  rw [Term.LeftLinear, hubSplitTerm_varOccurrences]
  exact (encodeHubOccurrences_nodup_disjoint base 0 [] (Term.varOccurrences t)
    (by simp) (by simp [AllBelowNat]) hbelow).1

/-- Crown for the generic hub transform: every rule-specific split LHS is
left-linear. -/
theorem hubSplitRuleLhs_leftLinear (rule : Rule sigma Nat) :
    Term.LeftLinear (hubSplitTerm (ruleFreshBase rule) rule.lhs) := by
  apply hubSplitTerm_leftLinear_of_below
  intro x hx
  exact lhs_occ_lt_ruleFreshBase hx

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.hubSeenStep
#check @OperatorKO7.Meta.UniqueNormalization.hubSeenAfter
#check @OperatorKO7.Meta.UniqueNormalization.encodeHubOccurrences
#check @OperatorKO7.Meta.UniqueNormalization.hubSeenAfter_append
#check @OperatorKO7.Meta.UniqueNormalization.encodeHubOccurrences_append
#check @OperatorKO7.Meta.UniqueNormalization.AllBelowNat
#check @OperatorKO7.Meta.UniqueNormalization.hubFresh_not_mem_encodeHubOccurrences_of_lt
#check @OperatorKO7.Meta.UniqueNormalization.encodeHubOccurrences_nodup_disjoint
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitTermAux_trace
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitListAux_trace
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitTerm_varOccurrences
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitTerm_leftLinear_of_below
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitRuleLhs_leftLinear

#print axioms OperatorKO7.Meta.UniqueNormalization.hubSeenAfter_append
#print axioms OperatorKO7.Meta.UniqueNormalization.encodeHubOccurrences_append
#print axioms OperatorKO7.Meta.UniqueNormalization.hubFresh_not_mem_encodeHubOccurrences_of_lt
#print axioms OperatorKO7.Meta.UniqueNormalization.encodeHubOccurrences_nodup_disjoint
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitTermAux_trace
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitListAux_trace
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitTerm_varOccurrences
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitTerm_leftLinear_of_below
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitRuleLhs_leftLinear
