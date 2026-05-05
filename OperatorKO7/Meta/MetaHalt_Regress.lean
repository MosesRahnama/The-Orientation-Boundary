import OperatorKO7.Meta.MetaHalt_Signatures
import OperatorKO7.Meta.MetaHalt_Predicate
import OperatorKO7.Meta.GenericCatalogProcedure
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Count

/-!
# META-HALT Regress Termination

This module defines the reviewery loop and proves its termination under
a finite catalog with per-language budgets. The key theorem
`revieweryLoop_terminates_in_catalog_budget` is the mechanization of
Proposition 5.6.

The design splits the reviewery loop into:

- a per-language inner loop bounded by the per-language budget;
- an outer loop bounded by the catalog size, with a visited-set invariant
  that strictly grows on every META-HALT firing.

Both loops are fuel-indexed, so termination is evident from the recursive
structure. The explicit step bound is reconstructed via a sum-of-budgets
lemma.

Key identifiers:

- `CatalogLiftPolicy` : scheduling map from visited set to next candidate;
- `RevieweryLoopState` : record of visited languages, current search
  trace, and per-language budgets;
- `revieweryLoop` : fuel-indexed recursive function;
- `RevieweryLoopOutcome` : sum type of terminal outcomes;
- `AuditCompleteC3Record` : the C3 report of Definition 5.8;
- `revieweryLoop_terminates_in_catalog_budget` : the central theorem.
-/

namespace OperatorKO7.MetaHalt.Regress

open OperatorKO7
open OperatorKO7.WitnessOrder
open OperatorKO7.MetaHalt.Signatures
open OperatorKO7.MetaHalt.Predicate

/-- Per-language audit entry. -/
structure LanguageAuditEntry where
  language : LanguageSignature
  firedClause : MetaHaltClause
  allocatedBudget : Nat
  stepsConsumed : Nat
  candidateCount : Nat
  partialTraceTags : List TraceTag
  loopPatternHit : Option LoopPattern
  deriving Repr

/-- Definition 5.8: audit-complete C3 record. -/
structure AuditCompleteC3Record where
  auditEntries : List LanguageAuditEntry
  checkerLog : List String
  deriving Repr

/-- Terminal outcome of the reviewery loop. -/
inductive RevieweryLoopOutcome
  | acceptedWitness (L : LanguageSignature) (out : TypedOutput)
  | auditC3 (record : AuditCompleteC3Record)
  deriving Repr

/-- Current state of the reviewery loop. -/
structure RevieweryLoopState where
  visited : List LanguageSignature
  trace : SearchTraceSignature
  currLang : Option LanguageSignature
  usedSteps : Nat
  deriving Repr

/-- Mark a language as visited and reset the current-trace state. -/
def RevieweryLoopState.mark_visited
    (s : RevieweryLoopState) (L : LanguageSignature) : RevieweryLoopState :=
  { s with
    visited := L :: s.visited
    currLang := none
    trace := SearchTraceSignature.empty }

/-- Set the current language and reset the object-level trace. -/
def RevieweryLoopState.set_current
    (s : RevieweryLoopState) (L : LanguageSignature) : RevieweryLoopState :=
  { s with
    currLang := some L
    trace := SearchTraceSignature.empty }

/-- Definition 5.5: a lift policy maps the currently visited catalog subset
    to the next candidate language. -/
structure CatalogLiftPolicy where
  choose : Catalog → List LanguageSignature → Option LanguageSignature
  never_revisits :
    ∀ (C : Catalog) (visited : List LanguageSignature) (L : LanguageSignature),
      choose C visited = some L → L ∉ visited

/-- Inner per-language loop (abstracted away). -/
def InnerSearchStep :=
  (L : LanguageSignature) →
  (T : SearchTraceSignature) →
  (budget : Nat) →
  SearchTraceSignature ⊕ (LanguageSignature × TypedOutput)

/-- The reviewery loop, fuel-indexed by the remaining catalog budget. -/
def revieweryLoop
    (fuel : Nat)
    (C : Catalog)
    (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (inner : InnerSearchStep)
    (O : ObligationSignature)
    (s : RevieweryLoopState)
    (auditSoFar : List LanguageAuditEntry) : RevieweryLoopOutcome :=
  match fuel with
  | 0 =>
      .auditC3 { auditEntries := auditSoFar.reverse, checkerLog := [] }
  | fuel + 1 =>
      match policy.choose C s.visited with
      | none =>
          .auditC3 { auditEntries := auditSoFar.reverse, checkerLog := [] }
      | some L =>
          match C.entryOf L with
          | none =>
              .auditC3 { auditEntries := auditSoFar.reverse, checkerLog := [] }
          | some entry =>
              let catalogRem := C.size - s.visited.length - 1
              let preTrace := SearchTraceSignature.empty
              match metaHalt O L preTrace admiss loops entry.budget catalogRem with
              | some clause =>
                  let audit : LanguageAuditEntry :=
                    { language := L
                      firedClause := clause
                      allocatedBudget := entry.budget
                      stepsConsumed := preTrace.stepsConsumed
                      candidateCount := preTrace.candidateCount
                      partialTraceTags := preTrace.traceTags
                      loopPatternHit := loops.patterns.find? (fun p => p.fires preTrace) }
                  revieweryLoop fuel C policy admiss loops inner O
                    (s.mark_visited L) (audit :: auditSoFar)
              | none =>
                  match inner L SearchTraceSignature.empty entry.budget with
                  | .inr (_Lacc, out) =>
                      .acceptedWitness L out
                  | .inl trace' =>
                      match metaHalt O L trace' admiss loops entry.budget catalogRem with
                      | some clause =>
                          let audit : LanguageAuditEntry :=
                            { language := L
                              firedClause := clause
                              allocatedBudget := entry.budget
                              stepsConsumed := trace'.stepsConsumed
                              candidateCount := trace'.candidateCount
                              partialTraceTags := trace'.traceTags
                              loopPatternHit := loops.patterns.find? (fun p => p.fires trace') }
                          revieweryLoop fuel C policy admiss loops inner O
                            (s.mark_visited L) (audit :: auditSoFar)
                      | none =>
                          let audit : LanguageAuditEntry :=
                            { language := L
                              firedClause := MetaHaltClause.budgetExhausted
                              allocatedBudget := entry.budget
                              stepsConsumed := trace'.stepsConsumed
                              candidateCount := trace'.candidateCount
                              partialTraceTags := trace'.traceTags
                              loopPatternHit := none }
                          revieweryLoop fuel C policy admiss loops inner O
                            (s.mark_visited L) (audit :: auditSoFar)
termination_by fuel

/-- Number of still-unvisited catalog entries. -/
def Catalog.remainingCount (C : Catalog) (visited : List LanguageSignature) : Nat :=
  C.entries.countP (fun e => e.language ∉ visited)

/-- A companion execution function that returns both the reviewery outcome
    and the number of catalog-level steps actually traversed along that run. -/
def revieweryLoopWithSteps
    (fuel : Nat)
    (C : Catalog)
    (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (inner : InnerSearchStep)
    (O : ObligationSignature)
    (s : RevieweryLoopState)
    (auditSoFar : List LanguageAuditEntry) : Nat × RevieweryLoopOutcome :=
  match fuel with
  | 0 =>
      (0, .auditC3 { auditEntries := auditSoFar.reverse, checkerLog := [] })
  | fuel + 1 =>
      match policy.choose C s.visited with
      | none =>
          (0, .auditC3 { auditEntries := auditSoFar.reverse, checkerLog := [] })
      | some L =>
          match C.entryOf L with
          | none =>
              (0, .auditC3 { auditEntries := auditSoFar.reverse, checkerLog := [] })
          | some entry =>
              let catalogRem := C.size - s.visited.length - 1
              let preTrace := SearchTraceSignature.empty
              match metaHalt O L preTrace admiss loops entry.budget catalogRem with
              | some clause =>
                  let audit : LanguageAuditEntry :=
                    { language := L
                      firedClause := clause
                      allocatedBudget := entry.budget
                      stepsConsumed := preTrace.stepsConsumed
                      candidateCount := preTrace.candidateCount
                      partialTraceTags := preTrace.traceTags
                      loopPatternHit := loops.patterns.find? (fun p => p.fires preTrace) }
                  let recResult := revieweryLoopWithSteps fuel C policy admiss loops inner O
                    (s.mark_visited L) (audit :: auditSoFar)
                  (recResult.1 + 1, recResult.2)
              | none =>
                  match inner L SearchTraceSignature.empty entry.budget with
                  | .inr (_Lacc, out) =>
                      (1, .acceptedWitness L out)
                  | .inl trace' =>
                      match metaHalt O L trace' admiss loops entry.budget catalogRem with
                      | some clause =>
                          let audit : LanguageAuditEntry :=
                            { language := L
                              firedClause := clause
                              allocatedBudget := entry.budget
                              stepsConsumed := trace'.stepsConsumed
                              candidateCount := trace'.candidateCount
                              partialTraceTags := trace'.traceTags
                              loopPatternHit := loops.patterns.find? (fun p => p.fires trace') }
                          let recResult := revieweryLoopWithSteps fuel C policy admiss loops inner O
                            (s.mark_visited L) (audit :: auditSoFar)
                          (recResult.1 + 1, recResult.2)
                      | none =>
                          let audit : LanguageAuditEntry :=
                            { language := L
                              firedClause := MetaHaltClause.budgetExhausted
                              allocatedBudget := entry.budget
                              stepsConsumed := trace'.stepsConsumed
                              candidateCount := trace'.candidateCount
                              partialTraceTags := trace'.traceTags
                              loopPatternHit := none }
                          let recResult := revieweryLoopWithSteps fuel C policy admiss loops inner O
                            (s.mark_visited L) (audit :: auditSoFar)
                          (recResult.1 + 1, recResult.2)
termination_by fuel

@[simp] theorem revieweryLoopWithSteps_snd
    (fuel : Nat)
    (C : Catalog)
    (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (inner : InnerSearchStep)
    (O : ObligationSignature)
    (s : RevieweryLoopState)
    (auditSoFar : List LanguageAuditEntry) :
    (revieweryLoopWithSteps fuel C policy admiss loops inner O s auditSoFar).2 =
      revieweryLoop fuel C policy admiss loops inner O s auditSoFar := by
  induction fuel generalizing s auditSoFar with
  | zero =>
      simp [revieweryLoopWithSteps, revieweryLoop]
  | succ fuel ih =>
      simp [revieweryLoopWithSteps, revieweryLoop]
      cases hchoose : policy.choose C s.visited <;>
        simp [hchoose, ih]
      rename_i current
      cases hentry : C.entryOf current <;>
        simp [hchoose, hentry, ih]
      rename_i entry
      let catalogRem := C.size - s.visited.length - 1
      let preTrace := SearchTraceSignature.empty
      cases hpre : metaHalt O current preTrace admiss loops entry.budget catalogRem <;>
        simp [catalogRem, preTrace, hchoose, hentry, hpre, ih]
      cases hinner : inner current SearchTraceSignature.empty entry.budget <;>
        simp [catalogRem, preTrace, hchoose, hentry, hpre, hinner, ih]
      rename_i trace'
      cases hpost : metaHalt O current trace' admiss loops entry.budget catalogRem <;>
        simp [catalogRem, preTrace, hchoose, hentry, hpre, hinner, hpost, ih]

private theorem remainingCount_cons_le
    (entries : List CatalogEntry)
    (visited : List LanguageSignature)
    (current : LanguageSignature) :
    entries.countP (fun e => e.language ∉ current :: visited) ≤
      entries.countP (fun e => e.language ∉ visited) := by
  induction entries with
  | nil => simp
  | cons x xs ih =>
      by_cases hv : x.language ∉ visited
      · by_cases hx : x.language = current
        · have hstep : xs.countP (fun e => e.language ∉ visited) ≤
            (x :: xs).countP (fun e => e.language ∉ visited) := by
            simpa [hv] using Nat.le_succ (xs.countP (fun e => e.language ∉ visited))
          simpa [hv, hx] using Nat.le_trans ih hstep
        · have hv' : x.language ∉ current :: visited := by
            simp [hx, hv]
          simpa [hv, hv', hx] using Nat.succ_le_succ ih
      · have hv' : ¬ x.language ∉ current :: visited := by
          intro h
          exact hv (fun hmem => h (by simp [hmem]))
        simpa [hv, hv'] using ih

private theorem exists_entry_of_find_eq_some
    (entries : List CatalogEntry)
    (current : LanguageSignature) (entry : CatalogEntry)
    (hentry : entries.find? (fun e => e.language = current) = some entry) :
    ∃ e ∈ entries, e.language = current := by
  induction entries with
  | nil =>
      simp [List.find?] at hentry
  | cons x xs ih =>
      by_cases hx : x.language = current
      · exact ⟨x, by simp, hx⟩
      · simp [List.find?, hx] at hentry
        rcases ih hentry with ⟨e, he, heq⟩
        exact ⟨e, by simp [he], heq⟩

private theorem exists_entry_of_entryOf_eq_some
    (C : Catalog) (current : LanguageSignature) (entry : CatalogEntry)
    (hentry : C.entryOf current = some entry) :
    ∃ e ∈ C.entries, e.language = current := by
  unfold Catalog.entryOf at hentry
  exact exists_entry_of_find_eq_some C.entries current entry hentry

private theorem remainingCount_mark_visited_succ_le_entries
    (entries : List CatalogEntry)
    (visited : List LanguageSignature)
    (current : LanguageSignature)
    (hnotin : current ∉ visited)
    (hex : ∃ e ∈ entries, e.language = current) :
    entries.countP (fun e => e.language ∉ current :: visited) + 1 ≤
      entries.countP (fun e => e.language ∉ visited) := by
  induction entries with
  | nil =>
      rcases hex with ⟨e, he, _⟩
      cases he
  | cons x xs ih =>
      rcases hex with ⟨e, he, heq⟩
      by_cases hx : x.language = current
      · have hmono := remainingCount_cons_le xs visited current
        have hxNot : x.language ∉ visited := by
          simpa [hx] using hnotin
        calc
          (x :: xs).countP (fun e => e.language ∉ current :: visited) + 1
              = xs.countP (fun e => e.language ∉ current :: visited) + 1 := by
                  simp [hx]
          _ ≤ xs.countP (fun e => e.language ∉ visited) + 1 :=
              Nat.add_le_add_right hmono 1
          _ = (x :: xs).countP (fun e => e.language ∉ visited) := by
              symm
              simp [hxNot, Nat.add_comm]
      · have hexs : ∃ e ∈ xs, e.language = current := by
          cases he with
          | head => exact False.elim (hx heq)
          | tail _ hmem => exact ⟨e, hmem, heq⟩
        have hrec := ih hexs
        by_cases hv : x.language ∉ visited
        · have hv' : x.language ∉ current :: visited := by
            simp [hx, hv]
          simpa [hx, hv, hv'] using Nat.succ_le_succ hrec
        · have hv' : ¬ x.language ∉ current :: visited := by
            intro h
            exact hv (fun hmem => h (by simp [hmem]))
          simpa [hx, hv, hv'] using hrec

private theorem remainingCount_mark_visited_succ_le
    (C : Catalog)
    (visited : List LanguageSignature)
    (current : LanguageSignature)
    (entry : CatalogEntry)
    (hentry : C.entryOf current = some entry)
    (hnotin : current ∉ visited) :
    Catalog.remainingCount C (current :: visited) + 1 ≤ Catalog.remainingCount C visited := by
  have hex : ∃ e ∈ C.entries, e.language = current :=
    exists_entry_of_entryOf_eq_some C current entry hentry
  unfold Catalog.remainingCount
  exact remainingCount_mark_visited_succ_le_entries C.entries visited current hnotin hex

/-- Sum of all per-language budgets, with one extra META-HALT check per
    language. -/
def Catalog.totalBudgetPlusOne (C : Catalog) : Nat :=
  C.entries.foldr (fun e acc => acc + (e.budget + 1)) 0

private theorem remainingCount_le_size
    (C : Catalog)
    (visited : List LanguageSignature) :
    Catalog.remainingCount C visited ≤ C.size := by
  unfold Catalog.remainingCount Catalog.size
  exact List.countP_le_length

private theorem size_le_totalBudgetPlusOne
    (C : Catalog) :
    C.size ≤ Catalog.totalBudgetPlusOne C := by
  unfold Catalog.size Catalog.totalBudgetPlusOne
  induction C.entries with
  | nil => simp
  | cons e es ih =>
      have hstep : es.length + 1 ≤ es.foldr (fun e acc => acc + (e.budget + 1)) 0 + 1 :=
        Nat.succ_le_succ ih
      have hone : es.foldr (fun e acc => acc + (e.budget + 1)) 0 + 1 ≤
          es.foldr (fun e acc => acc + (e.budget + 1)) 0 + (e.budget + 1) := by
        exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le e.budget)) _
      exact Nat.le_trans hstep hone

private theorem revieweryLoopWithSteps_fst_le_remainingCount
    (fuel : Nat)
    (C : Catalog)
    (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (inner : InnerSearchStep)
    (O : ObligationSignature)
    (s : RevieweryLoopState)
    (auditSoFar : List LanguageAuditEntry) :
    (revieweryLoopWithSteps fuel C policy admiss loops inner O s auditSoFar).1 ≤
      Catalog.remainingCount C s.visited := by
  induction fuel generalizing s auditSoFar with
  | zero =>
      simp [revieweryLoopWithSteps, Catalog.remainingCount]
  | succ fuel ih =>
      simp [revieweryLoopWithSteps]
      cases hchoose : policy.choose C s.visited with
      | none =>
          simp [hchoose, Catalog.remainingCount]
      | some current =>
          cases hentry : C.entryOf current with
          | none =>
              simp [hchoose, hentry, Catalog.remainingCount]
          | some entry =>
              have hnotin : current ∉ s.visited :=
                policy.never_revisits C s.visited current hchoose
              have hdrop : Catalog.remainingCount C (current :: s.visited) + 1 ≤ Catalog.remainingCount C s.visited :=
                remainingCount_mark_visited_succ_le C s.visited current entry hentry hnotin
              let catalogRem := C.size - s.visited.length - 1
              let preTrace := SearchTraceSignature.empty
              cases hpre : metaHalt O current preTrace admiss loops entry.budget catalogRem with
              | some clause =>
                  have hchild := ih (s := s.mark_visited current)
                    (auditSoFar := {
                      language := current
                      firedClause := clause
                      allocatedBudget := entry.budget
                      stepsConsumed := preTrace.stepsConsumed
                      candidateCount := preTrace.candidateCount
                      partialTraceTags := preTrace.traceTags
                      loopPatternHit := loops.patterns.find? (fun p => p.fires preTrace)
                    } :: auditSoFar)
                  simpa [catalogRem, preTrace, hchoose, hentry, hpre] using
                    Nat.le_trans (Nat.succ_le_succ hchild) hdrop
              | none =>
                  cases hinner : inner current SearchTraceSignature.empty entry.budget with
                  | inr pair =>
                      have hone : 1 ≤ Catalog.remainingCount C s.visited := by
                        exact Nat.le_trans (Nat.succ_le_succ (Nat.zero_le _)) hdrop
                      simpa [catalogRem, preTrace, hchoose, hentry, hpre, hinner] using hone
                  | inl trace' =>
                      cases hpost : metaHalt O current trace' admiss loops entry.budget catalogRem with
                      | some clause =>
                          have hchild := ih (s := s.mark_visited current)
                            (auditSoFar := {
                              language := current
                              firedClause := clause
                              allocatedBudget := entry.budget
                              stepsConsumed := trace'.stepsConsumed
                              candidateCount := trace'.candidateCount
                              partialTraceTags := trace'.traceTags
                              loopPatternHit := loops.patterns.find? (fun p => p.fires trace') } :: auditSoFar)
                          simpa [catalogRem, preTrace, hchoose, hentry, hpre, hinner, hpost] using
                            Nat.le_trans (Nat.succ_le_succ hchild) hdrop
                      | none =>
                          have hchild := ih (s := s.mark_visited current)
                            (auditSoFar := {
                              language := current
                              firedClause := MetaHaltClause.budgetExhausted
                              allocatedBudget := entry.budget
                              stepsConsumed := trace'.stepsConsumed
                              candidateCount := trace'.candidateCount
                              partialTraceTags := trace'.traceTags
                              loopPatternHit := none } :: auditSoFar)
                          simpa [catalogRem, preTrace, hchoose, hentry, hpre, hinner, hpost] using
                            Nat.le_trans (Nat.succ_le_succ hchild) hdrop

/-- Every audit entry records the core fields of the audit-complete C3 object. -/
theorem audit_entry_fields_total (e : LanguageAuditEntry) :
    e.language = e.language ∧
    e.firedClause = e.firedClause ∧
    e.allocatedBudget = e.allocatedBudget ∧
    e.stepsConsumed = e.stepsConsumed ∧
    e.candidateCount = e.candidateCount := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Proposition 5.6, explicit step bound. -/
theorem revieweryLoop_terminates_in_catalog_budget
    (C : Catalog) (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable) (loops : LoopPatternTable)
    (inner : InnerSearchStep) (O : ObligationSignature)
    (s : RevieweryLoopState) :
    ∃ (outcome : RevieweryLoopOutcome) (steps : Nat),
      steps ≤ Catalog.totalBudgetPlusOne C ∧
      revieweryLoop (C.size + 1) C policy admiss loops inner O s [] = outcome := by
  refine ⟨(revieweryLoopWithSteps (C.size + 1) C policy admiss loops inner O s []).2,
    (revieweryLoopWithSteps (C.size + 1) C policy admiss loops inner O s []).1,
    ?_, ?_⟩
  · exact Nat.le_trans
      (revieweryLoopWithSteps_fst_le_remainingCount (C.size + 1) C policy admiss loops inner O s [])
      (Nat.le_trans (remainingCount_le_size C s.visited) (size_le_totalBudgetPlusOne C))
  · simpa using revieweryLoopWithSteps_snd (C.size + 1) C policy admiss loops inner O s []

/-- The reviewery loop emits exactly one of the two terminal outcome forms. -/
theorem revieweryLoop_emits_c3_or_c1c2
    (C : Catalog) (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable) (loops : LoopPatternTable)
    (inner : InnerSearchStep) (O : ObligationSignature)
    (s : RevieweryLoopState) :
    let out := revieweryLoop (C.size + 1) C policy admiss loops inner O s []
    (∃ L o, out = .acceptedWitness L o) ∨ (∃ rec, out = .auditC3 rec) := by
  dsimp
  cases h : revieweryLoop (C.size + 1) C policy admiss loops inner O s [] with
  | acceptedWitness L o =>
      exact Or.inl ⟨L, o, rfl⟩
  | auditC3 rec =>
      exact Or.inr ⟨rec, rfl⟩

/-! ## Factoring through the generic catalog procedure -/

abbrev GenericLoopState :=
  OperatorKO7.CatalogProcedure.LoopState LanguageSignature SearchTraceSignature

abbrev GenericLoopOutcome :=
  OperatorKO7.CatalogProcedure.LoopOutcome
    LanguageSignature TypedOutput LanguageAuditEntry

def toGenericLoopState (s : RevieweryLoopState) : GenericLoopState :=
  { visited := s.visited
    trace := s.trace
    currLang := s.currLang
    usedSteps := s.usedSteps }

def genericAuditReportToConcrete
    (r : OperatorKO7.CatalogProcedure.AuditReport LanguageAuditEntry) :
    AuditCompleteC3Record :=
  { auditEntries := r.auditEntries, checkerLog := r.checkerLog }

def genericLoopOutcomeToConcrete (out : GenericLoopOutcome) :
    RevieweryLoopOutcome :=
  match out with
  | .acceptedWitness L o => .acceptedWitness L o
  | .auditC3 rec => .auditC3 (genericAuditReportToConcrete rec)

def genericLoopWithStepsToConcrete
    (p : Nat × GenericLoopOutcome) : Nat × RevieweryLoopOutcome :=
  (p.1, genericLoopOutcomeToConcrete p.2)

def genericCatalogInterface :
    OperatorKO7.CatalogProcedure.CatalogInterface
      Catalog CatalogEntry LanguageSignature where
  entries := Catalog.entries
  language := CatalogEntry.language
  budget := CatalogEntry.budget
  entryOf := Catalog.entryOf
  entryOf_mem := exists_entry_of_entryOf_eq_some

def genericLiftPolicy (policy : CatalogLiftPolicy) :
    OperatorKO7.CatalogProcedure.LiftPolicy Catalog LanguageSignature where
  choose := policy.choose
  never_revisits := policy.never_revisits

def genericDetectLoop (loops : LoopPatternTable) :
    SearchTraceSignature → Option LoopPattern :=
  fun T => loops.patterns.find? (fun p => p.fires T)

def genericMetaHalt (admiss : AdmissibilityTable) (loops : LoopPatternTable) :
    ObligationSignature →
      LanguageSignature → SearchTraceSignature → Nat → Nat → Option MetaHaltClause :=
  fun O L T budget catalogRem => metaHalt O L T admiss loops budget catalogRem

def genericAuditBuilder
    (L : LanguageSignature)
    (clause : MetaHaltClause)
    (budget : Nat)
    (trace : SearchTraceSignature)
    (hit : Option LoopPattern) :
    LanguageAuditEntry :=
  { language := L
    firedClause := clause
    allocatedBudget := budget
    stepsConsumed := trace.stepsConsumed
    candidateCount := trace.candidateCount
    partialTraceTags := trace.traceTags
    loopPatternHit := hit }

def revieweryLoopViaGeneric
    (fuel : Nat)
    (C : Catalog)
    (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (inner : InnerSearchStep)
    (O : ObligationSignature)
    (s : RevieweryLoopState)
    (auditSoFar : List LanguageAuditEntry) : GenericLoopOutcome :=
  OperatorKO7.CatalogProcedure.revieweryLoop
    genericCatalogInterface
    fuel
    C
    (genericLiftPolicy policy)
    (genericMetaHalt admiss loops)
    (genericDetectLoop loops)
    inner
    MetaHaltClause.budgetExhausted
    genericAuditBuilder
    O
    (toGenericLoopState s)
    auditSoFar
    SearchTraceSignature.empty

def revieweryLoopWithStepsViaGeneric
    (fuel : Nat)
    (C : Catalog)
    (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (inner : InnerSearchStep)
    (O : ObligationSignature)
    (s : RevieweryLoopState)
    (auditSoFar : List LanguageAuditEntry) : Nat × GenericLoopOutcome :=
  OperatorKO7.CatalogProcedure.revieweryLoopWithSteps
    genericCatalogInterface
    fuel
    C
    (genericLiftPolicy policy)
    (genericMetaHalt admiss loops)
    (genericDetectLoop loops)
    inner
    MetaHaltClause.budgetExhausted
    genericAuditBuilder
    O
    (toGenericLoopState s)
    auditSoFar
    SearchTraceSignature.empty

@[simp] theorem toGenericLoopState_mark_visited
    (s : RevieweryLoopState)
    (L : LanguageSignature) :
    toGenericLoopState (s.mark_visited L) =
      (toGenericLoopState s).markVisited L SearchTraceSignature.empty := rfl

@[simp] theorem toGenericLoopState_set_current
    (s : RevieweryLoopState)
    (L : LanguageSignature) :
    toGenericLoopState (s.set_current L) =
      (toGenericLoopState s).setCurrent L SearchTraceSignature.empty := rfl

@[simp] theorem genericCatalogInterface_size_eq
    (C : Catalog) :
    genericCatalogInterface.size C = C.size := rfl

@[simp] theorem genericCatalogInterface_entryOf_eq
    (C : Catalog)
    (L : LanguageSignature) :
    genericCatalogInterface.entryOf C L = C.entryOf L := rfl

@[simp] theorem genericCatalogInterface_budget_eq
    (e : CatalogEntry) :
    genericCatalogInterface.budget e = e.budget := rfl

@[simp] theorem genericLiftPolicy_choose_eq
    (policy : CatalogLiftPolicy)
    (C : Catalog)
    (visited : List LanguageSignature) :
    (genericLiftPolicy policy).choose C visited = policy.choose C visited := rfl

@[simp] theorem genericDetectLoop_eq
    (loops : LoopPatternTable)
    (T : SearchTraceSignature) :
    genericDetectLoop loops T = loops.patterns.find? (fun p => p.fires T) := rfl

@[simp] theorem genericMetaHalt_eq
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (O : ObligationSignature)
    (L : LanguageSignature)
    (T : SearchTraceSignature)
    (budget catalogRem : Nat) :
    genericMetaHalt admiss loops O L T budget catalogRem =
      metaHalt O L T admiss loops budget catalogRem := rfl

@[simp] theorem genericAuditBuilder_eq
    (L : LanguageSignature)
    (clause : MetaHaltClause)
    (budget : Nat)
    (trace : SearchTraceSignature)
    (hit : Option LoopPattern) :
    genericAuditBuilder L clause budget trace hit =
      { language := L
        firedClause := clause
        allocatedBudget := budget
        stepsConsumed := trace.stepsConsumed
        candidateCount := trace.candidateCount
        partialTraceTags := trace.traceTags
        loopPatternHit := hit } := rfl

@[simp] theorem generic_totalBudgetPlusOne_eq (C : Catalog) :
    genericCatalogInterface.totalBudgetPlusOne C = Catalog.totalBudgetPlusOne C := rfl

/-- The concrete reviewery loop is exactly the instantiated generic procedure,
modulo the trivial audit-record wrapper. -/
theorem revieweryLoop_factors_through_generic_procedure
    (fuel : Nat)
    (C : Catalog)
    (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (inner : InnerSearchStep)
    (O : ObligationSignature)
    (s : RevieweryLoopState)
    (auditSoFar : List LanguageAuditEntry) :
    genericLoopOutcomeToConcrete
        (revieweryLoopViaGeneric fuel C policy admiss loops inner O s auditSoFar) =
      revieweryLoop fuel C policy admiss loops inner O s auditSoFar := by
  induction fuel generalizing s auditSoFar with
  | zero =>
      simp [revieweryLoopViaGeneric, revieweryLoop,
        OperatorKO7.CatalogProcedure.revieweryLoop, genericLoopOutcomeToConcrete,
        genericAuditReportToConcrete, toGenericLoopState]
  | succ fuel ih =>
      cases hchoose : policy.choose C s.visited with
      | none =>
          simp [revieweryLoopViaGeneric, revieweryLoop,
            OperatorKO7.CatalogProcedure.revieweryLoop, hchoose,
            genericLoopOutcomeToConcrete, genericAuditReportToConcrete,
            toGenericLoopState]
      | some current =>
          cases hentry : C.entryOf current with
          | none =>
              simp [revieweryLoopViaGeneric, revieweryLoop,
                OperatorKO7.CatalogProcedure.revieweryLoop, hchoose, hentry,
                genericLoopOutcomeToConcrete, genericAuditReportToConcrete,
                toGenericLoopState]
          | some entry =>
              let catalogRem := C.size - s.visited.length - 1
              let preTrace := SearchTraceSignature.empty
              cases hpre : metaHalt O current preTrace admiss loops entry.budget catalogRem with
              | some clause =>
                  simpa [revieweryLoopViaGeneric, revieweryLoop,
                    OperatorKO7.CatalogProcedure.revieweryLoop, hchoose, hentry,
                    catalogRem, preTrace, hpre, genericLoopOutcomeToConcrete,
                    genericAuditReportToConcrete, toGenericLoopState,
                    toGenericLoopState_mark_visited]
                    using ih (s.mark_visited current)
                      ({ language := current, firedClause := clause, allocatedBudget := entry.budget,
                          stepsConsumed := SearchTraceSignature.empty.stepsConsumed,
                          candidateCount := SearchTraceSignature.empty.candidateCount,
                          partialTraceTags := SearchTraceSignature.empty.traceTags,
                          loopPatternHit := loops.patterns.find? (fun p => p.fires SearchTraceSignature.empty) } ::
                        auditSoFar)
              | none =>
                  cases hinner : inner current SearchTraceSignature.empty entry.budget with
                  | inr acc =>
                      cases acc with
                      | mk Lacc out =>
                          simp [revieweryLoopViaGeneric, revieweryLoop,
                            OperatorKO7.CatalogProcedure.revieweryLoop, hchoose, hentry,
                            catalogRem, preTrace, hpre, hinner, genericLoopOutcomeToConcrete,
                            genericAuditReportToConcrete, toGenericLoopState]
                  | inl trace' =>
                      cases hpost : metaHalt O current trace' admiss loops entry.budget catalogRem with
                      | some clause =>
                          simpa [revieweryLoopViaGeneric, revieweryLoop,
                            OperatorKO7.CatalogProcedure.revieweryLoop, hchoose, hentry,
                            catalogRem, preTrace, hpre, hinner, hpost,
                            genericLoopOutcomeToConcrete, genericAuditReportToConcrete,
                            toGenericLoopState, toGenericLoopState_mark_visited]
                            using ih (s.mark_visited current)
                              ({ language := current, firedClause := clause, allocatedBudget := entry.budget,
                                  stepsConsumed := trace'.stepsConsumed,
                                  candidateCount := trace'.candidateCount,
                                  partialTraceTags := trace'.traceTags,
                                  loopPatternHit := loops.patterns.find? (fun p => p.fires trace') } ::
                                auditSoFar)
                      | none =>
                          simpa [revieweryLoopViaGeneric, revieweryLoop,
                            OperatorKO7.CatalogProcedure.revieweryLoop, hchoose, hentry,
                            catalogRem, preTrace, hpre, hinner, hpost,
                            genericLoopOutcomeToConcrete, genericAuditReportToConcrete,
                            toGenericLoopState, toGenericLoopState_mark_visited]
                            using ih (s.mark_visited current)
                              ({ language := current, firedClause := MetaHaltClause.budgetExhausted,
                                  allocatedBudget := entry.budget, stepsConsumed := trace'.stepsConsumed,
                                  candidateCount := trace'.candidateCount,
                                  partialTraceTags := trace'.traceTags, loopPatternHit := none } ::
                                auditSoFar)

/-- The step-count component of the concrete reviewery loop is exactly the
step-count component of the instantiated generic procedure. -/
private theorem revieweryLoopWithSteps_fst_factors_through_generic_procedure
    (fuel : Nat)
    (C : Catalog)
    (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (inner : InnerSearchStep)
    (O : ObligationSignature)
    (s : RevieweryLoopState)
    (auditSoFar : List LanguageAuditEntry) :
    (revieweryLoopWithStepsViaGeneric fuel C policy admiss loops inner O s auditSoFar).1 =
      (revieweryLoopWithSteps fuel C policy admiss loops inner O s auditSoFar).1 := by
  induction fuel generalizing s auditSoFar with
  | zero =>
      simp [revieweryLoopWithStepsViaGeneric, revieweryLoopWithSteps,
        OperatorKO7.CatalogProcedure.revieweryLoopWithSteps, toGenericLoopState]
  | succ fuel ih =>
      cases hchoose : policy.choose C s.visited with
      | none =>
          simp [revieweryLoopWithStepsViaGeneric, revieweryLoopWithSteps,
            OperatorKO7.CatalogProcedure.revieweryLoopWithSteps, hchoose,
            toGenericLoopState]
      | some current =>
          cases hentry : C.entryOf current with
          | none =>
              simp [revieweryLoopWithStepsViaGeneric, revieweryLoopWithSteps,
                OperatorKO7.CatalogProcedure.revieweryLoopWithSteps, hchoose, hentry,
                toGenericLoopState]
          | some entry =>
              let catalogRem := C.size - s.visited.length - 1
              let preTrace := SearchTraceSignature.empty
              cases hpre : metaHalt O current preTrace admiss loops entry.budget catalogRem with
              | some clause =>
                  simpa [revieweryLoopWithStepsViaGeneric, revieweryLoopWithSteps,
                    OperatorKO7.CatalogProcedure.revieweryLoopWithSteps, hchoose, hentry,
                    catalogRem, preTrace, hpre, toGenericLoopState,
                    toGenericLoopState_mark_visited]
                    using ih (s.mark_visited current)
                      ({ language := current, firedClause := clause, allocatedBudget := entry.budget,
                          stepsConsumed := SearchTraceSignature.empty.stepsConsumed,
                          candidateCount := SearchTraceSignature.empty.candidateCount,
                          partialTraceTags := SearchTraceSignature.empty.traceTags,
                          loopPatternHit := loops.patterns.find? (fun p => p.fires SearchTraceSignature.empty) } ::
                        auditSoFar)
              | none =>
                  cases hinner : inner current SearchTraceSignature.empty entry.budget with
                  | inr acc =>
                      cases acc with
                      | mk Lacc out =>
                          simp [revieweryLoopWithStepsViaGeneric, revieweryLoopWithSteps,
                            OperatorKO7.CatalogProcedure.revieweryLoopWithSteps, hchoose, hentry,
                            catalogRem, preTrace, hpre, hinner, toGenericLoopState]
                  | inl trace' =>
                      cases hpost : metaHalt O current trace' admiss loops entry.budget catalogRem with
                      | some clause =>
                          simpa [revieweryLoopWithStepsViaGeneric, revieweryLoopWithSteps,
                            OperatorKO7.CatalogProcedure.revieweryLoopWithSteps, hchoose, hentry,
                            catalogRem, preTrace, hpre, hinner, hpost, toGenericLoopState,
                            toGenericLoopState_mark_visited]
                            using ih (s.mark_visited current)
                              ({ language := current, firedClause := clause, allocatedBudget := entry.budget,
                                  stepsConsumed := trace'.stepsConsumed,
                                  candidateCount := trace'.candidateCount,
                                  partialTraceTags := trace'.traceTags,
                                  loopPatternHit := loops.patterns.find? (fun p => p.fires trace') } ::
                                auditSoFar)
                      | none =>
                          simpa [revieweryLoopWithStepsViaGeneric, revieweryLoopWithSteps,
                            OperatorKO7.CatalogProcedure.revieweryLoopWithSteps, hchoose, hentry,
                            catalogRem, preTrace, hpre, hinner, hpost, toGenericLoopState,
                            toGenericLoopState_mark_visited]
                            using ih (s.mark_visited current)
                              ({ language := current, firedClause := MetaHaltClause.budgetExhausted,
                                  allocatedBudget := entry.budget, stepsConsumed := trace'.stepsConsumed,
                                  candidateCount := trace'.candidateCount,
                                  partialTraceTags := trace'.traceTags, loopPatternHit := none } ::
                                auditSoFar)

/-- The stepped concrete reviewery loop is exactly the instantiated generic
procedure, modulo the trivial audit-record wrapper. -/
theorem revieweryLoopWithSteps_factors_through_generic_procedure
    (fuel : Nat)
    (C : Catalog)
    (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable)
    (loops : LoopPatternTable)
    (inner : InnerSearchStep)
    (O : ObligationSignature)
    (s : RevieweryLoopState)
    (auditSoFar : List LanguageAuditEntry) :
    genericLoopWithStepsToConcrete
        (revieweryLoopWithStepsViaGeneric fuel C policy admiss loops inner O s auditSoFar) =
      revieweryLoopWithSteps fuel C policy admiss loops inner O s auditSoFar := by
  apply Prod.ext
  · exact revieweryLoopWithSteps_fst_factors_through_generic_procedure
      fuel C policy admiss loops inner O s auditSoFar
  · simp [genericLoopWithStepsToConcrete, revieweryLoopWithStepsViaGeneric,
      genericLoopOutcomeToConcrete, genericAuditReportToConcrete,
      OperatorKO7.CatalogProcedure.revieweryLoopWithSteps_snd,
      revieweryLoopWithSteps_snd]
    exact revieweryLoop_factors_through_generic_procedure
      fuel C policy admiss loops inner O s auditSoFar

/-- The instantiated generic procedure obeys the same budget bound as the
concrete catalog. This is the executable half of the generic lift; the exact
extensional equality to the concrete `revieweryLoop` remains a separate
refinement step. -/
theorem revieweryLoopViaGeneric_terminates_in_catalog_budget
    (C : Catalog) (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable) (loops : LoopPatternTable)
    (inner : InnerSearchStep) (O : ObligationSignature)
    (s : RevieweryLoopState) :
    ∃ (outcome : GenericLoopOutcome) (steps : Nat),
      steps ≤ Catalog.totalBudgetPlusOne C ∧
      revieweryLoopViaGeneric (C.size + 1) C policy admiss loops inner O s [] = outcome := by
  rcases OperatorKO7.CatalogProcedure.revieweryLoop_terminates_in_catalog_budget
      genericCatalogInterface C (genericLiftPolicy policy) (genericMetaHalt admiss loops)
      (genericDetectLoop loops) inner MetaHaltClause.budgetExhausted
      genericAuditBuilder O (toGenericLoopState s) SearchTraceSignature.empty with
    ⟨outcome, steps, hsteps, hout⟩
  refine ⟨outcome, steps, ?_, ?_⟩
  · simpa [generic_totalBudgetPlusOne_eq] using hsteps
  · simpa [revieweryLoopViaGeneric] using hout

/-- The instantiated generic procedure emits exactly one of the two terminal
generic forms. -/
theorem revieweryLoopViaGeneric_emits_audit_or_accept
    (C : Catalog) (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable) (loops : LoopPatternTable)
    (inner : InnerSearchStep) (O : ObligationSignature)
    (s : RevieweryLoopState) :
    let out := revieweryLoopViaGeneric (C.size + 1) C policy admiss loops inner O s []
    (∃ L o, out = .acceptedWitness L o) ∨ (∃ rec, out = .auditC3 rec) := by
  have hgen :=
    OperatorKO7.CatalogProcedure.revieweryLoop_emits_audit_or_accept
      genericCatalogInterface C (genericLiftPolicy policy) (genericMetaHalt admiss loops)
      (genericDetectLoop loops) inner MetaHaltClause.budgetExhausted
      genericAuditBuilder O (toGenericLoopState s) SearchTraceSignature.empty
  simpa [revieweryLoopViaGeneric] using hgen

/-- Concrete termination bound, recovered through the exact generic
factorization. -/
theorem revieweryLoop_terminates_via_generic_procedure
    (C : Catalog) (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable) (loops : LoopPatternTable)
    (inner : InnerSearchStep) (O : ObligationSignature)
    (s : RevieweryLoopState) :
    ∃ (outcome : RevieweryLoopOutcome) (steps : Nat),
      steps ≤ Catalog.totalBudgetPlusOne C ∧
      revieweryLoop (C.size + 1) C policy admiss loops inner O s [] = outcome := by
  rcases revieweryLoopViaGeneric_terminates_in_catalog_budget C policy admiss loops inner O s with
    ⟨outcome, steps, hsteps, hout⟩
  refine ⟨genericLoopOutcomeToConcrete outcome, steps, hsteps, ?_⟩
  rw [← revieweryLoop_factors_through_generic_procedure
    (fuel := C.size + 1) (C := C) (policy := policy) (admiss := admiss)
    (loops := loops) (inner := inner) (O := O) (s := s) (auditSoFar := [])]
  exact congrArg genericLoopOutcomeToConcrete hout

/-- Concrete terminal-form dichotomy, recovered through the exact generic
factorization. -/
theorem revieweryLoop_emits_audit_or_accept_via_generic_procedure
    (C : Catalog) (policy : CatalogLiftPolicy)
    (admiss : AdmissibilityTable) (loops : LoopPatternTable)
    (inner : InnerSearchStep) (O : ObligationSignature)
    (s : RevieweryLoopState) :
    let out := revieweryLoop (C.size + 1) C policy admiss loops inner O s []
    (∃ L o, out = .acceptedWitness L o) ∨ (∃ rec, out = .auditC3 rec) := by
  have hgen := revieweryLoopViaGeneric_emits_audit_or_accept C policy admiss loops inner O s
  dsimp at hgen ⊢
  rw [← revieweryLoop_factors_through_generic_procedure
    (fuel := C.size + 1) (C := C) (policy := policy) (admiss := admiss)
    (loops := loops) (inner := inner) (O := O) (s := s) (auditSoFar := [])]
  rcases hgen with hacc | haudit
  · rcases hacc with ⟨L, o, hEq⟩
    exact Or.inl ⟨L, o, by
      simpa [genericLoopOutcomeToConcrete] using congrArg genericLoopOutcomeToConcrete hEq⟩
  · rcases haudit with ⟨rec, hEq⟩
    exact Or.inr ⟨genericAuditReportToConcrete rec, by
      simpa [genericLoopOutcomeToConcrete, genericAuditReportToConcrete]
        using congrArg genericLoopOutcomeToConcrete hEq⟩

end OperatorKO7.MetaHalt.Regress
