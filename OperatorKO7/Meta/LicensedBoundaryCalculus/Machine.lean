import OperatorKO7.Meta.LicensedBoundaryCalculus.Core

/-!
# Licensed Boundary Calculus machine core

This module defines an executable, type-indexed checker interface. The central
object is `TypedOutput`: a dependent output whose evidence type is indexed by
the verdict. Each constructor stores an artifact together with a proof that its
corresponding Boolean checker returned `true`. Semantic certificate,
counterexample, impossibility, and halt-audit claims require plug-specific
checker-soundness theorems.

The module is intentionally abstract over domain data. Plug-specific
machines instantiate `MachineSpec`.

Scope:
* generic typed-output, trust-tier, and plug-contract definitions;
* Boolean-checker acceptance evidence;
* domain semantics supplied through plug-specific obligations.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus.Machine

universe u

/-- Typed supervisory verdict alphabet. -/
inductive Verdict where
  | yes
  | no
  | impossible
  | halt
  deriving DecidableEq, Repr

/-- Trust tiers compose by taking the lower tier. -/
inductive TrustTier where
  | untrusted
  | external
  | runtime
  | theorem
  | kernel
  deriving DecidableEq, Repr

namespace TrustTier

/-- Numeric rank used to state trust-tier monotonicity properties. -/
def rank : TrustTier → Nat
  | .untrusted => 0
  | .external => 1
  | .runtime => 2
  | .theorem => 3
  | .kernel => 4

/-- Composition takes the weaker trust tier. -/
def meet (a b : TrustTier) : TrustTier :=
  if rank a <= rank b then a else b

theorem meet_rank_le_left (a b : TrustTier) :
    rank (meet a b) <= rank a := by
  cases a <;> cases b <;> simp [meet, rank]

theorem meet_rank_le_right (a b : TrustTier) :
    rank (meet a b) <= rank b := by
  cases a <;> cases b <;> simp [meet, rank]

theorem meet_no_upgrade_left (a b : TrustTier) :
    rank (meet a b) <= rank a :=
  meet_rank_le_left a b

theorem meet_no_upgrade_right (a b : TrustTier) :
    rank (meet a b) <= rank b :=
  meet_rank_le_right a b

end TrustTier

/-- A license has a scope and a trust tier. Plug-specific licenses may extend
this domain-neutral interface with additional fields. -/
structure License where
  id : String
  scope : String
  tier : TrustTier
  deriving Repr

/-- The composed license tier is bounded above by each input tier. -/
def composeLicense (a b : License) : License :=
  { id := a.id ++ "+" ++ b.id
    scope := a.scope ++ " ; " ++ b.scope
    tier := TrustTier.meet a.tier b.tier }

theorem composeLicense_rank_le_left (a b : License) :
    (composeLicense a b).tier.rank <= a.tier.rank :=
  TrustTier.meet_rank_le_left a.tier b.tier

theorem composeLicense_rank_le_right (a b : License) :
    (composeLicense a b).tier.rank <= b.tier.rank :=
  TrustTier.meet_rank_le_right a.tier b.tier

/-- Domain-neutral machine specification. Boolean checkers are the executable
surface; evidence stores the proof that the relevant checker returned true. -/
structure MachineSpec where
  Problem : Type u
  Certificate : Type u
  CounterWitness : Type u
  ImpossibilityWitness : Type u
  HaltAudit : Type u
  Ledger : Type u
  checkYes : Certificate → Bool
  checkNo : CounterWitness → Bool
  checkImpossible : ImpossibilityWitness → Bool
  checkHalt : HaltAudit → Bool
  defaultHalt : HaltAudit
  defaultHalt_valid : checkHalt defaultHalt = true
  defaultLedger : Ledger

/-- Evidence family indexed by the verdict. -/
inductive TypedEvidence (S : MachineSpec.{u}) : Verdict → Type u where
  | yes (c : S.Certificate) (h : S.checkYes c = true) :
      TypedEvidence S .yes
  | no (w : S.CounterWitness) (h : S.checkNo w = true) :
      TypedEvidence S .no
  | impossible (u : S.ImpossibilityWitness) (h : S.checkImpossible u = true) :
      TypedEvidence S .impossible
  | halt (a : S.HaltAudit) (h : S.checkHalt a = true) :
      TypedEvidence S .halt

/-- The terminal output type. The evidence field depends on the verdict. -/
structure TypedOutput (S : MachineSpec.{u}) where
  problem : S.Problem
  verdict : Verdict
  evidence : TypedEvidence S verdict
  ledger : S.Ledger

/-- A `yes` output contains a certificate accepted by `checkYes`. -/
theorem output_yes_has_verified_certificate
    {S : MachineSpec.{u}} (o : TypedOutput S) (h : o.verdict = .yes) :
    ∃ c : S.Certificate, S.checkYes c = true := by
  cases o with
  | mk problem verdict evidence ledger =>
      cases evidence with
      | yes c hc => exact ⟨c, hc⟩
      | no w hw => cases h
      | impossible u hu => cases h
      | halt a ha => cases h

/-- A `no` output contains a counter-witness accepted by `checkNo`. -/
theorem output_no_has_checked_counter_witness
    {S : MachineSpec.{u}} (o : TypedOutput S) (h : o.verdict = .no) :
    ∃ w : S.CounterWitness, S.checkNo w = true := by
  cases o with
  | mk problem verdict evidence ledger =>
      cases evidence with
      | yes c hc => cases h
      | no w hw => exact ⟨w, hw⟩
      | impossible u hu => cases h
      | halt a ha => cases h

/-- An `impossible` output contains a witness accepted by
`checkImpossible`. -/
theorem output_impossible_has_checked_impossibility
    {S : MachineSpec.{u}} (o : TypedOutput S) (h : o.verdict = .impossible) :
    ∃ u : S.ImpossibilityWitness, S.checkImpossible u = true := by
  cases o with
  | mk problem verdict evidence ledger =>
      cases evidence with
      | yes c hc => cases h
      | no w hw => cases h
      | impossible u hu => exact ⟨u, hu⟩
      | halt a ha => cases h

/-- A `halt` output contains an audit accepted by `checkHalt`. -/
theorem output_halt_has_checked_audit
    {S : MachineSpec.{u}} (o : TypedOutput S) (h : o.verdict = .halt) :
    ∃ a : S.HaltAudit, S.checkHalt a = true := by
  cases o with
  | mk problem verdict evidence ledger =>
      cases evidence with
      | yes c hc => cases h
      | no w hw => cases h
      | impossible u hu => cases h
      | halt a ha => exact ⟨a, ha⟩

/-- Candidate evidence supplied by an upstream method/model/human. -/
structure SupervisorInput (S : MachineSpec.{u}) where
  problem : S.Problem
  yesCertificate? : Option S.Certificate := none
  noCounterWitness? : Option S.CounterWitness := none
  impossibilityWitness? : Option S.ImpossibilityWitness := none
  haltAudit? : Option S.HaltAudit := none

/-- Build a checker-accepted halt output from the supplied audit when its check
succeeds, with the machine's accepted default audit as the fallback. -/
def haltOutput (S : MachineSpec.{u}) (p : S.Problem) (ledger : S.Ledger)
    (audit? : Option S.HaltAudit) : TypedOutput S :=
  match audit? with
  | some a =>
      if h : S.checkHalt a = true then
        { problem := p, verdict := .halt, evidence := .halt a h, ledger := ledger }
      else
        { problem := p, verdict := .halt,
          evidence := .halt S.defaultHalt S.defaultHalt_valid, ledger := ledger }
  | none =>
      { problem := p, verdict := .halt,
        evidence := .halt S.defaultHalt S.defaultHalt_valid, ledger := ledger }

/-- Deterministic supervisor priority: checker-accepted `yes`, then `no`,
then `impossible`, with checker-accepted `halt` as the fallback. Each branch
stores the artifact and Boolean equality required by its constructor. -/
def supervise (S : MachineSpec.{u}) (i : SupervisorInput S) : TypedOutput S :=
  match i.yesCertificate? with
  | some c =>
      if h : S.checkYes c = true then
        { problem := i.problem, verdict := .yes,
          evidence := .yes c h, ledger := S.defaultLedger }
      else
        match i.noCounterWitness? with
        | some w =>
            if hw : S.checkNo w = true then
              { problem := i.problem, verdict := .no,
                evidence := .no w hw, ledger := S.defaultLedger }
            else
              match i.impossibilityWitness? with
              | some u =>
                  if hu : S.checkImpossible u = true then
                    { problem := i.problem, verdict := .impossible,
                      evidence := .impossible u hu, ledger := S.defaultLedger }
                  else
                    haltOutput S i.problem S.defaultLedger i.haltAudit?
              | none => haltOutput S i.problem S.defaultLedger i.haltAudit?
        | none =>
            match i.impossibilityWitness? with
            | some u =>
                if hu : S.checkImpossible u = true then
                  { problem := i.problem, verdict := .impossible,
                    evidence := .impossible u hu, ledger := S.defaultLedger }
                else
                  haltOutput S i.problem S.defaultLedger i.haltAudit?
            | none => haltOutput S i.problem S.defaultLedger i.haltAudit?
  | none =>
      match i.noCounterWitness? with
      | some w =>
          if hw : S.checkNo w = true then
            { problem := i.problem, verdict := .no,
              evidence := .no w hw, ledger := S.defaultLedger }
          else
            match i.impossibilityWitness? with
            | some u =>
                if hu : S.checkImpossible u = true then
                  { problem := i.problem, verdict := .impossible,
                    evidence := .impossible u hu, ledger := S.defaultLedger }
                else
                  haltOutput S i.problem S.defaultLedger i.haltAudit?
            | none => haltOutput S i.problem S.defaultLedger i.haltAudit?
      | none =>
          match i.impossibilityWitness? with
          | some u =>
              if hu : S.checkImpossible u = true then
                { problem := i.problem, verdict := .impossible,
                  evidence := .impossible u hu, ledger := S.defaultLedger }
              else
                haltOutput S i.problem S.defaultLedger i.haltAudit?
          | none => haltOutput S i.problem S.defaultLedger i.haltAudit?

theorem supervise_yes_has_verified_certificate
    {S : MachineSpec.{u}} (i : SupervisorInput S)
    (h : (supervise S i).verdict = .yes) :
    ∃ c : S.Certificate, S.checkYes c = true :=
  output_yes_has_verified_certificate (supervise S i) h

theorem supervise_no_has_checked_counter_witness
    {S : MachineSpec.{u}} (i : SupervisorInput S)
    (h : (supervise S i).verdict = .no) :
    ∃ w : S.CounterWitness, S.checkNo w = true :=
  output_no_has_checked_counter_witness (supervise S i) h

theorem supervise_halt_has_checked_audit
    {S : MachineSpec.{u}} (i : SupervisorInput S)
    (h : (supervise S i).verdict = .halt) :
    ∃ a : S.HaltAudit, S.checkHalt a = true :=
  output_halt_has_checked_audit (supervise S i) h

theorem supervise_impossible_has_checked_impossibility
    {S : MachineSpec.{u}} (i : SupervisorInput S)
    (h : (supervise S i).verdict = .impossible) :
    ∃ u : S.ImpossibilityWitness, S.checkImpossible u = true :=
  output_impossible_has_checked_impossibility (supervise S i) h

/-- Domain plug contract consumed by the build-layer compiler. This structure
is data; plug-specific generated obligations supply semantic soundness. -/
structure PlugContract where
  domain : String
  targetPredicate : String
  directInterface : String
  boundaryPredicate : String
  licenseScope : String
  certificateSchema : String
  runtimeVerifier : String
  deriving Repr

/-- Classification of attempted instantiation. -/
inductive InstantiationVerdict where
  | instance
  | conditional
  | nonInstance
  deriving DecidableEq, Repr

/-- Rejected-instantiation reports are first-class typed values. -/
structure InstantiationReport where
  verdict : InstantiationVerdict
  reason : String
  requiredFix : String
  deriving Repr

-- Trust-surface declarations for the machine layer.
#print axioms output_yes_has_verified_certificate
#print axioms output_no_has_checked_counter_witness
#print axioms output_impossible_has_checked_impossibility
#print axioms output_halt_has_checked_audit
#print axioms supervise_yes_has_verified_certificate
#print axioms supervise_no_has_checked_counter_witness
#print axioms supervise_halt_has_checked_audit
#print axioms supervise_impossible_has_checked_impossibility
#print axioms TrustTier.meet_no_upgrade_left
#print axioms TrustTier.meet_no_upgrade_right
#print axioms composeLicense_rank_le_left
#print axioms composeLicense_rank_le_right

end OperatorKO7.Meta.LicensedBoundaryCalculus.Machine
