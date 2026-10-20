import OperatorKO7.Meta.DependencyPairs_Works
import OperatorKO7.Meta.PolyInterpretation_FullStep

/-!
# Response provenance for the declared KO7 dependency-pair route

This module distinguishes three kinds of mathematical content:

* data that factor through a declared rule view;
* data that fail that factorization, witnessed by equal rule views with
  different outputs;
* proof-valued licenses that map a transformed conclusion to a source
  conclusion.

The concrete extraction below is the actual KO7 `rec_succ` dependency pair.
Its renaming results concern equivalences that preserve exactly the
constructors used by that rule. The concrete license is instance-level: it
uses the independently proved KO7 polynomial source-termination theorem and
does not assert a general dependency-pair processor theorem.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.ResponseProvenance

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.MetaDependencyPairs

/-! ## Semantic provenance properties -/

/-- A data family is rule-determined relative to `rules` when it factors
through that declared rule view. -/
def RuleDetermined {Config RuleView Data : Type*}
    (rules : Config -> RuleView) (data : Config -> Data) : Prop :=
  exists extract : RuleView -> Data,
    forall c : Config, data c = extract (rules c)

/-- Imported data are witnessed semantically: two configurations have the
same declared rule view but different data. -/
def ImportedData {Config RuleView Data : Type*}
    (rules : Config -> RuleView) (data : Config -> Data) : Prop :=
  exists c1 c2 : Config,
    rules c1 = rules c2 ∧ data c1 ≠ data c2

/-- Any explicitly supplied extractor makes its composite rule-determined. -/
theorem ruleDetermined_of_extractor {Config RuleView Data : Type*}
    (rules : Config -> RuleView) (extract : RuleView -> Data) :
    RuleDetermined rules (fun c => extract (rules c)) :=
  ⟨extract, fun _ => rfl⟩

/-- An equal-rule, unequal-data witness falsifies rule determination. -/
theorem importedData_falsifies_ruleDetermined
    {Config RuleView Data : Type*}
    {rules : Config -> RuleView} {data : Config -> Data}
    (hImported : ImportedData rules data) :
    Not (RuleDetermined rules data) := by
  rintro ⟨extract, hFactor⟩
  rcases hImported with ⟨c1, c2, hRules, hData⟩
  apply hData
  calc
    data c1 = extract (rules c1) := hFactor c1
    _ = extract (rules c2) := congrArg extract hRules
    _ = data c2 := (hFactor c2).symm

/-- A soundness license is theorem data connecting a transformed conclusion
to a source conclusion. It is not a route name or metadata tag. -/
structure SoundnessLicense (transformed source : Prop) : Prop where
  bridge : transformed -> source

/-- A transformed witness together with a failed source conclusion is a
falsifier for inhabitation of the corresponding license type. -/
theorem no_soundnessLicense_of_falsifier
    {transformed source : Prop}
    (hTransformed : transformed) (hSourceFails : Not source) :
    Not (Nonempty (SoundnessLicense transformed source)) := by
  rintro ⟨license⟩
  exact hSourceFails (license.bridge hTransformed)

/-! ## The actual KO7 `rec_succ` extraction -/

/-- Parameters of one presentation of the KO7 `rec_succ` rule. -/
structure RecSuccRule where
  base : Trace
  stepTerm : Trace
  counter : Trace

/-- Left side of the presented source rule. -/
def RecSuccRule.caller (r : RecSuccRule) : Trace :=
  recΔ r.base r.stepTerm (delta r.counter)

/-- Right side of the presented source rule. -/
def RecSuccRule.rhs (r : RecSuccRule) : Trace :=
  app r.stepTerm (recΔ r.base r.stepTerm r.counter)

/-- Recursive call extracted from the right side. -/
def RecSuccRule.callee (r : RecSuccRule) : Trace :=
  recΔ r.base r.stepTerm r.counter

/-- Pure extraction data: the actual caller/callee pair, its one-edge call
graph, and the zero-based counter coordinate. Proofs are kept outside this
record so data and certification remain separate. -/
structure DPPairData where
  caller : Trace
  callee : Trace
  callGraphEdge : Trace × Trace
  projectionCoordinate : Fin 3

/-- Extract the KO7 pair, singleton call-graph edge, and counter projection
coordinate from one `rec_succ` rule presentation. -/
def extractDPPairData (r : RecSuccRule) : DPPairData where
  caller := r.caller
  callee := r.callee
  callGraphEdge := (r.caller, r.callee)
  projectionCoordinate := ⟨2, by decide⟩

/-- The source rule step and the actual KO7 `DPPair` are extracted together.
This specializes `rec_succ_extracts_dependency_pair`, rather than introducing
an unrelated pair relation. -/
theorem recSuccRule_extracts_ko7DPPair (r : RecSuccRule) :
    Step r.caller r.rhs ∧ DPPair r.caller r.callee := by
  simpa [RecSuccRule.caller, RecSuccRule.rhs, RecSuccRule.callee] using
    (rec_succ_extracts_dependency_pair r.base r.stepTerm r.counter)

/-- The pure extraction record carries exactly the certified KO7 pair and its
singleton call-graph edge. -/
theorem extractDPPairData_certified (r : RecSuccRule) :
    DPPair (extractDPPairData r).caller (extractDPPairData r).callee
      ∧ (extractDPPairData r).callGraphEdge =
          ((extractDPPairData r).caller, (extractDPPairData r).callee) := by
  exact ⟨(recSuccRule_extracts_ko7DPPair r).2, rfl⟩

/-- Proof-bearing certificate for the checked transformed call. It records the
source step, the actual extracted pair, the call-graph edge, and strict drop of
the registered KO7 dependency-pair rank. -/
structure TransformedCallCertificate (r : RecSuccRule) : Prop where
  sourceStep : Step r.caller r.rhs
  extractedPair : DPPair r.caller r.callee
  callGraphEdge :
    (extractDPPairData r).callGraphEdge = (r.caller, r.callee)
  pairRankDrop : dpRank r.callee < dpRank r.caller

/-- The checked transformed-call certificate for every displayed KO7
`rec_succ` presentation. -/
def ko7CheckedTransformedCallCertificate
    (r : RecSuccRule) : TransformedCallCertificate r where
  sourceStep := (recSuccRule_extracts_ko7DPPair r).1
  extractedPair := (recSuccRule_extracts_ko7DPPair r).2
  callGraphEdge := rfl
  pairRankDrop :=
    dpPair_decreases (recSuccRule_extracts_ko7DPPair r).2

/-! ## Rule renaming and extractor equivariance -/

/-- A renaming of the displayed rule is a term equivalence preserving, in
both directions, exactly `delta`, `app`, and `recDelta`, the constructors used
by `rec_succ`. No claim is made about arbitrary rewrite signatures. -/
structure RecSuccRuleRenaming where
  termEquiv : Trace ≃ Trace
  map_delta : forall t : Trace,
    termEquiv (delta t) = delta (termEquiv t)
  map_app : forall x y : Trace,
    termEquiv (app x y) = app (termEquiv x) (termEquiv y)
  map_rec : forall b s n : Trace,
    termEquiv (recΔ b s n) =
      recΔ (termEquiv b) (termEquiv s) (termEquiv n)
  inverse_delta : forall t : Trace,
    termEquiv.symm (delta t) = delta (termEquiv.symm t)
  inverse_app : forall x y : Trace,
    termEquiv.symm (app x y) =
      app (termEquiv.symm x) (termEquiv.symm y)
  inverse_rec : forall b s n : Trace,
    termEquiv.symm (recΔ b s n) =
      recΔ (termEquiv.symm b) (termEquiv.symm s) (termEquiv.symm n)

/-- Reverse a rule renaming. -/
def RecSuccRuleRenaming.symm
    (rho : RecSuccRuleRenaming) : RecSuccRuleRenaming where
  termEquiv := rho.termEquiv.symm
  map_delta := rho.inverse_delta
  map_app := rho.inverse_app
  map_rec := rho.inverse_rec
  inverse_delta := by
    intro t
    simpa using rho.map_delta t
  inverse_app := by
    intro x y
    simpa using rho.map_app x y
  inverse_rec := by
    intro b s n
    simpa using rho.map_rec b s n

/-- Rename the three parameters of the displayed rule. -/
def RecSuccRule.rename
    (r : RecSuccRule) (rho : RecSuccRuleRenaming) : RecSuccRule where
  base := rho.termEquiv r.base
  stepTerm := rho.termEquiv r.stepTerm
  counter := rho.termEquiv r.counter

/-- Transport a caller/callee pair along a rule renaming. -/
def renamePair (rho : RecSuccRuleRenaming)
    (pair : Trace × Trace) : Trace × Trace :=
  (rho.termEquiv pair.1, rho.termEquiv pair.2)

/-- Transport all pure extraction data along a rule renaming. -/
def DPPairData.rename
    (data : DPPairData) (rho : RecSuccRuleRenaming) : DPPairData where
  caller := rho.termEquiv data.caller
  callee := rho.termEquiv data.callee
  callGraphEdge := renamePair rho data.callGraphEdge
  projectionCoordinate := data.projectionCoordinate

/-- The displayed source-rule caller and right side commute with renaming. -/
theorem recSucc_sourceRule_equivariant
    (rho : RecSuccRuleRenaming) (r : RecSuccRule) :
    rho.termEquiv r.caller = (r.rename rho).caller
      ∧ rho.termEquiv r.rhs = (r.rename rho).rhs := by
  constructor
  · simp only [RecSuccRule.caller, RecSuccRule.rename,
      rho.map_rec, rho.map_delta]
  · simp only [RecSuccRule.rhs, RecSuccRule.rename,
      rho.map_app, rho.map_rec]

/-- The actual KO7 dependency-pair relation is closed under the declared rule
renamings. -/
theorem ko7DPPair_closed_under_renaming
    (rho : RecSuccRuleRenaming) {a b : Trace}
    (hPair : DPPair a b) :
    DPPair (rho.termEquiv a) (rho.termEquiv b) := by
  cases hPair with
  | rec_succ base stepTerm counter =>
      simpa only [rho.map_rec, rho.map_delta] using
        (DPPair.rec_succ
          (rho.termEquiv base)
          (rho.termEquiv stepTerm)
          (rho.termEquiv counter))

/-- Because the renaming is an equivalence preserving the rule in both
directions, membership in the actual KO7 pair relation is invariant. -/
theorem ko7DPPair_renaming_iff
    (rho : RecSuccRuleRenaming) {a b : Trace} :
    DPPair (rho.termEquiv a) (rho.termEquiv b) ↔ DPPair a b := by
  constructor
  · intro hPair
    have hBack :
        DPPair
          (rho.termEquiv.symm (rho.termEquiv a))
          (rho.termEquiv.symm (rho.termEquiv b)) :=
      ko7DPPair_closed_under_renaming (rho := rho.symm) hPair
    simpa using hBack
  · exact ko7DPPair_closed_under_renaming rho

/-- The actual pair, singleton call graph, and projection coordinate commute
with the declared rule renaming. -/
theorem extractDPPairData_equivariant
    (rho : RecSuccRuleRenaming) (r : RecSuccRule) :
    (extractDPPairData r).rename rho =
      extractDPPairData (r.rename rho) := by
  simp only [DPPairData.rename, extractDPPairData, renamePair,
    RecSuccRule.caller, RecSuccRule.callee, RecSuccRule.rename,
    rho.map_rec, rho.map_delta]

/-- A canonical extractor stores its actual extraction together with the
renaming equation that constrains it. -/
structure CanonicalDPPairExtractor where
  extract : RecSuccRule -> DPPairData
  pairCertified : forall r : RecSuccRule,
    DPPair (extract r).caller (extract r).callee
  equivariant : forall (rho : RecSuccRuleRenaming) (r : RecSuccRule),
    (extract r).rename rho = extract (r.rename rho)

/-- The canonical extractor for the displayed KO7 rule. -/
def ko7CanonicalDPPairExtractor : CanonicalDPPairExtractor where
  extract := extractDPPairData
  pairCertified := fun r => (extractDPPairData_certified r).1
  equivariant := extractDPPairData_equivariant

/-- The concrete pair/call-graph/projection data factor through the declared
rule presentation. -/
theorem ko7DPPairData_ruleDetermined :
    RuleDetermined
      (fun r : RecSuccRule => r)
      ko7CanonicalDPPairExtractor.extract :=
  ⟨ko7CanonicalDPPairExtractor.extract, fun _ => rfl⟩

/-! ## Rule-determined projection and non-unique construction data -/

/-- An admissible construction rank for the fixed, actual KO7 pair relation. -/
structure AdmissibleConstructionRank where
  rank : Trace -> Nat
  pairDescent : forall {a b : Trace}, DPPair a b -> rank b < rank a

/-- The canonical extracted counter rank. -/
def canonicalConstructionRank : AdmissibleConstructionRank where
  rank := dpRank
  pairDescent := dpPair_decreases

/-- A genuinely different admissible rank for the same `DPPair` relation. -/
def shiftedConstructionRank : AdmissibleConstructionRank where
  rank := fun t => dpRank t + 1
  pairDescent := by
    intro a b hPair
    exact Nat.add_lt_add_right (dpPair_decreases hPair) 1

/-- The two admissible ranks differ already at `Trace.void`. -/
theorem canonicalConstructionRank_ne_shiftedConstructionRank :
    canonicalConstructionRank ≠ shiftedConstructionRank := by
  intro hEqual
  have hAtVoid := congrArg
    (fun rankData : AdmissibleConstructionRank => rankData.rank Trace.void)
    hEqual
  simp [canonicalConstructionRank, shiftedConstructionRank, dpRank] at hAtVoid

/-- Both distinct witnesses orient exactly the same KO7 pair relation. -/
theorem ko7ConstructionRank_nonunique :
    exists first second : AdmissibleConstructionRank,
      first ≠ second :=
  ⟨canonicalConstructionRank, shiftedConstructionRank,
    canonicalConstructionRank_ne_shiftedConstructionRank⟩

/-- The only declared construction choices used in the countermodel. -/
inductive ConstructionChoice
  | canonical
  | shifted

/-- Both choices expose the same fixed KO7 pair relation as their rule view. -/
def constructionRuleView
    (_ : ConstructionChoice) : Trace -> Trace -> Prop :=
  DPPair

/-- The external choice selects one of two admissible ranks. -/
def constructionRankData
    (choice : ConstructionChoice) : AdmissibleConstructionRank :=
  match choice with
  | .canonical => canonicalConstructionRank
  | .shifted => shiftedConstructionRank

/-- Relative to the declared rule view, construction-rank selection is
imported: the same `DPPair` relation admits two different selected ranks. -/
theorem ko7ConstructionRank_imported :
    ImportedData constructionRuleView constructionRankData :=
  ⟨ConstructionChoice.canonical, ConstructionChoice.shifted, rfl,
    canonicalConstructionRank_ne_shiftedConstructionRank⟩

/-- The explicit equal-rule, unequal-rank witness rules out factorization of
the selected construction rank through the fixed relation alone. -/
theorem ko7ConstructionRank_not_ruleDetermined :
    Not (RuleDetermined constructionRuleView constructionRankData) :=
  importedData_falsifies_ruleDetermined ko7ConstructionRank_imported

/-- Projection data extracted for confession: the coordinate and rank are
kept distinct from any source-soundness theorem. -/
structure ExtractedProjection where
  coordinate : Fin 3
  rank : Trace -> Nat
  pairDescent : forall {a b : Trace}, DPPair a b -> rank b < rank a

/-- The KO7 projection extracted by the canonical response. -/
def ko7ExtractedProjection : ExtractedProjection where
  coordinate := ⟨2, by decide⟩
  rank := dpRank
  pairDescent := dpPair_decreases

/-- Extract the projection coordinate from the rule's DP data and attach the
registered rank profile certified on the actual pair relation. -/
def extractProjection (r : RecSuccRule) : ExtractedProjection where
  coordinate := (extractDPPairData r).projectionCoordinate
  rank := dpRank
  pairDescent := dpPair_decreases

/-- The projection recipe factors through the declared rule presentation. -/
theorem ko7Projection_ruleDetermined :
    RuleDetermined
      (fun r : RecSuccRule => r)
      extractProjection :=
  ⟨extractProjection, fun _ => rfl⟩

/-! ## A proof-valued, instance-level soundness license -/

/-- The transformed conclusion for this exact KO7 pair problem. -/
abbrev KO7TransformedTermination : Prop :=
  WellFounded DPPairRev

/-- The source conclusion for the exact KO7 root-step relation. -/
abbrev KO7SourceRootTermination : Prop :=
  WellFounded (fun a b : Trace => Step b a)

/-- Concrete KO7 bridge. The source conclusion comes from the independent
polynomial proof, so this value makes no generic processor-soundness claim. -/
def ko7DPSoundnessLicense :
    SoundnessLicense KO7TransformedTermination KO7SourceRootTermination where
  bridge := fun _ => OperatorKO7.PolyInterpretation.wf_StepRev_poly

/-- Public theorem form of the concrete, proof-valued source bridge. -/
theorem ko7DPSoundnessLicense_bridge
    (hTransformed : KO7TransformedTermination) :
    KO7SourceRootTermination :=
  ko7DPSoundnessLicense.bridge hTransformed

/-- Response-side states for whether a proof-valued source bridge has been
supplied. This is not a classification of termination methods. -/
inductive LicenseSupply
  | absent
  | supplied
      (license : SoundnessLicense
        KO7TransformedTermination KO7SourceRootTermination)

/-- Both supply states expose the same fixed rule view. -/
def licenseSupplyRuleView
    (_ : LicenseSupply) : Trace -> Trace -> Prop :=
  DPPair

/-- Whether the response contains a proof-valued source bridge. -/
def licenseAvailable : LicenseSupply -> Bool
  | .absent => false
  | .supplied _ => true

/-- Supplying the proof changes license availability without changing the
declared KO7 pair relation. -/
theorem ko7SoundnessLicenseAvailability_imported :
    ImportedData licenseSupplyRuleView licenseAvailable := by
  refine ⟨LicenseSupply.absent,
    LicenseSupply.supplied ko7DPSoundnessLicense, rfl, ?_⟩
  intro hEqual
  cases hEqual

/-- Relative to the declared extractor language, license availability is not
rule-determined. This is a provenance statement about supplying the bridge,
not a claim that source termination is logically independent of the rules. -/
theorem ko7SoundnessLicense_outside_declaredExtractorLanguage :
    Not (RuleDetermined licenseSupplyRuleView licenseAvailable) :=
  importedData_falsifies_ruleDetermined
    ko7SoundnessLicenseAvailability_imported

/-- A confession response keeps rule-extracted projection data in one field
and the externally supplied source bridge in another. -/
structure ConfessionResponse where
  projection : ExtractedProjection
  license : SoundnessLicense KO7TransformedTermination KO7SourceRootTermination

/-- The canonical KO7 confession response with separately supplied data and
proof-valued license. -/
def ko7ConfessionResponse : ConfessionResponse where
  projection := ko7ExtractedProjection
  license := ko7DPSoundnessLicense

/-- The license actually maps the proved transformed conclusion to source
root termination. -/
theorem ko7ConfessionResponse_sourceTermination :
    KO7SourceRootTermination :=
  ko7ConfessionResponse.license.bridge wf_DPPairRev

end OperatorKO7.Meta.OperationalInexpressibility.ResponseProvenance
