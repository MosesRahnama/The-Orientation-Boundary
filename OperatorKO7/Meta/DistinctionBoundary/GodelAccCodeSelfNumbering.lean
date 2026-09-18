import OperatorKO7.Meta.DistinctionBoundary.GodelAcceptableNumberingStep

set_option autoImplicit false

/-!
# Self-numbering boundary of AccCode

`AccCode` already supports a relative universal interpreter for embedded
`PartialCode` and one-parameter specialization.  This module pushes that
surface to the strongest self-numbering question supported by the live
interpreter.

First, `AccCode` receives a faithful syntax code into `Trace` with a total
partial decoder on its image.  Second, arbitrary `AccCode` programs admit a
semantic one-parameter specialization by composing them with `.cons`.  Third,
the existing `.apply` interpreter is proved incapable of serving as a universal
self-interpreter for arbitrary `AccCode`, for every possible choice of syntax
encoding.  The obstruction is semantic: interpreting `.cons void` would force
one `PartialCode` to map `void` and `delta void` to two distinct compound
outputs, ruled out by `not_two_distinct_compounds`.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelPartial

/-! ## Faithful syntax coding -/

/-- Faithful meta-level syntax code for the extended carrier. -/
def encodeAcc : AccCode → Trace
  | .apply => .void
  | .cons a => .delta a
  | .embed c => .recΔ .void .void (encode c)
  | .compose f g => .merge (encodeAcc f) (encodeAcc g)

/-- Decoder for the `encodeAcc` syntax image. -/
def decodeAcc? : Trace → Option AccCode
  | .void => some .apply
  | .delta a => some (.cons a)
  | .recΔ .void .void z => (decode z).map AccCode.embed
  | .merge a b =>
      match decodeAcc? a, decodeAcc? b with
      | some f, some g => some (.compose f g)
      | _, _ => none
  | _ => none

/-- `decodeAcc?` is a left inverse of `encodeAcc`. -/
theorem decodeAcc?_encode : ∀ c : AccCode, decodeAcc? (encodeAcc c) = some c
  | .apply => rfl
  | .cons _ => rfl
  | .embed c => by simp [encodeAcc, decodeAcc?, decode_encode]
  | .compose f g => by
      simp [encodeAcc, decodeAcc?, decodeAcc?_encode f, decodeAcc?_encode g]

/-- The extended syntax coding is injective. -/
theorem encodeAcc_injective : Function.Injective encodeAcc := by
  intro a b h
  have := congrArg decodeAcc? h
  simpa [decodeAcc?_encode] using this

/-! ## Arbitrary AccCode specialization -/

/-- Specialize an arbitrary extended program at a fixed first argument. -/
def smnAcc (e : AccCode) (a : Trace) : AccCode :=
  .compose e (.cons a)

/-- Semantic s-m-n law for every `AccCode`: specialization at `a` maps `x` to
the behavior of `e` at `app a x`. -/
theorem smnAcc_spec (e : AccCode) (a x v : Trace) :
    convergesToAcc (smnAcc e a) x v ↔
      convergesToAcc e (Trace.app a x) v := by
  unfold smnAcc
  rw [convergesToAcc_compose_iff]
  constructor
  · rintro ⟨u, hu, hev⟩
    have hp : convergesToAcc (.cons a) x (Trace.app a x) := cons_pairs a x
    have hueq : u = Trace.app a x := convergesToAcc_unique hu hp
    simpa [hueq] using hev
  · intro h
    exact ⟨Trace.app a x, cons_pairs a x, h⟩

/-- Arbitrary extended specialization is a total meta-level compiler. -/
structure AccCodeSMN : Type where
  compiler : AccCode → Trace → AccCode
  spec : ∀ e a x v,
    convergesToAcc (compiler e a) x v ↔ convergesToAcc e (Trace.app a x) v

/-- The live carrier has the full semantic specialization operation. -/
def accCode_smn : AccCodeSMN where
  compiler := smnAcc
  spec := smnAcc_spec

/-! ## Self-universality test for the live `.apply` interpreter -/

/-- Self-universality of an extended interpreter relative to an arbitrary
chosen syntax encoding. -/
def IsUniversalAccWith (enc : AccCode → Trace) (U : AccCode) : Prop :=
  ∀ e x v,
    convergesToAcc U (Trace.app (enc e) x) v ↔ convergesToAcc e x v

/-- `.apply` on an arbitrary leading trace executes the quoted old
`PartialCode` on the second argument. -/
theorem apply_tracks_quote (a x v : Trace) :
    convergesToAcc .apply (Trace.app a x) v ↔ convergesTo (quote a) x v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => cases hn
    | succ n =>
      have hacc : stepAcc n (.embed (quote a)) x = some v := by
        simpa [stepAcc] using hn
      exact (embed_tracks (quote a) x v).mp ⟨n, hacc⟩
  · intro h
    have hacc : convergesToAcc (.embed (quote a)) x v :=
      (embed_tracks (quote a) x v).mpr h
    obtain ⟨n, hn⟩ := hacc
    refine ⟨n + 1, ?_⟩
    change stepAcc n (.embed (quote a)) x = some v
    exact hn

/-- The two outputs produced by `.cons void` at the two witness inputs are
compound and distinct. -/
theorem consVoid_outputs_obstruct_partialCode :
    ∀ U : PartialCode,
      ¬ (convergesTo U Trace.void (Trace.app Trace.void Trace.void) ∧
          convergesTo U (Trace.delta Trace.void)
            (Trace.app Trace.void (Trace.delta Trace.void))) := by
  intro U
  apply not_two_distinct_compounds U
  · trivial
  · trivial
  · intro h
    simpa using h

/-- For every proposed encoding of `AccCode`, the existing `.apply` program is
not a universal self-interpreter for the extended carrier. -/
theorem apply_not_universalAcc (enc : AccCode → Trace) :
    ¬ IsUniversalAccWith enc .apply := by
  intro hU
  let e : AccCode := .cons Trace.void
  have h1e : convergesToAcc e Trace.void (Trace.app Trace.void Trace.void) :=
    cons_pairs Trace.void Trace.void
  have h2e : convergesToAcc e (Trace.delta Trace.void)
      (Trace.app Trace.void (Trace.delta Trace.void)) :=
    cons_pairs Trace.void (Trace.delta Trace.void)
  have h1a : convergesToAcc .apply (Trace.app (enc e) Trace.void)
      (Trace.app Trace.void Trace.void) :=
    (hU e Trace.void (Trace.app Trace.void Trace.void)).2 h1e
  have h2a : convergesToAcc .apply (Trace.app (enc e) (Trace.delta Trace.void))
      (Trace.app Trace.void (Trace.delta Trace.void)) :=
    (hU e (Trace.delta Trace.void)
      (Trace.app Trace.void (Trace.delta Trace.void))).2 h2e
  have h1 : convergesTo (quote (enc e)) Trace.void
      (Trace.app Trace.void Trace.void) :=
    (apply_tracks_quote (enc e) Trace.void _).1 h1a
  have h2 : convergesTo (quote (enc e)) (Trace.delta Trace.void)
      (Trace.app Trace.void (Trace.delta Trace.void)) :=
    (apply_tracks_quote (enc e) (Trace.delta Trace.void) _).1 h2a
  exact consVoid_outputs_obstruct_partialCode (quote (enc e)) ⟨h1, h2⟩

/-- The roadmap's declared self-numbering route: faithful coding, the existing
`.apply` as self-universal interpreter, and arbitrary specialization. -/
structure AccCodeSelfNumberingRoute : Type where
  decoderCorrect : ∀ c, decodeAcc? (encodeAcc c) = some c
  universalApply : IsUniversalAccWith encodeAcc .apply
  smn : AccCodeSMN

/-- The declared self-numbering route is uninhabited.  Its s-m-n component
lands, while the `.apply` universality component is semantically impossible. -/
theorem accCodeSelfNumberingRoute_impossible : ¬ Nonempty AccCodeSelfNumberingRoute := by
  rintro ⟨h⟩
  exact apply_not_universalAcc encodeAcc h.universalApply

/-- Terminal T3D package: faithful coding and arbitrary specialization exist;
the live `.apply` self-universality route is killed. -/
structure AccCodeSelfNumberingDisposition : Type where
  faithfulCode : ∀ c, decodeAcc? (encodeAcc c) = some c
  injectiveCode : Function.Injective encodeAcc
  arbitrarySMN : AccCodeSMN
  applyUniversalImpossible : ¬ IsUniversalAccWith encodeAcc .apply
  declaredRouteImpossible : ¬ Nonempty AccCodeSelfNumberingRoute

/-- Complete disposition of the current extended carrier. -/
def accCode_self_numbering_disposition : AccCodeSelfNumberingDisposition where
  faithfulCode := decodeAcc?_encode
  injectiveCode := encodeAcc_injective
  arbitrarySMN := accCode_smn
  applyUniversalImpossible := apply_not_universalAcc encodeAcc
  declaredRouteImpossible := accCodeSelfNumberingRoute_impossible

#check @encodeAcc
#check @decodeAcc?
#check @decodeAcc?_encode
#check @encodeAcc_injective
#check @smnAcc
#check @smnAcc_spec
#check @AccCodeSMN
#check @accCode_smn
#check @IsUniversalAccWith
#check @apply_tracks_quote
#check @consVoid_outputs_obstruct_partialCode
#check @apply_not_universalAcc
#check @AccCodeSelfNumberingRoute
#check @accCodeSelfNumberingRoute_impossible
#check @AccCodeSelfNumberingDisposition
#check @accCode_self_numbering_disposition
#print axioms decodeAcc?_encode
#print axioms encodeAcc_injective
#print axioms smnAcc_spec
#print axioms accCode_smn
#print axioms apply_tracks_quote
#print axioms consVoid_outputs_obstruct_partialCode
#print axioms apply_not_universalAcc
#print axioms accCodeSelfNumberingRoute_impossible
#print axioms accCode_self_numbering_disposition

end OperatorKO7.Meta.DistinctionBoundary.GodelPartial
