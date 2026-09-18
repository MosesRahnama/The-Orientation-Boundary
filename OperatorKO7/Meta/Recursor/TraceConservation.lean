import OperatorKO7.Meta.SchemaCanonicalTrace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Linear and affine conservation of canonical trace coordinates

Relation: the canonical trace coordinates `trace_ctr`, `trace_pay`, `trace_wraps` of
`SchemaCanonicalTrace.lean`, read at the live stages `i < k` of a trace of depth `k`.
Closure: not applicable (coordinate arithmetic on `Nat`, cast to `Int`).
Strategy: not applicable.
Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`.

Along the trace the counter drops by one and the payload and wrapper counts rise by one at
every live stage. An integer linear functional `a·ctr + b·pay + c·wraps` is therefore
conserved along a trace of depth `k` exactly when either `k = 0` (the vacuous trace) or
`a = b + c`; at every positive depth this reduces to `a = b + c`.  The conserved
coefficient vectors form a rank-two lattice spanned by `ctr + wraps` (constant `k`) and
`pay − wraps` (constant `1`), and `ctr` alone is not conserved.  This is the exact
statement behind the informal "conservation law" reading of the two published identities
`ctr + #G = K` and `pay = wraps + 1`. Adding a constant coefficient gives three
free conserved coefficients. Their readings have only two free parameters:
the depth coefficient and the constant value. Theorems below classify both
coefficient vectors and their equality after restriction to trace stages.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Recursor.TraceConservation

open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem

/-- Integer linear functional of the three canonical trace coordinates at stage `i` of a
trace of depth `k`. -/
def affineCoordinate (a b c : Int) (k i : Nat) : Int :=
  a * (trace_ctr k i : Int) + b * (trace_pay i : Int) + c * (trace_wraps i : Int)

/-- The functional is conserved along every live stage of a trace of depth `k`. -/
def ConservedAlong (a b c : Int) (k : Nat) : Prop :=
  ∀ i, i < k → affineCoordinate a b c k (i + 1) = affineCoordinate a b c k i

/-- One live step changes the functional by exactly `b + c − a`. -/
theorem affineCoordinate_step (a b c : Int) {k i : Nat} (hik : i < k) :
    affineCoordinate a b c k (i + 1) = affineCoordinate a b c k i - a + b + c := by
  have h1 : ((k - (i + 1) : Nat) : Int) = ((k - i : Nat) : Int) - 1 := by omega
  simp only [affineCoordinate, trace_ctr, trace_pay, trace_wraps]
  rw [h1]
  push_cast
  ring

/-- **Affine conservation criterion.** On a trace of positive depth an integer affine
functional of the coordinates is conserved along the live stages if and only if
`a = b + c`. -/
theorem conservedAlong_iff (a b c : Int) {k : Nat} (hk : 0 < k) :
    ConservedAlong a b c k ↔ a = b + c := by
  constructor
  · intro h
    have h0 := h 0 hk
    rw [affineCoordinate_step a b c hk] at h0
    linarith
  · intro h i hik
    rw [affineCoordinate_step a b c hik, h]
    ring

/-- **Unconditional affine conservation criterion.** The only exceptional depth is
`k = 0`, where there are no live stages and every functional is vacuously conserved.
At every nonzero depth, conservation is equivalent to the coefficient balance
`a = b + c`. This is the strongest theorem over all natural trace depths. -/
theorem conservedAlong_iff_zeroDepth_or_balance (a b c : Int) (k : Nat) :
    ConservedAlong a b c k ↔ k = 0 ∨ a = b + c := by
  constructor
  · intro h
    by_cases hk : k = 0
    · exact Or.inl hk
    · exact Or.inr ((conservedAlong_iff a b c (Nat.pos_of_ne_zero hk)).1 h)
  · rintro (hk | hab)
    · subst k
      intro i hi
      omega
    · intro i hik
      rw [affineCoordinate_step a b c hik, hab]
      ring

/-- `ctr + wraps` is conserved on every trace. -/
theorem ctrWraps_conserved (k : Nat) : ConservedAlong 1 0 1 k := by
  intro i hik
  rw [affineCoordinate_step 1 0 1 hik]
  ring

/-- `pay − wraps` is conserved on every trace. -/
theorem payMinusWraps_conserved (k : Nat) : ConservedAlong 0 1 (-1) k := by
  intro i hik
  rw [affineCoordinate_step 0 1 (-1) hik]
  ring

/-- The value of `ctr + wraps` at every stage `i ≤ k` is the depth `k`. -/
theorem ctrWraps_value {k i : Nat} (hik : i ≤ k) :
    affineCoordinate 1 0 1 k i = k := by
  have h1 : ((k - i : Nat) : Int) = (k : Int) - i := by omega
  simp only [affineCoordinate, trace_ctr, trace_pay, trace_wraps]
  rw [h1]
  ring

/-- The value of `pay − wraps` at every stage is `1`. -/
theorem payMinusWraps_value (k i : Nat) : affineCoordinate 0 1 (-1) k i = 1 := by
  simp only [affineCoordinate, trace_ctr, trace_pay, trace_wraps]
  push_cast
  ring

/-- **Rank two.** Every conserved functional on a trace of positive depth is a unique
integer combination `α·(ctr + wraps) + β·(pay − wraps)`, with `α = a` and `β = b`. -/
theorem conserved_decomposition {a b c : Int} {k : Nat} (hk : 0 < k)
    (h : ConservedAlong a b c k) :
    ∃! p : Int × Int, (a, b, c) = (p.1, p.2, p.1 - p.2) := by
  have hab : a = b + c := (conservedAlong_iff a b c hk).1 h
  refine ⟨(a, b), ?_, ?_⟩
  · show (a, b, c) = (a, b, a - b)
    rw [show a - b = c by omega]
  · intro p hp
    simp only [Prod.mk.injEq] at hp
    obtain ⟨ha, hb, _⟩ := hp
    ext
    · exact ha.symm
    · exact hb.symm

/-- The two basis functionals are integrally independent. -/
theorem basis_independent (α β : Int)
    (h : α * (1 : Int) + β * 0 = 0 ∧ α * 0 + β * 1 = 0 ∧ α * 1 + β * (-1) = 0) :
    α = 0 ∧ β = 0 := by
  obtain ⟨h1, h2, _⟩ := h
  constructor <;> linarith

/-- The criterion is not vacuous: the counter alone is not conserved on any trace of
positive depth. -/
theorem ctr_not_conserved {k : Nat} (hk : 0 < k) : ¬ ConservedAlong 1 0 0 k := by
  intro h
  have := (conservedAlong_iff 1 0 0 hk).1 h
  omega

/-- Nor is the payload count alone. -/
theorem pay_not_conserved {k : Nat} (hk : 0 < k) : ¬ ConservedAlong 0 1 0 k := by
  intro h
  have := (conservedAlong_iff 0 1 0 hk).1 h
  omega

/-! ## Constant offsets and observational equivalence -/

/-- The full integer affine reading, including its constant coefficient. -/
def fullAffineCoordinate (a b c d : Int) (k i : Nat) : Int :=
  affineCoordinate a b c k i + d

def FullAffineConservedAlong (a b c d : Int) (k : Nat) : Prop :=
  ∀ i, i < k → fullAffineCoordinate a b c d k (i + 1) =
    fullAffineCoordinate a b c d k i

def FullAffineConservedEverywhere (a b c d : Int) : Prop :=
  ∀ k, FullAffineConservedAlong a b c d k

theorem fullAffineCoordinate_step (a b c d : Int) {k i : Nat} (hik : i < k) :
    fullAffineCoordinate a b c d k (i + 1) =
      fullAffineCoordinate a b c d k i - a + b + c := by
  unfold fullAffineCoordinate
  rw [affineCoordinate_step a b c hik]
  ring

/-- A constant offset neither creates nor destroys stepwise conservation. -/
theorem fullAffineConservedAlong_iff_linear (a b c d : Int) (k : Nat) :
    FullAffineConservedAlong a b c d k ↔ ConservedAlong a b c k := by
  unfold FullAffineConservedAlong ConservedAlong fullAffineCoordinate
  simp only [add_left_inj]

theorem fullAffineConservedAlong_iff (a b c d : Int) (k : Nat) :
    FullAffineConservedAlong a b c d k ↔ k = 0 ∨ a = b + c := by
  rw [fullAffineConservedAlong_iff_linear, conservedAlong_iff_zeroDepth_or_balance]

theorem fullAffineConservedEverywhere_iff (a b c d : Int) :
    FullAffineConservedEverywhere a b c d ↔ a = b + c := by
  constructor
  · intro h
    have h1 := (fullAffineConservedAlong_iff a b c d 1).1 (h 1)
    exact h1.resolve_left (by decide)
  · intro h k
    exact (fullAffineConservedAlong_iff a b c d k).2 (Or.inr h)

/-- The three coefficients that determine a reading on valid trace stages. -/
theorem fullAffineCoordinate_normalForm (a b c d : Int) {k i : Nat} (hik : i ≤ k) :
    fullAffineCoordinate a b c d k i =
      a * (k : Int) + (b + c - a) * (i : Int) + (b + d) := by
  have hki : ((k - i : Nat) : Int) = (k : Int) - i := by omega
  simp only [fullAffineCoordinate, affineCoordinate, trace_ctr, trace_pay, trace_wraps]
  rw [hki]
  push_cast
  ring

/-- Conservation has three independent coefficient parameters before restriction
to the trace equations. -/
theorem fullAffine_conservation_parameterization (a b c d : Int) :
    FullAffineConservedEverywhere a b c d ↔
      ∃! p : Int × Int × Int, (a, b, c, d) =
        (p.1, p.2.1, p.1 - p.2.1, p.2.2) := by
  rw [fullAffineConservedEverywhere_iff]
  constructor
  · intro hab
    refine ⟨(a, b, d), ?_, ?_⟩
    · show (a, b, c, d) = (a, b, a - b, d)
      rw [show a - b = c by omega]
    · rintro ⟨α, β, δ⟩ hp
      simp only [Prod.mk.injEq] at hp ⊢
      exact ⟨hp.1.symm, hp.2.1.symm, hp.2.2.2.symm⟩
  · rintro ⟨⟨α, β, δ⟩, hp, _⟩
    simp only [Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl, rfl, rfl⟩
    ring

/-- Equal readings on every valid stage, across all depths. -/
def TraceEquivalent (a b c d a' b' c' d' : Int) : Prop :=
  ∀ k i, i ≤ k →
    fullAffineCoordinate a b c d k i = fullAffineCoordinate a' b' c' d' k i

/-- Three concrete stage probes determine all trace readings. -/
theorem traceEquivalent_iff (a b c d a' b' c' d' : Int) :
    TraceEquivalent a b c d a' b' c' d' ↔
      a = a' ∧ b + c = b' + c' ∧ b + d = b' + d' := by
  constructor
  · intro h
    have h00 := h 0 0 (by omega)
    have h10 := h 1 0 (by omega)
    have h11 := h 1 1 (by omega)
    norm_num [fullAffineCoordinate, affineCoordinate, trace_ctr, trace_pay, trace_wraps]
      at h00 h10 h11
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨ha, hbc, hbd⟩ k i hik
    rw [fullAffineCoordinate_normalForm a b c d hik,
      fullAffineCoordinate_normalForm a' b' c' d' hik, ha, hbc, hbd]

/-- The only coefficient ambiguity adds a multiple of pay - wraps - 1. -/
theorem traceEquivalent_iff_offsetShift (a b c d a' b' c' d' : Int) :
    TraceEquivalent a b c d a' b' c' d' ↔
      ∃ z : Int, a' = a ∧ b' = b + z ∧ c' = c - z ∧ d' = d - z := by
  rw [traceEquivalent_iff]
  constructor
  · rintro ⟨ha, hbc, hbd⟩
    exact ⟨b' - b, ha.symm, by omega, by omega, by omega⟩
  · rintro ⟨z, ha, hb, hc, hd⟩
    exact ⟨ha.symm, by omega, by omega⟩

/-- Every reading has a unique expression in depth, stage and constant value. -/
theorem fullAffine_observation_parameterization (a b c d : Int) :
    ∃! q : Int × Int × Int, ∀ k i : Nat, i ≤ k →
      fullAffineCoordinate a b c d k i =
        q.1 * (k : Int) + q.2.1 * (i : Int) + q.2.2 := by
  refine ⟨(a, b + c - a, b + d), ?_, ?_⟩
  · intro k i hik
    exact fullAffineCoordinate_normalForm a b c d hik
  · rintro ⟨α, s, v⟩ h
    have h00 := h 0 0 (by omega)
    have h10 := h 1 0 (by omega)
    have h11 := h 1 1 (by omega)
    norm_num [fullAffineCoordinate, affineCoordinate, trace_ctr, trace_pay, trace_wraps]
      at h00 h10 h11
    simp only [Prod.mk.injEq]
    exact ⟨by linarith, by linarith, by linarith⟩

/-- Conserved observations have two parameters although conserved coefficient
vectors have three. -/
theorem fullAffine_conserved_observation_parameterization (a b c d : Int) :
    FullAffineConservedEverywhere a b c d ↔
      ∃! p : Int × Int, ∀ k i : Nat, i ≤ k →
        fullAffineCoordinate a b c d k i = p.1 * (k : Int) + p.2 := by
  constructor
  · intro h
    have hab := (fullAffineConservedEverywhere_iff a b c d).1 h
    refine ⟨(a, b + d), ?_, ?_⟩
    · intro k i hik
      rw [fullAffineCoordinate_normalForm a b c d hik]
      have hs : b + c - a = 0 := by omega
      simp [hs]
    · rintro ⟨α, v⟩ hp
      have h00 := hp 0 0 (by omega)
      have h10 := hp 1 0 (by omega)
      norm_num [fullAffineCoordinate, affineCoordinate, trace_ctr, trace_pay, trace_wraps]
        at h00 h10
      simp only [Prod.mk.injEq]
      exact ⟨by linarith, by linarith⟩
  · rintro ⟨p, hp, _⟩ k i hik
    rw [hp k (i + 1) (by omega), hp k i (by omega)]

/-- Equality of conserved readings is determined by the depth coefficient and
the value at depth zero. -/
theorem conserved_trace_equivalence_iff (a b c d a' b' c' d' : Int) :
    FullAffineConservedEverywhere a b c d ∧ TraceEquivalent a b c d a' b' c' d' ↔
      a = b + c ∧ a' = b' + c' ∧ a = a' ∧ b + d = b' + d' := by
  rw [fullAffineConservedEverywhere_iff, traceEquivalent_iff]
  constructor
  · rintro ⟨hab, ha, hbc, hbd⟩
    exact ⟨hab, by omega, ha, hbd⟩
  · rintro ⟨hab, hab', ha, hbd⟩
    exact ⟨hab, ha, by omega, hbd⟩

/-- Distinct coefficient vectors can give the same zero reading even outside
the live-stage range. -/
theorem nonzero_coefficient_zero_reading :
    ((0, 1, -1, -1) : Int × Int × Int × Int) ≠ (0, 0, 0, 0) ∧
      ∀ k i, fullAffineCoordinate 0 1 (-1) (-1) k i = 0 := by
  refine ⟨by decide, ?_⟩
  intro k i
  simp only [fullAffineCoordinate, affineCoordinate, trace_ctr, trace_pay, trace_wraps]
  push_cast
  ring

theorem constantOffset_conserved (d : Int) :
    FullAffineConservedEverywhere 0 0 0 d :=
  (fullAffineConservedEverywhere_iff 0 0 0 d).2 rfl

theorem constantOffset_value (d : Int) (k i : Nat) :
    fullAffineCoordinate 0 0 0 d k i = d := by
  simp [fullAffineCoordinate, affineCoordinate]

theorem offset_cannot_conserve_counter (d : Int) {k : Nat} (hk : 0 < k) :
    ¬ FullAffineConservedAlong 1 0 0 d k := by
  rw [fullAffineConservedAlong_iff_linear]
  exact ctr_not_conserved hk

end OperatorKO7.Meta.Recursor.TraceConservation
