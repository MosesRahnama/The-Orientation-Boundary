import OperatorKO7.Meta.MPO_FullStep

/-!
# Proof-theoretic upper bound for the KO7-specialized MPO proof

This file does not change the MPO development. It packages an explicit ordinal
envelope for the existing fixed-signature ranking from the full-step MPO module.

The point is reviewability: the KO7-specialized MPO proof is a direct ordinal
ranking argument on a fixed 7-constructor signature, and its rank lands below
`veblen 7 0`. This gives a concrete upper bound for the proof-strength row in
the paper without claiming a metatheoretic classification for generic path
orders.

The envelope lies below the Feferman-Schuette ordinal: `gamma0` is the least
fixed point of `a ↦ veblen a 0` reached from `0` by iteration, it equals
Mathlib's `Ordinal.gamma 0` (`gamma0_eq_gamma_zero`), it is a fixed point
(`veblen_gamma0_zero`) and the least one (`gamma0_le_of_veblen_le`), and
`veblen 7 0 < gamma0` (`veblen_seven_zero_lt_gamma0`, `mpoVeblenBound_lt_gamma0`).
`wf_StepRev_mpo_below_veblen7_below_gamma0` states the ranking below `veblen 7 0`
together with the comparison `veblen 7 0 < gamma0`.
-/

namespace OperatorKO7.MPOProofTheoreticBound

open scoped Ordinal
open OperatorKO7.Trace
open OperatorKO7.MetaMPO

/-- Explicit ordinal envelope for the KO7-specialized MPO ranking. -/
@[simp] noncomputable def mpoVeblenBound : Ordinal.{0} := Ordinal.veblen 7 0

lemma mpoVeblenBound_gt_one : (1 : Ordinal.{0}) < mpoVeblenBound := by
  simpa [mpoVeblenBound] using
    (veblen_gt_one_of_pos (k := (7 : Ordinal.{0})) (x := 0)
      (by exact_mod_cast (show 0 < (7 : Nat) by decide)))

lemma mpoVeblenBound_fixed :
    (ω : Ordinal.{0}) ^ mpoVeblenBound = mpoVeblenBound := by
  simpa [mpoVeblenBound] using
    (veblen_fixed_of_pos (k := (7 : Ordinal.{0})) (x := 0)
      (by exact_mod_cast (show 0 < (7 : Nat) by decide)))

lemma mpoVeblenBound_isSuccLimit :
    Order.IsSuccLimit mpoVeblenBound := by
  simpa [mpoVeblenBound] using
    (veblen_isSuccLimit_of_pos (k := (7 : Ordinal.{0})) (x := 0)
      (by exact_mod_cast (show 0 < (7 : Nat) by decide)))

lemma rank_lt_seven (s : Sym) : rank s < 7 := by
  cases s <;> decide

lemma rank_lt_seven_ord (s : Sym) : ((rank s : Nat) : Ordinal.{0}) < (7 : Ordinal.{0}) := by
  exact_mod_cast rank_lt_seven s

lemma veblen_lt_mpoVeblenBound_of_rank_lt
    {k p : Ordinal.{0}} (hk : k < 7) (hp : p < mpoVeblenBound) :
    Ordinal.veblen k p < mpoVeblenBound := by
  dsimp [mpoVeblenBound]
  exact (Ordinal.veblen_lt_veblen_iff).2
    (Or.inr (Or.inl ⟨hk, by simpa [mpoVeblenBound] using hp⟩))

/-- Every KO7-specialized MPO ordinal rank lies below the fixed envelope
`veblen 7 0`. -/
theorem mpoOrd_lt_mpoVeblenBound : ∀ t : Trace, mpoOrd t < mpoVeblenBound
  | void => by
      have hzero : (0 : Ordinal.{0}) < mpoVeblenBound := by
        have h0 : (0 : Ordinal.{0}) < 1 := by
          exact_mod_cast (show 0 < (1 : Nat) by decide)
        exact h0.trans mpoVeblenBound_gt_one
      have hk : ((rank (sym void)) : Ordinal.{0}) < (7 : Ordinal.{0}) := by
        change ((rank Sym.void : Nat) : Ordinal.{0}) < (7 : Ordinal.{0})
        exact rank_lt_seven_ord Sym.void
      simpa [mpoOrd, payloadOrd, mpoVeblenBound, sym, rank] using
        (veblen_lt_mpoVeblenBound_of_rank_lt hk hzero)
  | delta t => by
      have hpayload : Order.succ (mpoOrd t) < mpoVeblenBound := by
        exact mpoVeblenBound_isSuccLimit.succ_lt (mpoOrd_lt_mpoVeblenBound t)
      have hk : ((rank (sym (delta t))) : Ordinal.{0}) < (7 : Ordinal.{0}) := by
        change ((rank Sym.delta : Nat) : Ordinal.{0}) < (7 : Ordinal.{0})
        exact rank_lt_seven_ord Sym.delta
      simpa [mpoOrd, payloadOrd, mpoVeblenBound, sym, rank] using
        (veblen_lt_mpoVeblenBound_of_rank_lt hk hpayload)
  | integrate t => by
      have hpayload : Order.succ (mpoOrd t) < mpoVeblenBound := by
        exact mpoVeblenBound_isSuccLimit.succ_lt (mpoOrd_lt_mpoVeblenBound t)
      have hk : ((rank (sym (integrate t))) : Ordinal.{0}) < (7 : Ordinal.{0}) := by
        change ((rank Sym.integrate : Nat) : Ordinal.{0}) < (7 : Ordinal.{0})
        exact rank_lt_seven_ord Sym.integrate
      simpa [mpoOrd, payloadOrd, mpoVeblenBound, sym, rank] using
        (veblen_lt_mpoVeblenBound_of_rank_lt hk hpayload)
  | merge a b => by
      have hpayload :
          pairPayload (mpoOrd a) (mpoOrd b) < mpoVeblenBound := by
        exact pairPayload_lt_of_lt
          (mpoOrd_lt_mpoVeblenBound a)
          (mpoOrd_lt_mpoVeblenBound b)
          mpoVeblenBound_isSuccLimit mpoVeblenBound_fixed
      have hk : ((rank (sym (merge a b))) : Ordinal.{0}) < (7 : Ordinal.{0}) := by
        change ((rank Sym.merge : Nat) : Ordinal.{0}) < (7 : Ordinal.{0})
        exact rank_lt_seven_ord Sym.merge
      simpa [mpoOrd, payloadOrd, mpoVeblenBound, sym, rank] using
        (veblen_lt_mpoVeblenBound_of_rank_lt hk hpayload)
  | app a b => by
      have hpayload :
          pairPayload (mpoOrd a) (mpoOrd b) < mpoVeblenBound := by
        exact pairPayload_lt_of_lt
          (mpoOrd_lt_mpoVeblenBound a)
          (mpoOrd_lt_mpoVeblenBound b)
          mpoVeblenBound_isSuccLimit mpoVeblenBound_fixed
      have hk : ((rank (sym (app a b))) : Ordinal.{0}) < (7 : Ordinal.{0}) := by
        change ((rank Sym.app : Nat) : Ordinal.{0}) < (7 : Ordinal.{0})
        exact rank_lt_seven_ord Sym.app
      simpa [mpoOrd, payloadOrd, mpoVeblenBound, sym, rank] using
        (veblen_lt_mpoVeblenBound_of_rank_lt hk hpayload)
  | recΔ b s n => by
      have hpayload :
          triplePayload (mpoOrd b) (mpoOrd s) (mpoOrd n) < mpoVeblenBound := by
        exact triplePayload_lt_of_lt
          (mpoOrd_lt_mpoVeblenBound b)
          (mpoOrd_lt_mpoVeblenBound s)
          (mpoOrd_lt_mpoVeblenBound n)
          mpoVeblenBound_isSuccLimit mpoVeblenBound_fixed
      have hk : ((rank (sym (recΔ b s n))) : Ordinal.{0}) < (7 : Ordinal.{0}) := by
        change ((rank Sym.recΔ : Nat) : Ordinal.{0}) < (7 : Ordinal.{0})
        exact rank_lt_seven_ord Sym.recΔ
      simpa [mpoOrd, payloadOrd, mpoVeblenBound, sym, rank] using
        (veblen_lt_mpoVeblenBound_of_rank_lt hk hpayload)
  | eqW a b => by
      have hpayload :
          pairPayload (mpoOrd a) (mpoOrd b) < mpoVeblenBound := by
        exact pairPayload_lt_of_lt
          (mpoOrd_lt_mpoVeblenBound a)
          (mpoOrd_lt_mpoVeblenBound b)
          mpoVeblenBound_isSuccLimit mpoVeblenBound_fixed
      have hk : ((rank (sym (eqW a b))) : Ordinal.{0}) < (7 : Ordinal.{0}) := by
        change ((rank Sym.eqW : Nat) : Ordinal.{0}) < (7 : Ordinal.{0})
        exact rank_lt_seven_ord Sym.eqW
      simpa [mpoOrd, payloadOrd, mpoVeblenBound, sym, rank] using
        (veblen_lt_mpoVeblenBound_of_rank_lt hk hpayload)

/-- The fixed-signature MPO proof is witnessed by an ordinal ranking into the
initial segment below `veblen 7 0`. -/
theorem wf_StepRev_mpo_below_veblen7 :
    ∃ ρ : Trace → Ordinal.{0},
      (∀ t, ρ t < mpoVeblenBound) ∧
      (∀ {a b : Trace}, Step a b → ρ b < ρ a) := by
  refine ⟨mpoOrd, ?_, ?_⟩
  · intro t
    exact mpoOrd_lt_mpoVeblenBound t
  · intro a b hstep
    exact mpoOrd_strict_of_mpo (mpo_orients_step hstep)

/-! ## The envelope below the Feferman-Schuette ordinal -/

/-- The Feferman-Schuette ordinal `Γ₀`, written as the least fixed point of
`a ↦ veblen a 0` above `0` (Mathlib `Ordinal.nfp`).

Proves: nothing; a definition.
Does not prove: any proof-theoretic classification of path orders.
Relation: not applicable (an ordinal constant).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; Mathlib ordinal library.
Scope: the universe-`0` ordinals of the MPO envelope. -/
noncomputable def gamma0 : Ordinal.{0} := Ordinal.nfp (fun a => Ordinal.veblen a 0) 0

/-- Identity of `gamma0` with Mathlib's Feferman-Schuette ordinal `Ordinal.gamma 0`.

Proves: `gamma0 = Ordinal.gamma 0`.
Does not prove: any statement about the KO7 rewrite relation.
Relation: not applicable (ordinal equality).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; Mathlib `Ordinal.gamma0_eq_nfp`.
Scope: universe `0`. -/
theorem gamma0_eq_gamma_zero : gamma0 = Ordinal.gamma 0 := by
  rw [gamma0, Ordinal.gamma0_eq_nfp]

/-- `gamma0` is a fixed point of `a ↦ veblen a 0`.

Proves: `Ordinal.veblen gamma0 0 = gamma0`.
Does not prove: leastness (see `gamma0_le_of_veblen_le`).
Relation: not applicable (ordinal equality).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; Mathlib `Ordinal.veblen_gamma_zero`.
Scope: universe `0`. -/
theorem veblen_gamma0_zero : Ordinal.veblen gamma0 0 = gamma0 := by
  rw [gamma0_eq_gamma_zero]
  exact Ordinal.veblen_gamma_zero 0

/-- `gamma0` is the least fixed point of `a ↦ veblen a 0`: every ordinal `o` with
`veblen o 0 ≤ o` lies above it.

Proves: `Ordinal.veblen o 0 ≤ o → gamma0 ≤ o` for every universe-`0` ordinal `o`.
Does not prove: anything about ordinals that are not fixed points.
Relation: not applicable (ordinal order).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; Mathlib `Ordinal.gamma0_le_of_veblen_le`.
Scope: universe `0`. -/
theorem gamma0_le_of_veblen_le {o : Ordinal.{0}} (h : Ordinal.veblen o 0 ≤ o) :
    gamma0 ≤ o := by
  rw [gamma0_eq_gamma_zero]
  exact Ordinal.gamma0_le_of_veblen_le h

/-- The finite index `7` lies below `ε₀ = veblen 1 0`.

Proves: `(7 : Ordinal) < Ordinal.veblen 1 0`.
Does not prove: any bound on the MPO ranks themselves.
Relation: not applicable (ordinal order).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; Mathlib `Ordinal.natCast_lt_epsilon`.
Scope: universe `0`. -/
theorem seven_lt_epsilon0 : (7 : Ordinal.{0}) < Ordinal.veblen 1 0 := by
  simpa using Ordinal.natCast_lt_epsilon 7 0

/-- `φ₇(0) < Γ₀`: the third iterate of `a ↦ veblen a 0` from `0` is `veblen ε₀ 0`, which
lies above `veblen 7 0` because `7 < ε₀`, and every iterate lies below `Γ₀`.

Proves: `Ordinal.veblen 7 0 < gamma0`.
Does not prove: any statement about generic path orders.
Relation: not applicable (ordinal order).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; Mathlib Veblen hierarchy.
Scope: universe `0`; Veblen indexing with `veblen 0 = fun a => ω ^ a`. -/
theorem veblen_seven_zero_lt_gamma0 : Ordinal.veblen 7 0 < gamma0 := by
  have h1 : Ordinal.veblen 7 0 < Ordinal.veblen (Ordinal.veblen 1 0) 0 :=
    Ordinal.veblen_zero_lt_veblen_zero.2 seven_lt_epsilon0
  have h2 : Ordinal.veblen (Ordinal.veblen 1 0) 0 < gamma0 := by
    have h := Ordinal.iterate_veblen_lt_gamma0 3
    rw [← gamma0_eq_gamma_zero] at h
    have e : (fun a => Ordinal.veblen a 0)^[3] 0 = Ordinal.veblen (Ordinal.veblen 1 0) 0 := by
      simp [Function.iterate_succ, Ordinal.veblen_zero_apply]
    rwa [e] at h
  exact h1.trans h2

/-- The MPO envelope lies below the Feferman-Schuette ordinal.

Proves: `mpoVeblenBound < gamma0`.
Does not prove: any classification of the proof strength of generic path orders.
Relation: not applicable (ordinal order).
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; Mathlib Veblen hierarchy.
Scope: the fixed seven-constructor MPO envelope. -/
theorem mpoVeblenBound_lt_gamma0 : mpoVeblenBound < gamma0 := by
  simpa [mpoVeblenBound] using veblen_seven_zero_lt_gamma0

/-- The fixed-signature MPO proof ranks every KO7 trace below `φ₇(0)`, the rank strictly
decreases along every root step, and `φ₇(0) < Γ₀`.

Proves: `∃ ρ`, `ρ t < mpoVeblenBound` for every trace `t`, `mpoVeblenBound < gamma0`, and
`ρ b < ρ a` for every `Step a b`.
Does not prove: a decrease under contexts; a classification of generic path orders.
Relation: `Step` (the full kernel relation, eight rules).
Closure: root.
Strategy: full.
Trust: kernel-only; Mathlib ordinal library.
Scope: the seven-constructor KO7 signature with the fixed MPO precedence of
the full-step MPO module; witness `ρ = mpoOrd`. -/
theorem wf_StepRev_mpo_below_veblen7_below_gamma0 :
    ∃ ρ : Trace → Ordinal.{0},
      (∀ t, ρ t < mpoVeblenBound) ∧ mpoVeblenBound < gamma0 ∧
      (∀ {a b : Trace}, Step a b → ρ b < ρ a) := by
  obtain ⟨ρ, hbound, hstep⟩ := wf_StepRev_mpo_below_veblen7
  exact ⟨ρ, hbound, mpoVeblenBound_lt_gamma0, hstep⟩

end OperatorKO7.MPOProofTheoreticBound
