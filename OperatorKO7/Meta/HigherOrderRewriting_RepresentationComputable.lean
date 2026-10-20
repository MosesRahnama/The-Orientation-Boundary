import OperatorKO7.Meta.HigherOrderRewriting_EqualityUndecidable
import Mathlib.Logic.Denumerable

/-!
# Computable System T representatives for bounded halting

A computable map from partial-recursive codes to closed System T terms of type
`nat → nat` that represent the bounded-halting indicator. Lane L7a's pair-form
undecidability theorem is then applied with no remaining representation premise.

Relation: `Step` and its reflexive-transitive closure `StepStar` on the shared System T carrier.
Closure: reflexive-transitive reduction for representation; computability is Mathlib `Computable`.
Strategy: full contextual `Step`; no evaluator strategy is used in the representation theorem.
Trust: kernel-only plus Mathlib primitive-recursion and denumerable encodings, L7b
`primrec'_representable`, and L7a `systemT_natFun_equality_undecidable_of_representation_and_computable_code`.
Scope: partial-recursive codes mapped to closed System T terms of type `nat → nat`.

Premises that survive: none. `Primcodable SysTTerm` is an instance (item 2, via a
Denumerable bijection). The L7a weld is included (item 7).
-/

set_option autoImplicit false

namespace OperatorKO7.HigherOrderRewritingRepresentationComputable

open Encodable Denumerable
open List.Vector
open OperatorKO7.HigherOrderRewritingSystemT
open OperatorKO7.HigherOrderRewritingPrimrecRepresentation
open OperatorKO7.HigherOrderRewritingEqualityUndecidable
open Nat.Partrec.Code

/-! ## NameGate -/

#check @SysTTy
#check @SysTTerm
#check @natLit
#check @HasType
#check @HasType.app
#check @HasType.zero
#check @HasType.succ
#check @StepStar
#check @naryTy
#check @apps
#check @numerals
#check @RepresentsN
#check @primrec'_representable
#check @Represents
#check @primrecRepresentation
#check @haltStep
#check @haltStep_primrec
#check @ExtEqNat
#check @zeroFn
#check @systemT_natFun_equality_undecidable_of_representation_and_computable_code
#check @Nat.Partrec.Code.evaln
#check @Nat.Partrec.Code.primrec_evaln
#check @Nat.Partrec.Code.encodeCode
#check @Nat.Partrec.Code.ofNatCode
#check @Denumerable.ofNat
#check @Denumerable.ofNat_encode
#check @Denumerable.mk'
#check @Encodable.encodek
#check @Primrec
#check @Primrec.nat_iff
#check @Primrec₂
#check @Primrec.comp
#check @Primrec.ite
#check @Primrec.option_isSome
#check @Primrec.unpair
#check @Primrec.vector_head
#check @Primrec.vector_tail
#check @Primrec.nat_iterate
#check @Primrec.nat_add
#check @Primrec.nat_mul
#check @Primrec.encode
#check @Primrec.ofNat
#check @Primrec.ofNat_iff
#check @Primrec.encode_iff
#check @Primrec.to_comp
#check @Primrec₂.comp
#check @Primrec₂.natPair
#check @Nat.Primrec'.prim_iff₂
#check @Nat.Primrec'.of_prim
#check @Primcodable.ofEquiv
#check @Primcodable.ofDenumerable
#check @Primcodable.subtype
#check @Encodable
#check @Encodable.ofEquiv
#check @Computable
#check @Nat.unpair_left_le
#check @Nat.unpair_right_le
#check @Nat.pair

#synth Denumerable Nat.Partrec.Code
#synth Primcodable Nat.Partrec.Code

/-! ## Denumerable encodings (item 1 and item 2) -/

private def encodeTy : SysTTy → ℕ
  | .nat => 0
  | .arrow A B => Nat.pair (encodeTy A) (encodeTy B) + 1

private def ofNatTy : ℕ → SysTTy
  | 0 => .nat
  | n + 1 =>
    have _h1 : n.unpair.1 < n + 1 := Nat.lt_succ_of_le (Nat.unpair_left_le n)
    have _h2 : n.unpair.2 < n + 1 := Nat.lt_succ_of_le (Nat.unpair_right_le n)
    .arrow (ofNatTy n.unpair.1) (ofNatTy n.unpair.2)

private theorem ofNatTy_zero : ofNatTy 0 = .nat := by
  conv => lhs; unfold ofNatTy

private theorem ofNatTy_succ (n : ℕ) :
    ofNatTy (n + 1) = .arrow (ofNatTy n.unpair.1) (ofNatTy n.unpair.2) := by
  conv => lhs; unfold ofNatTy

private theorem encodeTy_ofNatTy (n : ℕ) : encodeTy (ofNatTy n) = n := by
  induction n using Nat.strong_induction_on with
  | h n IH =>
    cases n with
    | zero => rw [ofNatTy_zero, encodeTy]
    | succ n =>
      rw [ofNatTy_succ, encodeTy,
        IH _ (Nat.lt_succ_of_le (Nat.unpair_left_le n)),
        IH _ (Nat.lt_succ_of_le (Nat.unpair_right_le n)), Nat.pair_unpair]

private theorem ofNatTy_encodeTy : ∀ A, ofNatTy (encodeTy A) = A
  | .nat => by rw [encodeTy, ofNatTy_zero]
  | .arrow A B => by
    rw [encodeTy, ofNatTy_succ, Nat.unpair_pair, ofNatTy_encodeTy A, ofNatTy_encodeTy B]

instance instDenumerableSysTTy : Denumerable SysTTy :=
  Denumerable.mk' ⟨encodeTy, ofNatTy, ofNatTy_encodeTy, encodeTy_ofNatTy⟩

private def encodeVar (k : ℕ) : ℕ :=
  if k % 4 = 0 then 8 * (k / 4) + 1
  else if k % 4 = 1 then 8 * (k / 4) + 6
  else if k % 4 = 2 then 8 * (k / 4) + 7
  else 8 * (k / 4) + 8

private def encodeTm : SysTTerm → ℕ
  | .var k => encodeVar k
  | .lam A b => 8 * Nat.pair (encodeTy A) (encodeTm b) + 3
  | .app f a => 8 * Nat.pair (encodeTm f) (encodeTm a) + 4
  | .zero => 0
  | .succ t => 8 * encodeTm t + 2
  | .natrec z s n => 8 * Nat.pair (encodeTm z) (Nat.pair (encodeTm s) (encodeTm n)) + 5

private def ofNatTm : ℕ → SysTTerm
  | 0 => .zero
  | n + 1 =>
    have _hp : (n + 1) / 8 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by decide : 1 < 8)
    have _h1 : ((n + 1) / 8).unpair.1 < n + 1 :=
      Nat.lt_of_le_of_lt (Nat.unpair_left_le _) _hp
    have _h2 : ((n + 1) / 8).unpair.2 < n + 1 :=
      Nat.lt_of_le_of_lt (Nat.unpair_right_le _) _hp
    have _h21 : ((n + 1) / 8).unpair.2.unpair.1 < n + 1 :=
      Nat.lt_of_le_of_lt (Nat.le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) _hp
    have _h22 : ((n + 1) / 8).unpair.2.unpair.2 < n + 1 :=
      Nat.lt_of_le_of_lt (Nat.le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)) _hp
    if (n + 1) % 8 = 1 then .var (4 * ((n + 1) / 8))
    else if (n + 1) % 8 = 2 then .succ (ofNatTm ((n + 1) / 8))
    else if (n + 1) % 8 = 3 then
      .lam (ofNatTy ((n + 1) / 8).unpair.1) (ofNatTm ((n + 1) / 8).unpair.2)
    else if (n + 1) % 8 = 4 then
      .app (ofNatTm ((n + 1) / 8).unpair.1) (ofNatTm ((n + 1) / 8).unpair.2)
    else if (n + 1) % 8 = 5 then
      .natrec (ofNatTm ((n + 1) / 8).unpair.1)
        (ofNatTm ((n + 1) / 8).unpair.2.unpair.1)
        (ofNatTm ((n + 1) / 8).unpair.2.unpair.2)
    else if (n + 1) % 8 = 6 then .var (4 * ((n + 1) / 8) + 1)
    else if (n + 1) % 8 = 7 then .var (4 * ((n + 1) / 8) + 2)
    else .var (4 * ((n + 1) / 8) - 1)

private theorem ofNatTm_zero : ofNatTm 0 = .zero := by
  conv => lhs; unfold ofNatTm

private theorem ofNatTm_succ (n : ℕ) :
    ofNatTm (n + 1) =
      if (n + 1) % 8 = 1 then .var (4 * ((n + 1) / 8))
      else if (n + 1) % 8 = 2 then .succ (ofNatTm ((n + 1) / 8))
      else if (n + 1) % 8 = 3 then
        .lam (ofNatTy ((n + 1) / 8).unpair.1) (ofNatTm ((n + 1) / 8).unpair.2)
      else if (n + 1) % 8 = 4 then
        .app (ofNatTm ((n + 1) / 8).unpair.1) (ofNatTm ((n + 1) / 8).unpair.2)
      else if (n + 1) % 8 = 5 then
        .natrec (ofNatTm ((n + 1) / 8).unpair.1)
          (ofNatTm ((n + 1) / 8).unpair.2.unpair.1)
          (ofNatTm ((n + 1) / 8).unpair.2.unpair.2)
      else if (n + 1) % 8 = 6 then .var (4 * ((n + 1) / 8) + 1)
      else if (n + 1) % 8 = 7 then .var (4 * ((n + 1) / 8) + 2)
      else .var (4 * ((n + 1) / 8) - 1) := by
  conv => lhs; unfold ofNatTm

private theorem encodeVar_mul4 (q : ℕ) : encodeVar (4 * q) = 8 * q + 1 := by
  unfold encodeVar; split_ifs <;> omega

private theorem encodeVar_mul4_add1 (q : ℕ) : encodeVar (4 * q + 1) = 8 * q + 6 := by
  unfold encodeVar; split_ifs <;> omega

private theorem encodeVar_mul4_add2 (q : ℕ) : encodeVar (4 * q + 2) = 8 * q + 7 := by
  unfold encodeVar; split_ifs <;> omega

private theorem encodeVar_mul4_add3 (q : ℕ) : encodeVar (4 * q + 3) = 8 * q + 8 := by
  unfold encodeVar; split_ifs <;> omega

private theorem ofNatTm_mod1 (q : ℕ) : ofNatTm (8 * q + 1) = .var (4 * q) := by
  have hmod : (8 * q + 1) % 8 = 1 := by omega
  have hdiv : (8 * q + 1) / 8 = q := by omega
  rw [show 8 * q + 1 = (8 * q) + 1 from rfl, ofNatTm_succ, if_pos hmod, hdiv]

private theorem ofNatTm_mod2 (q : ℕ) : ofNatTm (8 * q + 2) = .succ (ofNatTm q) := by
  have hmod : (8 * q + 2) % 8 = 2 := by omega
  have hdiv : (8 * q + 2) / 8 = q := by omega
  rw [show 8 * q + 2 = (8 * q + 1) + 1 from rfl, ofNatTm_succ, if_neg (by omega),
    if_pos hmod, hdiv]

private theorem ofNatTm_mod3 (q : ℕ) :
    ofNatTm (8 * q + 3) = .lam (ofNatTy q.unpair.1) (ofNatTm q.unpair.2) := by
  have hmod : (8 * q + 3) % 8 = 3 := by omega
  have hdiv : (8 * q + 3) / 8 = q := by omega
  rw [show 8 * q + 3 = (8 * q + 2) + 1 from rfl, ofNatTm_succ, if_neg (by omega),
    if_neg (by omega), if_pos hmod, hdiv]

private theorem ofNatTm_mod4 (q : ℕ) :
    ofNatTm (8 * q + 4) = .app (ofNatTm q.unpair.1) (ofNatTm q.unpair.2) := by
  have hmod : (8 * q + 4) % 8 = 4 := by omega
  have hdiv : (8 * q + 4) / 8 = q := by omega
  rw [show 8 * q + 4 = (8 * q + 3) + 1 from rfl, ofNatTm_succ, if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos hmod, hdiv]

private theorem ofNatTm_mod5 (q : ℕ) :
    ofNatTm (8 * q + 5) =
      .natrec (ofNatTm q.unpair.1) (ofNatTm q.unpair.2.unpair.1)
        (ofNatTm q.unpair.2.unpair.2) := by
  have hmod : (8 * q + 5) % 8 = 5 := by omega
  have hdiv : (8 * q + 5) / 8 = q := by omega
  rw [show 8 * q + 5 = (8 * q + 4) + 1 from rfl, ofNatTm_succ, if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hmod, hdiv]

private theorem ofNatTm_mod6 (q : ℕ) : ofNatTm (8 * q + 6) = .var (4 * q + 1) := by
  have hmod : (8 * q + 6) % 8 = 6 := by omega
  have hdiv : (8 * q + 6) / 8 = q := by omega
  rw [show 8 * q + 6 = (8 * q + 5) + 1 from rfl, ofNatTm_succ, if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos hmod, hdiv]

private theorem ofNatTm_mod7 (q : ℕ) : ofNatTm (8 * q + 7) = .var (4 * q + 2) := by
  have hmod : (8 * q + 7) % 8 = 7 := by omega
  have hdiv : (8 * q + 7) / 8 = q := by omega
  rw [show 8 * q + 7 = (8 * q + 6) + 1 from rfl, ofNatTm_succ, if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos hmod, hdiv]

private theorem ofNatTm_mod0 (q : ℕ) : ofNatTm (8 * q + 8) = .var (4 * q + 3) := by
  have hmod : (8 * q + 8) % 8 = 0 := by omega
  have hdiv : (8 * q + 8) / 8 = q + 1 := by omega
  rw [show 8 * q + 8 = (8 * q + 7) + 1 from rfl, ofNatTm_succ, if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), hdiv]
  exact congrArg SysTTerm.var (by omega)

private theorem encodeTm_ofNatTm (n : ℕ) : encodeTm (ofNatTm n) = n := by
  induction n using Nat.strong_induction_on with
  | h n IH =>
    cases n with
    | zero => rw [ofNatTm_zero, encodeTm]
    | succ n =>
      have hp : (n + 1) / 8 < n + 1 :=
        Nat.div_lt_self (Nat.succ_pos n) (by decide : 1 < 8)
      have h1 : ((n + 1) / 8).unpair.1 < n + 1 :=
        Nat.lt_of_le_of_lt (Nat.unpair_left_le _) hp
      have h2 : ((n + 1) / 8).unpair.2 < n + 1 :=
        Nat.lt_of_le_of_lt (Nat.unpair_right_le _) hp
      have h21 : ((n + 1) / 8).unpair.2.unpair.1 < n + 1 :=
        Nat.lt_of_le_of_lt (Nat.le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) hp
      have h22 : ((n + 1) / 8).unpair.2.unpair.2 < n + 1 :=
        Nat.lt_of_le_of_lt (Nat.le_trans (Nat.unpair_right_le _) (Nat.unpair_right_le _)) hp
      have hsplit : (n + 1) % 8 = 0 ∨ (n + 1) % 8 = 1 ∨ (n + 1) % 8 = 2 ∨
          (n + 1) % 8 = 3 ∨ (n + 1) % 8 = 4 ∨ (n + 1) % 8 = 5 ∨
          (n + 1) % 8 = 6 ∨ (n + 1) % 8 = 7 := by omega
      have hdiv : n + 1 = 8 * ((n + 1) / 8) + (n + 1) % 8 := (Nat.div_add_mod (n + 1) 8).symm
      rcases hsplit with hr | hr | hr | hr | hr | hr | hr | hr
      · have hppos : 1 ≤ (n + 1) / 8 := by omega
        have hform : n + 1 = 8 * ((n + 1) / 8 - 1) + 8 := by omega
        rw [hform, ofNatTm_mod0, encodeTm, encodeVar_mul4_add3]
      · rw [hdiv, hr, ofNatTm_mod1, encodeTm, encodeVar_mul4]
      · rw [hdiv, hr, ofNatTm_mod2, encodeTm, IH _ hp]
      · rw [hdiv, hr, ofNatTm_mod3, encodeTm, encodeTy_ofNatTy, IH _ h2, Nat.pair_unpair]
      · rw [hdiv, hr, ofNatTm_mod4, encodeTm, IH _ h1, IH _ h2, Nat.pair_unpair]
      · rw [hdiv, hr, ofNatTm_mod5, encodeTm, IH _ h1, IH _ h21, IH _ h22,
          Nat.pair_unpair, Nat.pair_unpair]
      · rw [hdiv, hr, ofNatTm_mod6, encodeTm, encodeVar_mul4_add1]
      · rw [hdiv, hr, ofNatTm_mod7, encodeTm, encodeVar_mul4_add2]

private theorem ofNatTm_encodeTm : ∀ t, ofNatTm (encodeTm t) = t
  | .zero => by rw [encodeTm, ofNatTm_zero]
  | .var k => by
    rw [encodeTm]
    have hr : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
    rcases hr with hk | hk | hk | hk
    · have hk4 : k = 4 * (k / 4) := by omega
      rw [hk4, encodeVar_mul4, ofNatTm_mod1]
    · have hk4 : k = 4 * (k / 4) + 1 := by omega
      rw [hk4, encodeVar_mul4_add1, ofNatTm_mod6]
    · have hk4 : k = 4 * (k / 4) + 2 := by omega
      rw [hk4, encodeVar_mul4_add2, ofNatTm_mod7]
    · have hk4 : k = 4 * (k / 4) + 3 := by omega
      rw [hk4, encodeVar_mul4_add3, ofNatTm_mod0]
  | .succ t => by
    rw [encodeTm, ofNatTm_mod2, ofNatTm_encodeTm t]
  | .lam A b => by
    rw [encodeTm, ofNatTm_mod3, Nat.unpair_pair, ofNatTy_encodeTy, ofNatTm_encodeTm b]
  | .app f a => by
    rw [encodeTm, ofNatTm_mod4, Nat.unpair_pair, ofNatTm_encodeTm f, ofNatTm_encodeTm a]
  | .natrec z s t => by
    rw [encodeTm, ofNatTm_mod5, Nat.unpair_pair, Nat.unpair_pair, ofNatTm_encodeTm z,
      ofNatTm_encodeTm s, ofNatTm_encodeTm t]

instance instDenumerableSysTTerm : Denumerable SysTTerm :=
  Denumerable.mk' ⟨encodeTm, ofNatTm, ofNatTm_encodeTm, encodeTm_ofNatTm⟩

instance instPrimcodableSysTTy : Primcodable SysTTy :=
  Primcodable.ofDenumerable SysTTy

instance instPrimcodableSysTTerm : Primcodable SysTTerm :=
  Primcodable.ofDenumerable SysTTerm

private theorem encode_sysTTerm_eq : encode (α := SysTTerm) = encodeTm := rfl

private theorem ofNat_sysTTerm_eq (n : ℕ) : ofNat SysTTerm n = ofNatTm n :=
  ofNat_of_decode rfl

#synth Primcodable SysTTy
#synth Primcodable SysTTerm

example : encodeTm .zero = 0 := rfl
example : encodeTm (.succ .zero) = 2 := rfl
example : ofNatTm 0 = .zero := ofNatTm_zero
example : ofNatTm 1 = .var 0 := ofNatTm_mod1 0

/-! ## Primitive-recursive constructors and numerals -/

private theorem primrec_succ : Primrec SysTTerm.succ := by
  refine (Primrec.ofNat_iff (α := SysTTerm)).2 ?_
  refine Primrec.encode_iff.1 ?_
  have h : (fun n : ℕ => encode (SysTTerm.succ (ofNat SysTTerm n))) = fun n => 8 * n + 2 := by
    funext n
    rw [encode_sysTTerm_eq, ofNat_sysTTerm_eq, encodeTm, encodeTm_ofNatTm]
  rw [h]
  exact Primrec₂.comp Primrec.nat_add
    (Primrec₂.comp Primrec.nat_mul (Primrec.const 8) Primrec.id) (Primrec.const 2)

private theorem primrec_app : Primrec₂ SysTTerm.app := by
  refine (Primrec₂.ofNat_iff (α := SysTTerm) (β := SysTTerm)).2 ?_
  refine Primrec₂.encode_iff.1 ?_
  have h : (fun m n : ℕ => encode (SysTTerm.app (ofNat SysTTerm m) (ofNat SysTTerm n))) =
      fun m n => 8 * Nat.pair m n + 4 := by
    funext m n
    rw [encode_sysTTerm_eq, ofNat_sysTTerm_eq, ofNat_sysTTerm_eq, encodeTm, encodeTm_ofNatTm,
      encodeTm_ofNatTm]
  rw [h]
  exact Primrec₂.comp₂ Primrec.nat_add
    (Primrec₂.comp₂ Primrec.nat_mul (Primrec₂.const 8) Primrec₂.natPair) (Primrec₂.const 4)

private theorem natLit_iterate : ∀ n, natLit n = SysTTerm.succ^[n] SysTTerm.zero
  | 0 => rfl
  | n + 1 => by
    change SysTTerm.succ (natLit n) = SysTTerm.succ^[n + 1] SysTTerm.zero
    rw [natLit_iterate n]
    exact (Function.iterate_succ_apply' SysTTerm.succ n SysTTerm.zero).symm

private theorem primrec_natLit : Primrec natLit :=
  (Primrec.nat_iterate Primrec.id (Primrec.const SysTTerm.zero)
    (primrec_succ.comp₂ Primrec₂.right)).of_eq fun n => (natLit_iterate n).symm

/-! ## Binary bounded-halting indicator -/

/-- The binary bounded-halting indicator on a two-entry natural vector. -/
def haltStep₂ (v : List.Vector ℕ 2) : ℕ :=
  haltStep (ofNat Nat.Partrec.Code (head v)) (head (tail v))

/--
Proves: the two-argument bounded-halting indicator is pairing-free primitive recursive.
Does not prove: unbounded halting is decidable.
Relation: Mathlib primitive recursion, not System T reduction.
Closure: not applicable.
Strategy: compose the primitive-recursive fuel evaluator with code decoding and vector projections.
Trust: Mathlib `primrec_evaln`, `Primrec.ofNat`, vector projections, and Boolean case analysis.
Scope: all two-entry vectors of natural numbers.
-/
theorem haltStep₂_primrec' : Nat.Primrec' haltStep₂ := by
  have hc : Primrec fun v : List.Vector ℕ 2 => ofNat Nat.Partrec.Code (head v) :=
    (Primrec.ofNat Nat.Partrec.Code).comp Primrec.vector_head
  have hk : Primrec fun v : List.Vector ℕ 2 => head (tail v) :=
    Primrec.vector_head.comp Primrec.vector_tail
  have hArg : Primrec fun v : List.Vector ℕ 2 =>
      ((head (tail v), ofNat Nat.Partrec.Code (head v)), (0 : ℕ)) :=
    Primrec.pair (Primrec.pair hk hc) (Primrec.const 0)
  have hEval : Primrec fun v : List.Vector ℕ 2 =>
      evaln (head (tail v)) (ofNat Nat.Partrec.Code (head v)) 0 :=
    Nat.Partrec.Code.primrec_evaln.comp hArg
  have hSome : Primrec fun v : List.Vector ℕ 2 =>
      (evaln (head (tail v)) (ofNat Nat.Partrec.Code (head v)) 0).isSome :=
    Primrec.option_isSome.comp hEval
  have hPrim : Primrec haltStep₂ :=
    (Primrec.cond hSome (Primrec.const (1 : ℕ)) (Primrec.const (0 : ℕ))).of_eq fun v => by
      simp only [haltStep₂, haltStep]
      cases (evaln (head (tail v)) (ofNat Nat.Partrec.Code (head v)) 0).isSome <;> rfl
  exact Nat.Primrec'.of_prim hPrim

/-! ## One universal binary representative -/

/-- A closed System T representative of the binary bounded-halting indicator. -/
noncomputable def U : SysTTerm :=
  Classical.choose (primrec'_representable haltStep₂_primrec')

/--
Proves: `U` represents the binary bounded-halting indicator on every numeral pair.
Does not prove: that `U` is the unique such representative.
Relation: `StepStar` on full contextual `Step`.
Closure: reflexive-transitive.
Strategy: the L7b representation theorem for pairing-free primitive recursion.
Trust: `primrec'_representable` and `Classical.choice`.
Scope: all two-entry vectors of naturals.
-/
theorem U_represents : RepresentsN U haltStep₂ :=
  Classical.choose_spec (primrec'_representable haltStep₂_primrec')

/--
Proves: `U` is closed and has binary type `nat → nat → nat`.
Does not prove: any uniqueness or normal-form property of `U`.
Relation: `HasType` in the empty context.
Closure: not applicable.
Strategy: project the typing component of `U_represents`.
Trust: `U_represents`.
Scope: the chosen term `U`.
-/
theorem U_typed : HasType [] U (.arrow .nat (.arrow .nat .nat)) := by
  simpa [naryTy] using U_represents.1

/-! ## Computable code-to-term map -/

/-- The System T term for code `c`: apply the fixed representative `U` to the numeral of `c`. -/
noncomputable def codeTerm (c : Nat.Partrec.Code) : SysTTerm :=
  .app U (natLit (encode c))

/--
Proves: every Church-free numeral is well typed at `nat` in every context.
Does not prove: a cost bound for constructing the numeral.
Relation: `HasType`.
Closure: not applicable.
Strategy: induction on the numeral.
Trust: kernel-only.
Scope: every context and every `k : ℕ`.
-/
theorem natLit_typed {Γ : List SysTTy} (k : ℕ) : HasType Γ (natLit k) .nat := by
  induction k with
  | zero => exact HasType.zero
  | succ _k ih => exact HasType.succ ih

/--
Proves: `codeTerm c` is a closed term of type `nat → nat`.
Does not prove: uniqueness of this inhabitant.
Relation: `HasType` in the empty context.
Closure: not applicable.
Strategy: application of `U_typed` to a numeral.
Trust: `U_typed` and `natLit_typed`.
Scope: every partial-recursive code `c`.
-/
theorem codeTerm_typed (c : Nat.Partrec.Code) :
    HasType [] (codeTerm c) (.arrow .nat .nat) :=
  HasType.app U_typed (natLit_typed (encode c))

/--
Proves: `codeTerm c` represents the unary slice `haltStep c`.
Does not prove: a bound on the length of the witnessing `StepStar` reduction.
Relation: `Represents`, i.e. `HasType []` and `StepStar` of unary application.
Closure: reflexive-transitive.
Strategy: instantiate `U_represents` at the vector `[encode c, k]`.
Trust: `U_represents` and `Denumerable.ofNat_encode`.
Scope: every code `c` and every fuel `k`.
-/
theorem codeTerm_represents (c : Nat.Partrec.Code) :
    Represents (codeTerm c) (haltStep c) := by
  refine ⟨codeTerm_typed c, ?_⟩
  intro k
  have hv := U_represents.2 (cons (encode c) (cons k nil))
  have happs : apps U (numerals (cons (encode c) (cons k (nil : List.Vector ℕ 0)))) =
      .app (.app U (natLit (encode c))) (natLit k) := rfl
  have hhalt : haltStep₂ (cons (encode c) (cons k nil)) = haltStep c k := by
    simp [haltStep₂, ofNat_encode]
  simpa [happs, hhalt, codeTerm] using hv

/--
Proves: the map `codeTerm` is computable.
Does not prove: that `codeTerm` is primitive recursive as a map on codes (only computable).
Relation: Mathlib `Computable`, not System T reduction.
Closure: not applicable.
Strategy: `codeTerm = (fun n => app U (natLit n)) ∘ encode`; `natLit` by iterating successor,
application to the fixed term `U` is primitive recursive, and `encode` is primitive recursive.
Trust: `Primrec.to_comp`, `primrec_app`, `primrec_natLit`, `Primrec.encode`.
Scope: every `Nat.Partrec.Code`. No extra instance argument: `Primcodable SysTTerm` is an instance.
-/
theorem codeTerm_computable : Computable codeTerm := by
  have hAppU : Primrec fun n : ℕ => SysTTerm.app U (natLit n) :=
    Primrec₂.comp primrec_app (Primrec.const U) primrec_natLit
  exact (hAppU.comp (Primrec.encode (α := Nat.Partrec.Code))).to_comp

/-! ## Weld to L7a item 8 -/

/--
Proves: extensional equality of closed System T terms of type `nat → nat`, as a predicate on
term pairs, is not a `ComputablePred`.
Does not prove: syntactic equality of System T terms is undecidable as a separate statement
(that is the same predicate only after pairing with `zeroFn` in L7a).
Relation: `ExtEqNat` on `StepStar` joinability at every numeral.
Closure: reflexive-transitive joinability.
Strategy: feed `codeTerm` with `codeTerm_computable` and `codeTerm_represents` to L7a's
item-8 theorem.
Trust: L7a `systemT_natFun_equality_undecidable_of_representation_and_computable_code`,
and the `Primcodable SysTTerm` instance of this module.
Scope: every pair of `SysTTerm`. No remaining representation or encoding premise.
-/
theorem systemT_natFun_equality_undecidable :
    ¬ ComputablePred (fun p : SysTTerm × SysTTerm => ExtEqNat p.1 p.2) :=
  systemT_natFun_equality_undecidable_of_representation_and_computable_code
    ⟨codeTerm, codeTerm_computable, codeTerm_represents⟩

/-! ## Non-vacuity -/

/--
Proves: `codeTerm` of the zero code is well typed.
Does not prove: any reduction of that term.
Relation: `HasType`.
Closure: not applicable.
Strategy: specialise `codeTerm_typed`.
Trust: `codeTerm_typed`.
Scope: `Nat.Partrec.Code.zero`.
-/
theorem codeTerm_zero_typed :
    HasType [] (codeTerm Nat.Partrec.Code.zero) (.arrow .nat .nat) :=
  codeTerm_typed Nat.Partrec.Code.zero

/--
Proves: the zero code halts on input `0` at fuel `1`, so `haltStep` is `1`.
Does not prove: a closed form for `haltStep` at every fuel.
Relation: not a rewrite relation.
Closure: not applicable.
Strategy: unfolding of `evaln`.
Trust: kernel unfolding of `evaln`; also L7a `haltStep_zero_at_one`.
Scope: `Code.zero`, fuel `1`.
-/
theorem haltStep_zero_at_one_eval : haltStep Nat.Partrec.Code.zero 1 = 1 :=
  haltStep_zero_at_one

#print axioms codeTerm_represents
#print axioms codeTerm_computable
#print axioms systemT_natFun_equality_undecidable

end OperatorKO7.HigherOrderRewritingRepresentationComputable
