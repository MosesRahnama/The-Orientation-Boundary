import OperatorKO7.Meta.Methods.OrientationClosure.FreeDerivationalComplexity
import OperatorKO7.Meta.MPO_FullStep
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.SetTheory.Ordinal.FixedPoint
import Mathlib.Tactic

/-!
# Ordinal calibration of the escapes on the free schema

Natural-valued ranks. If a natural-valued function strictly decreases along a well-founded
relation, the ordinal height of every element is at most its value (`rank_le_natRank`), so every
height is finite. On the free recursor the polynomial escape is of this kind (the weight `qw`
drops on every contextual step), and so is the dependency-pair escape (the call rank drops by one
on every recursive call). Both relations reach every finite height, so each has height exactly
`ω` (`ctx_calibrated_omega`, `iSup_ctxHeight`, `call_calibrated_omega`).

The MPO escape. `MPO_FullStep.lean` ranks KO7 traces by `veblen (precedence) (payload)`. The same
path order and ranking at the four schema symbols, with precedence `zero < succ < wrap < recur`,
orient both free root rules (`freeMpo_orients_rootStep`); every comparison of the path order
decreases the ranking (`freeMpoOrd_strict_of_mpo`); every value lies below `veblen 4 0`
(`freeMpoOrd_lt_veblen_four`), and the values are cofinal in it (`iSup_freeMpoOrd`), because
`veblen 4 0` is the least fixed point of `veblen 3` and the tower
`recur (recur (... zero) zero zero) zero zero` passes every iterate of `veblen 3` at `0`.
The bound is a property of the ranking that the MPO proof uses, not of the height of the root
relation.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.FreeOrdinalCalibration

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.ProcessorSemantics
open OperatorKO7.Methods.OrientationClosure.MethodRowsSubstrate
open OperatorKO7.Methods.OrientationClosure.SourceChainSoundness
open OperatorKO7.Methods.OrientationClosure.FreeDerivationalComplexity
open OperatorKO7.MetaMPO (pairPayload triplePayload left_lt_pairPayload right_lt_pairPayload
  pairPayload_lt_of_lt first_lt_triplePayload second_lt_triplePayload third_lt_triplePayload
  triplePayload_lt_of_lt triplePayload_strictMono_right veblen_fixed_of_pos veblen_gt_one_of_pos
  veblen_isSuccLimit_of_pos lt_veblen_of_nonlimit)
open scoped Ordinal

/-! ## Natural-valued ranks -/

section NatRank

variable {α : Type} (r : α → α → Prop) [IsWellFounded α r]

/-- A natural-valued function that strictly decreases along `r` bounds the ordinal height. -/
theorem rank_le_natRank (f : α → Nat) (hf : ∀ a b, r a b → f a < f b) (a : α) :
    IsWellFounded.rank r a ≤ (f a : Ordinal) := by
  refine IsWellFounded.induction r (C := fun a => IsWellFounded.rank r a ≤ (f a : Ordinal)) a
    (fun x ih => ?_)
  show IsWellFounded.rank r x ≤ (f x : Ordinal)
  rw [IsWellFounded.rank_eq]
  refine Ordinal.iSup_le fun y => ?_
  have h1 : IsWellFounded.rank r y.1 ≤ (f y.1 : Ordinal) := ih y.1 y.2
  have h2 : ((f y.1 : Nat) : Ordinal) < (f x : Ordinal) := by exact_mod_cast hf y.1 x y.2
  exact Order.succ_le_of_lt (h1.trans_lt h2)

/-- Under a natural-valued decreasing function every height is finite. -/
theorem rank_lt_omega_of_natRank (f : α → Nat) (hf : ∀ a b, r a b → f a < f b) (a : α) :
    IsWellFounded.rank r a < ω :=
  (rank_le_natRank r f hf a).trans_lt (Ordinal.nat_lt_omega0 _)

/-- A chain of `m` steps from `a` to `c` lifts the height of `a` at least `m` above that of `c`. -/
theorem rank_add_le_of_relPow {R : α → α → Prop} (hR : ∀ a b, R a b → r b a) {m : Nat} {a c : α}
    (h : RelPow R m a c) : IsWellFounded.rank r c + (m : Ordinal) ≤ IsWellFounded.rank r a := by
  induction h with
  | zero => simp
  | @succ n a' b' c' _ hbc ih =>
    have h1 : IsWellFounded.rank r c' + 1 ≤ IsWellFounded.rank r b' := by
      rw [Ordinal.add_one_eq_succ]
      exact Order.succ_le_of_lt (IsWellFounded.rank_lt_of_rel (hR b' c' hbc))
    calc IsWellFounded.rank r c' + ((n + 1 : Nat) : Ordinal)
        = IsWellFounded.rank r c' + 1 + (n : Ordinal) := by
          rw [add_assoc, Ordinal.one_add_natCast, Order.succ_eq_add_one]
      _ ≤ IsWellFounded.rank r b' + (n : Ordinal) := add_le_add_right h1 _
      _ ≤ IsWellFounded.rank r a' := ih

end NatRank

/-! ## The polynomial escape is calibrated at `ω` -/

/-- The reversed contextual relation of the free recursor. -/
def CtxRev (u t : FreeTerm Nat) : Prop := ContextStep t u

instance : IsWellFounded (FreeTerm Nat) CtxRev :=
  ⟨FreePolynomialTermination.main_free_contextual_termination Nat⟩

/-- The height of a free term under contextual rewriting. -/
noncomputable def ctxHeight (t : FreeTerm Nat) : Ordinal := IsWellFounded.rank CtxRev t

theorem ctxHeight_le_qw (t : FreeTerm Nat) : ctxHeight t ≤ (qw t : Ordinal) :=
  rank_le_natRank CtxRev qw (fun _ _ h => qw_contextStep h) t

theorem ctxHeight_lt_omega (t : FreeTerm Nat) : ctxHeight t < ω :=
  rank_lt_omega_of_natRank CtxRev qw (fun _ _ h => qw_contextStep h) t

theorem le_ctxHeight_of_relPow {m : Nat} {t u : FreeTerm Nat} (h : RelPow ContextStep m t u) :
    (m : Ordinal) ≤ ctxHeight t :=
  (Ordinal.le_add_left _ _).trans (rank_add_le_of_relPow CtxRev (fun _ _ hs => hs) h)

theorem le_two_pow (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < 2 ^ k := by positivity
    rw [pow_succ]
    omega

/-- The nested payload family reaches every finite contextual height. -/
theorem ctxHeight_unbounded (n : Nat) : ∃ t, (n : Ordinal) ≤ ctxHeight t := by
  obtain ⟨m, u, hm, hd⟩ := nest_long_derivation 2 n
  refine ⟨nest 2 n, ?_⟩
  have h2 : ((n : Nat) : Ordinal) ≤ (m : Ordinal) := by exact_mod_cast (le_two_pow n).trans hm
  exact h2.trans (le_ctxHeight_of_relPow hd)

/-- The polynomial escape is calibrated at `ω`: every contextual height is finite and every
finite height is reached. -/
theorem ctx_calibrated_omega :
    (∀ t, ctxHeight t < ω) ∧ ∀ n : Nat, ∃ t, (n : Ordinal) ≤ ctxHeight t :=
  ⟨ctxHeight_lt_omega, ctxHeight_unbounded⟩

/-- The height of the free contextual relation is exactly `ω`. -/
theorem iSup_ctxHeight : ⨆ t, ctxHeight t = ω := by
  apply le_antisymm
  · exact Ordinal.iSup_le fun t => (ctxHeight_lt_omega t).le
  · refine le_of_forall_lt fun o ho => ?_
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.1 ho
    obtain ⟨t, ht⟩ := ctxHeight_unbounded (n + 1)
    rw [Ordinal.lt_iSup_iff]
    refine ⟨t, lt_of_lt_of_le ?_ ht⟩
    exact_mod_cast Nat.lt_succ_self n

/-! ## The dependency-pair escape is calibrated at `ω` -/

/-- The reversed recursive-call relation. -/
def CallRev (c a : FreeTerm Nat) : Prop := FreeRecursiveCallPair a c

theorem callRank_lt {c a : FreeTerm Nat} (h : CallRev c a) :
    recursiveCallRank c < recursiveCallRank a := by
  have := ObserverSufficiency.recursiveCallRank_call (show FreeRecursiveCallPair a c from h)
  omega

instance : IsWellFounded (FreeTerm Nat) CallRev :=
  ⟨Subrelation.wf (r := InvImage (· < ·) recursiveCallRank) (fun h => callRank_lt h)
    (InvImage.wf recursiveCallRank Nat.lt_wfRel.wf)⟩

/-- The height of a free term under recursive calls. -/
noncomputable def callHeight (t : FreeTerm Nat) : Ordinal := IsWellFounded.rank CallRev t

theorem callHeight_le (t : FreeTerm Nat) : callHeight t ≤ (recursiveCallRank t : Ordinal) :=
  rank_le_natRank CallRev recursiveCallRank (fun _ _ h => callRank_lt h) t

/-- A counter of `k` successors gives a chain of `k` recursive calls. -/
theorem callChain (b s : FreeTerm Nat) :
    ∀ k : Nat, RelPow FreeRecursiveCallPair k (.recur b s (sucOn k .zero)) (.recur b s .zero)
  | 0 => RelPow.zero _
  | k + 1 => by
    have h1 : RelPow FreeRecursiveCallPair 1 (.recur b s (sucOn (k + 1) .zero))
        (.recur b s (sucOn k .zero)) :=
      RelPow.succ (RelPow.zero _) (.successor b s (sucOn k .zero))
    have h2 := h1.append (callChain b s k)
    rw [Nat.add_comm 1 k] at h2
    exact h2

theorem le_callHeight_of_relPow {m : Nat} {a c : FreeTerm Nat}
    (h : RelPow FreeRecursiveCallPair m a c) : (m : Ordinal) ≤ callHeight a :=
  (Ordinal.le_add_left _ _).trans (rank_add_le_of_relPow CallRev (fun _ _ hs => hs) h)

/-- The dependency-pair escape is calibrated at `ω`: every call height is finite and every
finite height is reached. -/
theorem call_calibrated_omega :
    (∀ t, callHeight t < ω) ∧ ∀ n : Nat, ∃ t, (n : Ordinal) ≤ callHeight t :=
  ⟨fun t => (callHeight_le t).trans_lt (Ordinal.nat_lt_omega0 _),
    fun n => ⟨_, le_callHeight_of_relPow (callChain .zero .zero n)⟩⟩

/-! ## The MPO escape at the four schema symbols -/

/-- Precedence of the head symbol: variables and `zero` 0, `succ` 1, `wrap` 2, `recur` 3. -/
def headRank {ν : Type} : FreeTerm ν → Nat
  | .var _ => 0
  | .zero => 0
  | .succ _ => 1
  | .wrap _ _ => 2
  | .recur _ _ _ => 3

/-- Immediate arguments. -/
def freeArgs {ν : Type} : FreeTerm ν → List (FreeTerm ν)
  | .var _ => []
  | .zero => []
  | .succ t => [t]
  | .wrap s t => [s, t]
  | .recur b s n => [b, s, n]

/-- The path order of `MPO_FullStep.lean` at the four schema symbols: subterm, precedence with
dominated arguments, and decrease in the counter under the same `recur` head. -/
inductive FreeMPO {ν : Type} : FreeTerm ν → FreeTerm ν → Prop
  | subEq {s u : FreeTerm ν} : u ∈ freeArgs s → FreeMPO s u
  | subGt {s u t : FreeTerm ν} : u ∈ freeArgs s → FreeMPO u t → FreeMPO s t
  | byPrec {s t : FreeTerm ν} :
      headRank t < headRank s → (∀ u ∈ freeArgs t, FreeMPO s u) → FreeMPO s t
  | recArg {b s n n' : FreeTerm ν} : FreeMPO n' n → FreeMPO (.recur b s n') (.recur b s n)

theorem freeMpo_recurZero {ν : Type} (b s : FreeTerm ν) : FreeMPO (.recur b s .zero) b :=
  .subEq (by simp [freeArgs])

theorem freeMpo_recurSucc {ν : Type} (b s n : FreeTerm ν) :
    FreeMPO (.recur b s (.succ n)) (.wrap s (.recur b s n)) := by
  refine .byPrec (by simp [headRank]) ?_
  intro u hu
  simp [freeArgs] at hu
  rcases hu with rfl | rfl
  · exact .subEq (by simp [freeArgs])
  · exact .recArg (.subEq (by simp [freeArgs]))

/-- The path order orients both free root rules. -/
theorem freeMpo_orients_rootStep {ν : Type} {t u : FreeTerm ν} (h : RootStep t u) :
    FreeMPO t u := by
  cases h with
  | recurZero => exact freeMpo_recurZero _ _
  | recurSucc => exact freeMpo_recurSucc _ _ _

/-- The KO7 MPO ranking at the four schema symbols. -/
noncomputable def freeMpoOrd {ν : Type} : FreeTerm ν → Ordinal.{0}
  | .var _ => Ordinal.veblen 0 0
  | .zero => Ordinal.veblen 0 0
  | .succ t => Ordinal.veblen 1 (Order.succ (freeMpoOrd t))
  | .wrap s t => Ordinal.veblen 2 (pairPayload (freeMpoOrd s) (freeMpoOrd t))
  | .recur b s n =>
      Ordinal.veblen 3 (triplePayload (freeMpoOrd b) (freeMpoOrd s) (freeMpoOrd n))

/-- The payload under the Veblen head. -/
noncomputable def freePayloadOrd {ν : Type} : FreeTerm ν → Ordinal.{0}
  | .var _ => 0
  | .zero => 0
  | .succ t => Order.succ (freeMpoOrd t)
  | .wrap s t => pairPayload (freeMpoOrd s) (freeMpoOrd t)
  | .recur b s n => triplePayload (freeMpoOrd b) (freeMpoOrd s) (freeMpoOrd n)

theorem freeMpoOrd_eq_veblen {ν : Type} (t : FreeTerm ν) :
    freeMpoOrd t = Ordinal.veblen (headRank t : Ordinal.{0}) (freePayloadOrd t) := by
  cases t <;> simp [freeMpoOrd, freePayloadOrd, headRank]

theorem freeMpoOrd_limit {ν : Type} {t : FreeTerm ν} (h : 0 < headRank t) :
    Order.IsSuccLimit (freeMpoOrd t) := by
  rw [freeMpoOrd_eq_veblen]
  exact veblen_isSuccLimit_of_pos (by exact_mod_cast h)

theorem freeMpoOrd_fixed {ν : Type} {t : FreeTerm ν} (h : 0 < headRank t) :
    (ω : Ordinal.{0}) ^ freeMpoOrd t = freeMpoOrd t := by
  rw [freeMpoOrd_eq_veblen]
  exact veblen_fixed_of_pos (by exact_mod_cast h)

theorem one_lt_freeMpoOrd {ν : Type} {t : FreeTerm ν} (h : 0 < headRank t) :
    1 < freeMpoOrd t := by
  rw [freeMpoOrd_eq_veblen]
  exact veblen_gt_one_of_pos (by exact_mod_cast h)

theorem freeMpoOrd_lt_succ {ν : Type} (t : FreeTerm ν) : freeMpoOrd t < freeMpoOrd (.succ t) := by
  have h : Order.succ (freeMpoOrd t) < Ordinal.veblen 1 (Order.succ (freeMpoOrd t)) :=
    lt_veblen_of_nonlimit (by exact_mod_cast (show 0 < (1 : Nat) by decide))
      (Order.not_isSuccLimit_succ _)
  exact (Order.lt_succ _).trans h

theorem pair_lt_freeMpoOrd_wrap {ν : Type} (s t : FreeTerm ν) :
    pairPayload (freeMpoOrd s) (freeMpoOrd t) < freeMpoOrd (.wrap s t) :=
  lt_veblen_of_nonlimit (by exact_mod_cast (show 0 < (2 : Nat) by decide))
    (Order.not_isSuccLimit_succ _)

theorem triple_lt_freeMpoOrd_recur {ν : Type} (b s n : FreeTerm ν) :
    triplePayload (freeMpoOrd b) (freeMpoOrd s) (freeMpoOrd n) < freeMpoOrd (.recur b s n) :=
  lt_veblen_of_nonlimit (by exact_mod_cast (show 0 < (3 : Nat) by decide))
    (Order.not_isSuccLimit_succ _)

theorem freeMpoOrd_arg_lt {ν : Type} {s u : FreeTerm ν} (h : u ∈ freeArgs s) :
    freeMpoOrd u < freeMpoOrd s := by
  cases s with
  | var x => simp [freeArgs] at h
  | zero => simp [freeArgs] at h
  | succ t =>
    have hu : u = t := by simpa [freeArgs] using h
    subst hu
    exact freeMpoOrd_lt_succ _
  | wrap a b =>
    have hu : u = a ∨ u = b := by simpa [freeArgs] using h
    rcases hu with rfl | rfl
    · exact (left_lt_pairPayload _ _).trans (pair_lt_freeMpoOrd_wrap _ _)
    · exact (right_lt_pairPayload _ _).trans (pair_lt_freeMpoOrd_wrap _ _)
  | recur b m n =>
    have hu : u = b ∨ u = m ∨ u = n := by simpa [freeArgs] using h
    rcases hu with rfl | rfl | rfl
    · exact (first_lt_triplePayload _ _ _).trans (triple_lt_freeMpoOrd_recur _ _ _)
    · exact (second_lt_triplePayload _ _ _).trans (triple_lt_freeMpoOrd_recur _ _ _)
    · exact (third_lt_triplePayload _ _ _).trans (triple_lt_freeMpoOrd_recur _ _ _)

theorem freePayloadOrd_lt {ν : Type} {s t : FreeTerm ν} (hs : 0 < headRank s)
    (hargs : ∀ u ∈ freeArgs t, freeMpoOrd u < freeMpoOrd s) : freePayloadOrd t < freeMpoOrd s := by
  have hlim := freeMpoOrd_limit hs
  have hfix := freeMpoOrd_fixed hs
  cases t with
  | var x => exact zero_lt_one.trans (one_lt_freeMpoOrd hs)
  | zero => exact zero_lt_one.trans (one_lt_freeMpoOrd hs)
  | succ u => exact Order.IsSuccLimit.succ_lt hlim (hargs u (by simp [freeArgs]))
  | wrap a b =>
    exact pairPayload_lt_of_lt (hargs a (by simp [freeArgs])) (hargs b (by simp [freeArgs]))
      hlim hfix
  | recur b m n =>
    exact triplePayload_lt_of_lt (hargs b (by simp [freeArgs])) (hargs m (by simp [freeArgs]))
      (hargs n (by simp [freeArgs])) hlim hfix

theorem freeMpoOrd_lt_of_byPrec {ν : Type} {s t : FreeTerm ν} (hprec : headRank t < headRank s)
    (hargs : ∀ u ∈ freeArgs t, freeMpoOrd u < freeMpoOrd s) : freeMpoOrd t < freeMpoOrd s := by
  have hs : 0 < headRank s := Nat.zero_lt_of_lt hprec
  have hpay := freePayloadOrd_lt hs hargs
  have hprecOrd : (headRank t : Ordinal.{0}) < headRank s := by exact_mod_cast hprec
  rw [freeMpoOrd_eq_veblen t, freeMpoOrd_eq_veblen s]
  rw [freeMpoOrd_eq_veblen s] at hpay
  exact Ordinal.veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨hprecOrd, hpay⟩))

/-- Every comparison of the path order decreases the ranking. -/
theorem freeMpoOrd_strict_of_mpo {ν : Type} {a b : FreeTerm ν} (h : FreeMPO a b) :
    freeMpoOrd b < freeMpoOrd a := by
  induction h with
  | subEq hmem => exact freeMpoOrd_arg_lt hmem
  | subGt hmem _ ih => exact ih.trans (freeMpoOrd_arg_lt hmem)
  | byPrec hprec _ ih => exact freeMpoOrd_lt_of_byPrec hprec (fun u hu => ih u hu)
  | recArg _ ih => exact Ordinal.veblen_lt_veblen_iff_right.2 (triplePayload_strictMono_right _ _ ih)

theorem veblen_four_isSuccLimit : Order.IsSuccLimit (Ordinal.veblen 4 0 : Ordinal.{0}) :=
  veblen_isSuccLimit_of_pos (by exact_mod_cast (show 0 < (4 : Nat) by decide))

theorem veblen_four_fixed : (ω : Ordinal.{0}) ^ Ordinal.veblen 4 0 = Ordinal.veblen 4 0 :=
  veblen_fixed_of_pos (by exact_mod_cast (show 0 < (4 : Nat) by decide))

theorem veblen_lt_veblen_four {k p : Ordinal.{0}} (hk : k < 4) (hp : p < Ordinal.veblen 4 0) :
    Ordinal.veblen k p < Ordinal.veblen 4 0 :=
  Ordinal.veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨hk, hp⟩))

/-- Every value of the ranking lies below `veblen 4 0`. -/
theorem freeMpoOrd_lt_veblen_four {ν : Type} : ∀ t : FreeTerm ν, freeMpoOrd t < Ordinal.veblen 4 0
  | .var _ =>
      Ordinal.veblen_zero_lt_veblen_zero.2 (by exact_mod_cast (show 0 < (4 : Nat) by decide))
  | .zero =>
      Ordinal.veblen_zero_lt_veblen_zero.2 (by exact_mod_cast (show 0 < (4 : Nat) by decide))
  | .succ t =>
      veblen_lt_veblen_four (by exact_mod_cast (show 1 < (4 : Nat) by decide))
        (veblen_four_isSuccLimit.succ_lt (freeMpoOrd_lt_veblen_four t))
  | .wrap s t =>
      veblen_lt_veblen_four (by exact_mod_cast (show 2 < (4 : Nat) by decide))
        (pairPayload_lt_of_lt (freeMpoOrd_lt_veblen_four s) (freeMpoOrd_lt_veblen_four t)
          veblen_four_isSuccLimit veblen_four_fixed)
  | .recur b s n =>
      veblen_lt_veblen_four (by exact_mod_cast (show 3 < (4 : Nat) by decide))
        (triplePayload_lt_of_lt (freeMpoOrd_lt_veblen_four b) (freeMpoOrd_lt_veblen_four s)
          (freeMpoOrd_lt_veblen_four n) veblen_four_isSuccLimit veblen_four_fixed)

/-- The tower `recur (recur (... zero) zero zero) zero zero`. -/
def recurTower {ν : Type} : Nat → FreeTerm ν
  | 0 => .zero
  | k + 1 => .recur (recurTower k) .zero .zero

theorem iterate_le_freeMpoOrd_tower {ν : Type} :
    ∀ k : Nat, (Ordinal.veblen 3)^[k] 0 ≤ freeMpoOrd (recurTower (ν := ν) k)
  | 0 => Ordinal.zero_le _
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    have ih := iterate_le_freeMpoOrd_tower (ν := ν) k
    have h1 : freeMpoOrd (recurTower (ν := ν) k) <
        triplePayload (freeMpoOrd (recurTower (ν := ν) k)) (freeMpoOrd (.zero : FreeTerm ν))
          (freeMpoOrd (.zero : FreeTerm ν)) :=
      first_lt_triplePayload _ _ _
    calc Ordinal.veblen 3 ((Ordinal.veblen 3)^[k] 0)
        ≤ Ordinal.veblen 3 (freeMpoOrd (recurTower (ν := ν) k)) :=
          Ordinal.veblen_le_veblen_iff_right.2 ih
      _ ≤ Ordinal.veblen 3 (triplePayload (freeMpoOrd (recurTower (ν := ν) k))
            (freeMpoOrd (.zero : FreeTerm ν)) (freeMpoOrd (.zero : FreeTerm ν))) :=
          Ordinal.veblen_le_veblen_iff_right.2 h1.le
      _ = freeMpoOrd (recurTower (ν := ν) (k + 1)) := rfl

theorem veblen_four_zero_eq_nfp :
    (Ordinal.veblen 4 0 : Ordinal.{0}) = Ordinal.nfp (Ordinal.veblen 3) 0 := by
  have h : Order.succ (3 : Ordinal.{0}) = 4 := by
    rw [← Ordinal.add_one_eq_succ]
    norm_num
  rw [← h, Ordinal.veblen_succ, Ordinal.deriv_zero_right]

/-- The ranking is cofinal in `veblen 4 0`. -/
theorem freeMpoOrd_cofinal {ν : Type} {β : Ordinal.{0}} (hβ : β < Ordinal.veblen 4 0) :
    ∃ t : FreeTerm ν, β < freeMpoOrd t := by
  rw [veblen_four_zero_eq_nfp, Ordinal.lt_nfp_iff] at hβ
  obtain ⟨k, hk⟩ := hβ
  exact ⟨recurTower k, hk.trans_le (iterate_le_freeMpoOrd_tower k)⟩

/-- The MPO bound at the four schema symbols is exact: the supremum of the ranking is
`veblen 4 0`. -/
theorem iSup_freeMpoOrd {ν : Type} : ⨆ t : FreeTerm ν, freeMpoOrd t = Ordinal.veblen 4 0 := by
  apply le_antisymm
  · exact Ordinal.iSup_le fun t => (freeMpoOrd_lt_veblen_four t).le
  · refine le_of_forall_lt fun β hβ => ?_
    obtain ⟨t, ht⟩ := freeMpoOrd_cofinal (ν := ν) hβ
    exact ht.trans_le (Ordinal.le_iSup _ t)

/-- The MPO escape at the four schema symbols: the path order orients both root rules, every
comparison decreases the ranking, every value lies below `veblen 4 0`, and the supremum is
`veblen 4 0`. -/
theorem mpo_calibration {ν : Type} :
    (∀ {t u : FreeTerm ν}, RootStep t u → FreeMPO t u) ∧
      (∀ {a b : FreeTerm ν}, FreeMPO a b → freeMpoOrd b < freeMpoOrd a) ∧
      (∀ t : FreeTerm ν, freeMpoOrd t < Ordinal.veblen 4 0) ∧
      ⨆ t : FreeTerm ν, freeMpoOrd t = Ordinal.veblen 4 0 :=
  ⟨freeMpo_orients_rootStep, freeMpoOrd_strict_of_mpo, freeMpoOrd_lt_veblen_four,
    iSup_freeMpoOrd⟩

end OperatorKO7.Methods.OrientationClosure.FreeOrdinalCalibration
