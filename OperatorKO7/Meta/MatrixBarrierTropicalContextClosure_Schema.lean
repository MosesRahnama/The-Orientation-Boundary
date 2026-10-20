import OperatorKO7.Meta.MatrixBarrierTropicalNatural_Schema
import OperatorKO7.Meta.CompositionalMeasure_Impossibility
import OperatorKO7.Meta.ContextClosed_SN_Full

/-!
# Tropical context obstruction

`tropicalEscapeMeasure` orients every root duplicating rule on free syntax.
No tropical matrix interpretation orients the closure under both wrapper arguments
at a fixed strictly decreasing coordinate. A strict right-argument step forces a
finite right contribution. Retaining that argument bounds every left contribution,
contradicting the arbitrarily long recursor executions in the left argument.
The theorem requires neither finite diagonals nor a supplied bound.
-/

namespace OperatorKO7.StepDuplicating
namespace StepDuplicatingSchema
namespace TropicalContextClosure

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.CompositionalImpossibility

/-! ## Generic wrapper-context closure of the duplicating rule -/

/-- Root duplicating steps, closed under both wrapper arguments, on an arbitrary
step-duplicating schema. -/
inductive TropicalDupStepCtx (S : StepDuplicatingSchema) : S.T → S.T → Prop
  | root (b s n : S.T) :
      TropicalDupStepCtx S (S.recur b s (S.succ n)) (S.wrap s (S.recur b s n))
  | wrap_left {x x' : S.T} (y : S.T) :
      TropicalDupStepCtx S x x' → TropicalDupStepCtx S (S.wrap x y) (S.wrap x' y)
  | wrap_right (x : S.T) {y y' : S.T} :
      TropicalDupStepCtx S y y' → TropicalDupStepCtx S (S.wrap x y) (S.wrap x y')

/-- Repeated canonical wrappers on the right-active execution spine. -/
def tropicalWrapChain (S : StepDuplicatingSchema) (s : S.T) : Nat → S.T → S.T
  | 0, t => t
  | n + 1, t => S.wrap s (tropicalWrapChain S s n t)

@[simp] theorem tropicalWrapChain_zero (S : StepDuplicatingSchema) (s t : S.T) :
    tropicalWrapChain S s 0 t = t := rfl

@[simp] theorem tropicalWrapChain_succ (S : StepDuplicatingSchema) (s t : S.T) (n : Nat) :
    tropicalWrapChain S s (n + 1) t = S.wrap s (tropicalWrapChain S s n t) := rfl

/-- Pushing one canonical wrapper through an existing wrapper chain increments
the chain length. -/
theorem tropicalWrapChain_push (S : StepDuplicatingSchema) (s t : S.T) (n : Nat) :
    tropicalWrapChain S s n (S.wrap s t) = tropicalWrapChain S s (n + 1) t := by
  induction n with
  | zero => rfl
  | succ n ih => simp [tropicalWrapChain, ih]

/-- Wrapper-context closure lifts one duplicating edge through an arbitrary
canonical right-active wrapper chain. -/
theorem TropicalDupStepCtx.wrapChain_right {S : StepDuplicatingSchema}
    (s : S.T) (n : Nat) {a b : S.T} (h : TropicalDupStepCtx S a b) :
    TropicalDupStepCtx S (tropicalWrapChain S s n a) (tropicalWrapChain S s n b) := by
  induction n with
  | zero => simpa [tropicalWrapChain] using h
  | succ n ih =>
      simpa [tropicalWrapChain] using TropicalDupStepCtx.wrap_right s ih

/-- The canonical stage at depth `k`, after `j` recursor-successor contractions. -/
def tropicalCanonicalStage (S : StepDuplicatingSchema) (b s : S.T)
    (k j : Nat) : S.T :=
  tropicalWrapChain S s j (S.recur b s (succIter S (k - j)))

/-- Adjacent canonical stages are genuine single edges of the wrapper-context
closure. -/
theorem tropicalCanonicalStage_step (S : StepDuplicatingSchema) (b s : S.T)
    {k j : Nat} (hj : j < k) :
    TropicalDupStepCtx S
      (tropicalCanonicalStage S b s k j)
      (tropicalCanonicalStage S b s k (j + 1)) := by
  unfold tropicalCanonicalStage
  have hpos : 0 < k - j := Nat.sub_pos_of_lt hj
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  have hcounter : succIter S (k - j) = S.succ (succIter S m) := by
    rw [hm]
    rfl
  have hmsub : m = k - j - 1 := by omega
  have hroot : TropicalDupStepCtx S
      (S.recur b s (succIter S (k - j)))
      (S.wrap s (S.recur b s (succIter S (k - j - 1)))) := by
    rw [hcounter, hmsub]
    exact TropicalDupStepCtx.root b s (succIter S (k - j - 1))
  have hlift := TropicalDupStepCtx.wrapChain_right s j hroot
  have hsub : k - j - 1 = k - (j + 1) := by omega
  simpa [hsub, tropicalWrapChain_push] using hlift

/-! ## Min-plus finite cap -/

/-- Transitivity of the explicit tropical order. -/
theorem tropicalLe_trans {x y z : TropicalNat}
    (hxy : TropicalLe x y) (hyz : TropicalLe y z) : TropicalLe x z := by
  cases x <;> cases y <;> cases z <;> simp_all [TropicalLe]
  omega

/-- Forget `top` only after a proof that the value lies below a finite tropical
scalar. -/
def tropicalNatValue : TropicalNat → Nat
  | .top => 0
  | .fin n => n

/-- A tropical value bounded by a finite scalar is itself finite, with its
natural component bounded by the same cap. -/
theorem tropicalLe_fin_value {x : TropicalNat} {cap : Nat}
    (h : TropicalLe x (.fin cap)) :
    x = .fin (tropicalNatValue x) ∧ tropicalNatValue x ≤ cap := by
  cases x with
  | top => simp [TropicalLe] at h
  | fin n => exact ⟨rfl, h⟩

/-- The value of a wrapper is bounded above by its right matrix contribution. -/
theorem eval_wrap_le_right {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalNatMatrixMeasure S d) (x y : S.T) (i : Fin d) :
    TropicalLe (M.eval (S.wrap x y) i) (M.wrap_right.act (M.eval y) i) := by
  rw [M.eval_wrap]
  exact tropicalLe_trans (tropicalMin_le_right _ _) (tropicalMin_le_right _ _)

/-- The value of a wrapper is bounded above by its bias. -/
theorem eval_wrap_le_bias {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalNatMatrixMeasure S d) (x y : S.T) (i : Fin d) :
    TropicalLe (M.eval (S.wrap x y) i) (M.wrap_bias i) := by
  rw [M.eval_wrap]
  exact tropicalMin_le_left _ _

/-- The value of a wrapper is bounded above by its left matrix contribution. -/
theorem eval_wrap_le_left {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalNatMatrixMeasure S d) (x y : S.T) (i : Fin d) :
    TropicalLe (M.eval (S.wrap x y) i) (M.wrap_left.act (M.eval x) i) := by
  rw [M.eval_wrap]
  exact tropicalLe_trans (tropicalMin_le_right _ _) (tropicalMin_le_left _ _)

/-- A finite right diagonal and a finite retained right sibling give a fixed
finite cap for every left argument of the outer wrapper. -/
theorem eval_outer_wrapper_right_cap {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalNatMatrixMeasure S d) (i : Fin d) (sibling x : S.T)
    {diag siblingValue : Nat}
    (hdiag : M.wrap_right.coeff i i = .fin diag)
    (hsibling : M.eval sibling i = .fin siblingValue) :
    M.eval (S.wrap x sibling) i =
        .fin (tropicalNatValue (M.eval (S.wrap x sibling) i))
      ∧ tropicalNatValue (M.eval (S.wrap x sibling) i) ≤ diag + siblingValue := by
  have hright :
      TropicalLe (M.eval (S.wrap x sibling) i)
        (tropicalPlus (M.wrap_right.coeff i i) (M.eval sibling i)) :=
    tropicalLe_trans (eval_wrap_le_right M x sibling i)
      (TropicalMatrix.act_le_diag M.wrap_right (M.eval sibling) i)
  have hcap :
      TropicalLe (M.eval (S.wrap x sibling) i) (.fin (diag + siblingValue)) := by
    simpa [hdiag, hsibling, tropicalPlus] using hright
  exact tropicalLe_fin_value hcap

/-- Natural coordinate exposed by one outer wrapper with a fixed right sibling. -/
def outerWrapperValue {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalNatMatrixMeasure S d) (i : Fin d) (sibling x : S.T) : Nat :=
  tropicalNatValue (M.eval (S.wrap x sibling) i)

/-- The natural outer-wrapper coordinate is bounded by the finite right cap. -/
theorem outerWrapperValue_le_cap {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalNatMatrixMeasure S d) (i : Fin d) (sibling x : S.T)
    {diag siblingValue : Nat}
    (hdiag : M.wrap_right.coeff i i = .fin diag)
    (hsibling : M.eval sibling i = .fin siblingValue) :
    outerWrapperValue M i sibling x ≤ diag + siblingValue :=
  (eval_outer_wrapper_right_cap M i sibling x hdiag hsibling).2

/-- A globally oriented contextual edge strictly decreases the natural
outer-wrapper coordinate. -/
theorem outerWrapperValue_strict_of_orients
    {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalNatMatrixMeasure S d) (i : Fin d) (sibling : S.T)
    {diag siblingValue : Nat}
    (hdiag : M.wrap_right.coeff i i = .fin diag)
    (hsibling : M.eval sibling i = .fin siblingValue)
    (horients : ∀ {a b : S.T}, TropicalDupStepCtx S a b →
      TropicalLt (M.eval b i) (M.eval a i))
    {a b : S.T} (hstep : TropicalDupStepCtx S a b) :
    outerWrapperValue M i sibling b < outerWrapperValue M i sibling a := by
  have hlt := horients (TropicalDupStepCtx.wrap_left sibling hstep)
  have ha := eval_outer_wrapper_right_cap M i sibling a hdiag hsibling
  have hb := eval_outer_wrapper_right_cap M i sibling b hdiag hsibling
  rw [ha.1, hb.1] at hlt
  exact hlt

/-! ## Finite descending-chain contradiction -/

/-- A natural-valued sequence with `k` strict adjacent descents starts at a
value at least `k`. -/
theorem nat_strict_chain_length_le_start (v : Nat → Nat) :
    ∀ k : Nat, (∀ j : Nat, j < k → v (j + 1) < v j) → k ≤ v 0 := by
  intro k h
  induction k generalizing v with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have h0 : v 1 < v 0 := by
        simpa using h 0 (Nat.zero_lt_succ k)
      have htail : ∀ j : Nat, j < k →
          (fun n => v (n + 1)) (j + 1) < (fun n => v (n + 1)) j := by
        intro j hj
        simpa [Nat.add_assoc] using h (j + 1) (by omega)
      have hk : k ≤ v 1 := by
        simpa using ih (v := fun n => v (n + 1)) htail
      omega

/-- **Bounded-context obstruction.** Any endomorphism of the carrier that lifts
every contextual duplicating edge and places the tracked tropical coordinate
below one finite bound rules out strict orientation of the contextual relation.
The wrapper-specific barriers below are instances of this theorem. -/
theorem no_tropical_context_orientation_of_uniform_context_cap
    {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalNatMatrixMeasure S d) (i : Fin d)
    (embed : S.T → S.T) (cap : Nat)
    (hlift : ∀ {a b : S.T}, TropicalDupStepCtx S a b →
      TropicalDupStepCtx S (embed a) (embed b))
    (hcap : ∀ x : S.T, TropicalLe (M.eval (embed x) i) (.fin cap)) :
    ¬ (∀ {a b : S.T}, TropicalDupStepCtx S a b →
      TropicalLt (M.eval b i) (M.eval a i)) := by
  intro horients
  let depth : Nat := cap + 1
  let v : Nat → Nat := fun j =>
    tropicalNatValue
      (M.eval (embed (tropicalCanonicalStage S S.base S.base depth j)) i)
  have hchain : ∀ j : Nat, j < depth → v (j + 1) < v j := by
    intro j hj
    have hlt := horients
      (hlift (tropicalCanonicalStage_step S S.base S.base hj))
    have hjFinite := tropicalLe_fin_value
      (hcap (tropicalCanonicalStage S S.base S.base depth j))
    have hjNextFinite := tropicalLe_fin_value
      (hcap (tropicalCanonicalStage S S.base S.base depth (j + 1)))
    rw [hjNextFinite.1, hjFinite.1] at hlt
    simpa [v] using hlt
  have hlen : depth ≤ v 0 := nat_strict_chain_length_le_start v depth hchain
  have hbound : v 0 ≤ cap := by
    simpa [v] using
      (tropicalLe_fin_value
        (hcap (tropicalCanonicalStage S S.base S.base depth 0))).2
  dsimp [depth] at hlen
  omega

/-- A strict change through the right input of a minimum requires a finite
right contribution at the target. -/
theorem tropicalMin_strict_right_target_finite (bias left src tgt : TropicalNat)
    (h : TropicalLt (tropicalMin bias (tropicalMin left tgt))
      (tropicalMin bias (tropicalMin left src))) :
    ∃ n : Nat, tgt = .fin n := by
  cases tgt with
  | fin n => exact ⟨n, rfl⟩
  | top =>
      cases bias <;> cases left <;> cases src <;>
        simp_all [tropicalMin, TropicalLt]
      all_goals omega

/-- A tropical matrix interpretation cannot strictly orient the duplicating
rule and both wrapper congruences. The finite bound is derived from orientation. -/
theorem no_tropical_context_orientation
    {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalNatMatrixMeasure S d) (i : Fin d) :
    ¬ (∀ {a b : S.T}, TropicalDupStepCtx S a b →
      TropicalLt (M.eval b i) (M.eval a i)) := by
  intro horients
  let src := S.recur S.base S.base (S.succ S.base)
  let tgt := S.wrap S.base (S.recur S.base S.base S.base)
  have hroot : TropicalDupStepCtx S src tgt :=
    TropicalDupStepCtx.root S.base S.base S.base
  have hright := horients (TropicalDupStepCtx.wrap_right S.base hroot)
  rw [M.eval_wrap S.base tgt, M.eval_wrap S.base src] at hright
  obtain ⟨cap, hcap⟩ := tropicalMin_strict_right_target_finite
    (M.wrap_bias i) (M.wrap_left.act (M.eval S.base) i)
    (M.wrap_right.act (M.eval src) i) (M.wrap_right.act (M.eval tgt) i) hright
  apply no_tropical_context_orientation_of_uniform_context_cap
    M i (fun x => S.wrap x tgt) cap ?_ ?_ horients
  · intro a b h
    exact TropicalDupStepCtx.wrap_left tgt h
  · intro x
    simpa [hcap] using eval_wrap_le_right M x tgt i

/-- A finite wrapper bias supplies a uniform cap, independently of both wrapper
matrices and of the retained sibling. -/
theorem no_tropical_context_orientation_of_finite_wrap_bias
    {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalNatMatrixMeasure S d) (i : Fin d) (sibling : S.T)
    {bias : Nat} (hbias : M.wrap_bias i = .fin bias) :
    ¬ (∀ {a b : S.T}, TropicalDupStepCtx S a b →
      TropicalLt (M.eval b i) (M.eval a i)) := by
  apply no_tropical_context_orientation_of_uniform_context_cap
    M i (fun x => S.wrap x sibling) bias
  · intro a b h
    exact TropicalDupStepCtx.wrap_left sibling h
  · intro x
    simpa [hbias] using eval_wrap_le_bias M x sibling i

/-- A finite tracked left-wrapper diagonal and one finite retained left sibling
supply the symmetric finite cap. -/
theorem no_tropical_context_orientation_of_finite_left_cap
    {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalNatMatrixMeasure S d) (i : Fin d) (sibling : S.T)
    {diag siblingValue : Nat}
    (hdiag : M.wrap_left.coeff i i = .fin diag)
    (hsibling : M.eval sibling i = .fin siblingValue) :
    ¬ (∀ {a b : S.T}, TropicalDupStepCtx S a b →
      TropicalLt (M.eval b i) (M.eval a i)) := by
  apply no_tropical_context_orientation_of_uniform_context_cap
    M i (fun x => S.wrap sibling x) (diag + siblingValue)
  · intro a b h
    exact TropicalDupStepCtx.wrap_right sibling h
  · intro x
    have hleft :
        TropicalLe (M.eval (S.wrap sibling x) i)
          (tropicalPlus (M.wrap_left.coeff i i) (M.eval sibling i)) :=
      tropicalLe_trans (eval_wrap_le_left M sibling x i)
        (TropicalMatrix.act_le_diag M.wrap_left (M.eval sibling) i)
    simpa [hdiag, hsibling, tropicalPlus] using hleft

/-- **Universal tropical context no-go.** A finite tracked right-wrapper diagonal
and one finite retained right sibling rule out a global strict orientation of the
full wrapper-context closure of the duplicating rule. -/
theorem no_tropical_context_orientation_of_finite_right_cap
    {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalNatMatrixMeasure S d) (i : Fin d) (sibling : S.T)
    {diag siblingValue : Nat}
    (hdiag : M.wrap_right.coeff i i = .fin diag)
    (hsibling : M.eval sibling i = .fin siblingValue) :
    ¬ (∀ {a b : S.T}, TropicalDupStepCtx S a b →
      TropicalLt (M.eval b i) (M.eval a i)) := by
  intro horients
  let cap : Nat := diag + siblingValue
  let depth : Nat := cap + 1
  let v : Nat → Nat := fun j =>
    outerWrapperValue M i sibling
      (tropicalCanonicalStage S S.base S.base depth j)
  have hchain : ∀ j : Nat, j < depth → v (j + 1) < v j := by
    intro j hj
    exact outerWrapperValue_strict_of_orients M i sibling hdiag hsibling horients
      (tropicalCanonicalStage_step S S.base S.base hj)
  have hlen : depth ≤ v 0 := nat_strict_chain_length_le_start v depth hchain
  have hcap : v 0 ≤ cap := by
    exact outerWrapperValue_le_cap M i sibling
      (tropicalCanonicalStage S S.base S.base depth 0) hdiag hsibling
  dsimp [depth, cap] at hlen hcap
  omega

/-! ## Existing free syntax and KO7 specializations -/

/-- The generic context relation specializes exactly into the previously exposed
free-syntax context relation. -/
theorem tropicalDupStepCtx_to_free :
    ∀ {a b : FreeTerm}, TropicalDupStepCtx freeSchema a b → FreeDupStepCtx a b
  | _, _, TropicalDupStepCtx.root b s n => FreeDupStepCtx.root b s n
  | _, _, TropicalDupStepCtx.wrap_left y h =>
      FreeDupStepCtx.wrap_left y (tropicalDupStepCtx_to_free h)
  | _, _, TropicalDupStepCtx.wrap_right x h =>
      FreeDupStepCtx.wrap_right x (tropicalDupStepCtx_to_free h)

/-- Conversely, every previously exposed free-syntax contextual edge is an edge
of the generic context relation. -/
theorem free_to_tropicalDupStepCtx :
    ∀ {a b : FreeTerm}, FreeDupStepCtx a b → TropicalDupStepCtx freeSchema a b
  | _, _, FreeDupStepCtx.root b s n =>
      TropicalDupStepCtx.root (S := freeSchema) b s n
  | _, _, FreeDupStepCtx.wrap_left y h =>
      TropicalDupStepCtx.wrap_left y (free_to_tropicalDupStepCtx h)
  | _, _, FreeDupStepCtx.wrap_right x h =>
      TropicalDupStepCtx.wrap_right x (free_to_tropicalDupStepCtx h)

/-- Exact relation equality on the free carrier. -/
theorem tropicalDupStepCtx_iff_freeDupStepCtx {a b : FreeTerm} :
    TropicalDupStepCtx freeSchema a b ↔ FreeDupStepCtx a b :=
  ⟨tropicalDupStepCtx_to_free, free_to_tropicalDupStepCtx⟩

/-- Free-syntax specialization of the universal context no-go. -/
theorem no_freeDupStepCtx_orientation_of_finite_right_cap
    {d : Nat} (M : TropicalNatMatrixMeasure freeSchema d) (i : Fin d)
    (sibling : FreeTerm) {diag siblingValue : Nat}
    (hdiag : M.wrap_right.coeff i i = .fin diag)
    (hsibling : M.eval sibling i = .fin siblingValue) :
    ¬ (∀ {a b : FreeTerm}, FreeDupStepCtx a b →
      TropicalLt (M.eval b i) (M.eval a i)) := by
  intro horients
  exact no_tropical_context_orientation_of_finite_right_cap
    M i sibling hdiag hsibling (fun h => horients (tropicalDupStepCtx_to_free h))

/-- A finite wrapper bias alone rules out strict orientation of every
free-syntax contextual duplicating edge. -/
theorem no_freeDupStepCtx_orientation_of_finite_wrap_bias
    {d : Nat} (M : TropicalNatMatrixMeasure freeSchema d) (i : Fin d)
    (sibling : FreeTerm) {bias : Nat} (hbias : M.wrap_bias i = .fin bias) :
    ¬ (∀ {a b : FreeTerm}, FreeDupStepCtx a b →
      TropicalLt (M.eval b i) (M.eval a i)) := by
  intro horients
  exact no_tropical_context_orientation_of_finite_wrap_bias
    M i sibling hbias (fun h => horients (tropicalDupStepCtx_to_free h))

/-- Generic KO7 schema-context edges are actual full contextual kernel edges. -/
theorem tropicalDupStepCtx_ko7_to_stepCtxFull :
    ∀ {a b : Trace}, TropicalDupStepCtx ko7Schema a b → MetaSN_KO7.StepCtxFull a b
  | _, _, TropicalDupStepCtx.root b s n => by
      simpa [ko7Schema] using MetaSN_KO7.StepCtxFull.root (Step.R_rec_succ b s n)
  | _, _, TropicalDupStepCtx.wrap_left y h => by
      simpa [ko7Schema] using MetaSN_KO7.StepCtxFull.appL
        (tropicalDupStepCtx_ko7_to_stepCtxFull h)
  | _, _, TropicalDupStepCtx.wrap_right x h => by
      simpa [ko7Schema] using MetaSN_KO7.StepCtxFull.appR
        (tropicalDupStepCtx_ko7_to_stepCtxFull h)

/-- Every relation containing the wrapper-context duplicating relation inherits
the tropical obstruction. -/
theorem no_tropical_orientation_of_context_inclusion
    {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalNatMatrixMeasure S d) (i : Fin d) (R : S.T → S.T → Prop)
    (hR : ∀ {a b}, TropicalDupStepCtx S a b → R a b) :
    ¬ (∀ {a b}, R a b → TropicalLt (M.eval b i) (M.eval a i)) := by
  intro h
  exact no_tropical_context_orientation M i (fun hstep => h (hR hstep))

/-- The free-syntax context obstruction has no coefficient hypotheses. -/
theorem no_freeDupStepCtx_tropical_orientation
    {d : Nat} (M : TropicalNatMatrixMeasure freeSchema d) (i : Fin d) :
    ¬ (∀ {a b : FreeTerm}, FreeDupStepCtx a b →
      TropicalLt (M.eval b i) (M.eval a i)) :=
  no_tropical_orientation_of_context_inclusion M i FreeDupStepCtx
    tropicalDupStepCtx_to_free

/-- Every tracked tropical interpretation fails on the full contextual KO7 relation. -/
theorem no_ko7_stepCtxFull_tropical_orientation
    {d : Nat} (M : TropicalNatMatrixMeasure ko7Schema d) (i : Fin d) :
    ¬ (∀ {a b : Trace}, MetaSN_KO7.StepCtxFull a b →
      TropicalLt (M.eval b i) (M.eval a i)) :=
  no_tropical_orientation_of_context_inclusion M i MetaSN_KO7.StepCtxFull
    tropicalDupStepCtx_ko7_to_stepCtxFull

/-- A root orienter exists, whereas every tropical interpretation fails on
the wrapper-context closure, in every finite dimension. -/
theorem tropical_root_context_classification :
    (∃ M : TropicalNatMatrixMeasure freeSchema 1,
      ∀ b s n : FreeTerm,
        TropicalLt (M.eval (freeSchema.wrap s (freeSchema.recur b s n)) 0)
          (M.eval (freeSchema.recur b s (freeSchema.succ n)) 0)) ∧
    (∀ (d : Nat) (M : TropicalNatMatrixMeasure freeSchema d) (i : Fin d),
      ¬ (∀ {a b : FreeTerm}, FreeDupStepCtx a b →
        TropicalLt (M.eval b i) (M.eval a i))) :=
  ⟨⟨tropicalEscapeMeasure, tropicalEscapeMeasure_strictly_orients⟩,
    fun _ M i => no_freeDupStepCtx_tropical_orientation M i⟩

/-- **KO7 StepCtxFull specialization.** Under the same finite right-cap data, no
tracked coordinate of a tropical matrix measure can strictly orient every full
contextual KO7 step. -/
theorem no_ko7_stepCtxFull_tropical_orientation_of_finite_right_cap
    {d : Nat} (M : TropicalNatMatrixMeasure ko7Schema d) (i : Fin d)
    (sibling : Trace) {diag siblingValue : Nat}
    (hdiag : M.wrap_right.coeff i i = .fin diag)
    (hsibling : M.eval sibling i = .fin siblingValue) :
    ¬ (∀ {a b : Trace}, MetaSN_KO7.StepCtxFull a b →
      TropicalLt (M.eval b i) (M.eval a i)) := by
  intro horients
  exact no_tropical_context_orientation_of_finite_right_cap
    M i sibling hdiag hsibling
      (fun h => horients (tropicalDupStepCtx_ko7_to_stepCtxFull h))

/-- A finite wrapper bias alone rules out strict orientation of every full
contextual KO7 step by the tracked tropical coordinate. -/
theorem no_ko7_stepCtxFull_tropical_orientation_of_finite_wrap_bias
    {d : Nat} (M : TropicalNatMatrixMeasure ko7Schema d) (i : Fin d)
    (sibling : Trace) {bias : Nat} (hbias : M.wrap_bias i = .fin bias) :
    ¬ (∀ {a b : Trace}, MetaSN_KO7.StepCtxFull a b →
      TropicalLt (M.eval b i) (M.eval a i)) := by
  intro horients
  exact no_tropical_context_orientation_of_finite_wrap_bias
    M i sibling hbias
      (fun h => horients (tropicalDupStepCtx_ko7_to_stepCtxFull h))

/-- The concrete root escape satisfies the universal theorem's finite-cap
hypotheses with the retained sibling `base`. -/
theorem tropicalEscapeMeasure_not_context_orienter_universal :
    ¬ (∀ {a b : FreeTerm}, FreeDupStepCtx a b →
      TropicalLt (tropicalEscapeMeasure.eval b 0) (tropicalEscapeMeasure.eval a 0)) := by
  exact no_freeDupStepCtx_orientation_of_finite_wrap_bias
    tropicalEscapeMeasure 0 FreeTerm.base (bias := 0) rfl

/-- **Exact root/context split.** The same concrete certificate-free tropical
measure orients every root duplicating rule but cannot orient their wrapper-context
closure. -/
theorem tropical_root_context_split_exact :
    (∀ (b s n : FreeTerm),
      TropicalLt
        (tropicalEscapeMeasure.eval (freeSchema.wrap s (freeSchema.recur b s n)) 0)
        (tropicalEscapeMeasure.eval (freeSchema.recur b s (freeSchema.succ n)) 0))
      ∧ ¬ (∀ {a b : FreeTerm}, FreeDupStepCtx a b →
        TropicalLt (tropicalEscapeMeasure.eval b 0) (tropicalEscapeMeasure.eval a 0)) :=
  ⟨tropicalEscapeMeasure_strictly_orients,
    tropicalEscapeMeasure_not_context_orienter_universal⟩

/-! ## Classification of wrapper-congruence policies -/

/-- Root duplication with separately selected wrapper-congruence rules. -/
inductive WrapperPolicyStep (S : StepDuplicatingSchema) (left right : Bool) :
    S.T → S.T → Prop
  | root (b s n : S.T) :
      WrapperPolicyStep S left right (S.recur b s (S.succ n)) (S.wrap s (S.recur b s n))
  | wrap_left (enabled : left = true) (y : S.T) {x x' : S.T} :
      WrapperPolicyStep S left right x x' →
        WrapperPolicyStep S left right (S.wrap x y) (S.wrap x' y)
  | wrap_right (enabled : right = true) (x : S.T) {y y' : S.T} :
      WrapperPolicyStep S left right y y' →
        WrapperPolicyStep S left right (S.wrap x y) (S.wrap x y')

theorem wrapperPolicyStep_to_full {S : StepDuplicatingSchema} {left right : Bool}
    {a b : S.T} (h : WrapperPolicyStep S left right a b) : TropicalDupStepCtx S a b := by
  induction h with
  | root b s n => exact .root b s n
  | wrap_left _ y _ ih => exact .wrap_left y ih
  | wrap_right _ x _ ih => exact .wrap_right x ih

theorem full_to_wrapperPolicyStep {S : StepDuplicatingSchema} {a b : S.T}
    (h : TropicalDupStepCtx S a b) : WrapperPolicyStep S true true a b := by
  induction h with
  | root b s n => exact .root b s n
  | wrap_left y _ ih => exact .wrap_left rfl y ih
  | wrap_right x _ ih => exact .wrap_right rfl x ih

theorem wrapperPolicyStep_full_iff {S : StepDuplicatingSchema} {a b : S.T} :
    WrapperPolicyStep S true true a b ↔ TropicalDupStepCtx S a b :=
  ⟨wrapperPolicyStep_to_full, full_to_wrapperPolicyStep⟩

/-- The left selector measures the payload; the right selector measures the counter. -/
def oneSidedWeight (selector : Bool) : FreeTerm → Nat
  | .base => 0
  | .succ t => oneSidedWeight selector t + 1
  | .wrap x y => if selector then oneSidedWeight selector x else oneSidedWeight selector y
  | .recur _ s n =>
      if selector then oneSidedWeight selector s + 1 else oneSidedWeight selector n

/-- Both one-sided weights are genuine one-dimensional min-plus interpretations. -/
def oneSidedMeasure (selector : Bool) : TropicalNatMatrixMeasure freeSchema 1 where
  eval := fun t _ => .fin (oneSidedWeight selector t)
  base_vec := fun _ => .fin 0
  succ_bias := fun _ => .top
  succ_mat := ⟨fun _ _ => .fin 1⟩
  wrap_bias := fun _ => .top
  wrap_left := ⟨fun _ _ => if selector then .fin 0 else .top⟩
  wrap_right := ⟨fun _ _ => if selector then .top else .fin 0⟩
  recur_bias := fun _ => .top
  recur_base := ⟨fun _ _ => .top⟩
  recur_step := ⟨fun _ _ => if selector then .fin 1 else .top⟩
  recur_counter := ⟨fun _ _ => if selector then .top else .fin 0⟩
  eval_base := rfl
  eval_succ := by
    intro t
    funext i
    fin_cases i
    simp [freeSchema, oneSidedWeight, tropicalVecMin, tropicalMin, TropicalMatrix.act,
      tropicalPlus, List.finRange, Nat.add_comm]
  eval_wrap := by
    intro x y
    funext i
    fin_cases i
    cases selector <;>
      simp [freeSchema, oneSidedWeight, tropicalVecMin, tropicalMin, TropicalMatrix.act,
        tropicalPlus, List.finRange]
  eval_recur := by
    intro b s n
    funext i
    fin_cases i
    cases selector <;>
      simp [freeSchema, oneSidedWeight, tropicalVecMin, tropicalMin, TropicalMatrix.act,
        tropicalPlus, List.finRange, Nat.add_comm]

theorem oneSidedMeasure_coord_finite (selector : Bool) (t : FreeTerm) :
    (oneSidedMeasure selector).eval t 0 = .fin (oneSidedWeight selector t) := rfl

theorem oneSidedMeasure_nonconstant (selector : Bool) :
    (oneSidedMeasure selector).eval (.succ .base) 0 ≠
      (oneSidedMeasure selector).eval .base 0 := by
  simp [oneSidedMeasure, oneSidedWeight]

theorem wrapperPolicy_orients_of_projection_laws {S : StepDuplicatingSchema}
    (left right : Bool) (value : S.T → Nat)
    (root_decreases : ∀ b s n,
      value (S.wrap s (S.recur b s n)) < value (S.recur b s (S.succ n)))
    (hl : left = true → ∀ x y, value (S.wrap x y) = value x)
    (hr : right = true → ∀ x y, value (S.wrap x y) = value y)
    {a b : S.T} (h : WrapperPolicyStep S left right a b) : value b < value a := by
  induction h with
  | root b s n => exact root_decreases b s n
  | wrap_left enabled y _ ih => simpa [hl enabled] using ih
  | wrap_right enabled x _ ih => simpa [hr enabled] using ih

theorem oneSidedWeight_orients (selector left right : Bool)
    (hl : left = true → selector = true) (hr : right = true → selector = false)
    {a b : FreeTerm} (h : WrapperPolicyStep freeSchema left right a b) :
    oneSidedWeight selector b < oneSidedWeight selector a := by
  apply wrapperPolicy_orients_of_projection_laws left right (oneSidedWeight selector)
      (h := h)
  · intro b s n
    cases selector <;> simp [freeSchema, oneSidedWeight]
  · intro enabled x y
    simp [freeSchema, oneSidedWeight, hl enabled]
  · intro enabled x y
    simp [freeSchema, oneSidedWeight, hr enabled]

theorem oneSidedMeasure_orients (selector left right : Bool)
    (hl : left = true → selector = true) (hr : right = true → selector = false)
    {a b : FreeTerm} (h : WrapperPolicyStep freeSchema left right a b) :
    TropicalLt ((oneSidedMeasure selector).eval b 0)
      ((oneSidedMeasure selector).eval a 0) :=
  oneSidedWeight_orients selector left right hl hr h

/-- The four policies admit an interpretation precisely when at least one
wrapper-congruence rule is absent. Dimension one supplies every positive case. -/
theorem tropical_wrapper_policy_classification (left right : Bool) :
    (∃ (d : Nat) (M : TropicalNatMatrixMeasure freeSchema d) (i : Fin d),
      ∀ {a b : FreeTerm}, WrapperPolicyStep freeSchema left right a b →
        TropicalLt (M.eval b i) (M.eval a i)) ↔
      (left = false ∨ right = false) := by
  constructor
  · rintro ⟨d, M, i, h⟩
    cases left <;> cases right
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact False.elim (no_tropical_context_orientation M i
        (fun edge => h (full_to_wrapperPolicyStep edge)))
  · rintro (hl | hr)
    · refine ⟨1, oneSidedMeasure false, 0, ?_⟩
      intro a b h
      exact oneSidedMeasure_orients false left right
        (by intro enabled; simp [hl] at enabled) (fun _ => rfl) h
    · refine ⟨1, oneSidedMeasure true, 0, ?_⟩
      intro a b h
      exact oneSidedMeasure_orients true left right
        (fun _ => rfl) (by intro enabled; simp [hr] at enabled) h

end TropicalContextClosure
end StepDuplicatingSchema
end OperatorKO7.StepDuplicating
