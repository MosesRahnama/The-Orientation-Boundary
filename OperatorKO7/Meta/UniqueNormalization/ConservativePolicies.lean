import OperatorKO7.Meta.UniqueNormalization.NormalizerRealization
import Mathlib.Data.Set.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max

/-!
# Conservative deletion and normalization policies

The relation is an arbitrary reduction relation on an arbitrary carrier.
A deletion retains a reduction to an original normal form at every source.
Under UNR this preserves normal forms, normal-form reductions, conversion,
weak normalization and confluence. Termination is not assumed in that result.

-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.Normalization

open scoped BigOperators

universe u v w
variable {X : Type u} {R E : X → X → Prop}

/-- Deleting edges preserves each original normal form. -/
theorem nf_subrel (hsub : Subrel E R) {x : X} (hx : NF R x) : NF E x :=
  fun y hxy => hx y (hsub hxy)

/-- Retained normalizing paths are equivalent to WN with no new normal forms. -/
theorem retained_normalizing_paths_iff (hsub : Subrel E R) :
    (∀ x, ∃ r, NF R r ∧ Star E x r) ↔
      WN E ∧ (∀ x, NF E x → NF R x) := by
  constructor
  · intro h
    constructor
    · intro x
      obtain ⟨r, hr, hxr⟩ := h x
      exact ⟨r, nf_subrel hsub hr, hxr⟩
    · intro x hx
      obtain ⟨r, hr, hxr⟩ := h x
      have hEq : r = x := nf_star_eq hx hxr
      exact hEq ▸ hr
  · rintro ⟨hwn, hnf⟩ x
    obtain ⟨r, hr, hxr⟩ := hwn x
    exact ⟨r, hnf r hr, hxr⟩

/-- Under UNR, a deletion retaining original normalizing paths preserves
normal-form reductions and conversion, and both relations are WN and CR. -/
theorem conservative_deletion
    (hsub : Subrel E R) (hu : UNR R)
    (hret : ∀ x, ∃ r, NF R r ∧ Star E x r) :
    WN R ∧ WN E ∧ CR R ∧ CR E ∧
      (∀ x, NF E x ↔ NF R x) ∧
      (∀ x r, NF R r → (Star E x r ↔ Star R x r)) ∧
      (∀ x y, Conv E x y ↔ Conv R x y) := by
  obtain ⟨hwnE, hnfER⟩ := (retained_normalizing_paths_iff hsub).mp hret
  have hnf : ∀ x, NF E x ↔ NF R x :=
    fun x => ⟨hnfER x, nf_subrel hsub⟩
  have hwnR : WN R := by
    intro x
    obtain ⟨r, hr, hxr⟩ := hret x
    exact ⟨r, hr, star_mono hsub hxr⟩
  have huE : UNR E := by
    intro x r s hr hs hxr hxs
    exact hu (hnfER r hr) (hnfER s hs)
      (star_mono hsub hxr) (star_mono hsub hxs)
  have hcR : CR R := cr_of_wn_unr hwnR hu
  have hcE : CR E := cr_of_wn_unr hwnE huE
  have hpaths : ∀ x r, NF R r → (Star E x r ↔ Star R x r) := by
    intro x r hr
    constructor
    · exact star_mono hsub
    · intro hxr
      obtain ⟨s, hs, hxs⟩ := hret x
      have hsr : s = r := hu hs hr (star_mono hsub hxs) hxr
      exact hsr ▸ hxs
  have hconv : ∀ x y, Conv E x y ↔ Conv R x y := by
    intro x y
    constructor
    · exact conv_mono hsub
    · intro hxy
      obtain ⟨r, hr, hxr⟩ := hret x
      obtain ⟨s, hs, hys⟩ := hret y
      have hrs : Conv R r s :=
        .trans r x s (.symm x r (conv_of_star (star_mono hsub hxr)))
          (.trans x y s hxy (conv_of_star (star_mono hsub hys)))
      have heq : r = s := unc_of_cr hcR hr hs hrs
      subst s
      exact conv_of_join ⟨r, hxr, hys⟩
  exact ⟨hwnR, hwnE, hcR, hcE, hnf, hpaths, hconv⟩

/-- A conservative deletion realizes the same prescribed normalizer. -/
theorem conservative_deletion_realizes {n : X → X}
    (hR : Realizes R n) (hsub : Subrel E R)
    (hret : ∀ x, ∃ r, NF R r ∧ Star E x r) : Realizes E n := by
  have h := conservative_deletion hsub (unr_of_unc (unc_of_cr hR.cr)) hret
  refine ⟨h.2.2.2.1, fun x => ⟨?_, nf_subrel hsub (hR.normal x)⟩⟩
  exact (h.2.2.2.2.2.1 x (n x) (hR.normal x)).mpr (hR.reaches x)

/-- Over a terminating base, retaining one successor at every original redex
is exactly the condition for retaining the prescribed normalizer. -/
theorem terminating_deletion_iff {n : X → X}
    (hsn : SN R) (hR : Realizes R n) (hsub : Subrel E R) :
    Realizes E n ↔ ∀ x, ¬ NF R x → ∃ y, E x y := by
  classical
  constructor
  · intro hE x hx
    apply Classical.byContradiction
    intro he
    have hnfE : NF E x := fun y hxy => he ⟨y, hxy⟩
    exact hx ((hR.nf_iff x).mpr ((hE.nf_iff x).mp hnfE))
  · intro hout
    have hwn : WN E := wn_of_sn (sn_subrel hsub hsn)
    have hnf : ∀ x, NF E x → NF R x := by
      intro x hx
      apply Classical.byContradiction
      intro hn
      obtain ⟨y, hxy⟩ := hout x hn
      exact hx y hxy
    exact conservative_deletion_realizes hR hsub
      ((retained_normalizing_paths_iff hsub).mpr ⟨hwn, hnf⟩)

/-- A deletion policy chooses a nonempty set of retained successors at every
original redex and never introduces an edge. -/
def DeletionPolicy (R : X → X → Prop) :=
  { E : X → X → Prop // Subrel E R ∧ ∀ x, ¬ NF R x → ∃ y, E x y }

def Redex (R : X → X → Prop) := {x : X // ¬ NF R x}

def Successors (R : X → X → Prop) (x : Redex R) := {y : X // R x.1 y}

def PolicyRows (R : X → X → Prop) :=
  ∀ x : Redex R, {s : Set (Successors R x) // s.Nonempty}

/-- The semantic policy predicate agrees with realization for an SN base. -/
theorem deletion_policy_iff_realizes {n : X → X}
    (hsn : SN R) (hR : Realizes R n) :
    (Subrel E R ∧ ∀ x, ¬ NF R x → ∃ y, E x y) ↔
      Subrel E R ∧ Realizes E n := by
  constructor
  · rintro ⟨hs, ho⟩
    exact ⟨hs, (terminating_deletion_iff hsn hR hs).mpr ho⟩
  · rintro ⟨hs, he⟩
    exact ⟨hs, (terminating_deletion_iff hsn hR hs).mp he⟩

def policyToRows (p : DeletionPolicy R) : PolicyRows R := fun x =>
  ⟨{y | p.1 x.1 y.1}, by
    obtain ⟨y, hy⟩ := p.2.2 x.1 x.2
    exact ⟨⟨y, p.2.1 hy⟩, hy⟩⟩

def policyFromRows (q : PolicyRows R) : DeletionPolicy R :=
  ⟨fun x y => ∃ hx : ¬ NF R x, ∃ hy : R x y,
      (q ⟨x, hx⟩).1 ⟨y, hy⟩,
    ⟨by
      rintro x y ⟨_, hy, _⟩
      exact hy,
    by
      intro x hx
      obtain ⟨y, hy⟩ := (q ⟨x, hx⟩).2
      exact ⟨y.1, hx, y.2, hy⟩⟩⟩

/-- The policy carrier is the full product of nonempty successor subsets. -/
def policyRowsEquiv : DeletionPolicy R ≃ PolicyRows R where
  toFun := policyToRows
  invFun := policyFromRows
  left_inv := by
    intro p
    apply Subtype.ext
    funext x y
    apply propext
    constructor
    · rintro ⟨_, _, hxy⟩
      exact hxy
    · intro hxy
      exact ⟨fun hn => hn y (p.2.1 hxy), p.2.1 hxy, hxy⟩
  right_inv := by
    intro q
    funext x
    apply Subtype.ext
    funext y
    apply propext
    constructor
    · rintro ⟨_, _, hxy⟩
      exact hxy
    · intro hxy
      exact ⟨x.2, y.2, hxy⟩

/-- The product bijection preserves and reflects edge inclusion. -/
theorem policy_rows_subrel_iff (p q : DeletionPolicy R) :
    (∀ x, (policyToRows p x).1 ⊆ (policyToRows q x).1) ↔ Subrel p.1 q.1 := by
  constructor
  · intro h x y hxy
    have hx : ¬ NF R x := fun hn => hn y (p.2.1 hxy)
    exact @h ⟨x, hx⟩ ⟨y, p.2.1 hxy⟩ hxy
  · intro h x y hxy
    exact h hxy

/-- The largest policy retains all original edges. -/
noncomputable def fullPolicy (R : X → X → Prop) : DeletionPolicy R := by
  classical
  refine ⟨R, fun {_ _} h => h, ?_⟩
  intro x hx
  apply Classical.byContradiction
  intro hn
  exact hx (fun y hxy => hn ⟨y, hxy⟩)

/-- Any nonempty union of policies is a policy. -/
def policyUnion {I : Type v} (i₀ : I) (p : I → DeletionPolicy R) : DeletionPolicy R :=
  ⟨fun x y => ∃ i, (p i).1 x y,
    ⟨by
      rintro x y ⟨i, hxy⟩
      exact (p i).2.1 hxy,
    by
      intro x hx
      obtain ⟨y, hy⟩ := (p i₀).2.2 x hx
      exact ⟨y, i₀, hy⟩⟩⟩

theorem policy_union_le_iff {I : Type v} (i₀ : I)
    (p : I → DeletionPolicy R) (q : DeletionPolicy R) :
    Subrel (policyUnion i₀ p).1 q.1 ↔ ∀ i, Subrel (p i).1 q.1 := by
  constructor
  · intro h i x y hxy
    exact h ⟨i, hxy⟩
  · rintro h x y ⟨i, hxy⟩
    exact h i hxy

/-- Intersection is taken inside the original relation, also for an empty family. -/
def policyIntersection {I : Type v} (p : I → DeletionPolicy R) (x y : X) : Prop :=
  R x y ∧ ∀ i, (p i).1 x y

/-- A family has a common lower policy exactly when every intersection row
remains nonempty. Hence a failed row excludes every lower bound. -/
theorem policy_common_lower_bound_iff {I : Type v} (p : I → DeletionPolicy R) :
    (∃ q : DeletionPolicy R, ∀ i, Subrel q.1 (p i).1) ↔
      ∀ x, ¬ NF R x → ∃ y, policyIntersection p x y := by
  constructor
  · rintro ⟨q, hq⟩ x hx
    obtain ⟨y, hy⟩ := q.2.2 x hx
    exact ⟨y, q.2.1 hy, fun i => hq i hy⟩
  · intro h
    refine ⟨⟨policyIntersection p, fun {_ _} hp => hp.1, h⟩, ?_⟩
    intro i x y hxy
    exact hxy.2 i

def policyInf {I : Type v} (p : I → DeletionPolicy R)
    (h : ∀ x, ¬ NF R x → ∃ y, policyIntersection p x y) : DeletionPolicy R :=
  ⟨policyIntersection p, fun {_ _} hp => hp.1, h⟩

theorem policy_le_inf_iff {I : Type v} (p : I → DeletionPolicy R)
    (h : ∀ x, ¬ NF R x → ∃ y, policyIntersection p x y) (q : DeletionPolicy R) :
    Subrel q.1 (policyInf p h).1 ↔ ∀ i, Subrel q.1 (p i).1 := by
  constructor
  · intro hq i x y hxy
    exact (hq hxy).2 i
  · intro hq x y hxy
    exact ⟨q.2.1 hxy, fun i => hq i hxy⟩

/-- Inclusion-minimality in the complete policy family. -/
def MinimalPolicy (p : DeletionPolicy R) : Prop :=
  ∀ q : DeletionPolicy R, Subrel q.1 p.1 → Subrel p.1 q.1

/-- A least policy is below every policy, not merely minimal. -/
def LeastPolicy (p : DeletionPolicy R) : Prop :=
  ∀ q : DeletionPolicy R, Subrel p.1 q.1

/-- Retain a designated edge and remove its competitors at that source. -/
def policyKeepAt (p : DeletionPolicy R) {x y : X} (hxy : p.1 x y) :
    DeletionPolicy R :=
  ⟨fun a b => p.1 a b ∧ (a = x → b = y),
    ⟨fun {_ _} h => p.2.1 h.1, by
      intro a ha
      by_cases hax : a = x
      · subst a
        exact ⟨y, hxy, fun _ => rfl⟩
      · obtain ⟨b, hab⟩ := p.2.2 a ha
        exact ⟨b, hab, fun h => False.elim (hax h)⟩⟩⟩

/-- Minimal policies retain exactly one edge at every original redex. -/
theorem minimal_policy_iff_functional (p : DeletionPolicy R) :
    MinimalPolicy p ↔
      ∀ ⦃x y z⦄, p.1 x y → p.1 x z → y = z := by
  constructor
  · intro hm x y z hxy hxz
    have hz := hm (policyKeepAt p hxy) (fun {_ _} h => h.1) hxz
    exact (hz.2 rfl).symm
  · intro hf q hq x y hxy
    have hx : ¬ NF R x := fun hn => hn y (p.2.1 hxy)
    obtain ⟨z, hxz⟩ := q.2.2 x hx
    have hyz : y = z := hf hxy (hq hxz)
    exact hyz.symm ▸ hxz

/-- A least deletion policy exists exactly when the base has no branching. -/
theorem exists_least_policy_iff :
    (∃ p : DeletionPolicy R, LeastPolicy p) ↔
      ∀ ⦃x y z⦄, R x y → R x z → y = z := by
  constructor
  · rintro ⟨p, hp⟩ x y z hxy hxz
    have hx : ¬ NF R x := fun hn => hn y hxy
    obtain ⟨w, hw⟩ := p.2.2 x hx
    have hwy : w = y :=
      (hp (policyKeepAt (fullPolicy R) hxy) hw).2 rfl
    have hwz : w = z :=
      (hp (policyKeepAt (fullPolicy R) hxz) hw).2 rfl
    exact hwy.symm.trans hwz
  · intro hf
    refine ⟨fullPolicy R, ?_⟩
    intro q x y hxy
    have hx : ¬ NF R x := fun hn => hn y hxy
    obtain ⟨z, hxz⟩ := q.2.2 x hx
    have hyz : y = z := hf hxy (q.2.1 hxz)
    exact hyz.symm ▸ hxz

def PolicyChoices (R : X → X → Prop) := ∀ x : Redex R, Successors R x

def policyFromChoices (f : PolicyChoices R) : DeletionPolicy R :=
  policyFromRows (fun x => ⟨{f x}, ⟨f x, rfl⟩⟩)

theorem policyFromChoices_step_iff (f : PolicyChoices R) (x y : X) :
    (policyFromChoices f).1 x y ↔
      ∃ hx : ¬ NF R x, (f ⟨x, hx⟩).1 = y := by
  constructor
  · rintro ⟨hx, hy, heq⟩
    exact ⟨hx, (congrArg Subtype.val heq).symm⟩
  · rintro ⟨hx, heq⟩
    refine ⟨hx, heq ▸ (f ⟨x, hx⟩).2, ?_⟩
    exact Subtype.ext heq.symm

theorem policyFromChoices_minimal (f : PolicyChoices R) :
    MinimalPolicy (policyFromChoices f) := by
  apply (minimal_policy_iff_functional _).mpr
  intro x y z hxy hxz
  obtain ⟨hx, hy⟩ := (policyFromChoices_step_iff f x y).mp hxy
  obtain ⟨_, hz⟩ := (policyFromChoices_step_iff f x z).mp hxz
  exact hy.symm.trans hz

noncomputable def choosePolicySuccessor (p : DeletionPolicy R) : PolicyChoices R :=
  fun x => ⟨Classical.choose (p.2.2 x.1 x.2),
    p.2.1 (Classical.choose_spec (p.2.2 x.1 x.2))⟩

theorem choosePolicySuccessor_mem (p : DeletionPolicy R) (x : Redex R) :
    p.1 x.1 (choosePolicySuccessor p x).1 :=
  Classical.choose_spec (p.2.2 x.1 x.2)

/-- Minimal policies are in bijection with independent single-successor choices. -/
noncomputable def minimalPoliciesEquivChoices :
    {p : DeletionPolicy R // MinimalPolicy p} ≃ PolicyChoices R where
  toFun := fun p => choosePolicySuccessor p.1
  invFun := fun f => ⟨policyFromChoices f, policyFromChoices_minimal f⟩
  left_inv := by
    intro p
    apply Subtype.ext
    apply Subtype.ext
    funext x y
    apply propext
    constructor
    · intro hxy
      obtain ⟨hx, heq⟩ :=
        (policyFromChoices_step_iff (choosePolicySuccessor p.1) x y).mp hxy
      exact heq ▸ choosePolicySuccessor_mem p.1 ⟨x, hx⟩
    · intro hxy
      have hx : ¬ NF R x := fun hn => hn y (p.1.2.1 hxy)
      apply (policyFromChoices_step_iff _ x y).mpr
      refine ⟨hx, ?_⟩
      exact (minimal_policy_iff_functional p.1).mp p.2
        (choosePolicySuccessor_mem p.1 ⟨x, hx⟩) hxy
  right_inv := by
    intro f
    funext x
    apply Subtype.ext
    have hm := choosePolicySuccessor_mem (policyFromChoices f) x
    obtain ⟨_, heq⟩ := (policyFromChoices_step_iff f x.1 _).mp hm
    exact heq.symm

/-- Each minimal policy has exactly one edge for every original redex. -/
noncomputable def minimalPolicyEdgeSourceEquiv (p : DeletionPolicy R)
    (hp : MinimalPolicy p) :
    {e : X × X // p.1 e.1 e.2} ≃ Redex R where
  toFun := fun e => ⟨e.1.1, fun hn => hn e.1.2 (p.2.1 e.2)⟩
  invFun := fun x => ⟨(x.1, (choosePolicySuccessor p x).1),
    choosePolicySuccessor_mem p x⟩
  left_inv := by
    intro e
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (minimal_policy_iff_functional p).mp hp
        (choosePolicySuccessor_mem p ⟨e.1.1, fun hn => hn e.1.2 (p.2.1 e.2)⟩) e.2
  right_inv := by
    intro x
    exact Subtype.ext rfl

instance deletionPolicyOrder : PartialOrder (DeletionPolicy R) := by
  unfold DeletionPolicy
  infer_instance

instance policyRowsOrder : PartialOrder (PolicyRows R) := by
  unfold PolicyRows
  infer_instance

/-- The product identification is an order isomorphism. -/
def policyRowsOrderIso : DeletionPolicy R ≃o PolicyRows R where
  toEquiv := policyRowsEquiv
  map_rel_iff' := by
    intro p q
    exact policy_rows_subrel_iff p q

/-- Choice selects a minimal policy below any given policy. -/
theorem exists_minimal_policy_below (p : DeletionPolicy R) :
    ∃ q : DeletionPolicy R, MinimalPolicy q ∧ Subrel q.1 p.1 := by
  refine ⟨policyFromChoices (choosePolicySuccessor p),
    policyFromChoices_minimal _, ?_⟩
  intro x y hxy
  obtain ⟨hx, heq⟩ := (policyFromChoices_step_iff _ x y).mp hxy
  exact heq ▸ choosePolicySuccessor_mem p ⟨x, hx⟩

section FinitePolicies

variable [Fintype X]
attribute [local instance] Classical.propDecidable

noncomputable instance redexFintype : Fintype (Redex R) := by
  unfold Redex
  infer_instance

noncomputable instance successorsFintype (x : Redex R) : Fintype (Successors R x) := by
  unfold Successors
  infer_instance

noncomputable instance policyRowsFintype : Fintype (PolicyRows R) := by
  unfold PolicyRows
  infer_instance

noncomputable instance deletionPolicyFintype : Fintype (DeletionPolicy R) :=
  Fintype.ofEquiv (PolicyRows R) policyRowsEquiv.symm

noncomputable instance policyChoicesFintype : Fintype (PolicyChoices R) := by
  unfold PolicyChoices
  infer_instance

/-- The nonempty subsets of a finite carrier number two to its cardinality minus one. -/
theorem card_nonempty_subsets {A : Type v} [Fintype A] :
    Fintype.card {s : Set A // s.Nonempty} = 2 ^ Fintype.card A - 1 := by
  let e : {s : Set A // s.Nonempty} ≃ {s : Set A // ¬ s = ∅} :=
    { toFun := fun s => ⟨s.1, by
        intro he
        obtain ⟨a, ha⟩ := s.2
        rw [he] at ha
        exact ha⟩
      invFun := fun s => ⟨s.1, by
        apply Classical.byContradiction
        intro hn
        apply s.2
        funext a
        apply propext
        exact ⟨fun ha => False.elim (hn ⟨a, ha⟩), fun ha => False.elim ha⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₀ : {s : Set A // s = ∅} ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨∅, rfl⟩
      left_inv := by
        rintro ⟨s, hs⟩
        exact Subtype.ext hs.symm
      right_inv := by
        intro x
        cases x
        rfl }
  have hz : Fintype.card {s : Set A // s = ∅} = 1 := by
    rw [Fintype.card_congr e₀]
    simp
  calc
    Fintype.card {s : Set A // s.Nonempty} =
        Fintype.card {s : Set A // ¬ s = ∅} := Fintype.card_congr e
    _ = Fintype.card (Set A) - Fintype.card {s : Set A // s = ∅} :=
      Fintype.card_subtype_compl (fun s : Set A => s = ∅)
    _ = 2 ^ Fintype.card A - 1 := by rw [Fintype.card_set, hz]

/-- Finite policies are counted independently at each original redex. -/
theorem deletion_policy_count :
    Fintype.card (DeletionPolicy R) =
      ∏ x : Redex R, (2 ^ Fintype.card (Successors R x) - 1) := by
  calc
    Fintype.card (DeletionPolicy R) = Fintype.card (PolicyRows R) :=
      Fintype.card_congr policyRowsEquiv
    _ = ∏ x : Redex R, Fintype.card {s : Set (Successors R x) // s.Nonempty} :=
      Fintype.card_pi
    _ = ∏ x : Redex R, (2 ^ Fintype.card (Successors R x) - 1) := by
      apply Finset.prod_congr rfl
      intro x _
      exact card_nonempty_subsets

theorem minimal_deletion_policy_count :
    Fintype.card {p : DeletionPolicy R // MinimalPolicy p} =
      ∏ x : Redex R, Fintype.card (Successors R x) := by
  calc
    Fintype.card {p : DeletionPolicy R // MinimalPolicy p} =
        Fintype.card (PolicyChoices R) := Fintype.card_congr minimalPoliciesEquivChoices
    _ = ∏ x : Redex R, Fintype.card (Successors R x) := Fintype.card_pi

theorem minimal_deletion_policy_edge_count (p : DeletionPolicy R) (hp : MinimalPolicy p) :
    Fintype.card {e : X × X // p.1 e.1 e.2} =
      Fintype.card X - Fintype.card {x : X // NF R x} := by
  calc
    Fintype.card {e : X × X // p.1 e.1 e.2} = Fintype.card (Redex R) :=
      Fintype.card_congr (minimalPolicyEdgeSourceEquiv p hp)
    _ = Fintype.card X - Fintype.card {x : X // NF R x} :=
      Fintype.card_subtype_compl (NF R)

end FinitePolicies

/-- Mutual finite reachability is the strongly connected component relation. -/
def SameSCC (R : X → X → Prop) (x y : X) : Prop := Star R x y ∧ Star R y x

/-- No edge leaves the strongly connected component containing the point. -/
def SinkSCC (R : X → X → Prop) (x : X) : Prop :=
  ∀ ⦃y z⦄, SameSCC R x y → R y z → SameSCC R x z

theorem sinkSCC_iff_return (x : X) :
    SinkSCC R x ↔ ∀ y, Star R x y → Star R y x := by
  constructor
  · intro hs y hp
    induction hp with
    | refl => exact .refl
    | @tail b c p h ih => exact (hs ⟨p, ih⟩ h).2
  · intro hr y z hxy hyz
    have hxz : Star R x z := hxy.1.tail hyz
    exact ⟨hxz, hr z hxz⟩

/-- On a finite carrier every point reaches a sink strongly connected component. -/
theorem finite_reaches_sinkSCC [Fintype X] (x : X) :
    ∃ y, Star R x y ∧ SinkSCC R y := by
  classical
  let reach : X → Finset X := fun a => Finset.univ.filter (Star R a)
  have hex : ∃ k : Nat, ∃ y, Star R x y ∧ (reach y).card = k :=
    ⟨(reach x).card, x, .refl, rfl⟩
  obtain ⟨y, hxy, hy⟩ := Nat.find_spec hex
  refine ⟨y, hxy, (sinkSCC_iff_return y).mpr ?_⟩
  intro z hyz
  have hsub : reach z ⊆ reach y := by
    intro a ha
    have hza : Star R z a := (Finset.mem_filter.mp ha).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hyz.trans hza⟩
  have hmin : (reach y).card ≤ (reach z).card := by
    rw [hy]
    exact Nat.find_min' hex ⟨z, hxy.trans hyz, rfl⟩
  have heq : reach z = reach y := Finset.eq_of_subset_of_card_le hsub hmin
  have hmem : y ∈ reach y := Finset.mem_filter.mpr ⟨Finset.mem_univ y, .refl⟩
  rw [← heq] at hmem
  exact (Finset.mem_filter.mp hmem).2

/-- The finite graph criterion quantifies over the actual sink SCCs, including
loops, and requires each to be a singleton fixed root. -/
theorem finite_realizes_iff_sinkSCC [Fintype X] {n : X → X}
    (hs : Subrel R (MaxRel n)) :
    Realizes R n ↔ ∀ x, SinkSCC R x →
      x = n x ∧ ∀ y, SameSCC R x y → y = x := by
  constructor
  · intro h x hx
    have hback : Star R (n x) x := (sinkSCC_iff_return x).mp hx (n x) (h.reaches x)
    have hfix : x = n x := nf_star_eq (h.normal x) hback
    refine ⟨hfix, ?_⟩
    intro y hxy
    exact nf_star_eq ((h.nf_iff x).mpr hfix) hxy.1
  · intro h
    apply realizes_of_subrel_maxRel hs
    intro x
    obtain ⟨y, hxy, hy⟩ := finite_reaches_sinkSCC (R := R) x
    have hroot : y = n y := (h y hy).1
    have hlabel : n x = n y := star_invariant n (fun {_ _} hab => (hs hab).2) hxy
    have hyroot : y = n x := hroot.trans hlabel.symm
    exact hyroot ▸ hxy

section RuleFamilies

variable {I : Type v} {n : X → X}

/-- A selected rule contributes all edges in its declared semantic instance relation. -/
def RuleUnion (A : I → X → X → Prop) (J : I → Prop) (x y : X) : Prop :=
  ∃ i, J i ∧ A i x y

def SafeRule (A : I → X → X → Prop) (n : X → X) (i : I) : Prop :=
  Subrel (A i) (MaxRel n)

def CutRule (A : I → X → X → Prop) (n : X → X) (U : X → Prop) (i : I) : Prop :=
  SafeRule A n i ∧ Exits (A i) U

/-- Hitting is quantified over every nonempty root-free subset of each fiber. -/
def HitsRuleCuts (A : I → X → X → Prop) (n : X → X) (J : I → Prop) : Prop :=
  ∀ (r : X) (U : X → Prop), (∃ x, U x) → RootFree n U →
    (∀ x, U x → n x = r) → ∃ i, J i ∧ CutRule A n U i

/-- Full-instance rule selection is exactly safety plus the canonical cut constraints. -/
theorem rule_family_realizes_iff (A : I → X → X → Prop) (J : I → Prop) :
    Realizes (RuleUnion A J) n ↔
      (∀ i, J i → SafeRule A n i) ∧ HitsRuleCuts A n J := by
  constructor
  · intro h
    have hs : ∀ i, J i → SafeRule A n i := by
      intro i hi x y hxy
      exact h.subrel_maxRel ⟨i, hi, hxy⟩
    refine ⟨hs, ?_⟩
    intro r U hU hf hlabel
    obtain ⟨x, y, hx, ⟨i, hi, hxy⟩, hy⟩ :=
      (root_reach_iff_fiber_cuts h.subrel_maxRel).mp h.reaches r U hU hf hlabel
    exact ⟨i, hi, hs i hi, x, y, hx, hxy, hy⟩
  · rintro ⟨hs, hh⟩
    apply realizes_iff_fiber_cuts.mpr
    constructor
    · rintro x y ⟨i, hi, hxy⟩
      exact hs i hi hxy
    · intro r U hU hf hlabel
      obtain ⟨i, hi, _, x, y, hx, hxy, hy⟩ := hh r U hU hf hlabel
      exact ⟨x, y, hx, ⟨i, hi, hxy⟩, hy⟩

/-- The family of all safe rules is feasible exactly when every cut has a safe rule. -/
theorem safe_rule_family_realizes_iff (A : I → X → X → Prop) :
    Realizes (RuleUnion A (SafeRule A n)) n ↔
      ∀ (r : X) (U : X → Prop), (∃ x, U x) → RootFree n U →
        (∀ x, U x → n x = r) → ∃ i, CutRule A n U i := by
  rw [rule_family_realizes_iff]
  constructor
  · rintro ⟨_, hh⟩ r U hU hf hl
    obtain ⟨i, _, hi⟩ := hh r U hU hf hl
    exact ⟨i, hi⟩
  · intro hh
    refine ⟨fun _ h => h, ?_⟩
    intro r U hU hf hl
    obtain ⟨i, hi⟩ := hh r U hU hf hl
    exact ⟨i, hi.1, hi⟩

theorem safe_rule_family_greatest (A : I → X → X → Prop) (J : I → Prop)
    (h : Realizes (RuleUnion A J) n) : ∀ i, J i → SafeRule A n i :=
  (rule_family_realizes_iff A J).mp h |>.1

theorem rule_family_feasible_iff_safe (A : I → X → X → Prop) :
    (∃ J, Realizes (RuleUnion A J) n) ↔ Realizes (RuleUnion A (SafeRule A n)) n := by
  constructor
  · rintro ⟨J, hJ⟩
    apply realizes_of_subrel_maxRel
    · rintro x y ⟨i, hi, hxy⟩
      exact hi hxy
    · intro x
      apply star_mono (p := hJ.reaches x)
      rintro a b ⟨i, hi, hab⟩
      exact ⟨i, safe_rule_family_greatest A J hJ i hi, hab⟩
  · intro h
    exact ⟨SafeRule A n, h⟩

def MinimalRuleFamily (A : I → X → X → Prop) (n : X → X) (J : I → Prop) : Prop :=
  Realizes (RuleUnion A J) n ∧
    ∀ K : I → Prop, (∀ i, K i → J i) → Realizes (RuleUnion A K) n → ∀ i, J i → K i

/-- Minimal rule families are exactly minimal transversals of the semantic cuts.
No edge-level functionality or termination conclusion is part of this statement. -/
theorem minimal_rule_family_iff (A : I → X → X → Prop) (J : I → Prop) :
    MinimalRuleFamily A n J ↔
      (∀ i, J i → SafeRule A n i) ∧ HitsRuleCuts A n J ∧
        ∀ K : I → Prop, (∀ i, K i → J i) → HitsRuleCuts A n K → ∀ i, J i → K i := by
  constructor
  · rintro ⟨hJ, hm⟩
    obtain ⟨hs, hh⟩ := (rule_family_realizes_iff A J).mp hJ
    refine ⟨hs, hh, ?_⟩
    intro K hK hhK
    exact hm K hK ((rule_family_realizes_iff A K).mpr
      ⟨fun i hi => hs i (hK i hi), hhK⟩)
  · rintro ⟨hs, hh, hm⟩
    refine ⟨(rule_family_realizes_iff A J).mpr ⟨hs, hh⟩, ?_⟩
    intro K hK hreal
    exact hm K hK ((rule_family_realizes_iff A K).mp hreal).2

/-- Any nonempty feasible family has a minimum for a natural-valued rule cost. -/
theorem exists_minimum_rule_cost (A : I → X → X → Prop)
    (cost : (I → Prop) → Nat) (hf : ∃ J, Realizes (RuleUnion A J) n) :
    ∃ J, Realizes (RuleUnion A J) n ∧
      ∀ K, Realizes (RuleUnion A K) n → cost J ≤ cost K := by
  classical
  have hex : ∃ k : Nat, ∃ J, Realizes (RuleUnion A J) n ∧ cost J = k := by
    obtain ⟨J, hJ⟩ := hf
    exact ⟨cost J, J, hJ, rfl⟩
  obtain ⟨J, hJ, hj⟩ := Nat.find_spec hex
  refine ⟨J, hJ, ?_⟩
  intro K hK
  rw [hj]
  exact Nat.find_min' hex ⟨K, hK, rfl⟩

/-- Unsafe indices never occur in a cut. Unrestricted inclusion-minimal hitting
sets therefore contain only safe indices, without a separate safety premise. -/
theorem minimal_rule_family_iff_transversal (A : I → X → X → Prop) (J : I → Prop) :
    MinimalRuleFamily A n J ↔
      HitsRuleCuts A n J ∧
        ∀ K : I → Prop, (∀ i, K i → J i) → HitsRuleCuts A n K → ∀ i, J i → K i := by
  constructor
  · intro h
    obtain ⟨_, hh, hm⟩ := (minimal_rule_family_iff A J).mp h
    exact ⟨hh, hm⟩
  · rintro ⟨hh, hm⟩
    have hsafeHit : HitsRuleCuts A n (fun i => J i ∧ SafeRule A n i) := by
      intro r U hU hf hl
      obtain ⟨i, hi, hs, he⟩ := hh r U hU hf hl
      exact ⟨i, ⟨hi, hs⟩, hs, he⟩
    have hsubset := hm (fun i => J i ∧ SafeRule A n i) (fun _ h => h.1) hsafeHit
    exact (minimal_rule_family_iff A J).mpr
      ⟨fun i hi => (hsubset i hi).2, hh, hm⟩

/-- With finitely many candidates, every linearly ordered cost has a feasible
minimum. The term or state carrier remains arbitrary. -/
theorem exists_minimum_rule_cost_finite [Fintype I] {W : Type w} [LinearOrder W]
    (A : I → X → X → Prop) (cost : (I → Prop) → W)
    (hf : ∃ J, Realizes (RuleUnion A J) n) :
    ∃ J, Realizes (RuleUnion A J) n ∧
      ∀ K, Realizes (RuleUnion A K) n → cost J ≤ cost K := by
  classical
  let choices : Finset (I → Prop) :=
    Finset.univ.filter (fun J => Realizes (RuleUnion A J) n)
  have hn : choices.Nonempty := by
    obtain ⟨J, hJ⟩ := hf
    exact ⟨J, Finset.mem_filter.mpr ⟨Finset.mem_univ J, hJ⟩⟩
  obtain ⟨J, hJ, hmin⟩ := Finset.exists_min_image choices cost hn
  refine ⟨J, (Finset.mem_filter.mp hJ).2, ?_⟩
  intro K hK
  exact hmin K (Finset.mem_filter.mpr ⟨Finset.mem_univ K, hK⟩)

/-- Finite feasible candidate families have an inclusion-minimal selection.
Minimum cardinality is a valid construction, even with an infinite state carrier. -/
theorem exists_minimal_rule_family [Fintype I] (A : I → X → X → Prop)
    (hf : ∃ J, Realizes (RuleUnion A J) n) :
    ∃ J, MinimalRuleFamily A n J := by
  classical
  let selected : (I → Prop) → Finset I := fun J => Finset.univ.filter J
  obtain ⟨J, hJ, hmin⟩ :=
    exists_minimum_rule_cost A (fun J => (selected J).card) hf
  refine ⟨J, hJ, ?_⟩
  intro K hK hreal i hi
  have hsub : selected K ⊆ selected J := by
    intro j hj
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ j, hK j (Finset.mem_filter.mp hj).2⟩
  have heq : selected K = selected J :=
    Finset.eq_of_subset_of_card_le hsub (hmin K hreal)
  have himem : i ∈ selected J :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  rw [← heq] at himem
  exact (Finset.mem_filter.mp himem).2

/-- A selected singleton contributes exactly its designated rule bundle. -/
theorem singleton_rule_selection_realizes (A : I → X → X → Prop) (i₀ : I)
    (h : Realizes (A i₀) n) : Realizes (RuleUnion A (fun i => i = i₀)) n := by
  have heq : RuleUnion A (fun i => i = i₀) = A i₀ := by
    funext x y
    apply propext
    constructor
    · rintro ⟨i, rfl, hxy⟩
      exact hxy
    · intro hxy
      exact ⟨i₀, rfl, hxy⟩
  rw [heq]
  exact h

/-- A single realizing rule bundle is a minimal selection whenever the
normalizer has a nonfixed input, regardless of that bundle's internal dynamics. -/
theorem singleton_rule_family_minimal (A : I → X → X → Prop) (i₀ : I)
    (h : Realizes (A i₀) n) (hnt : ∃ x, x ≠ n x) :
    MinimalRuleFamily A n (fun i => i = i₀) := by
  classical
  refine ⟨singleton_rule_selection_realizes A i₀ h, ?_⟩
  intro K hK hreal i hi
  subst i
  apply Classical.byContradiction
  intro hk
  obtain ⟨x, hx⟩ := hnt
  have hnf : NF (RuleUnion A K) x := by
    rintro y ⟨j, hj, _⟩
    have heq : j = i₀ := hK j hj
    exact hk (heq ▸ hj)
  exact hx ((hreal.nf_iff x).mp hnf)

end RuleFamilies

namespace BundledRuleControl

def loopBundle (_ : Unit) : Bool → Bool → Prop := MaxRel (fun _ => false)

/-- Minimality of a rule selection neither forces termination nor one successor
per state: the one selected bundle contains a loop and two outgoing choices. -/
theorem minimal_bundle_with_loop :
    MinimalRuleFamily loopBundle (fun _ => false) (fun i => i = ()) ∧
      ¬ SN (RuleUnion loopBundle (fun i => i = ())) ∧
      ¬ (∀ ⦃x y z : Bool⦄,
        RuleUnion loopBundle (fun i => i = ()) x y →
        RuleUnion loopBundle (fun i => i = ()) x z → y = z) := by
  have hm : MinimalRuleFamily loopBundle (fun _ => false) (fun i => i = ()) :=
    singleton_rule_family_minimal loopBundle () (maxRel_realizes (fun _ => rfl))
      ⟨true, by decide⟩
  have htt : RuleUnion loopBundle (fun i => i = ()) true true :=
    ⟨(), rfl, ⟨by decide, rfl⟩⟩
  have htf : RuleUnion loopBundle (fun i => i = ()) true false :=
    ⟨(), rfl, ⟨by decide, rfl⟩⟩
  refine ⟨hm, fun hs => sn_irrefl hs true htt, ?_⟩
  intro hf
  exact Bool.noConfusion (hf htt htf)

def duplicateBundle (_ : Bool) : Bool → Bool → Prop := MaxRel (fun _ => false)

/-- The two different singleton selections induce exactly the same step relation. -/
theorem duplicate_selection_same_relation :
    RuleUnion duplicateBundle (fun i => i = false) =
      RuleUnion duplicateBundle (fun i => i = true) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨i, _, hxy⟩
    exact ⟨true, rfl, hxy⟩
  · rintro ⟨i, _, hxy⟩
    exact ⟨false, rfl, hxy⟩

/-- Duplicate rule meanings can yield incomparable minimal index selections. -/
theorem duplicate_minima_incomparable :
    MinimalRuleFamily duplicateBundle (fun _ => false) (fun i => i = false) ∧
    MinimalRuleFamily duplicateBundle (fun _ => false) (fun i => i = true) ∧
    ¬ (∀ i : Bool, i = false → i = true) ∧
    ¬ (∀ i : Bool, i = true → i = false) := by
  refine ⟨singleton_rule_family_minimal duplicateBundle false
    (maxRel_realizes (fun _ => rfl)) ⟨true, by decide⟩,
    singleton_rule_family_minimal duplicateBundle true
    (maxRel_realizes (fun _ => rfl)) ⟨true, by decide⟩, ?_, ?_⟩
  · intro h
    exact Bool.noConfusion (h false rfl)
  · intro h
    exact Bool.noConfusion (h true rfl)

def splitBundle (i x y : Fin 3) : Prop :=
  (i = 0 ∧ x ≠ 0 ∧ y = 0) ∨
  (i = 1 ∧ x = 1 ∧ y = 0) ∨
  (i = 2 ∧ x = 2 ∧ y = 0)

/-- The same finite candidate family has minimal selections of sizes one and two. -/
theorem minimal_bundle_sizes_differ :
    MinimalRuleFamily splitBundle (fun _ => 0) (fun i => i = 0) ∧
    MinimalRuleFamily splitBundle (fun _ => 0) (fun i => i = 1 ∨ i = 2) ∧
    (Finset.univ.filter (fun i : Fin 3 => i = 0)).card = 1 ∧
    (Finset.univ.filter (fun i : Fin 3 => i = 1 ∨ i = 2)).card = 2 := by
  have hs : ∀ i : Fin 3, Subrel (splitBundle i) (MaxRel (fun _ => 0)) := by
    intro i x y hxy
    rcases hxy with ⟨_, hx, _⟩ | ⟨_, hx, _⟩ | ⟨_, hx, _⟩
    · exact ⟨hx, rfl⟩
    · subst x
      exact ⟨by decide, rfl⟩
    · subst x
      exact ⟨by decide, rfl⟩
  have hwhole : Realizes (splitBundle 0) (fun _ => 0) := by
    apply realizes_of_subrel_maxRel (hs 0)
    intro x
    by_cases hx : x = 0
    · subst x
      exact .refl
    · exact .single (Or.inl ⟨rfl, hx, rfl⟩)
  have hpair : Realizes (RuleUnion splitBundle (fun i => i = 1 ∨ i = 2))
      (fun _ => 0) := by
    apply realizes_of_subrel_maxRel
    · rintro x y ⟨i, _, hxy⟩
      exact hs i hxy
    · intro x
      have hcases : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
      rcases hcases x with hx | hx | hx
      · subst x
        exact .refl
      · subst x
        exact .single ⟨1, Or.inl rfl, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)⟩
      · subst x
        exact .single ⟨2, Or.inr rfl, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩
  have hAtOne : ∀ i y : Fin 3, splitBundle i 1 y → i = 0 ∨ i = 1 := by
    unfold splitBundle
    decide
  have hAtTwo : ∀ i y : Fin 3, splitBundle i 2 y → i = 0 ∨ i = 2 := by
    unfold splitBundle
    decide
  have hzero : ¬ ((0 : Fin 3) = 1 ∨ (0 : Fin 3) = 2) := by decide
  have hpairmin : MinimalRuleFamily splitBundle (fun _ => 0)
      (fun i => i = 1 ∨ i = 2) := by
    refine ⟨hpair, ?_⟩
    intro K hK hreal i hi
    have hk1 : K 1 := by
      apply Classical.byContradiction
      intro hn
      have hnf : NF (RuleUnion splitBundle K) 1 := by
        rintro y ⟨j, hj, hxy⟩
        rcases hAtOne j y hxy with heq | heq
        · subst j
          exact hzero (hK 0 hj)
        · subst j
          exact hn hj
      exact (by decide : (1 : Fin 3) ≠ 0) ((hreal.nf_iff 1).mp hnf)
    have hk2 : K 2 := by
      apply Classical.byContradiction
      intro hn
      have hnf : NF (RuleUnion splitBundle K) 2 := by
        rintro y ⟨j, hj, hxy⟩
        rcases hAtTwo j y hxy with heq | heq
        · subst j
          exact hzero (hK 0 hj)
        · subst j
          exact hn hj
      exact (by decide : (2 : Fin 3) ≠ 0) ((hreal.nf_iff 2).mp hnf)
    rcases hi with hi | hi
    · exact hi.symm ▸ hk1
    · exact hi.symm ▸ hk2
  exact ⟨singleton_rule_family_minimal splitBundle 0 hwhole ⟨1, by decide⟩,
    hpairmin, by decide, by decide⟩

end BundledRuleControl

/-- The deletion theorem supplies a common normalizer, not merely equality
of normal-form and conversion predicates. -/
theorem conservative_deletion_common_normalizer
    (hsub : Subrel E R) (hu : UNR R)
    (hret : ∀ x, ∃ r, NF R r ∧ Star E x r) :
    ∃ n : X → X, Realizes R n ∧ Realizes E n := by
  have h := conservative_deletion hsub hu hret
  obtain ⟨n, hn⟩ := exists_normalizer_iff_wn_cr.mpr ⟨h.1, h.2.2.1⟩
  exact ⟨n, hn, conservative_deletion_realizes hn hsub hret⟩

/-- Every terminating confluent base admits one normalizer classifying all its
deletion policies by their nonempty successor rows. -/
theorem terminating_base_policy_normalizer (hsn : SN R) (hc : CR R) :
    ∃ n : X → X, Realizes R n ∧
      ∀ E : X → X → Prop, Subrel E R →
        (Realizes E n ↔ ∀ x, ¬ NF R x → ∃ y, E x y) := by
  obtain ⟨n, hn⟩ := exists_normalizer_iff_wn_cr.mpr ⟨wn_of_sn hsn, hc⟩
  exact ⟨n, hn, fun _ he => terminating_deletion_iff hsn hn he⟩

end OperatorKO7.Meta.UniqueNormalization.Normalization
