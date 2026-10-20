import OperatorKO7.Meta.UniqueNormalization.NormalizationCore
import OperatorKO7.Meta.UniqueNormalization.NormalizationDomains
import OperatorKO7.Meta.UniqueNormalization.NormalizerForests
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.DeriveFintype

/-!
# Finite controls for normalization classifications
All finite truth checks use kernel reduction via decide. Reduction paths and
conversion are proved from their inductive definitions; no evaluator axiom is used.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.Normalization.Examples

open OperatorKO7.Meta.UniqueNormalization.Normalization

universe u

instance decidableNF {X : Type u} [Fintype X] (R : X → X → Prop)
    [DecidableRel R] (x : X) : Decidable (NF R x) :=
  inferInstanceAs (Decidable (∀ y, ¬ R x y))

inductive Five where
  | a | b | c | d | e
  deriving DecidableEq, Fintype

def fiveRel (x y : Five) : Prop :=
  (x = .a ∧ y = .b) ∨ (x = .a ∧ y = .c) ∨
  (x = .c ∧ y = .c) ∨ (x = .d ∧ y = .c) ∨ (x = .d ∧ y = .e)

instance : DecidableRel fiveRel := fun x y => inferInstanceAs
  (Decidable ((x = .a ∧ y = .b) ∨ (x = .a ∧ y = .c) ∨
    (x = .c ∧ y = .c) ∨ (x = .d ∧ y = .c) ∨ (x = .d ∧ y = .e)))

theorem five_transitive : Transitive fiveRel := by
  unfold Transitive
  decide

theorem five_star_iff (x y : Five) :
    Star fiveRel x y ↔ x = y ∨ fiveRel x y := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ hab ih =>
        rcases ih with he | hx
        · subst_vars; exact Or.inr hab
        · exact Or.inr (five_transitive hx hab)
  · rintro (rfl | h)
    · exact .refl
    · exact .single h

theorem five_nf_iff (x : Five) : NF fiveRel x ↔ x = .b ∨ x = .e := by
  have h : ∀ x : Five, NF fiveRel x ↔ x = .b ∨ x = .e := by decide
  exact h x

theorem five_unr : UNR fiveRel := by
  have h : ∀ x r s : Five, NF fiveRel r → NF fiveRel s →
      (x = r ∨ fiveRel x r) → (x = s ∨ fiveRel x s) → r = s := by decide
  intro x r s hr hs hxr hxs
  exact h x r s hr hs ((five_star_iff x r).mp hxr) ((five_star_iff x s).mp hxs)

theorem five_not_unc : ¬ UNC fiveRel := by
  intro hu
  have hb : NF fiveRel .b := by decide
  have he : NF fiveRel .e := by decide
  have hba : Conv fiveRel .b .a := .symm _ _ (.rel _ _ (by decide))
  have hac : Conv fiveRel .a .c := .rel _ _ (by decide)
  have hcd : Conv fiveRel .c .d := .symm _ _ (.rel _ _ (by decide))
  have hde : Conv fiveRel .d .e := .rel _ _ (by decide)
  have h := hu hb he (.trans _ _ _ hba (.trans _ _ _ hac (.trans _ _ _ hcd hde)))
  cases h

inductive Three where
  | a | b | r
  deriving DecidableEq, Fintype

def escapeRel (x y : Three) : Prop :=
  (x = .a ∧ y = .r) ∨ (x = .a ∧ y = .b) ∨ (x = .b ∧ y = .b)

instance : DecidableRel escapeRel := fun x y => inferInstanceAs
  (Decidable ((x = .a ∧ y = .r) ∨ (x = .a ∧ y = .b) ∨ (x = .b ∧ y = .b)))

theorem escape_transitive : Transitive escapeRel := by
  unfold Transitive
  decide

theorem escape_star_iff (x y : Three) :
    Star escapeRel x y ↔ x = y ∨ escapeRel x y := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ hab ih =>
        rcases ih with he | hx
        · subst_vars; exact Or.inr hab
        · exact Or.inr (escape_transitive hx hab)
  · rintro (rfl | h)
    · exact .refl
    · exact .single h

theorem escape_nf_iff (x : Three) : NF escapeRel x ↔ x = .r := by
  have h : ∀ x : Three, NF escapeRel x ↔ x = .r := by decide
  exact h x

theorem escape_normalizes_iff (x : Three) : Normalizes escapeRel x ↔ x ≠ .b := by
  have h : ∀ x : Three,
      (∃ root, NF escapeRel root ∧ (x = root ∨ escapeRel x root)) ↔ x ≠ .b := by decide
  simpa only [Normalizes, escape_star_iff] using h x

theorem escape_unc : UNC escapeRel := by
  intro root other hr hs _
  exact ((escape_nf_iff root).mp hr).trans ((escape_nf_iff other).mp hs).symm

theorem escape_conv_root (x : Three) : Conv escapeRel x .r := by
  cases x with
  | a => exact .rel _ _ (by decide)
  | b =>
      exact .trans Three.b Three.a Three.r
        (.symm Three.a Three.b (.rel Three.a Three.b (by decide)))
        (.rel Three.a Three.r (by decide))
  | r => exact .refl _

theorem escape_not_wn : ¬ WN escapeRel := by
  intro h
  exact (escape_normalizes_iff .b).mp (h .b) rfl

theorem escape_not_nfp : ¬ NFP escapeRel := by
  intro h
  have hp := h (show NF escapeRel .r by decide) (escape_conv_root .b)
  have hn : ¬ Star escapeRel .b .r := by rw [escape_star_iff]; decide
  exact hn hp

theorem escape_not_cr : ¬ CR escapeRel := by
  intro hc
  exact escape_not_nfp (nfp_of_cr hc)

def deletionBase (x y : Three) : Prop :=
  escapeRel x y ∨ (x = .b ∧ y = .r)

instance : DecidableRel deletionBase := fun x y =>
  inferInstanceAs (Decidable (escapeRel x y ∨ (x = .b ∧ y = .r)))

theorem deletion_same_nf (x : Three) : NF deletionBase x ↔ NF escapeRel x := by
  have h : ∀ x : Three, NF deletionBase x ↔ NF escapeRel x := by decide
  exact h x

theorem deletion_base_wn : WN deletionBase := by
  intro x
  refine ⟨.r, by decide, ?_⟩
  cases x with
  | a => exact .single (by decide)
  | b => exact .single (by decide)
  | r => exact .refl

theorem deletion_base_unc : UNC deletionBase := by
  intro root other hr hs _
  exact ((escape_nf_iff root).mp ((deletion_same_nf root).mp hr)).trans
    ((escape_nf_iff other).mp ((deletion_same_nf other).mp hs)).symm

theorem deletion_base_cr : CR deletionBase :=
  cr_of_wn_unr deletion_base_wn (unr_of_unc deletion_base_unc)

theorem deletion_subrel : Subrel escapeRel deletionBase := fun {_ _} h => Or.inl h

theorem deletion_same_conv (x y : Three) :
    Conv deletionBase x y ↔ Conv escapeRel x y := by
  constructor
  · intro _
    exact .trans _ _ _ (escape_conv_root x) (.symm _ _ (escape_conv_root y))
  · exact conv_mono deletion_subrel

theorem deletion_control :
    CR deletionBase ∧ WN deletionBase ∧ Subrel escapeRel deletionBase ∧
    (∀ x, NF deletionBase x ↔ NF escapeRel x) ∧
    (∀ x y, Conv deletionBase x y ↔ Conv escapeRel x y) ∧
    ¬ WN escapeRel ∧ ¬ CR escapeRel :=
  ⟨deletion_base_cr, deletion_base_wn, deletion_subrel, deletion_same_nf,
    deletion_same_conv, escape_not_wn, escape_not_cr⟩

def directRoot (x y : Three) : Prop := x ≠ .r ∧ y = .r
def chain (x y : Three) : Prop :=
  (x = .a ∧ y = .b) ∨ (x = .b ∧ y = .r)

instance : DecidableRel directRoot := fun x y =>
  inferInstanceAs (Decidable (x ≠ .r ∧ y = .r))
instance : DecidableRel chain := fun x y =>
  inferInstanceAs (Decidable ((x = .a ∧ y = .b) ∨ (x = .b ∧ y = .r)))

theorem chain_nf_iff (x : Three) : NF chain x ↔ x = .r := by
  have h : ∀ x : Three, NF chain x ↔ x = .r := by decide
  exact h x

theorem chain_root_predecessor_unique :
    ∀ x y : Three, chain x .r → chain y .r → x = y := by decide

theorem direct_root_paths (x : Three) : Star directRoot x .r := by
  cases x with
  | a => exact .single (by decide)
  | b => exact .single (by decide)
  | r => exact .refl

theorem chain_root_paths (x : Three) : Star chain x .r := by
  cases x with
  | a =>
      exact (Relation.ReflTransGen.single (show chain .a .b by decide)).tail
        (show chain .b .r by decide)
  | b => exact .single (by decide)
  | r => exact .refl

theorem direct_root_sn : SN directRoot := by
  have hr : NF directRoot .r := by decide
  have ar : Acc (fun y x => directRoot x y) .r :=
    Acc.intro _ (fun y h => False.elim (hr y h))
  constructor
  intro x
  apply Acc.intro
  intro y hxy
  have hy := hxy.2
  subst y
  exact ar

theorem chain_sn : SN chain := by
  have hr : NF chain .r := by decide
  have ar : Acc (fun y x => chain x y) .r :=
    Acc.intro _ (fun y h => False.elim (hr y h))
  have hb : ∀ y : Three, chain .b y → y = .r := by decide
  have ab : Acc (fun y x => chain x y) .b := by
    apply Acc.intro
    intro y hy
    have hey := hb y hy
    subst y
    exact ar
  have ha : ∀ y : Three, chain .a y → y = .b := by decide
  have aa : Acc (fun y x => chain x y) .a := by
    apply Acc.intro
    intro y hy
    have hey := ha y hy
    subst y
    exact ab
  exact ⟨fun x => by cases x; exact aa; exact ab; exact ar⟩

theorem star_chain_same_normalizer :
    (CR directRoot ∧ ∀ x, Star directRoot x .r ∧ NF directRoot .r) ∧
    (CR chain ∧ ∀ x, Star chain x .r ∧ NF chain .r) := by
  exact ⟨⟨cr_of_reachable_invariant (fun _ => Three.r) (fun {_ _} _ => rfl)
      direct_root_paths, fun x => ⟨direct_root_paths x, by decide⟩⟩,
    ⟨cr_of_reachable_invariant (fun _ => Three.r) (fun {_ _} _ => rfl)
      chain_root_paths, fun x => ⟨chain_root_paths x, by decide⟩⟩⟩

def reverseChain (x y : Three) : Prop :=
  (x = .b ∧ y = .a) ∨ (x = .a ∧ y = .r)

instance : DecidableRel reverseChain := fun x y =>
  inferInstanceAs (Decidable ((x = .b ∧ y = .a) ∨ (x = .a ∧ y = .r)))

theorem reverse_chain_paths (x : Three) : Star reverseChain x .r := by
  cases x with
  | a => exact .single (by decide)
  | b =>
      exact (Relation.ReflTransGen.single (show reverseChain .b .a by decide)).tail
        (show reverseChain .a .r by decide)
  | r => exact .refl

theorem reverse_chain_sn : SN reverseChain := by
  have hr : NF reverseChain .r := by decide
  have ar : Acc (fun y x => reverseChain x y) .r :=
    Acc.intro _ (fun y h => False.elim (hr y h))
  have ha : ∀ y : Three, reverseChain .a y → y = .r := by decide
  have aa : Acc (fun y x => reverseChain x y) .a := by
    apply Acc.intro
    intro y hy
    have hey := ha y hy
    subst y
    exact ar
  have hb : ∀ y : Three, reverseChain .b y → y = .a := by decide
  have ab : Acc (fun y x => reverseChain x y) .b := by
    apply Acc.intro
    intro y hy
    have hey := hb y hy
    subst y
    exact aa
  exact ⟨fun x => by cases x; exact aa; exact ab; exact ar⟩

theorem opposite_chains_same_normalizer :
    (CR chain ∧ ∀ x, Star chain x .r ∧ NF chain .r) ∧
    (CR reverseChain ∧ ∀ x, Star reverseChain x .r ∧ NF reverseChain .r) := by
  exact ⟨star_chain_same_normalizer.2,
    ⟨cr_of_reachable_invariant (fun _ => Three.r) (fun {_ _} _ => rfl)
      reverse_chain_paths, fun x => ⟨reverse_chain_paths x, by decide⟩⟩⟩

theorem terminating_realizations_union_not_sn :
    SN chain ∧ SN reverseChain ∧ ¬ SN (fun x y => chain x y ∨ reverseChain x y) := by
  refine ⟨chain_sn, reverse_chain_sn, ?_⟩
  intro hs
  exact sn_no_two_cycle hs .a .b (Or.inl (by decide)) (Or.inr (by decide))

theorem star_chain_not_graph_isomorphic :
    ¬ ∃ h : Three ≃ Three, ∀ x y, directRoot x y ↔ chain (h x) (h y) := by
  rintro ⟨h, he⟩
  have hr : NF chain (h .r) := by
    intro y hy
    obtain ⟨z, rfl⟩ := h.surjective y
    have hz := (he .r z).mpr hy
    exact hz.1 rfl
  have hrr := (chain_nf_iff (h .r)).mp hr
  have ha := (he .a .r).mp (by decide)
  have hb := (he .b .r).mp (by decide)
  rw [hrr] at ha hb
  have hab := h.injective (chain_root_predecessor_unique _ _ ha hb)
  cases hab

def fork (x y : Three) : Prop := x = .a ∧ (y = .b ∨ y = .r)

instance : DecidableRel fork := fun x y =>
  inferInstanceAs (Decidable (x = .a ∧ (y = .b ∨ y = .r)))

theorem fork_wn : WN fork := by
  intro x
  cases x with
  | a => exact ⟨.b, by decide, .single (by decide)⟩
  | b => exact ⟨.b, by decide, .refl⟩
  | r => exact ⟨.r, by decide, .refl⟩

theorem fork_not_nfp : ¬ NFP fork := by
  intro hn
  have hc : Conv fork .b .r :=
    .trans Three.b Three.a Three.r
      (.symm Three.a Three.b (.rel Three.a Three.b (by decide)))
      (.rel Three.a Three.r (by decide))
  have hp := hn (show NF fork .r by decide) hc
  have he := nf_star_eq (show NF fork .b by decide) hp
  cases he

theorem fork_all_descendants_normalize (x y : Three) (_h : Star fork x y) :
    Normalizes fork y := fork_wn y

theorem escape_hereditarily_iff (x : Three) :
    HereditarilyNormalizes escapeRel x ↔ x = .r := by
  cases x with
  | a =>
      constructor
      · intro hd
        exact False.elim ((escape_normalizes_iff .b).mp
          (hd .b (.single (by decide))) rfl)
      · intro h; cases h
  | b =>
      constructor
      · intro hd
        exact False.elim ((escape_normalizes_iff .b).mp (hd .b .refl) rfl)
      · intro h; cases h
  | r =>
      constructor
      · intro _; rfl
      · intro _ y hp
        have hy := nf_star_eq (show NF escapeRel .r by decide) hp
        subst y
        exact normalizes_of_nf (by decide)

theorem escape_normalizes_exact (x : Three) :
    Normalizes escapeRel x ↔ x = .a ∨ x = .r := by
  rw [escape_normalizes_iff]
  cases x <;> decide

theorem escape_converts_to_nf (x : Three) : ConvertsToNF escapeRel x :=
  ⟨.r, by decide, escape_conv_root x⟩

theorem escape_three_domains :
    UNC escapeRel ∧
    (∀ x, HereditarilyNormalizes escapeRel x ↔ x = .r) ∧
    (∀ x, Normalizes escapeRel x ↔ x = .a ∨ x = .r) ∧
    (∀ x, ConvertsToNF escapeRel x) :=
  ⟨escape_unc, escape_hereditarily_iff, escape_normalizes_exact,
    escape_converts_to_nf⟩

theorem escape_step_map_does_not_preserve_normalizing_carrier :
    ∃ c : Three → Three,
      (∀ x y, escapeRel x y → escapeRel (c x) (c y)) ∧
      Normalizes escapeRel .r ∧ ¬ Normalizes escapeRel (c .r) := by
  refine ⟨fun _ => .b, fun _ _ _ => (show escapeRel Three.b Three.b by decide),
    normalizes_of_nf (by decide), ?_⟩
  intro hn
  exact (escape_normalizes_iff .b).mp hn rfl

theorem fork_domains_equal_without_nfp :
    (∀ x, HereditarilyNormalizes fork x ∧ Normalizes fork x ∧
      ConvertsToNF fork x) ∧ ¬ NFP fork := by
  refine ⟨?_, fork_not_nfp⟩
  intro x
  obtain ⟨root, hr, hp⟩ := fork_wn x
  exact ⟨fun y _ => fork_wn y, fork_wn x, root, hr, conv_of_star hp⟩

theorem fork_nonnormal_nfp : NonnormalNFP fork := by
  intro x root hx hr _
  have hs : ∀ x : Three, ¬ NF fork x → x = .a := by decide
  have he := hs x hx
  subst x
  have he : ∀ root : Three, NF fork root → fork .a root := by decide
  exact .single (he root hr)

theorem fork_sat_iff (x y : Three) :
    Saturate fork x y ↔ fork x y ∨ (x = .a ∧ y = .a) := by
  constructor
  · intro h
    have hs : ∀ x : Three, ¬ NF fork x → x = .a := by decide
    have hx := hs x h.1
    subst x
    cases y <;> decide
  · rintro (h | ⟨rfl, rfl⟩)
    · exact sat_extensive h
    · exact ⟨by decide, .refl _⟩

theorem fork_same_nf_reductions_sat : SameNormalFormReductions fork (Saturate fork) :=
  same_nf_reductions_sat_iff_nonnormal_nfp.mpr fork_nonnormal_nfp

theorem fork_saturation_control :
    SameNormalFormReductions fork (Saturate fork) ∧ ¬ NFP fork ∧
      (∀ x y, Saturate fork x y ↔ fork x y ∨ (x = .a ∧ y = .a)) :=
  ⟨fork_same_nf_reductions_sat, fork_not_nfp, fork_sat_iff⟩

def chainRank : Three → Nat
  | .a => 2
  | .b => 1
  | .r => 0

theorem chain_rank_step :
    ∀ x y, chain x y → chainRank x = chainRank y + 1 := by decide

theorem chain_path_rank {k : Nat} {x y : Three} (p : PathLen chain k x y) :
    chainRank x = chainRank y + k := by
  induction p with
  | nil _ => exact (Nat.add_zero _).symm
  | @cons k start mid finish h _ ih =>
      calc
        chainRank start = chainRank mid + 1 := chain_rank_step start mid h
        _ = (chainRank finish + k) + 1 := congrArg (fun j => j + 1) ih
        _ = chainRank finish + (k + 1) := Nat.add_assoc _ _ _

theorem chain_rootDistance (x : Three) :
    RootDistance chain (fun _ => Three.r) x = chainRank x := by
  have h := chain_path_rank (rootDistance_spec (n := fun _ => Three.r) (chain_root_paths x))
  simpa only [chainRank, Nat.zero_add] using h.symm

def shortcut (x y : Three) : Prop := chain x y ∨ (x = .a ∧ y = .r)

instance : DecidableRel shortcut := fun x y =>
  inferInstanceAs (Decidable (chain x y ∨ (x = .a ∧ y = .r)))

theorem shortcut_rootDistance_a : RootDistance shortcut (fun _ => Three.r) .a = 1 := by
  have hp : PathLen shortcut 1 .a .r := .cons (by decide) (.nil _)
  have hn : RootDistance shortcut (fun _ => Three.r) .a ≠ 0 := by
    intro hz
    have he := (rootDistance_eq_zero_iff hp.toStar).mp hz
    cases he
  exact Nat.le_antisymm (rootDistance_le hp) (Nat.pos_of_ne_zero hn)

theorem shortcut_rootDistance_b : RootDistance shortcut (fun _ => Three.r) .b = 1 := by
  have hp : PathLen shortcut 1 .b .r := .cons (by decide) (.nil _)
  have hn : RootDistance shortcut (fun _ => Three.r) .b ≠ 0 := by
    intro hz
    have he := (rootDistance_eq_zero_iff hp.toStar).mp hz
    cases he
  exact Nat.le_antisymm (rootDistance_le hp) (Nat.pos_of_ne_zero hn)

theorem shortcut_realizes : Realizes shortcut (fun _ => Three.r) := by
  have hp : ∀ x, Star shortcut x .r :=
    fun x => star_mono (fun {_ _} h => Or.inl h) (chain_root_paths x)
  exact ⟨cr_of_reachable_invariant (fun _ => Three.r) (fun {_ _} _ => rfl) hp,
    fun x => ⟨hp x, (show NF shortcut Three.r by decide)⟩⟩

theorem shortestRel_nonmonotone_control :
    Realizes chain (fun _ => Three.r) ∧
    Realizes shortcut (fun _ => Three.r) ∧ Subrel chain shortcut ∧
    ¬ Subrel (ShortestRel chain (fun _ => Three.r))
      (ShortestRel shortcut (fun _ => Three.r)) := by
  refine ⟨star_chain_same_normalizer.2, shortcut_realizes, fun {_ _} h => Or.inl h, ?_⟩
  intro hm
  have he : ShortestRel chain (fun _ => Three.r) .a .b := by
    refine ⟨by decide, ?_⟩
    rw [chain_rootDistance, chain_rootDistance]
    rfl
  have hf := (hm he).2
  rw [shortcut_rootDistance_a, shortcut_rootDistance_b] at hf
  cases hf

end OperatorKO7.Meta.UniqueNormalization.Normalization.Examples

