import OperatorKO7.Meta.UniqueNormalization.Coalgebra
import Mathlib.Data.List.Sublists

/-!
# Finite decision for omega-unification

The algorithm enumerates finite classes on the input subterms and checks symbol
and argument compatibility. Correctness uses the existing UnifClosure and
infinite-term substitution semantics. No finite signature assumption is needed.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.FiniteRationalUnification

open OperatorKO7.Meta.Rewriting

universe u v w z
variable {sigma : Type u} {nu : Type v}

/-- All lists of the specified length over the given finite choices. -/
def tuples {alpha : Type w} (choices : List alpha) : Nat → List (List alpha)
  | 0 => [[]]
  | n + 1 => choices.flatMap (fun x => (tuples choices n).map (List.cons x))

theorem mem_tuples_iff {alpha : Type w} (choices : List alpha) (n : Nat)
    (xs : List alpha) :
    xs ∈ tuples choices n ↔ xs.length = n ∧ ∀ x ∈ xs, x ∈ choices := by
  induction n generalizing xs with
  | zero =>
      cases xs <;> simp [tuples]
  | succ n ih =>
      cases xs with
      | nil => simp [tuples]
      | cons x xs =>
          constructor
          · intro h
            obtain ⟨y, hy, hmem⟩ := List.mem_flatMap.mp h
            obtain ⟨ys, hys, heq⟩ := List.mem_map.mp hmem
            obtain ⟨hyx, hysx⟩ := List.cons.inj heq
            subst y
            subst ys
            obtain ⟨hlen, hall⟩ := (ih xs).mp hys
            refine ⟨congrArg Nat.succ hlen, ?_⟩
            intro a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · exact hy
            · exact hall a ha
          · rintro ⟨hlen, hall⟩
            apply List.mem_flatMap.mpr
            refine ⟨x, hall x (List.mem_cons_self ..), List.mem_map.mpr ?_⟩
            refine ⟨xs, (ih xs).mpr ⟨Nat.succ.inj hlen, ?_⟩, rfl⟩
            intro a ha
            exact hall a (List.mem_cons_of_mem x ha)

/-- The original finite terms supply every vertex inspected by the algorithm. -/
def support (s t : Term sigma nu) : List (Term sigma nu) :=
  subterms s ++ subterms t

theorem mem_support_iff (s t x : Term sigma nu) :
    x ∈ support s t ↔ Subterm x s ∨ Subterm x t := by
  simp only [support, List.mem_append, mem_subterms_iff]

theorem left_mem_support (s t : Term sigma nu) : s ∈ support s t :=
  (mem_support_iff s t s).mpr (Or.inl (Subterm.refl s))

theorem right_mem_support (s t : Term sigma nu) : t ∈ support s t :=
  (mem_support_iff s t t).mpr (Or.inr (Subterm.refl t))

theorem arg_mem_support {s t : Term sigma nu} {f : sigma}
    {xs : List (Term sigma nu)} (happ : Term.app f xs ∈ support s t)
    {x : Term sigma nu} (hx : x ∈ xs) : x ∈ support s t := by
  have hsub : Subterm x (.app f xs) := Subterm.arg hx (Subterm.refl x)
  rcases (mem_support_iff s t _).mp happ with hs | ht
  · exact (mem_support_iff s t x).mpr (Or.inl (hsub.trans hs))
  · exact (mem_support_iff s t x).mpr (Or.inr (hsub.trans ht))

/-- One possible class for each input-support vertex; duplicate classes are permitted. -/
def candidates (s t : Term sigma nu) : List (List (List (Term sigma nu))) :=
  tuples (support s t).sublists (support s t).length

def forall₂Decision {alpha : Type w} {beta : Type z}
    (P : alpha → beta → Prop) [DecidableRel P] :
    (xs : List alpha) → (ys : List beta) → Decidable (List.Forall₂ P xs ys)
  | [], [] => isTrue List.Forall₂.nil
  | [], _ :: _ => isFalse (fun h => by cases h)
  | _ :: _, [] => isFalse (fun h => by cases h)
  | x :: xs, y :: ys => by
      cases (inferInstance : Decidable (P x y)) with
      | isFalse hn =>
          exact isFalse (fun h => by cases h with | cons hp _ => exact hn hp)
      | isTrue hp =>
          cases forall₂Decision P xs ys with
          | isFalse hn =>
              exact isFalse (fun h => by cases h with | cons _ hs => exact hn hs)
          | isTrue hs => exact isTrue (List.Forall₂.cons hp hs)

instance forall₂Decidable {alpha : Type w} {beta : Type z}
    (P : alpha → beta → Prop) [DecidableRel P] (xs : List alpha) (ys : List beta) :
    Decidable (List.Forall₂ P xs ys) := forall₂Decision P xs ys

instance classesRelDecidable [DecidableEq sigma] [DecidableEq nu]
    (Cs : List (List (Term sigma nu))) (a b : Term sigma nu) :
    Decidable (classesRel Cs a b) := by
  unfold classesRel
  infer_instance

/-- Application pairs must have equal symbols and related arguments. -/
def AppCompatible (Cs : List (List (Term sigma nu))) :
    Term sigma nu → Term sigma nu → Prop
  | .app f xs, .app g ys => f = g ∧ List.Forall₂ (classesRel Cs) xs ys
  | _, _ => True

instance appCompatibleDecidable [DecidableEq sigma] [DecidableEq nu]
    (Cs : List (List (Term sigma nu))) (a b : Term sigma nu) :
    Decidable (AppCompatible Cs a b) := by
  cases a <;> cases b <;> simp only [AppCompatible] <;> infer_instance

/-- All quantifiers range over finite class lists and their members. -/
def Valid (Cs : List (List (Term sigma nu))) : Prop :=
  (∀ C ∈ Cs, ∀ D ∈ Cs, ∀ x ∈ C, x ∈ D → ∀ y ∈ D, y ∈ C) ∧
  (∀ C ∈ Cs, ∀ a ∈ C, ∀ b ∈ C, AppCompatible Cs a b)

instance validDecidable [DecidableEq sigma] [DecidableEq nu]
    (Cs : List (List (Term sigma nu))) : Decidable (Valid Cs) := by
  unfold Valid
  infer_instance

theorem Valid.unifClosure {Cs : List (List (Term sigma nu))} (h : Valid Cs) :
    UnifClosure (classesRel Cs) :=
  unifClosure_classesRel Cs h.1
    (fun C hC f g xs ys hx hy => h.2 C hC (.app f xs) hx (.app g ys) hy)

def sharedDecision [DecidableEq sigma] [DecidableEq nu] (s t : Term sigma nu) : Bool :=
  decide (∃ Cs ∈ candidates s t, Valid Cs ∧ classesRel Cs s t)

theorem sharedDecision_sound [DecidableEq sigma] [DecidableEq nu]
    {s t : Term sigma nu} (h : sharedDecision s t = true) :
    OmegaUnifiableShared s t := by
  obtain ⟨Cs, _, hv, hst⟩ :
      ∃ Cs ∈ candidates s t, Valid Cs ∧ classesRel Cs s t := by
    simpa only [sharedDecision, decide_eq_true_eq] using h
  exact ⟨classesRel Cs, hv.unifClosure, hst⟩

/-- Restrict a semantic equivalence class to the finite input support. -/
def classOf (S : List (Term sigma nu)) (E : Term sigma nu → Term sigma nu → Prop)
    [DecidableRel E] (a : Term sigma nu) : List (Term sigma nu) :=
  S.filter (fun b => decide (E a b))

theorem mem_classOf_iff (S : List (Term sigma nu))
    (E : Term sigma nu → Term sigma nu → Prop) [DecidableRel E]
    (a b : Term sigma nu) :
    b ∈ classOf S E a ↔ b ∈ S ∧ E a b := by
  simp only [classOf, List.mem_filter, decide_eq_true_eq]

def restrictedClasses (S : List (Term sigma nu))
    (E : Term sigma nu → Term sigma nu → Prop) [DecidableRel E] :
    List (List (Term sigma nu)) :=
  S.map (classOf S E)

theorem classOf_mem_restrictedClasses {S : List (Term sigma nu)}
    {E : Term sigma nu → Term sigma nu → Prop} [DecidableRel E]
    {a : Term sigma nu} (ha : a ∈ S) :
    classOf S E a ∈ restrictedClasses S E :=
  List.mem_map.mpr ⟨a, ha, rfl⟩

theorem restrictedClasses_rel_of {S : List (Term sigma nu)}
    {E : Term sigma nu → Term sigma nu → Prop} [DecidableRel E]
    (hE : UnifClosure E) {a b : Term sigma nu} (ha : a ∈ S) (hb : b ∈ S)
    (hab : E a b) : classesRel (restrictedClasses S E) a b :=
  Or.inr ⟨classOf S E a, classOf_mem_restrictedClasses ha,
    (mem_classOf_iff S E a a).mpr ⟨ha, hE.rfl' a⟩,
    (mem_classOf_iff S E a b).mpr ⟨hb, hab⟩⟩

theorem restrictedClasses_rel_iff {S : List (Term sigma nu)}
    {E : Term sigma nu → Term sigma nu → Prop} [DecidableRel E]
    (hE : UnifClosure E) {a b : Term sigma nu} (ha : a ∈ S) (hb : b ∈ S) :
    classesRel (restrictedClasses S E) a b ↔ E a b := by
  constructor
  · rintro (rfl | ⟨C, hC, haC, hbC⟩)
    · exact hE.rfl' _
    · obtain ⟨c, _, hc⟩ := List.mem_map.mp hC
      subst C
      exact hE.trans' (hE.symm' ((mem_classOf_iff S E c a).mp haC).2)
        ((mem_classOf_iff S E c b).mp hbC).2
  · exact restrictedClasses_rel_of hE ha hb

theorem forall₂_map_on_members {alpha : Type w} {beta : Type z}
    {P Q : alpha → beta → Prop} {xs : List alpha} {ys : List beta}
    (h : List.Forall₂ P xs ys)
    (hmap : ∀ x ∈ xs, ∀ y ∈ ys, P x y → Q x y) : List.Forall₂ Q xs ys := by
  revert hmap
  induction h with
  | nil => exact fun _ => List.Forall₂.nil
  | @cons x y xs ys hxy htail ih =>
      intro hmap
      refine List.Forall₂.cons
        (hmap x (List.mem_cons_self ..) y (List.mem_cons_self ..) hxy) (ih ?_)
      intro a ha b hb hab
      exact hmap a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem y hb) hab

theorem restrictedClasses_valid {S : List (Term sigma nu)}
    {E : Term sigma nu → Term sigma nu → Prop} [DecidableRel E]
    (hE : UnifClosure E)
    (hargs : ∀ f xs, Term.app f xs ∈ S → ∀ x ∈ xs, x ∈ S) :
    Valid (restrictedClasses S E) := by
  constructor
  · intro C hC D hD x hxC hxD y hyD
    obtain ⟨c, _, hc⟩ := List.mem_map.mp hC
    obtain ⟨d, _, hd⟩ := List.mem_map.mp hD
    subst C
    subst D
    have hcx := (mem_classOf_iff S E c x).mp hxC
    have hdx := (mem_classOf_iff S E d x).mp hxD
    have hdy := (mem_classOf_iff S E d y).mp hyD
    exact (mem_classOf_iff S E c y).mpr
      ⟨hdy.1, hE.trans' hcx.2 (hE.trans' (hE.symm' hdx.2) hdy.2)⟩
  · intro C hC a ha b hb
    obtain ⟨c, _, hc⟩ := List.mem_map.mp hC
    subst C
    have hca := (mem_classOf_iff S E c a).mp ha
    have hcb := (mem_classOf_iff S E c b).mp hb
    have hab : E a b := hE.trans' (hE.symm' hca.2) hcb.2
    cases a with
    | var _ => trivial
    | app f xs =>
        cases b with
        | var _ => trivial
        | app g ys =>
            obtain ⟨hfg, hall⟩ := hE.decomp hab
            refine ⟨hfg, forall₂_map_on_members hall ?_⟩
            intro x hx y hy hxy
            exact restrictedClasses_rel_of hE
              (hargs f xs hca.1 x hx) (hargs g ys hcb.1 y hy) hxy

theorem restrictedClasses_mem_candidates {s t : Term sigma nu}
    (E : Term sigma nu → Term sigma nu → Prop) [DecidableRel E] :
    restrictedClasses (support s t) E ∈ candidates s t := by
  apply (mem_tuples_iff _ _ _).mpr
  constructor
  · simp only [restrictedClasses, List.length_map]
  · intro C hC
    obtain ⟨a, _, ha⟩ := List.mem_map.mp hC
    subst C
    exact List.mem_sublists.mpr List.filter_sublist

theorem finite_certificate_complete {s t : Term sigma nu}
    (h : OmegaUnifiableShared s t) :
    ∃ Cs ∈ candidates s t, Valid Cs ∧ classesRel Cs s t := by
  classical
  obtain ⟨E, hE, hst⟩ := h
  refine ⟨restrictedClasses (support s t) E, restrictedClasses_mem_candidates E, ?_, ?_⟩
  · exact restrictedClasses_valid hE
      (fun _ _ happ _ hx => arg_mem_support happ hx)
  · exact restrictedClasses_rel_of hE (left_mem_support s t) (right_mem_support s t) hst

theorem sharedDecision_complete [DecidableEq sigma] [DecidableEq nu]
    {s t : Term sigma nu} (h : OmegaUnifiableShared s t) :
    sharedDecision s t = true := by
  simpa only [sharedDecision, decide_eq_true_eq] using finite_certificate_complete h

theorem sharedDecision_true_iff [DecidableEq sigma] [DecidableEq nu]
    (s t : Term sigma nu) : sharedDecision s t = true ↔ OmegaUnifiableShared s t :=
  ⟨sharedDecision_sound, sharedDecision_complete⟩

theorem sharedDecision_infinite_iff [DecidableEq sigma] [DecidableEq nu]
    (s t : Term sigma nu) :
    sharedDecision s t = true ↔ InfiniteOmegaUnifiableShared s t :=
  (sharedDecision_true_iff s t).trans (omegaUnifiableShared_iff_infinite s t)

/-- Distinct variable alphabets implement the existing rename-apart convention. -/
def decision [DecidableEq sigma] [DecidableEq nu] (s t : Term sigma nu) : Bool :=
  sharedDecision (leftCopy s) (rightCopy t)

theorem decision_true_iff [DecidableEq sigma] [DecidableEq nu]
    (s t : Term sigma nu) : decision s t = true ↔ OmegaUnifiable s t :=
  sharedDecision_true_iff (leftCopy s) (rightCopy t)

theorem decision_infinite_iff [DecidableEq sigma] [DecidableEq nu]
    (s t : Term sigma nu) : decision s t = true ↔ InfiniteOmegaUnifiable s t :=
  (decision_true_iff s t).trans (omegaUnifiable_iff_infinite s t)

theorem sharedDecision_false_iff [DecidableEq sigma] [DecidableEq nu]
    (s t : Term sigma nu) : sharedDecision s t = false ↔ ¬ OmegaUnifiableShared s t := by
  rw [← sharedDecision_true_iff]
  cases sharedDecision s t <;> simp

theorem decision_false_iff [DecidableEq sigma] [DecidableEq nu]
    (s t : Term sigma nu) : decision s t = false ↔ ¬ OmegaUnifiable s t := by
  rw [← decision_true_iff]
  cases decision s t <;> simp

theorem occursCheck_accepted :
    sharedDecision OccursCheck.xTm OccursCheck.fxTm = true :=
  sharedDecision_complete OccursCheck.omegaUnifiableShared

theorem occursCheck_separates_finite_unification :
    sharedDecision OccursCheck.xTm OccursCheck.fxTm = true ∧
      ¬ ∃ r : Subst Nat Nat,
        Subst.apply r OccursCheck.xTm = Subst.apply r OccursCheck.fxTm :=
  ⟨occursCheck_accepted, OccursCheck.not_unifiable⟩

/-! ## Executable certificates and exact finite search size -/

theorem length_flatMap_of_constant {alpha : Type w} {beta : Type z}
    (xs : List alpha) (f : alpha → List beta) (n : Nat)
    (hn : ∀ x ∈ xs, (f x).length = n) :
    (xs.flatMap f).length = xs.length * n := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.flatMap_cons, List.length_append, hn x (List.mem_cons_self ..),
        ih (fun a ha => hn a (List.mem_cons_of_mem x ha))]
      simp only [List.length_cons, Nat.succ_mul]
      exact Nat.add_comm _ _

theorem length_tuples {alpha : Type w} (choices : List alpha) (n : Nat) :
    (tuples choices n).length = choices.length ^ n := by
  induction n with
  | zero => simp [tuples]
  | succ n ih =>
      rw [tuples, length_flatMap_of_constant choices _ (choices.length ^ n)
        (fun _ _ => by simp only [List.length_map, ih])]
      rw [pow_succ]
      exact Nat.mul_comm _ _

theorem candidates_length (s t : Term sigma nu) :
    (candidates s t).length = 2 ^ ((support s t).length * (support s t).length) := by
  rw [candidates, length_tuples, List.length_sublists, ← pow_mul]

/-- Search returns the first accepted finite class list, not only a Boolean. -/
def findCertificate [DecidableEq sigma] [DecidableEq nu] (s t : Term sigma nu) :
    Option (List (List (Term sigma nu))) :=
  (candidates s t).find? (fun Cs => decide (Valid Cs ∧ classesRel Cs s t))

theorem findCertificate_spec [DecidableEq sigma] [DecidableEq nu]
    {s t : Term sigma nu} {Cs : List (List (Term sigma nu))}
    (h : findCertificate s t = some Cs) :
    Cs ∈ candidates s t ∧ Valid Cs ∧ classesRel Cs s t := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have hc := List.find?_some h
  simpa only [decide_eq_true_eq] using hc

theorem findCertificate_isSome_iff [DecidableEq sigma] [DecidableEq nu]
    (s t : Term sigma nu) :
    (findCertificate s t).isSome = true ↔ OmegaUnifiableShared s t := by
  constructor
  · intro h
    have hgood : ∃ Cs ∈ candidates s t, Valid Cs ∧ classesRel Cs s t := by
      simpa only [findCertificate, List.find?_isSome, decide_eq_true_eq] using h
    obtain ⟨Cs, _, hv, hst⟩ := hgood
    exact ⟨classesRel Cs, hv.unifClosure, hst⟩
  · intro h
    have hgood := finite_certificate_complete h
    simpa only [findCertificate, List.find?_isSome, decide_eq_true_eq] using hgood

theorem findCertificate_none_iff [DecidableEq sigma] [DecidableEq nu]
    (s t : Term sigma nu) :
    findCertificate s t = none ↔ ¬ OmegaUnifiableShared s t := by
  rw [← findCertificate_isSome_iff]
  cases findCertificate s t <;> simp

theorem findCertificate_none_iff_no_infinite [DecidableEq sigma] [DecidableEq nu]
    (s t : Term sigma nu) :
    findCertificate s t = none ↔ ¬ InfiniteOmegaUnifiableShared s t := by
  rw [findCertificate_none_iff, omegaUnifiableShared_iff_infinite]

theorem findCertificate_sizes [DecidableEq sigma] [DecidableEq nu]
    {s t : Term sigma nu} {Cs : List (List (Term sigma nu))}
    (h : findCertificate s t = some Cs) :
    Cs.length = (support s t).length ∧
      ∀ C ∈ Cs, List.Sublist C (support s t) := by
  have hmem := (findCertificate_spec h).1
  obtain ⟨hlen, hall⟩ := (mem_tuples_iff _ _ _).mp hmem
  exact ⟨hlen, fun C hC => List.mem_sublists.mp (hall C hC)⟩

/-- The returned certificate determines an actual substitution into infinite terms. -/
noncomputable def certificateSubst (Cs : List (List (Term sigma nu))) (h : Valid Cs) :
    InfSubst sigma nu Unit :=
  fun x => unfoldQ h.unifClosure (.var x)

theorem findCertificate_subst_solves [DecidableEq sigma] [DecidableEq nu]
    {s t : Term sigma nu} {Cs : List (List (Term sigma nu))}
    (h : findCertificate s t = some Cs) :
    InfApply (certificateSubst Cs (findCertificate_spec h).2.1) s =
      InfApply (certificateSubst Cs (findCertificate_spec h).2.1) t := by
  unfold certificateSubst
  rw [infApply_unfoldQ, infApply_unfoldQ]
  exact unfoldQ_eq_of_rel (findCertificate_spec h).2.1.unifClosure
    (findCertificate_spec h).2.2

instance omegaSharedDecidable [DecidableEq sigma] [DecidableEq nu]
    (s t : Term sigma nu) : Decidable (OmegaUnifiableShared s t) :=
  if h : sharedDecision s t = true then
    isTrue ((sharedDecision_true_iff s t).mp h)
  else
    isFalse (fun hs => h ((sharedDecision_true_iff s t).mpr hs))

instance omegaDecidable [DecidableEq sigma] [DecidableEq nu]
    (s t : Term sigma nu) : Decidable (OmegaUnifiable s t) :=
  if h : decision s t = true then
    isTrue ((decision_true_iff s t).mp h)
  else
    isFalse (fun hs => h ((decision_true_iff s t).mpr hs))

theorem sharedDecision_symbol_clash [DecidableEq sigma] [DecidableEq nu]
    {f g : sigma} (hfg : f ≠ g) (xs ys : List (Term sigma nu)) :
    sharedDecision (.app f xs) (.app g ys) = false := by
  apply (sharedDecision_false_iff _ _).mpr
  rintro ⟨E, hE, hrel⟩
  exact hfg (hE.decomp hrel).1

theorem sharedDecision_arity_clash [DecidableEq sigma] [DecidableEq nu]
    (f g : sigma) {xs ys : List (Term sigma nu)} (hlen : xs.length ≠ ys.length) :
    sharedDecision (.app f xs) (.app g ys) = false := by
  apply (sharedDecision_false_iff _ _).mpr
  rintro ⟨E, hE, hrel⟩
  exact hlen (hE.decomp hrel).2.length_eq

theorem occursCheck_certificate_exists :
    (findCertificate OccursCheck.xTm OccursCheck.fxTm).isSome = true :=
  (findCertificate_isSome_iff _ _).mpr OccursCheck.omegaUnifiableShared


/-! ## Finite-state infinite-term substitutions -/

/-- The certificate classes represented by a finite list of terms. -/
abbrev FiniteState (S : List (Term sigma nu)) (Cs : List (List (Term sigma nu)))
    (hv : Valid Cs) :=
  {q : UClass hv.unifClosure //
    q ∈ S.map (Quotient.mk (unifSetoid hv.unifClosure))}

def stateOf (S : List (Term sigma nu)) (Cs : List (List (Term sigma nu)))
    (hv : Valid Cs) (t : Term sigma nu) (ht : t ∈ S) : FiniteState S Cs hv :=
  ⟨Quotient.mk (unifSetoid hv.unifClosure) t, List.mem_map.mpr ⟨t, ht, rfl⟩⟩

instance finiteStateFinite (S : List (Term sigma nu))
    (Cs : List (List (Term sigma nu))) (hv : Valid Cs) :
    Finite (FiniteState S Cs hv) := by
  let fromIndex : Fin S.length → FiniteState S Cs hv :=
    fun i => stateOf S Cs hv (S.get i) (List.get_mem S i)
  apply Finite.of_surjective fromIndex
  rintro ⟨q, hq⟩
  obtain ⟨t, ht, hq⟩ := List.mem_map.mp hq
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ht
  refine ⟨i, Subtype.ext ?_⟩
  exact (congrArg (Quotient.mk (unifSetoid hv.unifClosure)) hi).trans hq

theorem application_representative_mem
    {S : List (Term sigma nu)} {Cs : List (List (Term sigma nu))}
    (hv : Valid Cs) (hCs : ∀ C ∈ Cs, ∀ t ∈ C, t ∈ S)
    (q : FiniteState S Cs hv) {f : sigma} {xs : List (Term sigma nu)}
    (happ : Quotient.mk (unifSetoid hv.unifClosure) (.app f xs) = q.val) :
    Term.app f xs ∈ S := by
  obtain ⟨t, ht, hq⟩ := List.mem_map.mp q.property
  have hrel : classesRel Cs (.app f xs) t :=
    (Quotient.eq).mp (happ.trans hq.symm)
  rcases hrel with heq | ⟨C, hC, hmem, _⟩
  · rw [heq]
    exact ht
  · exact hCs C hC _ hmem

/-- Every child chosen by the existing infinite unfolding stays in finite support. -/
theorem closureViewQ_children_supported
    {S : List (Term sigma nu)} {Cs : List (List (Term sigma nu))}
    (hv : Valid Cs) (hCs : ∀ C ∈ Cs, ∀ t ∈ C, t ∈ S)
    (hargs : ∀ f xs, Term.app f xs ∈ S → ∀ x ∈ xs, x ∈ S)
    (q : FiniteState S Cs hv) :
    ∀ i, (closureViewQ hv.unifClosure q.val).2 i ∈
      S.map (Quotient.mk (unifSetoid hv.unifClosure)) := by
  classical
  by_cases h : Nonempty (QAppRep hv.unifClosure q.val)
  · let r := chooseQAppRep h
    have hmem : Term.app r.head r.args ∈ S :=
      application_representative_mem hv hCs q r.class_eq
    have hview : closureViewQ hv.unifClosure q.val =
        (⟨Sum.inr (r.head, r.args.length),
          fun i => Quotient.mk (unifSetoid hv.unifClosure) (r.args.get i)⟩ :
          (infTermP sigma Unit) (UClass hv.unifClosure)) := by
      rw [closureViewQ]
      exact dif_pos h
    rw [hview]
    intro i
    exact List.mem_map.mpr ⟨r.args.get i,
      hargs r.head r.args hmem _ (List.get_mem r.args i), rfl⟩
  · have hview : closureViewQ hv.unifClosure q.val =
        (⟨Sum.inl (), fun i => Fin.elim0 i⟩ :
          (infTermP sigma Unit) (UClass hv.unifClosure)) := by
      rw [closureViewQ]
      exact dif_neg h
    rw [hview]
    intro i
    exact Fin.elim0 i

noncomputable def finiteView (S : List (Term sigma nu))
    (Cs : List (List (Term sigma nu))) (hv : Valid Cs)
    (hCs : ∀ C ∈ Cs, ∀ t ∈ C, t ∈ S)
    (hargs : ∀ f xs, Term.app f xs ∈ S → ∀ x ∈ xs, x ∈ S)
    (q : FiniteState S Cs hv) : (infTermP sigma Unit) (FiniteState S Cs hv) :=
  ⟨(closureViewQ hv.unifClosure q.val).1,
    fun i => ⟨(closureViewQ hv.unifClosure q.val).2 i,
      closureViewQ_children_supported hv hCs hargs q i⟩⟩

theorem finiteView_corec_eq
    {S : List (Term sigma nu)} {Cs : List (List (Term sigma nu))}
    (hv : Valid Cs) (hCs : ∀ C ∈ Cs, ∀ t ∈ C, t ∈ S)
    (hargs : ∀ f xs, Term.app f xs ∈ S → ∀ x ∈ xs, x ∈ S)
    (q : FiniteState S Cs hv) :
    PFunctor.M.corec (finiteView S Cs hv hCs hargs) q =
      PFunctor.M.corec (closureViewQ hv.unifClosure) q.val := by
  have heq :=
    PFunctor.M.corec_unique (finiteView S Cs hv hCs hargs)
      (fun x : FiniteState S Cs hv =>
        PFunctor.M.corec (closureViewQ hv.unifClosure) x.val)
      (by
        intro x
        rw [PFunctor.M.dest_corec]
        rfl)
  exact (congrFun heq q).symm

/-- Variables outside the input support receive the fixed supported state. -/
noncomputable def finiteAssignment (S : List (Term sigma nu))
    (Cs : List (List (Term sigma nu))) (hv : Valid Cs)
    (base : Term sigma nu) (hbase : base ∈ S) (x : nu) : FiniteState S Cs hv := by
  classical
  exact if hx : Term.var x ∈ S then stateOf S Cs hv (.var x) hx
    else stateOf S Cs hv base hbase

theorem finiteAssignment_of_mem
    {S : List (Term sigma nu)} {Cs : List (List (Term sigma nu))}
    (hv : Valid Cs) (base : Term sigma nu) (hbase : base ∈ S)
    (x : nu) (hx : Term.var x ∈ S) :
    finiteAssignment S Cs hv base hbase x = stateOf S Cs hv (.var x) hx := by
  simp only [finiteAssignment, dif_pos hx]

/-- The finite-state substitution agrees with certificate unfolding on every
supported term, including all terms occurring in the input. -/
theorem finiteAssignment_applies
    {S : List (Term sigma nu)} {Cs : List (List (Term sigma nu))}
    (hv : Valid Cs) (hCs : ∀ C ∈ Cs, ∀ t ∈ C, t ∈ S)
    (hargs : ∀ f xs, Term.app f xs ∈ S → ∀ x ∈ xs, x ∈ S)
    (base : Term sigma nu) (hbase : base ∈ S)
    (t : Term sigma nu) (ht : t ∈ S) :
    InfApply (fun x => PFunctor.M.corec (finiteView S Cs hv hCs hargs)
      (finiteAssignment S Cs hv base hbase x)) t = unfoldQ hv.unifClosure t := by
  revert ht
  induction t using Term.rec' with
  | hvar x =>
      intro ht
      simp only [InfApply]
      change PFunctor.M.corec (finiteView S Cs hv hCs hargs)
        (finiteAssignment S Cs hv base hbase x) = _
      rw [finiteAssignment_of_mem hv base hbase x ht, finiteView_corec_eq]
      rfl
  | happ f xs ih =>
      intro ht
      simp only [InfApply]
      rw [unfoldQ_app]
      apply congrArg (InfTerm.app f)
      exact List.map_congr_left (fun x hx => ih x hx (hargs f xs ht x hx))

/-- Existence of a shared substitution whose variable images all unfold from
one finite coalgebra. This asserts a rational solution exists, not that every
infinite solution is rational. -/
def RationalOmegaUnifiableShared (s t : Term sigma nu) : Prop :=
  ∃ Q : Type (max u v), Finite Q ∧
    ∃ view : Q → (infTermP sigma Unit) Q, ∃ assignment : nu → Q,
      InfApply (fun x => PFunctor.M.corec view (assignment x)) s =
        InfApply (fun x => PFunctor.M.corec view (assignment x)) t

theorem rationalOmegaUnifiableShared_of_omega {s t : Term sigma nu}
    (h : OmegaUnifiableShared s t) : RationalOmegaUnifiableShared s t := by
  classical
  obtain ⟨Cs, hmem, hv, hst⟩ := finite_certificate_complete h
  have hclasses := ((mem_tuples_iff _ _ _).mp hmem).2
  have hCs : ∀ C ∈ Cs, ∀ x ∈ C, x ∈ support s t := by
    intro C hC x hx
    exact (List.mem_sublists.mp (hclasses C hC)).subset hx
  have hargs : ∀ f xs, Term.app f xs ∈ support s t →
      ∀ x ∈ xs, x ∈ support s t := fun _ _ happ _ hx => arg_mem_support happ hx
  refine ⟨FiniteState (support s t) Cs hv, inferInstance,
    finiteView (support s t) Cs hv hCs hargs,
    finiteAssignment (support s t) Cs hv s (left_mem_support s t), ?_⟩
  rw [finiteAssignment_applies hv hCs hargs s (left_mem_support s t) s
      (left_mem_support s t),
    finiteAssignment_applies hv hCs hargs s (left_mem_support s t) t
      (right_mem_support s t)]
  exact unfoldQ_eq_of_rel hv.unifClosure hst

theorem rationalOmegaUnifiableShared_iff (s t : Term sigma nu) :
    RationalOmegaUnifiableShared s t ↔ OmegaUnifiableShared s t := by
  constructor
  · rintro ⟨Q, _, view, assignment, hst⟩
    exact omegaUnifiableShared_of_infiniteSubst
      (fun x => PFunctor.M.corec view (assignment x)) hst
  · exact rationalOmegaUnifiableShared_of_omega

theorem rational_iff_infinite (s t : Term sigma nu) :
    RationalOmegaUnifiableShared s t ↔ InfiniteOmegaUnifiableShared s t :=
  (rationalOmegaUnifiableShared_iff s t).trans (omegaUnifiableShared_iff_infinite s t)

theorem sharedDecision_rational_iff [DecidableEq sigma] [DecidableEq nu]
    (s t : Term sigma nu) :
    sharedDecision s t = true ↔ RationalOmegaUnifiableShared s t :=
  (sharedDecision_true_iff s t).trans (rationalOmegaUnifiableShared_iff s t).symm

theorem decision_rational_iff [DecidableEq sigma] [DecidableEq nu]
    (s t : Term sigma nu) :
    decision s t = true ↔ RationalOmegaUnifiableShared (leftCopy s) (rightCopy t) :=
  sharedDecision_rational_iff (leftCopy s) (rightCopy t)

theorem occursCheck_rational_witness :
    RationalOmegaUnifiableShared OccursCheck.xTm OccursCheck.fxTm :=
  rationalOmegaUnifiableShared_of_omega OccursCheck.omegaUnifiableShared


/-! ## Whole-system omega-overlap decision and returned counterexamples -/

theorem rule_eq_iff (r s : Rule sigma nu) :
    r = s ↔ r.lhs = s.lhs ∧ r.rhs = s.rhs := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hl, hr⟩
    cases r
    cases s
    cases hl
    cases hr
    rfl

instance ruleDecidableEq [DecidableEq sigma] [DecidableEq nu] :
    DecidableEq (Rule sigma nu) := fun r s =>
  if h : r.lhs = s.lhs ∧ r.rhs = s.rhs then
    isTrue ((rule_eq_iff r s).mpr h)
  else
    isFalse (fun he => h ((rule_eq_iff r s).mp he))

/-- Every ordered rule pair and every subterm of the first left-hand side. -/
def overlapCandidates (R : TRS sigma nu) :
    List (Rule sigma nu × Rule sigma nu × Term sigma nu) :=
  R.flatMap (fun r => R.flatMap (fun s => (subterms r.lhs).map (fun t => (r, s, t))))

theorem mem_overlapCandidates_iff (R : TRS sigma nu)
    (w : Rule sigma nu × Rule sigma nu × Term sigma nu) :
    w ∈ overlapCandidates R ↔
      w.1 ∈ R ∧ w.2.1 ∈ R ∧ Subterm w.2.2 w.1.lhs := by
  rcases w with ⟨r, s, t⟩
  constructor
  · intro h
    obtain ⟨r', hr, hm⟩ := List.mem_flatMap.mp h
    obtain ⟨s', hs, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨t', ht, he⟩ := List.mem_map.mp hm
    cases he
    exact ⟨hr, hs, (mem_subterms_iff _).mp ht⟩
  · rintro ⟨hr, hs, ht⟩
    exact List.mem_flatMap.mpr ⟨r, hr, List.mem_flatMap.mpr
      ⟨s, hs, List.mem_map.mpr ⟨t, (mem_subterms_iff r.lhs).mpr ht, rfl⟩⟩⟩

/-- A non-variable omega-overlap outside the identical-rule root exception. -/
def ForbiddenOmegaOverlap (w : Rule sigma nu × Rule sigma nu × Term sigma nu) : Prop :=
  w.2.2.isApp = true ∧ OmegaUnifiable w.2.2 w.2.1.lhs ∧
    ¬ (w.1 = w.2.1 ∧ w.2.2 = w.1.lhs)

def forbiddenOverlapDecision [DecidableEq sigma] [DecidableEq nu]
    (w : Rule sigma nu × Rule sigma nu × Term sigma nu) : Bool := by
  letI : Decidable (ForbiddenOmegaOverlap w) := by
    unfold ForbiddenOmegaOverlap
    infer_instance
  exact decide (ForbiddenOmegaOverlap w)

theorem forbiddenOverlapDecision_iff [DecidableEq sigma] [DecidableEq nu]
    (w : Rule sigma nu × Rule sigma nu × Term sigma nu) :
    forbiddenOverlapDecision w = true ↔ ForbiddenOmegaOverlap w := by
  simp only [forbiddenOverlapDecision, decide_eq_true_eq]

theorem exists_forbidden_overlap_iff (R : TRS sigma nu) :
    (∃ w ∈ overlapCandidates R, ForbiddenOmegaOverlap w) ↔ ¬ NonOmegaOverlapping R := by
  classical
  constructor
  · rintro ⟨w, hw, happ, huni, hbad⟩ hno
    obtain ⟨hr, hs, hsub⟩ := (mem_overlapCandidates_iff R w).mp hw
    exact hbad (hno w.1 hr w.2.1 hs w.2.2 hsub happ huni)
  · intro hn
    by_contra hnone
    apply hn
    intro r hr s hs t ht happ huni
    by_contra hbad
    exact hnone ⟨(r, s, t),
      (mem_overlapCandidates_iff R (r, s, t)).mpr ⟨hr, hs, ht⟩,
      happ, huni, hbad⟩

/-- The search returns the offending rules and the actual overlapping subterm. -/
def findForbiddenOverlap [DecidableEq sigma] [DecidableEq nu] (R : TRS sigma nu) :
    Option (Rule sigma nu × Rule sigma nu × Term sigma nu) :=
  (overlapCandidates R).find? forbiddenOverlapDecision

theorem findForbiddenOverlap_spec [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {w : Rule sigma nu × Rule sigma nu × Term sigma nu}
    (h : findForbiddenOverlap R = some w) :
    w.1 ∈ R ∧ w.2.1 ∈ R ∧ Subterm w.2.2 w.1.lhs ∧
      w.2.2.isApp = true ∧ OmegaUnifiable w.2.2 w.2.1.lhs ∧
        ¬ (w.1 = w.2.1 ∧ w.2.2 = w.1.lhs) := by
  obtain ⟨hr, hs, ht⟩ :=
    (mem_overlapCandidates_iff R w).mp (List.mem_of_find?_eq_some h)
  have hbad := (forbiddenOverlapDecision_iff w).mp (List.find?_some h)
  exact ⟨hr, hs, ht, hbad⟩

theorem findForbiddenOverlap_isSome_iff [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) :
    (findForbiddenOverlap R).isSome = true ↔ ¬ NonOmegaOverlapping R := by
  simpa only [findForbiddenOverlap, List.find?_isSome, forbiddenOverlapDecision_iff]
    using exists_forbidden_overlap_iff R

theorem findForbiddenOverlap_none_iff [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) :
    findForbiddenOverlap R = none ↔ NonOmegaOverlapping R := by
  classical
  have h := findForbiddenOverlap_isSome_iff R
  cases hf : findForbiddenOverlap R <;> simp_all

/-- Whole-system decision, including the proper-subterm and rule-identity tests. -/
def nonOmegaDecision [DecidableEq sigma] [DecidableEq nu] (R : TRS sigma nu) : Bool :=
  !(findForbiddenOverlap R).isSome

theorem nonOmegaDecision_true_iff [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) :
    nonOmegaDecision R = true ↔ NonOmegaOverlapping R := by
  rw [← findForbiddenOverlap_none_iff]
  unfold nonOmegaDecision
  cases findForbiddenOverlap R <;> simp

theorem nonOmegaDecision_false_iff [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) :
    nonOmegaDecision R = false ↔ ¬ NonOmegaOverlapping R := by
  rw [← nonOmegaDecision_true_iff]
  cases nonOmegaDecision R <;> simp

instance nonOmegaOverlappingDecidable [DecidableEq sigma] [DecidableEq nu]
    (R : TRS sigma nu) : Decidable (NonOmegaOverlapping R) :=
  if h : nonOmegaDecision R = true then
    isTrue ((nonOmegaDecision_true_iff R).mp h)
  else
    isFalse (fun hn => h ((nonOmegaDecision_true_iff R).mpr hn))

theorem findForbiddenOverlap_infinite [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {w : Rule sigma nu × Rule sigma nu × Term sigma nu}
    (h : findForbiddenOverlap R = some w) :
    InfiniteOmegaUnifiable w.2.2 w.2.1.lhs :=
  (omegaUnifiable_iff_infinite _ _).mp (findForbiddenOverlap_spec h).2.2.2.2.1

/-- Every returned overlap also has a returned, renamed-apart finite unifier. -/
theorem findForbiddenOverlap_certificate [DecidableEq sigma] [DecidableEq nu]
    {R : TRS sigma nu} {w : Rule sigma nu × Rule sigma nu × Term sigma nu}
    (h : findForbiddenOverlap R = some w) :
    ∃ Cs, findCertificate (leftCopy w.2.2) (rightCopy w.2.1.lhs) = some Cs := by
  have huni : OmegaUnifiableShared (leftCopy w.2.2) (rightCopy w.2.1.lhs) :=
    (findForbiddenOverlap_spec h).2.2.2.2.1
  have hs := (findCertificate_isSome_iff _ _).mpr huni
  cases hc : findCertificate (leftCopy w.2.2) (rightCopy w.2.1.lhs) with
  | none => simp_all
  | some Cs => exact ⟨Cs, rfl⟩

theorem nonOmegaDecision_nil [DecidableEq sigma] [DecidableEq nu] :
    nonOmegaDecision ([] : TRS sigma nu) = true := rfl

end OperatorKO7.Meta.UniqueNormalization.FiniteRationalUnification
