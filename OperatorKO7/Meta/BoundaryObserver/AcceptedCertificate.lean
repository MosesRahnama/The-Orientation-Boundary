import Init

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.AcceptedCertificate

universe u v w z r s

/-- A certificate interface states its permissions, acceptance rule, and selected property. -/
structure Interface (X : Type u) (W : Type v) (P : X → Prop) where
  permitted : X → W → Prop
  accepts : X → W → Prop
  sound : ∀ x w, permitted x w → accepts x w → P x

/-- Accepted membership requires both permission and acceptance. -/
def Accepted {X : Type u} {W : Type v} {P : X → Prop}
    (C : Interface X W P) (x : X) (w : W) : Prop :=
  C.permitted x w ∧ C.accepts x w

/-- Certificate availability means that the accepted set is inhabited. -/
def Cert {X : Type u} {W : Type v} {P : X → Prop}
    (C : Interface X W P) (x : X) : Prop :=
  ∃ w, Accepted C x w

theorem accepted_sound {X : Type u} {W : Type v} {P : X → Prop}
    (C : Interface X W P) {x : X} {w : W} (h : Accepted C x w) : P x :=
  C.sound x w h.1 h.2

theorem cert_sound {X : Type u} {W : Type v} {P : X → Prop}
    (C : Interface X W P) {x : X} (h : Cert C x) : P x := by
  cases h with
  | intro w hw => exact accepted_sound C hw

/-- The observation carrier contains precisely records of demanded objects. -/
def Observed {X : Type u} {O : Type v} (q : X → O) (D : X → Prop) :=
  {o : O // ∃ x, D x ∧ q x = o}

def observation {X : Type u} {O : Type v} (q : X → O) (D : X → Prop)
    (x : X) (hx : D x) : Observed q D :=
  ⟨q x, ⟨x, hx, rfl⟩⟩

/-- A readout meets every demanded object's accepted-certificate predicate. -/
def Returns {X : Type u} {O : Type v} {W : Type w}
    (q : X → O) (D : X → Prop) (A : X → W → Prop)
    (r : Observed q D → W) : Prop :=
  ∀ x hx, A x (r (observation q D x hx))

/-- Fiber acceptance is the intersection of accepted sets at one observed record. -/
def FiberAccepted {X : Type u} {O : Type v} {W : Type w}
    (q : X → O) (D : X → Prop) (A : X → W → Prop)
    (o : Observed q D) (w : W) : Prop :=
  ∀ x, D x → q x = o.val → A x w

theorem returns_iff_fibers {X : Type u} {O : Type v} {W : Type w}
    (q : X → O) (D : X → Prop) (A : X → W → Prop)
    (r : Observed q D → W) :
    Returns q D A r ↔ ∀ o, FiberAccepted q D A o (r o) := by
  constructor
  · intro h o x hx hq
    have ho : observation q D x hx = o := Subtype.eq hq
    have hv : r (observation q D x hx) = r o := congrArg r ho
    exact hv ▸ h x hx
  · intro h x hx
    exact h (observation q D x hx) x hx rfl

/-- Classical choice selects one common certificate in each observation fiber. -/
theorem exists_readout_iff_fibers {X : Type u} {O : Type v} {W : Type w}
    (q : X → O) (D : X → Prop) (A : X → W → Prop) :
    (∃ r, Returns q D A r) ↔ ∀ o, ∃ w, FiberAccepted q D A o w := by
  constructor
  · intro h o
    cases h with
    | intro r hr =>
        exact ⟨r o, (returns_iff_fibers q D A r).mp hr o⟩
  · intro h
    refine ⟨fun o => Classical.choose (h o), ?_⟩
    apply (returns_iff_fibers q D A _).mpr
    intro o
    exact Classical.choose_spec (h o)

theorem permitted_readout_iff_fibers {X : Type u} {O : Type v} {W : Type w}
    (q : X → O) (D : X → Prop) (A : X → W → Prop)
    (permitted : (Observed q D → W) → Prop) :
    (∃ r, permitted r ∧ Returns q D A r) ↔
      ∃ r, permitted r ∧ ∀ o, FiberAccepted q D A o (r o) := by
  constructor
  · intro h
    cases h with
    | intro r hr =>
        exact ⟨r, hr.1, (returns_iff_fibers q D A r).mp hr.2⟩
  · intro h
    cases h with
    | intro r hr =>
        exact ⟨r, hr.1, (returns_iff_fibers q D A r).mpr hr.2⟩

/-- Soundness of an accepted source certificate establishes the transported property. -/
theorem property_transfer {X : Type u} {A : Type v} {W : Type w}
    (α : X → A) (P : X → Prop) (Q : A → Prop)
    (C : Interface A W Q) (transport : ∀ x, Q (α x) → P x)
    {x : X} (h : Cert C (α x)) : P x :=
  transport x (cert_sound C h)

theorem property_transfer_comp {X : Type u} {A : Type v} {B : Type w}
    (α : X → A) (β : A → B) (P : X → Prop) (Q : A → Prop) (S : B → Prop)
    (hα : ∀ x, Q (α x) → P x) (hβ : ∀ a, S (β a) → Q a) :
    ∀ x, S (β (α x)) → P x :=
  fun x h => hα x (hβ (α x) h)

/-- An acceptance-preserving constructor returns an accepted destination certificate. -/
theorem certificate_transfer {X : Type u} {A : Type v}
    {WX : Type w} {WA : Type z} {P : X → Prop} {Q : A → Prop}
    (α : X → A) (CX : Interface X WX P) (CA : Interface A WA Q)
    (τ : X → WA → WX)
    (preserves : ∀ x w, Accepted CA (α x) w → Accepted CX x (τ x w))
    {x : X} (h : Cert CA (α x)) : Cert CX x := by
  cases h with
  | intro w hw => exact ⟨τ x w, preserves x w hw⟩

theorem certificate_construction_comp {X : Type u} {A : Type v} {B : Type w}
    {WX : Type z} {WA : Type r} {WB : Type s}
    {P : X → Prop} {Q : A → Prop} {S : B → Prop}
    (α : X → A) (β : A → B)
    (CX : Interface X WX P) (CA : Interface A WA Q) (CB : Interface B WB S)
    (τ : X → WA → WX) (σ : A → WB → WA)
    (hτ : ∀ x w, Accepted CA (α x) w → Accepted CX x (τ x w))
    (hσ : ∀ a w, Accepted CB (β a) w → Accepted CA a (σ a w)) :
    ∀ x w, Accepted CB (β (α x)) w →
      Accepted CX x (τ x (σ (α x) w)) :=
  fun x w hw => hτ x (σ (α x) w) (hσ (α x) w hw)

/-- A cumulative family retains every accepted certificate at the next level. -/
def Cumulative {X : Type u} {W : Type v} (A : Nat → X → W → Prop) : Prop :=
  ∀ n x w, A n x w → A (n + 1) x w

def Available {X : Type u} {W : Type v} (A : Nat → X → W → Prop)
    (n : Nat) (x : X) : Prop :=
  ∃ w, A n x w

def Failure {X : Type u} {W : Type v} (A : Nat → X → W → Prop)
    (n : Nat) (x : X) : Prop :=
  ¬ Available A n x

theorem cumulative_le {X : Type u} {W : Type v} (A : Nat → X → W → Prop)
    (hA : Cumulative A) {n m : Nat} (hnm : n ≤ m)
    {x : X} {w : W} (h : A n x w) : A m x w := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact hA _ x w ih

theorem available_mono {X : Type u} {W : Type v} (A : Nat → X → W → Prop)
    (hA : Cumulative A) {n m : Nat} (hnm : n ≤ m)
    {x : X} (h : Available A n x) : Available A m x := by
  cases h with
  | intro w hw => exact ⟨w, cumulative_le A hA hnm hw⟩

theorem failure_antitone {X : Type u} {W : Type v} (A : Nat → X → W → Prop)
    (hA : Cumulative A) {n m : Nat} (hnm : n ≤ m)
    {x : X} (h : Failure A m x) : Failure A n x :=
  fun hn => h (available_mono A hA hnm hn)

/-- Strong induction gives a least index for any inhabited predicate on natural numbers. -/
theorem exists_least_nat (P : Nat → Prop) (h : ∃ n, P n) :
    ∃ k, P k ∧ ∀ n, P n → k ≤ n := by
  have at_index : ∀ n, P n → ∃ k, P k ∧ ∀ m, P m → k ≤ m := by
    intro n
    refine Nat.strongRecOn
      (motive := fun n => P n → ∃ k, P k ∧ ∀ m, P m → k ≤ m) n ?_
    intro n ih hn
    cases Classical.em (∃ m, m < n ∧ P m) with
    | inl smaller =>
        cases smaller with
        | intro m hm => exact ih m hm.1 hm.2
    | inr no_smaller =>
        refine ⟨n, hn, ?_⟩
        intro m hm
        exact Nat.le_of_not_lt (fun hmn => no_smaller ⟨m, hmn, hm⟩)
  cases h with
  | intro n hn => exact at_index n hn

/-- The first level is selected from the proved least-element property. -/
noncomputable def firstLevel {X : Type u} {W : Type v}
    (A : Nat → X → W → Prop) (x : X) (h : ∃ n, Available A n x) : Nat :=
  Classical.choose (exists_least_nat (fun n => Available A n x) h)

theorem firstLevel_spec {X : Type u} {W : Type v}
    (A : Nat → X → W → Prop) (x : X) (h : ∃ n, Available A n x) :
    Available A (firstLevel A x h) x ∧
      ∀ n, Available A n x → firstLevel A x h ≤ n :=
  Classical.choose_spec (exists_least_nat (fun n => Available A n x) h)

theorem available_iff_firstLevel_le {X : Type u} {W : Type v}
    (A : Nat → X → W → Prop) (hA : Cumulative A)
    (x : X) (h : ∃ n, Available A n x) (n : Nat) :
    Available A n x ↔ firstLevel A x h ≤ n := by
  constructor
  · intro hn
    exact (firstLevel_spec A x h).2 n hn
  · intro hn
    exact available_mono A hA hn (firstLevel_spec A x h).1

theorem failure_iff_lt_firstLevel {X : Type u} {W : Type v}
    (A : Nat → X → W → Prop) (hA : Cumulative A)
    (x : X) (h : ∃ n, Available A n x) (n : Nat) :
    Failure A n x ↔ n < firstLevel A x h := by
  constructor
  · intro hn
    apply Nat.not_le.mp
    intro hle
    exact hn ((available_iff_firstLevel_le A hA x h n).mpr hle)
  · intro hlt hn
    exact Nat.not_le_of_lt hlt ((available_iff_firstLevel_le A hA x h n).mp hn)

/-- A path records a finite sequence of steps, including the sequence of length zero. -/
inductive Path {S : Type u} (R : S → S → Prop) : S → S → Prop where
  | refl (s : S) : Path R s s
  | step {s t z : S} : Path R s t → R t z → Path R s z

theorem path_single {S : Type u} (R : S → S → Prop)
    {s t : S} (h : R s t) : Path R s t :=
  Path.step (Path.refl s) h

theorem path_trans {S : Type u} (R : S → S → Prop)
    {s t z : S} (hst : Path R s t) (htz : Path R t z) : Path R s z := by
  induction htz with
  | refl => exact hst
  | step _ edge ih => exact Path.step ih edge

def ForwardInvariant {S : Type u} (R : S → S → Prop) (P : S → Prop) : Prop :=
  ∀ s t, R s t → P s → P t

theorem path_preserves {S : Type u} (R : S → S → Prop) (P : S → Prop)
    (invariant : ForwardInvariant R P) {s t : S} (h : Path R s t) :
    P s → P t := by
  induction h with
  | refl => exact fun hs => hs
  | step _ edge ih => exact fun hs => invariant _ _ edge (ih hs)

/-- The box predicate requires the selected predicate at every reachable state. -/
def Box {S : Type u} (R : S → S → Prop) (P : S → Prop) (s : S) : Prop :=
  ∀ t, Path R s t → P t

theorem box_subset {S : Type u} (R : S → S → Prop) (P : S → Prop) :
    ∀ s, Box R P s → P s :=
  fun s h => h s (Path.refl s)

theorem box_forward {S : Type u} (R : S → S → Prop) (P : S → Prop) :
    ForwardInvariant R (Box R P) :=
  fun _ _ edge hbox z path => hbox z (path_trans R (path_single R edge) path)

theorem box_greatest {S : Type u} (R : S → S → Prop) (P Q : S → Prop)
    (below : ∀ s, Q s → P s) (invariant : ForwardInvariant R Q) :
    ∀ s, Q s → Box R P s :=
  fun _ hs t path => below t (path_preserves R Q invariant path hs)

theorem not_box_iff_reachable_not {S : Type u}
    (R : S → S → Prop) (P : S → Prop) (s : S) :
    ¬ Box R P s ↔ ∃ t, Path R s t ∧ ¬ P t := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro no_bad
    apply h
    intro t path
    apply Classical.byContradiction
    intro hnot
    exact no_bad ⟨t, path, hnot⟩
  · intro h hbox
    cases h with
    | intro t ht => exact ht.2 (hbox t ht.1)

/-- Object sensitivity requires two objects with different answers at the same state. -/
def Exogenous {S : Type u} {O : Type v} {A : Type w}
    (answer : S → O → A) (s : S) : Prop :=
  ∃ o o', answer s o ≠ answer s o'

/-- An echo state gives the same answer at every object coordinate. -/
def Echo {S : Type u} {O : Type v} {A : Type w}
    (answer : S → O → A) (s : S) : Prop :=
  ∀ o o', answer s o = answer s o'

theorem not_exogenous_iff_echo {S : Type u} {O : Type v} {A : Type w}
    (answer : S → O → A) (s : S) : ¬ Exogenous answer s ↔ Echo answer s := by
  constructor
  · intro hn o o'
    exact Classical.byContradiction (fun hne => hn ⟨o, o', hne⟩)
  · intro he hx
    cases hx with
    | intro o rest =>
        cases rest with
        | intro o' hne => exact hne (he o o')

def Persistent {S : Type u} {O : Type v} {A : Type w}
    (R : S → S → Prop) (answer : S → O → A) : S → Prop :=
  Box R (Exogenous answer)

theorem persistent_subset {S : Type u} {O : Type v} {A : Type w}
    (R : S → S → Prop) (answer : S → O → A) :
    ∀ s, Persistent R answer s → Exogenous answer s :=
  box_subset R (Exogenous answer)

theorem persistent_forward {S : Type u} {O : Type v} {A : Type w}
    (R : S → S → Prop) (answer : S → O → A) :
    ForwardInvariant R (Persistent R answer) :=
  box_forward R (Exogenous answer)

theorem persistent_greatest {S : Type u} {O : Type v} {A : Type w}
    (R : S → S → Prop) (answer : S → O → A) (Q : S → Prop)
    (below : ∀ s, Q s → Exogenous answer s) (invariant : ForwardInvariant R Q) :
    ∀ s, Q s → Persistent R answer s :=
  box_greatest R (Exogenous answer) Q below invariant

theorem not_persistent_iff_reachable_echo {S : Type u} {O : Type v} {A : Type w}
    (R : S → S → Prop) (answer : S → O → A) (s : S) :
    ¬ Persistent R answer s ↔ ∃ t, Path R s t ∧ Echo answer t := by
  constructor
  · intro h
    cases (not_box_iff_reachable_not R (Exogenous answer) s).mp h with
    | intro t ht =>
        exact ⟨t, ht.1, (not_exogenous_iff_echo answer t).mp ht.2⟩
  · intro h
    apply (not_box_iff_reachable_not R (Exogenous answer) s).mpr
    cases h with
    | intro t ht =>
        exact ⟨t, ht.1, (not_exogenous_iff_echo answer t).mpr ht.2⟩

/-- The guarded relation retains each original step that preserves the selected predicate. -/
def SafeRel {S : Type u} (R : S → S → Prop) (P : S → Prop) (s t : S) : Prop :=
  R s t ∧ (P s → P t)

theorem safe_subrelation {S : Type u} (R : S → S → Prop) (P : S → Prop) :
    ∀ s t, SafeRel R P s t → R s t :=
  fun _ _ h => h.1

theorem safe_forward {S : Type u} (R : S → S → Prop) (P : S → Prop) :
    ForwardInvariant (SafeRel R P) P :=
  fun _ _ h => h.2

theorem safe_greatest {S : Type u} (R T : S → S → Prop) (P : S → Prop)
    (subrelation : ∀ s t, T s t → R s t) (invariant : ForwardInvariant T P) :
    ∀ s t, T s t → SafeRel R P s t :=
  fun s t h => ⟨subrelation s t h, invariant s t h⟩

theorem safe_box_iff {S : Type u} (R : S → S → Prop) (P : S → Prop) (s : S) :
    Box (SafeRel R P) P s ↔ P s := by
  constructor
  · exact box_subset (SafeRel R P) P s
  · intro hs t path
    exact path_preserves (SafeRel R P) P (safe_forward R P) path hs

theorem safe_box_eq {S : Type u} (R : S → S → Prop) (P : S → Prop) :
    Box (SafeRel R P) P = P :=
  funext (fun s => propext (safe_box_iff R P s))

theorem persistent_repair_iff {S : Type u} {O : Type v} {A : Type w}
    (R : S → S → Prop) (answer : S → O → A) (s : S) :
    Persistent (SafeRel R (Exogenous answer)) answer s ↔ Exogenous answer s :=
  safe_box_iff R (Exogenous answer) s

namespace Examples

/-- The empty and singleton interfaces certify the same constant true property. -/
def emptyInterface : Interface Unit Empty (fun _ => True) where
  permitted := fun _ _ => True
  accepts := fun _ _ => True
  sound := fun _ _ _ _ => True.intro

def singletonInterface : Interface Unit Unit (fun _ => True) where
  permitted := fun _ _ => True
  accepts := fun _ _ => True
  sound := fun _ _ _ _ => True.intro

theorem no_empty_certificate (x : Unit) : ¬ Cert emptyInterface x := by
  intro h
  cases h with
  | intro w _ => cases w

theorem singleton_certificate (x : Unit) : Cert singletonInterface x :=
  ⟨(), True.intro, True.intro⟩

def collapsedObservation (_ : Bool) : Unit := ()

def allObjects (_ : Bool) : Prop := True

def matchesObject (x w : Bool) : Prop := w = x

theorem pointwise_certificates : ∀ x, ∃ w, matchesObject x w :=
  fun x => ⟨x, rfl⟩

/-- Equal observations cannot support these two incompatible singleton demands. -/
theorem no_joint_readout :
    ¬ ∃ r, Returns collapsedObservation allObjects matchesObject r := by
  intro h
  cases h with
  | intro r hr =>
      have hfalse :
          r (observation collapsedObservation allObjects false True.intro) = false :=
        hr false True.intro
      have htrue :
          r (observation collapsedObservation allObjects true True.intro) = true :=
        hr true True.intro
      have same_record :
          observation collapsedObservation allObjects false True.intro =
            observation collapsedObservation allObjects true True.intro :=
        Subtype.eq rfl
      have impossible : false = true :=
        hfalse.symm.trans ((congrArg r same_record).trans htrue)
      cases impossible

def constantAbstraction (_ : Nat) : Unit := ()

theorem constant_property_transfer (n : Nat) : 0 ≤ n :=
  property_transfer constantAbstraction (fun n => 0 ≤ n) (fun _ => True)
    singletonInterface (fun n _ => Nat.zero_le n) (singleton_certificate ())

theorem constantAbstraction_no_left_inverse :
    ¬ ∃ g : Unit → Nat, ∀ n, g (constantAbstraction n) = n := by
  intro h
  cases h with
  | intro g hg =>
      have impossible : (0 : Nat) = 1 := (hg 0).symm.trans (hg 1)
      cases impossible

/-- This additional control transfers a property with both true and false instances. -/
def flagInterface : Interface Bool Unit (fun b => b = true) where
  permitted := fun _ _ => True
  accepts := fun b _ => b = true
  sound := fun _ _ _ h => h

def flagProjection (x : Bool × Nat) : Bool := x.1

theorem flag_certificate_iff (b : Bool) : Cert flagInterface b ↔ b = true := by
  constructor
  · exact cert_sound flagInterface
  · intro h
    exact ⟨(), True.intro, h⟩

theorem true_flag_certificate : Cert flagInterface true :=
  (flag_certificate_iff true).mpr rfl

theorem false_flag_no_certificate : ¬ Cert flagInterface false := by
  intro h
  have impossible : false = true := (flag_certificate_iff false).mp h
  cases impossible

theorem flag_property_transfer (x : Bool × Nat)
    (h : Cert flagInterface (flagProjection x)) : x.1 = true :=
  property_transfer flagProjection (fun x => x.1 = true) (fun b => b = true)
    flagInterface (fun _ h => h) h

theorem flagProjection_no_left_inverse :
    ¬ ∃ g : Bool → Bool × Nat, ∀ x, g (flagProjection x) = x := by
  intro h
  cases h with
  | intro g hg =>
      have pair_eq : ((true, 0) : Bool × Nat) = (true, 1) :=
        (hg (true, 0)).symm.trans (hg (true, 1))
      have impossible : (0 : Nat) = 1 := congrArg Prod.snd pair_eq
      cases impossible

/-- The accepted set is empty below level two and contains its unique member thereafter. -/
def delayed (n : Nat) (_ : Unit) (_ : Unit) : Prop := 2 ≤ n

theorem delayed_cumulative : Cumulative delayed :=
  fun _ _ _ h => Nat.le.step h

theorem delayed_success_two (x : Unit) : Available delayed 2 x :=
  ⟨(), Nat.le_refl 2⟩

theorem delayed_eventual (x : Unit) : ∃ n, Available delayed n x :=
  ⟨2, delayed_success_two x⟩

noncomputable def delayedLevel (x : Unit) : Nat :=
  firstLevel delayed x (delayed_eventual x)

theorem delayedLevel_eq_two (x : Unit) : delayedLevel x = 2 := by
  have spec := firstLevel_spec delayed x (delayed_eventual x)
  apply Nat.le_antisymm
  · exact spec.2 2 (delayed_success_two x)
  · cases spec.1 with
    | intro w hw => exact hw

theorem delayedLevel_constant (x y : Unit) : delayedLevel x = delayedLevel y :=
  (delayedLevel_eq_two x).trans (delayedLevel_eq_two y).symm

theorem delayed_failure_zero (x : Unit) : Failure delayed 0 x := by
  intro h
  cases h with
  | intro w hw => exact Nat.not_succ_le_zero 1 hw

theorem delayed_failure_with_known_level :
    Failure delayed 0 () ∧ delayedLevel () = 2 :=
  ⟨delayed_failure_zero (), delayedLevel_eq_two ()⟩

/-- The false state reads the object; the true state returns the constant false answer. -/
def lossAnswer : Bool → Bool → Bool
  | false, o => o
  | true, _ => false

def lossStep (s t : Bool) : Prop := s = t ∨ (s = false ∧ t = true)

theorem loss_initial_sensitive : Exogenous lossAnswer false := by
  refine ⟨false, true, ?_⟩
  intro impossible
  cases impossible

theorem loss_final_echo : Echo lossAnswer true :=
  fun _ _ => rfl

theorem loss_one_step : Path lossStep false true :=
  path_single lossStep (Or.inr ⟨rfl, rfl⟩)

theorem loss_not_persistent : ¬ Persistent lossStep lossAnswer false :=
  (not_persistent_iff_reachable_echo lossStep lossAnswer false).mpr
    ⟨true, loss_one_step, loss_final_echo⟩

theorem loss_destructive_step_rejected :
    ¬ SafeRel lossStep (Exogenous lossAnswer) false true :=
  fun h => (not_exogenous_iff_echo lossAnswer true).mpr loss_final_echo
    (h.2 loss_initial_sensitive)

theorem loss_self_step_retained :
    SafeRel lossStep (Exogenous lossAnswer) false false :=
  ⟨Or.inl rfl, fun h => h⟩

theorem loss_repaired_persistent :
    Persistent (SafeRel lossStep (Exogenous lossAnswer)) lossAnswer false :=
  (persistent_repair_iff lossStep lossAnswer false).mpr loss_initial_sensitive

end Examples


#check @Interface
#print axioms Interface
#check @Interface.mk
#print axioms Interface.mk
#check @Interface.permitted
#print axioms Interface.permitted
#check @Interface.accepts
#print axioms Interface.accepts
#check @Interface.sound
#print axioms Interface.sound
#check @Accepted
#print axioms Accepted
#check @Cert
#print axioms Cert
#check @accepted_sound
#print axioms accepted_sound
#check @cert_sound
#print axioms cert_sound
#check @Observed
#print axioms Observed
#check @observation
#print axioms observation
#check @Returns
#print axioms Returns
#check @FiberAccepted
#print axioms FiberAccepted
#check @returns_iff_fibers
#print axioms returns_iff_fibers
#check @exists_readout_iff_fibers
#print axioms exists_readout_iff_fibers
#check @permitted_readout_iff_fibers
#print axioms permitted_readout_iff_fibers
#check @property_transfer
#print axioms property_transfer
#check @property_transfer_comp
#print axioms property_transfer_comp
#check @certificate_transfer
#print axioms certificate_transfer
#check @certificate_construction_comp
#print axioms certificate_construction_comp
#check @Cumulative
#print axioms Cumulative
#check @Available
#print axioms Available
#check @Failure
#print axioms Failure
#check @cumulative_le
#print axioms cumulative_le
#check @available_mono
#print axioms available_mono
#check @failure_antitone
#print axioms failure_antitone
#check @exists_least_nat
#print axioms exists_least_nat
#check @firstLevel
#print axioms firstLevel
#check @firstLevel_spec
#print axioms firstLevel_spec
#check @available_iff_firstLevel_le
#print axioms available_iff_firstLevel_le
#check @failure_iff_lt_firstLevel
#print axioms failure_iff_lt_firstLevel
#check @Path
#print axioms Path
#check @Path.refl
#print axioms Path.refl
#check @Path.step
#print axioms Path.step
#check @path_single
#print axioms path_single
#check @path_trans
#print axioms path_trans
#check @ForwardInvariant
#print axioms ForwardInvariant
#check @path_preserves
#print axioms path_preserves
#check @Box
#print axioms Box
#check @box_subset
#print axioms box_subset
#check @box_forward
#print axioms box_forward
#check @box_greatest
#print axioms box_greatest
#check @not_box_iff_reachable_not
#print axioms not_box_iff_reachable_not
#check @Exogenous
#print axioms Exogenous
#check @Echo
#print axioms Echo
#check @not_exogenous_iff_echo
#print axioms not_exogenous_iff_echo
#check @Persistent
#print axioms Persistent
#check @persistent_subset
#print axioms persistent_subset
#check @persistent_forward
#print axioms persistent_forward
#check @persistent_greatest
#print axioms persistent_greatest
#check @not_persistent_iff_reachable_echo
#print axioms not_persistent_iff_reachable_echo
#check @SafeRel
#print axioms SafeRel
#check @safe_subrelation
#print axioms safe_subrelation
#check @safe_forward
#print axioms safe_forward
#check @safe_greatest
#print axioms safe_greatest
#check @safe_box_iff
#print axioms safe_box_iff
#check @safe_box_eq
#print axioms safe_box_eq
#check @persistent_repair_iff
#print axioms persistent_repair_iff
#check @Examples.emptyInterface
#print axioms Examples.emptyInterface
#check @Examples.singletonInterface
#print axioms Examples.singletonInterface
#check @Examples.no_empty_certificate
#print axioms Examples.no_empty_certificate
#check @Examples.singleton_certificate
#print axioms Examples.singleton_certificate
#check @Examples.collapsedObservation
#print axioms Examples.collapsedObservation
#check @Examples.allObjects
#print axioms Examples.allObjects
#check @Examples.matchesObject
#print axioms Examples.matchesObject
#check @Examples.pointwise_certificates
#print axioms Examples.pointwise_certificates
#check @Examples.no_joint_readout
#print axioms Examples.no_joint_readout
#check @Examples.constantAbstraction
#print axioms Examples.constantAbstraction
#check @Examples.constant_property_transfer
#print axioms Examples.constant_property_transfer
#check @Examples.constantAbstraction_no_left_inverse
#print axioms Examples.constantAbstraction_no_left_inverse
#check @Examples.flagInterface
#print axioms Examples.flagInterface
#check @Examples.flagProjection
#print axioms Examples.flagProjection
#check @Examples.flag_certificate_iff
#print axioms Examples.flag_certificate_iff
#check @Examples.true_flag_certificate
#print axioms Examples.true_flag_certificate
#check @Examples.false_flag_no_certificate
#print axioms Examples.false_flag_no_certificate
#check @Examples.flag_property_transfer
#print axioms Examples.flag_property_transfer
#check @Examples.flagProjection_no_left_inverse
#print axioms Examples.flagProjection_no_left_inverse
#check @Examples.delayed
#print axioms Examples.delayed
#check @Examples.delayed_cumulative
#print axioms Examples.delayed_cumulative
#check @Examples.delayed_success_two
#print axioms Examples.delayed_success_two
#check @Examples.delayed_eventual
#print axioms Examples.delayed_eventual
#check @Examples.delayedLevel
#print axioms Examples.delayedLevel
#check @Examples.delayedLevel_eq_two
#print axioms Examples.delayedLevel_eq_two
#check @Examples.delayedLevel_constant
#print axioms Examples.delayedLevel_constant
#check @Examples.delayed_failure_zero
#print axioms Examples.delayed_failure_zero
#check @Examples.delayed_failure_with_known_level
#print axioms Examples.delayed_failure_with_known_level
#check @Examples.lossAnswer
#print axioms Examples.lossAnswer
#check @Examples.lossStep
#print axioms Examples.lossStep
#check @Examples.loss_initial_sensitive
#print axioms Examples.loss_initial_sensitive
#check @Examples.loss_final_echo
#print axioms Examples.loss_final_echo
#check @Examples.loss_one_step
#print axioms Examples.loss_one_step
#check @Examples.loss_not_persistent
#print axioms Examples.loss_not_persistent
#check @Examples.loss_destructive_step_rejected
#print axioms Examples.loss_destructive_step_rejected
#check @Examples.loss_self_step_retained
#print axioms Examples.loss_self_step_retained
#check @Examples.loss_repaired_persistent
#print axioms Examples.loss_repaired_persistent

end OperatorKO7.Meta.BoundaryObserver.AcceptedCertificate
