import OperatorKO7.Meta.UniqueNormalization.Section7FiberReduction

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization.ChainClassification

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

abbrev CT (sigma : Type u) (nu : Type v) :=
  Term (sigma ⊕ sigma) nu

def wrap (d : sigma) (a : CT sigma nu) : CT sigma nu :=
  .app (.inr d) [a]

def tower (c d : sigma) : Nat → CT sigma nu
  | 0 => .app (.inl c) []
  | i + 1 => wrap d (tower c d i)

def carrier (c d : sigma) (n : Nat) : List (CT sigma nu) :=
  (List.range (n + 1)).map (tower c d)

def eraseRule (d : sigma) (x : nu) : Rule (sigma ⊕ sigma) nu where
  lhs := wrap d (.var x)
  rhs := .var x
  lhs_isApp := rfl

def eraseRules (d : sigma) (x : nu) : TRS (sigma ⊕ sigma) nu :=
  [eraseRule d x]

variable {c d : sigma} {x : nu}
variable {n i j k : Nat} {a b : CT sigma nu}

local notation "t" => tower (nu := nu) c d
local notation "A" => carrier (nu := nu) c d n
local notation "R" => eraseRules d x

theorem wrap_injective : Function.Injective (wrap (nu := nu) d) := by
  intro p q h
  have h' : ([p] : List (CT sigma nu)) = [q] := (Term.app.inj h).2
  simpa using h'

theorem tower_zero : t 0 = .app (.inl c) [] := rfl

theorem tower_succ (i : Nat) : t (i + 1) = wrap d (t i) := rfl

theorem tower_injective : Function.Injective t := by
  intro i
  induction i with
  | zero =>
      intro j h
      cases j with
      | zero => rfl
      | succ k => simp [tower, wrap] at h
  | succ i ih =>
      intro j h
      cases j with
      | zero => simp [tower, wrap] at h
      | succ k =>
          have h' : t i = t k :=
            wrap_injective (d := d) (by simpa [tower, wrap] using h)
          rw [ih h']

theorem tower_eq_iff : t i = t j ↔ i = j :=
  ⟨fun h => tower_injective h, fun h => by rw [h]⟩

theorem tower_zero_conTopped : ConTopped (t 0) :=
  Or.inr ⟨c, [], rfl⟩

theorem tower_succ_not_conTopped (i : Nat) : ¬ ConTopped (t (i + 1)) :=
  not_conTopped_destructor [tower c d i]

theorem mem_carrier_iff : a ∈ A ↔ ∃ i, i ≤ n ∧ a = t i := by
  simp only [carrier, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i, by omega, h.symm⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨i, by omega, h.symm⟩

theorem tower_mem_iff : t i ∈ A ↔ i ≤ n := by
  rw [mem_carrier_iff]
  constructor
  · rintro ⟨j, hj, h⟩
    have hji : j = i := (tower_eq_iff).mp h.symm
    omega
  · intro hi
    exact ⟨i, hi, rfl⟩

theorem carrier_length : (carrier (nu := nu) c d n).length = n + 1 := by
  simp [carrier]

theorem carrier_nodup : (carrier (nu := nu) c d n).Nodup := by
  unfold carrier
  exact List.Nodup.map (tower_injective (c := c) (d := d)) List.nodup_range

private theorem forall₂_singleton_left {r : CT sigma nu → CT sigma nu → Prop}
    {u : CT sigma nu} {bs : List (CT sigma nu)}
    (h : List.Forall₂ r [u] bs) : ∃ v, r u v ∧ bs = [v] := by
  cases h with
  | cons hd ht =>
      cases ht with
      | nil => exact ⟨_, hd, rfl⟩

private theorem subterm_tower_iff_aux (i : Nat) (a : CT sigma nu) :
    Subterm a (tower c d i) ↔ ∃ j, j ≤ i ∧ a = tower c d j := by
  induction i generalizing a with
  | zero =>
      constructor
      · intro h
        cases h with
        | refl => exact ⟨0, le_rfl, rfl⟩
        | arg hmem _ => simp at hmem
      · rintro ⟨j, hj, rfl⟩
        have hj0 : j = 0 := by omega
        subst hj0
        exact Subterm.refl _
  | succ i ih =>
      constructor
      · intro h
        cases h with
        | refl => exact ⟨i + 1, le_rfl, rfl⟩
        | arg hmem hsub =>
            cases (List.mem_singleton.mp hmem)
            obtain ⟨j, hj, ha⟩ := (ih a).mp hsub
            exact ⟨j, by omega, ha⟩
      · rintro ⟨j, hj, rfl⟩
        by_cases hji : j = i + 1
        · subst hji
          exact Subterm.refl _
        · have hj' : j ≤ i := by omega
          exact Subterm.arg (by simp) ((ih (tower c d j)).mpr ⟨j, hj', rfl⟩)

theorem subterm_tower_iff (i : Nat) :
    Subterm a (t i) ↔ ∃ j, j ≤ i ∧ a = t j :=
  subterm_tower_iff_aux i a

theorem carrier_coalgebra : Coalgebra A := by
  intro u hu v hv
  obtain ⟨i, hi, rfl⟩ := (mem_carrier_iff).mp hu
  obtain ⟨j, hj, rfl⟩ := (subterm_tower_iff i).mp hv
  exact (tower_mem_iff).mpr (by omega)

theorem eraseRules_constructor : ConstructorRules R := by
  intro r hr
  have hr' : r = eraseRule d x := by simpa [eraseRules] using hr
  subst hr'
  refine ⟨d, [.var x], rfl, ?_⟩
  intro p hp
  have hp' : p = .var x := by simpa using hp
  subst hp'
  exact ConOnly.var x

theorem eraseRule_rhsDetermined : Rule.RhsDetermined (eraseRule d x) := by
  intro p q h
  change wrap d (p x) = wrap d (q x) at h
  change p x = q x
  simpa [wrap] using h

theorem eraseRules_strong : StronglyAlmostNonOmegaOverlapping R := by
  constructor
  · intro r₁ hr₁ r₂ hr₂ s hsub happ _
    have h₁ : r₁ = eraseRule d x := by simpa [eraseRules] using hr₁
    subst h₁
    obtain ⟨f, args, u, heq, hu, hsu⟩ := hsub
    change Term.app (.inr d) [.var x] = Term.app f args at heq
    obtain ⟨_, hargs⟩ := Term.app.inj heq
    have hu' : u = .var x := by simpa only [← hargs, List.mem_singleton] using hu
    subst hu'
    have hs : s = .var x := hsu.eq_of_var
    subst hs
    exact Bool.noConfusion happ
  · intro r₁ hr₁ r₂ hr₂ _
    have h₁ : r₁ = eraseRule d x := by simpa [eraseRules] using hr₁
    have h₂ : r₂ = eraseRule d x := by simpa [eraseRules] using hr₂
    subst h₁
    subst h₂
    refine ⟨CommonGeneralisation.self (eraseRule d x)
      (eraseRule_rhsDetermined (d := d) (x := x)), ?_⟩
    intro z hz
    change VarOccurs z (.var x) at hz
    change VarOccurs z (wrap d (.var x))
    exact VarOccurs.arg (by simp) hz

theorem rootStep_iff : rootStep R a b ↔ a = wrap d b := by
  constructor
  · rintro ⟨r, hr, sub, ha, hb⟩
    have hr' : r = eraseRule d x := by simpa [eraseRules] using hr
    subst hr'
    change a = wrap d (sub x) at ha
    change b = sub x at hb
    exact ha.trans (congrArg (wrap d) hb.symm)
  · intro h
    exact ⟨eraseRule d x, by simp [eraseRules], fun _ => b, h, rfl⟩

theorem rootStep_tower_iff : rootStep R (t i) (t j) ↔ i = j + 1 := by
  rw [rootStep_iff]
  show t i = t (j + 1) ↔ i = j + 1
  exact tower_eq_iff

theorem down_tower_zero (hi : i ≤ n) : DownOn A R (t i) (t 0) := by
  revert hi
  induction i with
  | zero =>
      intro _
      exact DownOn.refl ((tower_mem_iff).mpr (Nat.zero_le n))
  | succ i ih =>
      intro hi
      have hi' : i ≤ n := by omega
      have hroot : rootStep R (t (i + 1)) (t i) := (rootStep_tower_iff).mpr rfl
      exact DownOn.rootComp ((tower_mem_iff).mpr hi) ((tower_mem_iff).mpr hi')
        hroot (ih hi')

theorem down_tower_pair (hi : i ≤ n) (hj : j ≤ n) : DownOn A R (t i) (t j) := by
  revert hj
  induction i with
  | zero =>
      intro hj
      exact DownOn.symm (down_tower_zero (i := j) hj)
  | succ i ih =>
      intro hj
      have hi' : i ≤ n := by omega
      have hroot : rootStep R (t (i + 1)) (t i) := (rootStep_tower_iff).mpr rfl
      exact DownOn.rootComp ((tower_mem_iff).mpr hi) ((tower_mem_iff).mpr hi')
        hroot (ih hi' hj)

theorem down_all (ha : a ∈ A) (hb : b ∈ A) : DownOn A R a b := by
  obtain ⟨i, hi, rfl⟩ := (mem_carrier_iff).mp ha
  obtain ⟨j, hj, rfl⟩ := (mem_carrier_iff).mp hb
  exact down_tower_pair hi hj

private theorem barStep_tower_target (hi : i ≤ n) {b : CT sigma nu}
    (h : BarStepOn A R (t i) b) :
    ∃ l, l ≤ n ∧ 0 < l ∧ b = t l := by
  rcases h with ⟨_, hbA, hrel⟩
  rcases hrel with ⟨f, as, bs, ⟨e, he⟩, ha, hb, hall⟩
  subst he
  cases i with
  | zero => simp [tower] at ha
  | succ i' =>
      have ha' : Term.app (.inr d) [tower c d i'] = Term.app (.inr e) as := by
        simpa [tower, wrap] using ha
      obtain ⟨h1, h2⟩ := Term.app.inj ha'
      have hee : e = d := by cases h1; rfl
      rw [hee] at hb
      have has : as = [tower c d i'] := h2.symm
      subst has
      obtain ⟨v, hdv, hbs⟩ := forall₂_singleton_left hall
      have hvA : v ∈ A := (DownOn.mem hdv).2
      obtain ⟨l, hl, hvl⟩ := (mem_carrier_iff).mp hvA
      have hbEq : b = t (l + 1) := by rw [hb, hbs, hvl]; rfl
      refine ⟨l + 1, ?_, Nat.succ_pos l, hbEq⟩
      rw [hbEq] at hbA
      exact (tower_mem_iff).mp hbA

theorem barStep_tower_iff (hi : i ≤ n) (hj : j ≤ n) :
    BarStepOn A R (t i) (t j) ↔ 0 < i ∧ 0 < j := by
  constructor
  · intro h
    obtain ⟨l, hl, hlpos, hjl⟩ := barStep_tower_target hi h
    have hjpos : 0 < j := by
      have hlj : j = l := (tower_eq_iff).mp hjl
      omega
    refine ⟨?_, hjpos⟩
    by_contra hi0
    have hi0' : i = 0 := Nat.eq_zero_of_not_pos hi0
    subst hi0'
    rcases h.2.2 with ⟨f, as, bs, ⟨e, he⟩, ha, _, _⟩
    subst he
    simp [tower] at ha
  · rintro ⟨hi0, hj0⟩
    obtain ⟨i', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi0)
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hj0)
    refine ⟨(tower_mem_iff).mpr hi, (tower_mem_iff).mpr hj, ?_⟩
    exact ⟨.inr d, [tower c d i'], [tower c d j'], ⟨d, rfl⟩, rfl, rfl,
      List.Forall₂.cons (down_tower_pair (by omega) (by omega)) List.Forall₂.nil⟩

private theorem barReachN_tower_iff (m : Nat) :
    ∀ (i : Nat) (u : CT sigma nu), i ≤ n → u ∈ A →
      BarReachN A R m (t i) u → ∃ j, u = t j ∧ (i = 0 ↔ j = 0) := by
  induction m with
  | zero =>
      intro i u _ _ h
      exact ⟨i, (BarReachN.zero_inv h).symm, Iff.rfl⟩
  | succ m ih =>
      intro i u hi hu h
      obtain ⟨b, hstep, htail⟩ := BarReachN.succ_inv h
      obtain ⟨l, hl, hlpos, hbl⟩ := barStep_tower_target hi hstep
      obtain ⟨j, huj, hiff⟩ := ih l u hl hu (by rwa [hbl] at htail)
      have hi0 : i ≠ 0 := by
        intro h0
        subst h0
        rcases hstep.2.2 with ⟨f, as, bs, ⟨e, he⟩, ha, _, _⟩
        subst he
        simp [tower] at ha
      have hl0 : l ≠ 0 := Nat.pos_iff_ne_zero.mp hlpos
      have hj0 : j ≠ 0 := fun hj => hl0 (hiff.mpr hj)
      exact ⟨j, huj, ⟨fun h0 => absurd h0 hi0, fun h0 => absurd h0 hj0⟩⟩

theorem barReach_tower_iff (hi : i ≤ n) (hj : j ≤ n) :
    BarReachOn A R (t i) (t j) ↔ (i = 0 ↔ j = 0) := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h.toBarReachN
    obtain ⟨l, hjl, hiff⟩ :=
      barReachN_tower_iff m i (t j) hi ((tower_mem_iff).mpr hj) hm
    have hlj : j = l := (tower_eq_iff).mp hjl
    subst hlj
    exact hiff
  · intro h
    by_cases hi0 : i = 0
    · have hj0 : j = 0 := h.mp hi0
      subst hi0
      subst hj0
      exact BarReachOn.refl _
    · have hj0 : j ≠ 0 := fun hj0' => hi0 (h.mpr hj0')
      exact BarReachOn.single ((barStep_tower_iff hi hj).mpr
        ⟨Nat.pos_of_ne_zero hi0, Nat.pos_of_ne_zero hj0⟩)

theorem grey_zero_iff (E : CRel sigma nu) :
    Grey A R E (t 0) b ↔ b = t 0 := by
  constructor
  · intro h
    rcases h with hroot | hbar | hhat
    · obtain ⟨e, args, hshape⟩ :=
        rootStep_source_destructor (eraseRules_constructor (d := d) (x := x)) hroot
      simp [tower] at hshape
    · rcases hbar with ⟨f, as, bs, ⟨e, he⟩, ha, _, _⟩
      subst he
      simp [tower] at ha
    · rcases hhat with ⟨y, h1, _⟩ | ⟨f, as, bs, ⟨e, he⟩, ha, hb, hall⟩
      · simp [tower] at h1
      · subst he
        have ha' : Term.app (.inl c) ([] : List (CT sigma nu)) =
            Term.app (.inl e) as := by
          simpa [tower] using ha
        obtain ⟨h1, h2⟩ := Term.app.inj ha'
        have hec : e = c := by cases h1; rfl
        subst hec
        have has : as = [] := h2.symm
        subst has
        cases hall with
        | nil => simpa [tower] using hb
  · intro hb
    subst hb
    exact Or.inr (Or.inr (Or.inr
      ⟨Sum.inl c, [], [], ⟨c, rfl⟩, rfl, rfl, List.Forall₂.nil⟩))

theorem grey_to_zero_iff (E : CRel sigma nu) (hi : 0 < i) :
    Grey A R E (t i) (t 0) ↔ i = 1 := by
  constructor
  · intro h
    rcases h with hroot | hbar | hhat
    · simpa using (rootStep_tower_iff (i := i) (j := 0)).mp hroot
    · rcases hbar with ⟨f, as, bs, ⟨e, he⟩, _, hb, _⟩
      subst he
      simp [tower] at hb
    · rcases hhat with ⟨y, h1, _⟩ | ⟨f, as, bs, ⟨e, he⟩, ha, _, _⟩
      · cases i with
        | zero => omega
        | succ i' => simp [tower, wrap] at h1
      · subst he
        cases i with
        | zero => omega
        | succ i' =>
            simp [tower, wrap] at ha
  · intro hi1
    subst hi1
    exact Or.inl ((rootStep_tower_iff (i := 1) (j := 0)).mpr rfl)

theorem zero_nf (rho : PGraph A R) : rho.NF (t 0) := by
  cases hp : rho.par (t 0) with
  | none => exact hp
  | some b =>
      have hb0 : b = t 0 :=
        (grey_zero_iff (EqvOn A rho.par)).mp (rho.grey hp)
      exact (rho.term.no_parent_cycle hp (by rw [hb0]; exact Reach.refl _)).elim

theorem nf_eqv_iff (rho : PGraph A R) (ha : a ∈ A) (hb : b ∈ A)
    (hna : rho.NF a) (hnb : rho.NF b) :
    EqvOn A rho.par a b ↔ a = b := by
  constructor
  · rintro ⟨_, _, s, has, hbs⟩
    have has' : a = s := by
      rcases has.head_inv with h | ⟨c, hac, _⟩
      · exact h
      · rw [hna] at hac
        contradiction
    have hbs' : b = s := by
      rcases hbs.head_inv with h | ⟨c, hbc, _⟩
      · exact h
      · rw [hnb] at hbc
        contradiction
    rw [has', hbs']
  · intro h
    subst h
    exact EqvOn.refl ha

theorem complete_nf_grey_eqv (rho : PGraph A R)
    (hc : rho.Complete) (ha : a ∈ A) (hb : b ∈ A)
    (hna : rho.NF a) (hg : Grey A R (EqvOn A rho.par) a b) :
    EqvOn A rho.par a b := by
  by_contra hne
  obtain ⟨beta, hExt, hedge⟩ :=
    rho.extend_one carrier_coalgebra (eraseRules_constructor (d := d) (x := x))
      ha hb hna hne hg
  have hBack : beta.Extends rho := hc beta hExt
  have hOld : rho.par a = some b := hBack hedge
  rw [hna] at hOld
  contradiction

section QuotientAdapters

variable {B : List (CT sigma nu)} {S : TRS (sigma ⊕ sigma) nu}

noncomputable def quotientTarget (q : Section7Target B S) : Target B S where
  pick := Quotient.lift (fun a : {u // u ∈ B} => q.pick a.1)
    (fun a b hab => q.respectsFiber a.2 b.2 hab)
  pick_mem := fun C => Quotient.inductionOn C (fun a => q.pick_mem a.2)
  inFiber := by
    intro w hw
    exact q.inFiber hw
  redexPriority := by
    intro w hw hred
    obtain ⟨u, hu, htu, v, hv, huv⟩ := hred
    exact q.redex_if_available hw ⟨u, v, hu, hv, htu, huv⟩

theorem quotientTarget_pick (q : Section7Target B S)
    (a : CT sigma nu) (ha : a ∈ B) :
    (quotientTarget q).pick (barClassOf B S a ha) = q.pick a := rfl

noncomputable def quotientGraph (rho : TermTargetedPGraph B S) : TargetedPGraph B S where
  graph := rho.graph
  target := quotientTarget rho.target
  guided_or_nf := by
    intro w hw
    rcases rho.guided_or_nf hw with h | h
    · exact Or.inl (by rwa [quotientTarget_pick rho.target w hw])
    · exact Or.inr h
  target_exit := by
    intro w hw u hedge
    rw [quotientTarget_pick rho.target w hw] at hedge
    exact rho.target_edge_exits_fiber hw hedge

theorem quotientGraph_graph (rho : TermTargetedPGraph B S) :
    (quotientGraph rho).graph = rho.graph := rfl

theorem quotientGraph_universal_iff (rho : TermTargetedPGraph B S) :
    (quotientGraph rho).graph.Universal ↔ rho.Universal := by
  rw [PGraph.universal_iff_down_subset]
  exact Iff.rfl

end QuotientAdapters

theorem positive_reach_zero_forces_one_parent (rho : PGraph A R)
    (ha : a ∈ A) (hne : a ≠ t 0) (hr : Reach rho.par a (t 0)) :
    rho.par (t 1) = some (t 0) := by
  revert ha hne
  revert hr
  generalize hz : (t 0 : CT sigma nu) = z
  intro hr
  induction hr with
  | refl =>
      intro _ hne
      exact absurd rfl hne
  | head hedge htail ih =>
      rename_i src mid tgt
      intro ha hne
      by_cases hmid : mid = t 0
      · subst hmid
        have hg : Grey A R (EqvOn A rho.par) src (t 0) := rho.grey hedge
        obtain ⟨i, hi, rfl⟩ := (mem_carrier_iff).mp ha
        have hi0 : 0 < i := by
          by_contra h
          have h0' : i = 0 := Nat.eq_zero_of_not_pos h
          subst h0'
          exact hne hz
        have hi1 : i = 1 := (grey_to_zero_iff (EqvOn A rho.par) hi0).mp hg
        subst hi1
        rw [hz] at hedge
        exact hedge
      · exact ih hz (rho.mem_edge hedge).2 (fun hmt => hmid (hmt.trans hz.symm))

theorem universal_one_parent (rho : PGraph A R)
    (hn : 0 < n) (hu : rho.Universal) :
    rho.par (t 1) = some (t 0) := by
  have hdown : DownOn A R (t 1) (t 0) :=
    down_tower_pair (by omega) (Nat.zero_le n)
  have heqv : EqvOn A rho.par (t 1) (t 0) := (hu (t 1) (t 0)).mpr hdown
  obtain ⟨_, _, s, h1s, h0s⟩ := heqv
  have hs : s = t 0 := by
    rcases h0s.head_inv with h | ⟨c, hc, _⟩
    · exact h.symm
    · rw [zero_nf rho] at hc
      contradiction
  subst hs
  have h1A : t 1 ∈ A := (tower_mem_iff).mpr (by omega)
  have h10 : t 1 ≠ t 0 := by
    intro h
    have : (1 : Nat) = 0 := (tower_eq_iff).mp h
    omega
  exact positive_reach_zero_forces_one_parent rho h1A h10 h1s

theorem complete_one_parent_reach_zero (rho : PGraph A R)
    (hc : rho.Complete) (hn : 0 < n)
    (he : rho.par (t 1) = some (t 0)) (ha : a ∈ A) :
    Reach rho.par a (t 0) := by
  by_cases ha0 : a = t 0
  · subst ha0
    exact Reach.refl _
  · obtain ⟨r, har, hrnf⟩ := exists_root rho.term a
    have hrA : r ∈ A := rho.mem_of_reach_right ha har
    have hr0 : r = t 0 := by
      by_contra hrne
      obtain ⟨i, hi, rfl⟩ := (mem_carrier_iff).mp hrA
      have hi0 : 0 < i := by
        by_contra h
        have h0 : i = 0 := Nat.eq_zero_of_not_pos h
        subst h0
        exact hrne rfl
      by_cases hi1 : i = 1
      · subst hi1
        have h1A : t 1 ∈ A := (tower_mem_iff).mpr (by omega)
        have h0A : t 0 ∈ A := (tower_mem_iff).mpr (Nat.zero_le n)
        have heqv : EqvOn A rho.par (t 1) (t 0) :=
          EqvOn.of_reach h1A h0A (Reach.head he (Reach.refl _))
        have heq : t 1 = t 0 :=
          (nf_eqv_iff rho h1A h0A hrnf (zero_nf rho)).mp heqv
        have h10 : (1 : Nat) = 0 := (tower_eq_iff).mp heq
        omega
      · have hi2 : 2 ≤ i := by omega
        have hiA : t i ∈ A := (tower_mem_iff).mpr hi
        have h1A : t 1 ∈ A := (tower_mem_iff).mpr (by omega)
        have h0A : t 0 ∈ A := (tower_mem_iff).mpr (Nat.zero_le n)
        have hstep : BarStepOn A R (t i) (t 1) :=
          (barStep_tower_iff hi (by omega)).mpr ⟨hi0, by omega⟩
        have heqv1 : EqvOn A rho.par (t i) (t 1) :=
          complete_nf_grey_eqv rho hc hiA h1A hrnf (Or.inr (Or.inl hstep.2.2))
        have heqv2 : EqvOn A rho.par (t 1) (t 0) :=
          EqvOn.of_reach h1A h0A (Reach.head he (Reach.refl _))
        have heqv : EqvOn A rho.par (t i) (t 0) := EqvOn.trans heqv1 heqv2
        have heq : t i = t 0 :=
          (nf_eqv_iff rho hiA h0A hrnf (zero_nf rho)).mp heqv
        have hi0' : i = 0 := (tower_eq_iff).mp heq
        omega
    rw [hr0] at har
    exact har

theorem complete_graph_universal_iff_parent (rho : PGraph A R)
    (hc : rho.Complete) (hn : 0 < n) :
    rho.Universal ↔ rho.par (t 1) = some (t 0) := by
  constructor
  · exact universal_one_parent rho hn
  · intro he
    rw [PGraph.universal_iff_down_subset]
    intro p q hdown
    exact ⟨hdown.mem.1, hdown.mem.2, t 0,
      complete_one_parent_reach_zero rho hc hn he hdown.mem.1,
      complete_one_parent_reach_zero rho hc hn he hdown.mem.2⟩

theorem target_zero (q : Section7Target A R) : q.pick (t 0) = t 0 :=
  q.pick_eq_self_of_conTopped ((tower_mem_iff).mpr (Nat.zero_le n))
    tower_zero_conTopped

theorem target_index_exists_unique (hn : 0 < n) (q : Section7Target A R) :
    ∃! k : Nat, 0 < k ∧ k ≤ n ∧ q.pick (t 1) = t k := by
  have h1A : t 1 ∈ A := (tower_mem_iff).mpr (by omega)
  obtain ⟨k, hk, hpk⟩ := (mem_carrier_iff).mp (q.pick_mem h1A)
  have hk0 : 0 < k := by
    by_contra h
    have h0 : k = 0 := Nat.eq_zero_of_not_pos h
    subst h0
    have hbar : BarReachOn A R (t 1) (t 0) := by
      rw [← hpk]
      exact q.inFiber h1A
    have hiff := (barReach_tower_iff (by omega) (Nat.zero_le n)).mp hbar
    have h10 : (1 : Nat) = 0 := hiff.mpr rfl
    omega
  refine ⟨k, ⟨hk0, hk, hpk⟩, ?_⟩
  rintro j ⟨_, _, hpj⟩
  exact (tower_eq_iff).mp (hpj.symm.trans hpk)

theorem target_positive (q : Section7Target A R)
    (hi : 0 < i) (hin : i ≤ n) (hn : 0 < n) :
    q.pick (t i) = q.pick (t 1) := by
  have hiA : t i ∈ A := (tower_mem_iff).mpr hin
  have h1A : t 1 ∈ A := (tower_mem_iff).mpr (by omega)
  have hbar : BarReachOn A R (t 1) (t i) :=
    (barReach_tower_iff (by omega) hin).mpr ⟨fun h => by omega, fun h => by omega⟩
  exact (q.respectsFiber h1A hiA hbar).symm

theorem selected_high_nf (rho : TermTargetedPGraph A R)
    (hk : 2 ≤ k) (hkn : k ≤ n) (hp : rho.target.pick (t 1) = t k) :
    rho.graph.NF (t k) := by
  cases hpar : rho.graph.par (t k) with
  | none => exact hpar
  | some b =>
      obtain ⟨j, hjn, rfl⟩ := (mem_carrier_iff).mp ((rho.graph.mem_edge hpar).2)
      have hgrey : Grey A R (EqvOn A rho.graph.par) (t k) (t j) := rho.graph.grey hpar
      by_cases hj0 : j = 0
      · subst hj0
        have hk1 : k = 1 :=
          (grey_to_zero_iff (EqvOn A rho.graph.par) (by omega)).mp hgrey
        omega
      · have h1A : t 1 ∈ A := (tower_mem_iff).mpr (by omega)
        have hbar : BarReachOn A R (t 1) (t j) :=
          (barReach_tower_iff (by omega) hjn).mpr ⟨fun h => by omega, fun h => by omega⟩
        have hpar' : rho.graph.par (rho.target.pick (t 1)) = some (t j) := by
          rw [hp]
          exact hpar
        exact (rho.target_edge_exits_fiber h1A hpar') hbar |>.elim

theorem selected_high_not_universal (rho : TermTargetedPGraph A R)
    (hk : 2 ≤ k) (hkn : k ≤ n) (hp : rho.target.pick (t 1) = t k) :
    ¬ rho.Universal := by
  intro hu
  have hkNF : rho.graph.NF (t k) := selected_high_nf rho hk hkn hp
  have hkA : t k ∈ A := (tower_mem_iff).mpr hkn
  have h0A : t 0 ∈ A := (tower_mem_iff).mpr (Nat.zero_le n)
  have heqv : EqvOn A rho.graph.par (t k) (t 0) :=
    hu (down_tower_pair hkn (Nat.zero_le n))
  have heq : t k = t 0 :=
    (nf_eqv_iff rho.graph hkA h0A hkNF (zero_nf rho.graph)).mp heqv
  have : k = 0 := (tower_eq_iff).mp heq
  omega

theorem complete_low_parent (rho : TermTargetedPGraph A R)
    (hc : rho.graph.Complete) (hn : 0 < n)
    (hp : rho.target.pick (t 1) = t 1) :
    rho.graph.par (t 1) = some (t 0) := by
  cases hpar : rho.graph.par (t 1) with
  | none =>
      have h1A : t 1 ∈ A := (tower_mem_iff).mpr (by omega)
      have h0A : t 0 ∈ A := (tower_mem_iff).mpr (Nat.zero_le n)
      have hgrey : Grey A R (EqvOn A rho.graph.par) (t 1) (t 0) :=
        Or.inl ((rootStep_tower_iff (i := 1) (j := 0)).mpr rfl)
      have heqv : EqvOn A rho.graph.par (t 1) (t 0) :=
        complete_nf_grey_eqv rho.graph hc h1A h0A hpar hgrey
      have heq : t 1 = t 0 :=
        (nf_eqv_iff rho.graph h1A h0A hpar (zero_nf rho.graph)).mp heqv
      have : (1 : Nat) = 0 := (tower_eq_iff).mp heq
      omega
  | some b =>
      obtain ⟨j, hjn, rfl⟩ := (mem_carrier_iff).mp ((rho.graph.mem_edge hpar).2)
      by_cases hj0 : j = 0
      · subst hj0
        rfl
      · have h1A : t 1 ∈ A := (tower_mem_iff).mpr (by omega)
        have hbar : BarReachOn A R (t 1) (t j) :=
          (barReach_tower_iff (by omega) hjn).mpr ⟨fun h => by omega, fun h => by omega⟩
        have hpar' : rho.graph.par (rho.target.pick (t 1)) = some (t j) := by
          rw [hp]
          exact hpar
        exact (rho.target_edge_exits_fiber h1A hpar') hbar |>.elim

theorem complete_low_positive_not_nf (rho : TermTargetedPGraph A R)
    (hc : rho.graph.Complete) (hn : 0 < n)
    (hp : rho.target.pick (t 1) = t 1) (hi : 0 < i) (hin : i ≤ n) :
    ¬ rho.graph.NF (t i) := by
  intro hnf
  have hlow : rho.graph.par (t 1) = some (t 0) := complete_low_parent rho hc hn hp
  have h1A : t 1 ∈ A := (tower_mem_iff).mpr (by omega)
  have h0A : t 0 ∈ A := (tower_mem_iff).mpr (Nat.zero_le n)
  have hiA : t i ∈ A := (tower_mem_iff).mpr hin
  have heqv1 : EqvOn A rho.graph.par (t i) (t 0) := by
    by_cases hi1 : i = 1
    · subst hi1
      exact ⟨h1A, h0A, t 0, Reach.head hlow (Reach.refl _), Reach.refl _⟩
    · have hi2 : 2 ≤ i := by omega
      have hstep : BarStepOn A R (t i) (t 1) :=
        (barStep_tower_iff hin (by omega)).mpr ⟨hi, by omega⟩
      have heqv_i1 : EqvOn A rho.graph.par (t i) (t 1) :=
        complete_nf_grey_eqv rho.graph hc hiA h1A hnf (Or.inr (Or.inl hstep.2.2))
      have heqv_10 : EqvOn A rho.graph.par (t 1) (t 0) :=
        ⟨h1A, h0A, t 0, Reach.head hlow (Reach.refl _), Reach.refl _⟩
      exact EqvOn.trans heqv_i1 heqv_10
  have heq : t i = t 0 :=
    (nf_eqv_iff rho.graph hiA h0A hnf (zero_nf rho.graph)).mp heqv1
  have : i = 0 := (tower_eq_iff).mp heq
  omega

theorem complete_low_reach (rho : TermTargetedPGraph A R)
    (hc : rho.graph.Complete) (hn : 0 < n)
    (hp : rho.target.pick (t 1) = t 1) (ha : a ∈ A) :
    Reach rho.graph.par a (t 0) := by
  by_cases ha0 : a = t 0
  · subst ha0
    exact Reach.refl _
  · obtain ⟨r, har, hrnf⟩ := exists_root rho.graph.term a
    have hrA : r ∈ A := rho.graph.mem_of_reach_right ha har
    have hr0 : r = t 0 := by
      by_contra hrne
      obtain ⟨i, hi, rfl⟩ := (mem_carrier_iff).mp hrA
      have hi0 : 0 < i := by
        by_contra h
        have h0 : i = 0 := Nat.eq_zero_of_not_pos h
        subst h0
        exact hrne rfl
      exact absurd hrnf (complete_low_positive_not_nf rho hc hn hp hi0 hi)
    rw [hr0] at har
    exact har

theorem complete_high_positive_reach (rho : TermTargetedPGraph A R)
    (hc : rho.graph.Complete) (hk : 2 ≤ k) (hkn : k ≤ n)
    (hp : rho.target.pick (t 1) = t k) (hi : 0 < i) (hin : i ≤ n) :
    Reach rho.graph.par (t i) (t k) := by
  have hiA : t i ∈ A := (tower_mem_iff).mpr hin
  rcases rho.guided_or_nf hiA with hguided | hnf
  · have hreach : Reach rho.graph.par (t i) (rho.target.pick (t i)) := hguided.toReach
    have hpicki : rho.target.pick (t i) = t k :=
      (target_positive rho.target hi hin (by omega)).trans hp
    rwa [hpicki] at hreach
  · have hkNF : rho.graph.NF (t k) := selected_high_nf rho hk hkn hp
    have hkA : t k ∈ A := (tower_mem_iff).mpr hkn
    have hstep : BarStepOn A R (t i) (t k) :=
      (barStep_tower_iff hin hkn).mpr ⟨hi, by omega⟩
    have heqv : EqvOn A rho.graph.par (t i) (t k) :=
      complete_nf_grey_eqv rho.graph hc hiA hkA hnf (Or.inr (Or.inl hstep.2.2))
    have heq : t i = t k :=
      (nf_eqv_iff rho.graph hiA hkA hnf hkNF).mp heqv
    rw [heq]
    exact Reach.refl _

theorem complete_target_universal_iff (rho : TermTargetedPGraph A R)
    (hc : rho.graph.Complete) (hn : 0 < n) :
    rho.Universal ↔ rho.target.pick (t 1) = t 1 := by
  constructor
  · intro hu
    by_contra hp
    obtain ⟨k, ⟨hk0, hkn, hpk⟩, _⟩ := target_index_exists_unique hn rho.target
    by_cases hk1 : k = 1
    · exact hp (by rw [hk1] at hpk; exact hpk)
    · have hk2 : 2 ≤ k := by omega
      exact selected_high_not_universal rho hk2 hkn hpk hu
  · intro hp
    intro p q hdown
    exact ⟨hdown.mem.1, hdown.mem.2, t 0,
      complete_low_reach rho hc hn hp hdown.mem.1,
      complete_low_reach rho hc hn hp hdown.mem.2⟩

private theorem complete_high_zero_eqv (rho : TermTargetedPGraph A R)
    (hc : rho.graph.Complete) (hk : 2 ≤ k) (hkn : k ≤ n)
    (hp : rho.target.pick (t 1) = t k) {x : Nat} (hxn : x ≤ n)
    (heqv : EqvOn A rho.graph.par (t 0) (t x)) : x = 0 := by
  by_contra hx0
  have hxpos : 0 < x := Nat.pos_of_ne_zero hx0
  obtain ⟨_, _, s, h0s, hxs⟩ := heqv
  have hs : s = t 0 := by
    rcases h0s.head_inv with h | ⟨c, hc', _⟩
    · exact h.symm
    · rw [zero_nf rho.graph] at hc'
      contradiction
  subst hs
  have hxk : Reach rho.graph.par (t x) (t k) :=
    complete_high_positive_reach rho hc hk hkn hp hxpos hxn
  rcases Reach.comparable hxs hxk with h | h
  · have hz : t 0 = t k := by
      rcases h.head_inv with h' | ⟨c, hc', _⟩
      · exact h'
      · rw [zero_nf rho.graph] at hc'
        contradiction
    exact absurd ((tower_eq_iff).mp hz) (by omega)
  · have hz : t k = t 0 := by
      rcases h.head_inv with h' | ⟨c, hc', _⟩
      · exact h'
      · rw [selected_high_nf rho hk hkn hp] at hc'
        contradiction
    exact absurd ((tower_eq_iff).mp hz) (by omega)

theorem complete_target_eqv_iff (rho : TermTargetedPGraph A R)
    (hc : rho.graph.Complete) (hk : 0 < k) (hkn : k ≤ n)
    (hp : rho.target.pick (t 1) = t k) (hin : i ≤ n) (hjn : j ≤ n) :
    EqvOn A rho.graph.par (t i) (t j) ↔ k = 1 ∨ (i = 0 ↔ j = 0) := by
  by_cases hk1 : k = 1
  · constructor
    · intro _
      exact Or.inl hk1
    · intro _
      have hp1 : rho.target.pick (t 1) = t 1 := by rw [hp, hk1]
      have huniv : rho.Universal :=
        (complete_target_universal_iff rho hc (by omega)).mpr hp1
      exact huniv (down_tower_pair hin hjn)
  · have hk2 : 2 ≤ k := by omega
    constructor
    · intro heqv
      refine Or.inr ⟨?_, ?_⟩
      · intro hi0
        subst hi0
        exact complete_high_zero_eqv rho hc hk2 hkn hp hjn heqv
      · intro hj0
        subst hj0
        exact complete_high_zero_eqv rho hc hk2 hkn hp hin (EqvOn.symm heqv)
    · intro h
      rcases h with hk1' | hij
      · exact absurd hk1' hk1
      · by_cases hi0 : i = 0
        · have hj0 : j = 0 := hij.mp hi0
          subst hi0
          subst hj0
          exact EqvOn.refl ((tower_mem_iff).mpr hin)
        · have hj0 : j ≠ 0 := fun h0 => hi0 (hij.mpr h0)
          have hipos : 0 < i := Nat.pos_of_ne_zero hi0
          have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
          exact ⟨(tower_mem_iff).mpr hin, (tower_mem_iff).mpr hjn, t k,
            complete_high_positive_reach rho hc hk2 hkn hp hipos hin,
            complete_high_positive_reach rho hc hk2 hkn hp hjpos hjn⟩

theorem complete_target_nf_iff (rho : TermTargetedPGraph A R)
    (hc : rho.graph.Complete) (hk : 0 < k) (hkn : k ≤ n)
    (hp : rho.target.pick (t 1) = t k) (hin : i ≤ n) :
    rho.graph.NF (t i) ↔ i = 0 ∨ (2 ≤ k ∧ i = k) := by
  constructor
  · intro hnf
    by_cases hi0 : i = 0
    · exact Or.inl hi0
    · right
      have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      by_cases hk1 : k = 1
      · have hp1 : rho.target.pick (t 1) = t 1 := by rw [hp, hk1]
        exact absurd hnf (complete_low_positive_not_nf rho hc (by omega) hp1 hipos hin)
      · have hk2 : 2 ≤ k := by omega
        refine ⟨hk2, ?_⟩
        by_contra hik
        have hreach := complete_high_positive_reach rho hc hk2 hkn hp hipos hin
        have heq : t i = t k := by
          rcases hreach.head_inv with h' | ⟨c, hc', _⟩
          · exact h'
          · rw [hnf] at hc'
            contradiction
        exact absurd ((tower_eq_iff).mp heq) hik
  · intro h
    rcases h with hi0 | ⟨hk2, hik⟩
    · subst hi0
      exact zero_nf rho.graph
    · subst hik
      exact selected_high_nf rho hk2 hkn hp

theorem quotient_complete_target_universal_iff (rho : TargetedPGraph A R)
    (hc : rho.graph.Complete) (hn : 0 < n) :
    rho.graph.Universal ↔ rho.target.pickAt (t 1) = t 1 := by
  have h1A : t 1 ∈ A := (tower_mem_iff).mpr (by omega)
  have hgraph_iff : (rho.toTermTargeted).graph.Universal ↔ rho.toTermTargeted.Universal := by
    rw [PGraph.universal_iff_down_subset]
    exact Iff.rfl
  have hiff := complete_target_universal_iff rho.toTermTargeted hc hn
  have hp : (rho.toTermTargeted).target.pick (t 1) = rho.target.pickAt (t 1) := by
    change (Section7Target.ofTarget rho.target).pick (t 1) = rho.target.pickAt (t 1)
    rw [Section7Target.ofTarget_pick rho.target h1A, Target.pickAt_of_mem rho.target h1A]
  rw [hp] at hiff
  exact hgraph_iff.trans hiff

def towerTest [DecidableEq sigma] (c d : sigma) (a : CT sigma nu) : Nat → Bool
  | 0 =>
      match a with
      | .app (.inl f) [] => decide (f = c)
      | _ => false
  | i + 1 =>
      match a with
      | .app (.inr f) [b] => decide (f = d) && towerTest c d b i
      | _ => false

def towerIndex? [DecidableEq sigma] (c d : sigma) (n : Nat)
    (a : CT sigma nu) : Option Nat :=
  (List.range (n + 1)).find? (fun i => towerTest c d a i)

def ValidTarget (n k : Nat) : Prop :=
  (n = 0 ∧ k = 0) ∨ (0 < k ∧ k ≤ n)

instance validTargetDecidable (n k : Nat) : Decidable (ValidTarget n k) := by
  unfold ValidTarget
  infer_instance

def parentIndex (k i : Nat) : Option Nat :=
  if i = 0 then none
  else if k = 1 then (if i = 1 then some 0 else some 1)
  else if i = k then none else some k

def parent [DecidableEq sigma] (c d : sigma) (n k : Nat)
    (a : CT sigma nu) : Option (CT sigma nu) :=
  (towerIndex? c d n a).bind
    (fun i => (parentIndex k i).map (tower c d))

def pick [DecidableEq sigma] (c d : sigma) (n k : Nat)
    (a : CT sigma nu) : CT sigma nu :=
  match towerIndex? c d n a with
  | none => a
  | some 0 => tower c d 0
  | some (_ + 1) => tower c d k

def indexRank (k i : Nat) : Nat :=
  if k = 1 then (if i = 0 then 0 else if i = 1 then 1 else 2)
  else if i = 0 ∨ i = k then 0 else 1

def rank [DecidableEq sigma] (c d : sigma) (n k : Nat)
    (a : CT sigma nu) : Nat :=
  match towerIndex? c d n a with
  | none => 0
  | some i => indexRank k i

section Executable

variable [DecidableEq sigma]

theorem towerTest_true_iff : towerTest c d a i = true ↔ a = t i := by
  induction i generalizing a with
  | zero =>
      cases a with
      | var y => simp [towerTest, tower]
      | app f args =>
          cases f with
          | inl e =>
              cases args with
              | nil => simp [towerTest, tower]
              | cons b bs =>
                  cases bs with
                  | nil => simp [towerTest, tower]
                  | cons c' cs => simp [towerTest, tower]
          | inr e => simp [towerTest, tower]
  | succ i ih =>
      cases a with
      | var y => simp [towerTest, tower, wrap]
      | app f args =>
          cases f with
          | inl e => cases args <;> simp [towerTest, tower, wrap]
          | inr e =>
              cases args with
              | nil => simp [towerTest, tower, wrap]
              | cons b bs =>
                  cases bs with
                  | nil => simp [towerTest, ih, tower, wrap]
                  | cons c' cs => simp [towerTest, tower, wrap]

theorem towerIndex_some_iff :
    towerIndex? c d n a = some i ↔ i ≤ n ∧ a = t i := by
  constructor
  · intro hsome
    have his : (towerIndex? c d n a).isSome = true := by rw [hsome]; rfl
    obtain ⟨x, hxmem, hxtest⟩ := List.find?_isSome.mp his
    have hxle : x ≤ n := by
      have := List.mem_range.mp hxmem
      omega
    have hax : a = t x := (towerTest_true_iff).mp hxtest
    have hait : a = t i := (towerTest_true_iff).mp (List.find?_some hsome)
    have hix : i = x := (tower_eq_iff).mp (hait.symm.trans hax)
    exact ⟨by omega, hait⟩
  · rintro ⟨hin, rfl⟩
    cases hidx : towerIndex? c d n (t i) with
    | none =>
        have hall := (List.find?_eq_none).mp hidx
        have hmem : i ∈ List.range (n + 1) := List.mem_range.mpr (by omega)
        have htest : towerTest c d (t i) i = true := (towerTest_true_iff).mpr rfl
        exact absurd htest (hall i hmem)
    | some j =>
        have htj : t i = t j := (towerTest_true_iff).mp (List.find?_some hidx)
        have hji : j = i := (tower_eq_iff).mp htj.symm
        rw [hji]

theorem towerIndex_none_iff : towerIndex? c d n a = none ↔ a ∉ A := by
  constructor
  · intro h ha
    unfold towerIndex? at h
    obtain ⟨i, hi, rfl⟩ := (mem_carrier_iff).mp ha
    have hall := (List.find?_eq_none).mp h
    have hmem : i ∈ List.range (n + 1) := List.mem_range.mpr (by omega)
    exact absurd ((towerTest_true_iff).mpr rfl) (hall i hmem)
  · intro h
    unfold towerIndex?
    rw [List.find?_eq_none]
    intro x hxmem hxtest
    have hxle : x ≤ n := by
      have := List.mem_range.mp hxmem
      omega
    exact h (by rw [(towerTest_true_iff).mp hxtest]; exact (tower_mem_iff).mpr hxle)

theorem parent_tower (hi : i ≤ n) :
    parent c d n k (t i) = (parentIndex k i).map t := by
  unfold parent
  rw [(towerIndex_some_iff).mpr ⟨hi, rfl⟩]
  rfl

theorem parent_outside (ha : a ∉ A) : parent c d n k a = none := by
  unfold parent
  rw [(towerIndex_none_iff).mpr ha]
  rfl

theorem parentIndex_mem (hv : ValidTarget n k) (hi : i ≤ n)
    (he : parentIndex k i = some j) : j ≤ n := by
  rcases hv with ⟨hn0, hk0⟩ | ⟨hk0, hkn⟩
  · have hi0 : i = 0 := by omega
    unfold parentIndex at he
    rw [if_pos hi0] at he
    cases he
  · unfold parentIndex at he
    by_cases hi0 : i = 0
    · rw [if_pos hi0] at he
      cases he
    · rw [if_neg hi0] at he
      by_cases hk1 : k = 1
      · rw [if_pos hk1] at he
        by_cases hi1 : i = 1
        · rw [if_pos hi1] at he
          have hj : j = 0 := (Option.some.inj he).symm
          omega
        · rw [if_neg hi1] at he
          have hj : j = 1 := (Option.some.inj he).symm
          omega
      · rw [if_neg hk1] at he
        by_cases hik : i = k
        · rw [if_pos hik] at he
          cases he
        · rw [if_neg hik] at he
          have hj : j = k := (Option.some.inj he).symm
          omega

theorem parentIndex_decreases (he : parentIndex k i = some j) :
    indexRank k j < indexRank k i := by
  unfold parentIndex at he
  by_cases hi0 : i = 0
  · rw [if_pos hi0] at he
    cases he
  · rw [if_neg hi0] at he
    by_cases hk1 : k = 1
    · rw [if_pos hk1] at he
      by_cases hi1 : i = 1
      · rw [if_pos hi1] at he
        have hj : j = 0 := (Option.some.inj he).symm
        subst hj
        subst hi1
        simp [indexRank, hk1]
      · rw [if_neg hi1] at he
        have hj : j = 1 := (Option.some.inj he).symm
        subst hj
        simp [indexRank, hk1, hi0, hi1]
    · rw [if_neg hk1] at he
      by_cases hik : i = k
      · rw [if_pos hik] at he
        cases he
      · rw [if_neg hik] at he
        have hj : j = k := (Option.some.inj he).symm
        subst hj
        simp [indexRank, hk1, hi0, hik]

theorem parent_mem (hv : ValidTarget n k) (he : parent c d n k a = some b) :
    a ∈ A ∧ b ∈ A := by
  unfold parent at he
  cases hidx : towerIndex? c d n a with
  | none =>
      rw [hidx] at he
      cases he
  | some i =>
      rw [hidx] at he
      change (parentIndex k i).map t = some b at he
      obtain ⟨hin, ha⟩ := (towerIndex_some_iff).mp hidx
      cases hpi : parentIndex k i with
      | none =>
          rw [hpi] at he
          cases he
      | some j =>
          rw [hpi] at he
          have hbj : b = t j := (Option.some.inj he).symm
          refine ⟨?_, ?_⟩
          · rw [ha]
            exact (tower_mem_iff).mpr hin
          · rw [hbj]
            exact (tower_mem_iff).mpr (parentIndex_mem hv hin hpi)

theorem parent_decreases (hv : ValidTarget n k) (he : parent c d n k a = some b) :
    rank c d n k b < rank c d n k a := by
  unfold parent at he
  cases hidx : towerIndex? c d n a with
  | none =>
      rw [hidx] at he
      cases he
  | some i =>
      rw [hidx] at he
      change (parentIndex k i).map t = some b at he
      obtain ⟨hin, ha⟩ := (towerIndex_some_iff).mp hidx
      cases hpi : parentIndex k i with
      | none =>
          rw [hpi] at he
          cases he
      | some j =>
          rw [hpi] at he
          have hbj : b = t j := (Option.some.inj he).symm
          have hjn : j ≤ n := parentIndex_mem hv hin hpi
          subst ha
          subst hbj
          have h1 : rank c d n k (t j) = indexRank k j := by
            unfold rank
            rw [(towerIndex_some_iff).mpr ⟨hjn, rfl⟩]
          have h2 : rank c d n k (t i) = indexRank k i := by
            unfold rank
            rw [(towerIndex_some_iff).mpr ⟨hin, rfl⟩]
          rw [h1, h2]
          exact parentIndex_decreases hpi

theorem parent_terminating (hv : ValidTarget n k) :
    Terminating (parent (nu := nu) c d n k) := by
  refine Subrelation.wf ?_ (InvImage.wf (rank (nu := nu) c d n k) Nat.lt_wfRel.wf)
  intro x y hxy
  exact parent_decreases hv hxy

theorem parent_grey (hv : ValidTarget n k) (he : parent c d n k a = some b) :
    Grey A R (EqvOn A (parent c d n k)) a b := by
  unfold parent at he
  cases hidx : towerIndex? c d n a with
  | none =>
      rw [hidx] at he
      cases he
  | some i =>
      rw [hidx] at he
      change (parentIndex k i).map t = some b at he
      obtain ⟨hin, ha⟩ := (towerIndex_some_iff).mp hidx
      cases hpi : parentIndex k i with
      | none =>
          rw [hpi] at he
          cases he
      | some j =>
          rw [hpi] at he
          have hbj : b = t j := (Option.some.inj he).symm
          subst ha
          subst hbj
          unfold parentIndex at hpi
          by_cases hi0 : i = 0
          · rw [if_pos hi0] at hpi
            cases hpi
          · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
            rw [if_neg hi0] at hpi
            by_cases hk1 : k = 1
            · rw [if_pos hk1] at hpi
              by_cases hi1 : i = 1
              · rw [if_pos hi1] at hpi
                have hj : j = 0 := (Option.some.inj hpi).symm
                subst hj
                subst hi1
                exact Or.inl ((rootStep_tower_iff (i := 1) (j := 0)).mpr rfl)
              · rw [if_neg hi1] at hpi
                have hj : j = 1 := (Option.some.inj hpi).symm
                subst hj
                obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
                refine Or.inr (Or.inl ⟨.inr d, [tower c d i'], [tower c d 0],
                  ⟨d, rfl⟩, rfl, rfl, List.Forall₂.cons ?_ List.Forall₂.nil⟩)
                exact down_tower_pair (by omega) (Nat.zero_le n)
            · rw [if_neg hk1] at hpi
              by_cases hik : i = k
              · rw [if_pos hik] at hpi
                cases hpi
              · rw [if_neg hik] at hpi
                have hkj : j = k := (Option.some.inj hpi).symm
                rw [hkj]
                obtain ⟨hk0, hkn⟩ : 0 < k ∧ k ≤ n := by
                  rcases hv with ⟨rfl, rfl⟩ | h
                  · omega
                  · exact h
                obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
                obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
                refine Or.inr (Or.inl ⟨.inr d, [tower c d i'], [tower c d k'],
                  ⟨d, rfl⟩, rfl, rfl, List.Forall₂.cons ?_ List.Forall₂.nil⟩)
                exact down_tower_pair (by omega) (by omega)

def graph (hv : ValidTarget n k) : PGraph A R where
  par := parent c d n k
  mem_edge := parent_mem hv
  term := parent_terminating hv
  sub := fun h => down_all h.mem.1 h.mem.2
  grey := parent_grey hv

theorem graph_par (hv : ValidTarget n k) :
    (graph (c := c) (d := d) (x := x) hv).par = parent c d n k := rfl

theorem pick_tower_zero : pick c d n k (t 0) = t 0 := by
  unfold pick
  rw [(towerIndex_some_iff).mpr ⟨Nat.zero_le n, rfl⟩]

theorem pick_tower_positive (hi : 0 < i) (hin : i ≤ n) :
    pick c d n k (t i) = t k := by
  unfold pick
  rw [(towerIndex_some_iff).mpr ⟨hin, rfl⟩]
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rfl

def target (hv : ValidTarget n k) : Section7Target A R where
  pick := pick c d n k
  pick_mem := by
    intro w hw
    obtain ⟨i, hin, rfl⟩ := (mem_carrier_iff).mp hw
    by_cases hi0 : i = 0
    · subst hi0
      rw [pick_tower_zero]
      exact (tower_mem_iff).mpr (Nat.zero_le n)
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      rw [pick_tower_positive hipos hin]
      rcases hv with ⟨hn0, hk0⟩ | ⟨hk0, hkn⟩
      · omega
      · exact (tower_mem_iff).mpr hkn
  inFiber := by
    intro w hw
    obtain ⟨i, hin, rfl⟩ := (mem_carrier_iff).mp hw
    by_cases hi0 : i = 0
    · subst hi0
      rw [pick_tower_zero]
      exact BarReachOn.refl _
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      rw [pick_tower_positive hipos hin]
      rcases hv with ⟨hn0, hk0⟩ | ⟨hk0, hkn⟩
      · omega
      · exact (barReach_tower_iff hin (by omega)).mpr
          ⟨fun h => by omega, fun h => by omega⟩
  respectsFiber := by
    intro w v hw hv' hwv
    obtain ⟨i, hin, rfl⟩ := (mem_carrier_iff).mp hw
    obtain ⟨j, hjn, rfl⟩ := (mem_carrier_iff).mp hv'
    have hiff := (barReach_tower_iff hin hjn).mp hwv
    by_cases hi0 : i = 0
    · subst hi0
      have hj0 : j = 0 := hiff.mp rfl
      subst hj0
      rfl
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      have hj0 : j ≠ 0 := fun hj0' => hi0 (hiff.mpr hj0')
      have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      rw [pick_tower_positive hipos hin, pick_tower_positive hjpos hjn]
  redex_if_available := by
    intro w hw hred
    obtain ⟨i, hin, rfl⟩ := (mem_carrier_iff).mp hw
    by_cases hi0 : i = 0
    · subst hi0
      exact absurd hred ((no_rootRedexInFiber_of_conTopped
        (eraseRules_constructor (d := d) (x := x))) tower_zero_conTopped)
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      by_cases hk1 : k = 1
      · subst hk1
        refine ⟨t 0, (tower_mem_iff).mpr (Nat.zero_le n), ?_⟩
        rw [pick_tower_positive hipos hin]
        exact (rootStep_tower_iff (i := 1) (j := 0)).mpr rfl
      · obtain ⟨hk0, hkn⟩ : 0 < k ∧ k ≤ n := by
          rcases hv with ⟨rfl, rfl⟩ | h
          · omega
          · exact h
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        refine ⟨t k', (tower_mem_iff).mpr (by omega), ?_⟩
        rw [pick_tower_positive hipos hin]
        exact (rootStep_tower_iff (i := k' + 1) (j := k')).mpr rfl

theorem target_pick (hv : ValidTarget n k) :
    (target (c := c) (d := d) (x := x) hv).pick = pick c d n k := rfl

theorem graph_guided (hv : ValidTarget n k) (ha : a ∈ A) :
    GuidedReach (graph (c := c) (d := d) (x := x) hv) a (pick c d n k a) := by
  obtain ⟨i, hin, rfl⟩ := (mem_carrier_iff).mp ha
  by_cases hi0 : i = 0
  · subst hi0
    rw [pick_tower_zero]
    exact Relation.ReflTransGen.refl
  · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
    rw [pick_tower_positive hipos hin]
    by_cases hk1 : k = 1
    · subst hk1
      by_cases hi1 : i = 1
      · subst hi1
        exact Relation.ReflTransGen.refl
      · have hpar : (graph (c := c) (d := d) (x := x) hv).par (t i) = some (t 1) := by
          rw [graph_par, parent_tower hin]
          unfold parentIndex
          rw [if_neg hi0, if_pos rfl, if_neg hi1]
          rfl
        refine Relation.ReflTransGen.single ⟨hpar, ?_⟩
        exact (barStep_tower_iff hin (by omega)).mpr ⟨hipos, by omega⟩
    · obtain ⟨hk0, hkn⟩ : 0 < k ∧ k ≤ n := by
        rcases hv with ⟨rfl, rfl⟩ | h
        · omega
        · exact h
      by_cases hik : i = k
      · subst hik
        exact Relation.ReflTransGen.refl
      · have hpar : (graph (c := c) (d := d) (x := x) hv).par (t i) = some (t k) := by
          rw [graph_par, parent_tower hin]
          unfold parentIndex
          rw [if_neg hi0, if_neg hk1, if_neg hik]
          rfl
        refine Relation.ReflTransGen.single ⟨hpar, ?_⟩
        exact (barStep_tower_iff hin hkn).mpr ⟨hipos, hk0⟩

theorem graph_target_exit (hv : ValidTarget n k) (ha : a ∈ A)
    (he : (graph (c := c) (d := d) (x := x) hv).par (pick c d n k a) = some b) :
    ¬ BarReachOn A R a b := by
  obtain ⟨i, hin, rfl⟩ := (mem_carrier_iff).mp ha
  by_cases hi0 : i = 0
  · subst hi0
    rw [pick_tower_zero, graph_par, parent_tower (Nat.zero_le n)] at he
    unfold parentIndex at he
    rw [if_pos rfl] at he
    cases he
  · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
    by_cases hk1 : k = 1
    · subst hk1
      rw [pick_tower_positive hipos hin, graph_par,
        parent_tower (i := 1) (by omega)] at he
      have hb0 : b = t 0 := by
        unfold parentIndex at he
        rw [if_neg (by decide : ¬ (1 : Nat) = 0), if_pos rfl, if_pos rfl] at he
        exact (Option.some.inj he).symm
      subst hb0
      intro hbar
      have hiff := (barReach_tower_iff hin (Nat.zero_le n)).mp hbar
      have : i = 0 := hiff.mpr rfl
      omega
    · obtain ⟨hk0, hkn⟩ : 0 < k ∧ k ≤ n := by
        rcases hv with ⟨rfl, rfl⟩ | h
        · omega
        · exact h
      rw [pick_tower_positive hipos hin, graph_par, parent_tower hkn] at he
      unfold parentIndex at he
      rw [if_neg (Nat.pos_iff_ne_zero.mp hk0), if_neg hk1, if_pos rfl] at he
      cases he

def targeted (hv : ValidTarget n k) : TermTargetedPGraph A R where
  graph := graph (c := c) (d := d) (x := x) hv
  target := target (c := c) (d := d) (x := x) hv
  guided_or_nf := fun {_} hw => Or.inl (graph_guided hv hw)
  target_edge_exits_fiber := fun {_ _} hw he => graph_target_exit hv hw he

theorem targeted_graph (hv : ValidTarget n k) :
    (targeted (c := c) (d := d) (x := x) hv).graph = graph hv := rfl

theorem graph_complete (hv : ValidTarget n k) : (graph (c := c) (d := d) (x := x) hv).Complete := by
  intro beta hExt w p hab
  have hwA : w ∈ A := (beta.mem_edge hab).1
  obtain ⟨i, hin, rfl⟩ := (mem_carrier_iff).mp hwA
  have hpA : p ∈ A := (beta.mem_edge hab).2
  obtain ⟨j, hjn, rfl⟩ := (mem_carrier_iff).mp hpA
  by_cases hi0 : i = 0
  · subst hi0
    have hg : Grey A R (EqvOn A beta.par) (t 0) (t j) := beta.grey hab
    have hj0 : j = 0 := (tower_eq_iff).mp ((grey_zero_iff (EqvOn A beta.par)).mp hg)
    subst hj0
    exact (beta.term.no_parent_cycle hab (Reach.refl _)).elim
  · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
    by_cases hik : i = k
    · subst hik
      by_cases hi1 : i = 1
      · subst hi1
        have hpar : (graph (c := c) (d := d) (x := x) hv).par (t 1) = some (t 0) := by
          rw [graph_par, parent_tower (i := 1) (by omega)]
          unfold parentIndex
          rw [if_neg (by decide : ¬ (1 : Nat) = 0), if_pos rfl, if_pos rfl]
          rfl
        have hb : beta.par (t 1) = some (t 0) := hExt hpar
        have hj0 : j = 0 := by
          rw [hb] at hab
          exact (tower_eq_iff.mp (Option.some.inj hab)).symm
        subst hj0
        exact hpar
      · have hg : Grey A R (EqvOn A beta.par) (t i) (t j) := beta.grey hab
        by_cases hj0 : j = 0
        · subst hj0
          have hi1' : i = 1 :=
            (grey_to_zero_iff (EqvOn A beta.par) hipos).mp hg
          omega
        · by_cases hji : j = i
          · subst hji
            exact (beta.term.no_parent_cycle hab (Reach.refl _)).elim
          · have hparji : (graph (c := c) (d := d) (x := x) hv).par (t j) = some (t i) := by
              rw [graph_par, parent_tower hjn]
              unfold parentIndex
              rw [if_neg hj0, if_neg hi1, if_neg hji]
              rfl
            have hbeta := hExt hparji
            exact (beta.term.no_parent_cycle hab
              (Reach.head hbeta (Reach.refl _))).elim
    · by_cases hk1 : k = 1
      · subst hk1
        have hpar : (graph (c := c) (d := d) (x := x) hv).par (t i) = some (t 1) := by
          rw [graph_par, parent_tower hin]
          unfold parentIndex
          rw [if_neg hi0, if_pos rfl, if_neg (by omega : ¬ i = 1)]
          rfl
        have hbeta := hExt hpar
        have hj1 : j = 1 := by
          rw [hbeta] at hab
          exact (tower_eq_iff.mp (Option.some.inj hab)).symm
        subst hj1
        exact hpar
      · have hpar : (graph (c := c) (d := d) (x := x) hv).par (t i) = some (t k) := by
          rw [graph_par, parent_tower hin]
          unfold parentIndex
          rw [if_neg hi0, if_neg hk1, if_neg hik]
          rfl
        have hbeta := hExt hpar
        have hjk : j = k := by
          rw [hbeta] at hab
          exact (tower_eq_iff.mp (Option.some.inj hab)).symm
        subst hjk
        exact hpar

theorem targeted_universal_iff (hv : ValidTarget n k) :
    (targeted (c := c) (d := d) (x := x) hv).Universal ↔ n = 0 ∨ k = 1 := by
  rcases hv with ⟨hn0, hk0⟩ | ⟨hk0, hkn⟩
  · constructor
    · intro _
      exact Or.inl hn0
    · intro _
      intro w p hdown
      have hw : w = t 0 := by
        obtain ⟨i, hi, hw⟩ := (mem_carrier_iff).mp hdown.mem.1
        have hi' : i = 0 := by omega
        subst hi'
        exact hw
      have hp : p = t 0 := by
        obtain ⟨j, hj, hp⟩ := (mem_carrier_iff).mp hdown.mem.2
        have hj' : j = 0 := by omega
        subst hj'
        exact hp
      subst hw
      subst hp
      exact EqvOn.refl ((tower_mem_iff).mpr (Nat.zero_le n))
  · constructor
    · intro hu
      have hv2 : ValidTarget n k := Or.inr ⟨hk0, hkn⟩
      have hp1 := (complete_target_universal_iff (targeted (c := c) (d := d) (x := x) hv2)
        (graph_complete hv2) (by omega : 0 < n)).mp hu
      have hpk : (targeted (c := c) (d := d) (x := x) hv2).target.pick (t 1) = t k := by
        change (target (c := c) (d := d) (x := x) hv2).pick (t 1) = t k
        rw [target_pick]
        exact pick_tower_positive (by omega) (by omega)
      exact Or.inr ((tower_eq_iff).mp (hpk.symm.trans hp1))
    · intro h
      have hv2 : ValidTarget n k := Or.inr ⟨hk0, hkn⟩
      rcases h with h | h
      · omega
      · have hp1 : (targeted (c := c) (d := d) (x := x) hv2).target.pick (t 1) = t 1 := by
          change (target (c := c) (d := d) (x := x) hv2).pick (t 1) = t 1
          rw [target_pick, pick_tower_positive (by omega) (by omega), h]
        intro p q hdown
        exact (complete_target_universal_iff (targeted (c := c) (d := d) (x := x) hv2)
          (graph_complete hv2) (by omega : 0 < n)).mpr hp1 hdown

end Executable


section GeneralRepairObstruction

variable {B : List (CT sigma nu)} {S : TRS (sigma ⊕ sigma) nu}

theorem complete_nonuniversal_no_edge_extension
    (rho beta : PGraph B S) (hc : rho.Complete)
    (hn : ¬ rho.Universal) (hu : beta.Universal) :
    ¬ rho.Extends beta := by
  intro hext
  apply hn
  rw [PGraph.universal_iff_down_subset]
  intro p q hdown
  exact EqvOn.mono (hc beta hext) ((hu p q).mpr hdown)

theorem complete_nonuniversal_changed_edge
    (rho beta : PGraph B S) (hc : rho.Complete)
    (hn : ¬ rho.Universal) (hu : beta.Universal) :
    ∃ a b, rho.par a = some b ∧ beta.par a ≠ some b := by
  classical
  by_contra h
  apply complete_nonuniversal_no_edge_extension rho beta hc hn hu
  intro p q hpq
  by_contra hne
  exact h ⟨p, q, hpq, hne⟩

end GeneralRepairObstruction

/-- The repair selects target index one at every positive depth. -/
def repairTarget (n : Nat) : Nat := if n = 0 then 0 else 1

theorem repairTarget_zero : repairTarget 0 = 0 := rfl

theorem repairTarget_pos {n : Nat} (hn : n ≠ 0) : repairTarget n = 1 := by
  unfold repairTarget
  rw [if_neg hn]

theorem repairTarget_eq (n : Nat) : n = 0 ∨ repairTarget n = 1 := by
  by_cases hn : n = 0
  · exact Or.inl hn
  · exact Or.inr (repairTarget_pos hn)

theorem repairTarget_valid (n : Nat) : ValidTarget n (repairTarget n) := by
  by_cases hn : n = 0
  · subst hn
    exact Or.inl ⟨rfl, rfl⟩
  · refine Or.inr ⟨?_, ?_⟩ <;> rw [repairTarget_pos hn] <;> omega

section ExecutableRepair

variable [DecidableEq sigma]

def repaired : TermTargetedPGraph A R :=
  targeted (c := c) (d := d) (x := x) (n := n) (k := repairTarget n)
    (repairTarget_valid n)

theorem repaired_complete :
    (repaired (c := c) (d := d) (x := x) (n := n)).graph.Complete :=
  graph_complete (c := c) (d := d) (x := x) (n := n) (k := repairTarget n)
    (repairTarget_valid n)

theorem repaired_universal :
    (repaired (c := c) (d := d) (x := x) (n := n)).Universal :=
  (targeted_universal_iff (c := c) (d := d) (x := x) (n := n) (k := repairTarget n)
    (repairTarget_valid n)).mpr (repairTarget_eq n)

theorem repaired_target_pick (hn : n ≠ 0) :
    (repaired (c := c) (d := d) (x := x) (n := n)).target.pick (t 1) = t 1 := by
  rw [show (repaired (c := c) (d := d) (x := x) (n := n)).target =
    target (c := c) (d := d) (x := x) (n := n) (k := repairTarget n)
      (repairTarget_valid n) from rfl]
  rw [target_pick]
  rw [pick_tower_positive (i := 1) (by omega) (by omega), repairTarget_pos hn]

theorem repaired_reaches_zero (ha : a ∈ A) :
    Reach (repaired (c := c) (d := d) (x := x) (n := n)).graph.par a (t 0) := by
  by_cases hn0 : n = 0
  · subst hn0
    obtain ⟨i, hi, rfl⟩ := (mem_carrier_iff).mp ha
    have hi0 : i = 0 := by omega
    subst hi0
    exact Reach.refl _
  · have hp := repaired_target_pick (c := c) (d := d) (x := x) (n := n) hn0
    exact complete_low_reach (repaired (c := c) (d := d) (x := x) (n := n))
      (repaired_complete (c := c) (d := d) (x := x) (n := n)) (by omega) hp ha

theorem repaired_nf_iff (hi : i ≤ n) :
    (repaired (c := c) (d := d) (x := x) (n := n)).graph.NF (t i) ↔ i = 0 := by
  by_cases hn0 : n = 0
  · subst hn0
    have hi0 : i = 0 := by omega
    subst hi0
    constructor
    · intro _
      rfl
    · intro _
      exact zero_nf (repaired (c := c) (d := d) (x := x) (n := 0)).graph
  · have hp := repaired_target_pick (c := c) (d := d) (x := x) (n := n) hn0
    have h := complete_target_nf_iff (k := repairTarget n)
      (repaired (c := c) (d := d) (x := x) (n := n))
      (repaired_complete (c := c) (d := d) (x := x) (n := n))
      (by rw [repairTarget_pos hn0]; omega)
      (by rw [repairTarget_pos hn0]; omega)
      (by rw [repairTarget_pos hn0]; exact hp) hi
    have hk2 : ¬ 2 ≤ repairTarget n := by
      rw [repairTarget_pos hn0]
      omega
    constructor
    · intro hnf
      rcases h.mp hnf with hi0 | ⟨h2, -⟩
      · exact hi0
      · exact absurd h2 hk2
    · intro hi0
      subst hi0
      exact h.mpr (Or.inl rfl)

theorem repaired_preserves_eqv (rho : PGraph A R) :
    rho.EqualityExtends (repaired (c := c) (d := d) (x := x) (n := n)).graph := by
  intro p q hpq
  exact repaired_universal (c := c) (d := d) (x := x) (n := n) (rho.sub hpq)

theorem repaired_rootStepsRepresented :
    RootStepsRepresented A R (repaired (c := c) (d := d) (x := x) (n := n)).graph := by
  intro p q hp hq hroot
  exact repaired_universal (DownOn.rootComp hp hq hroot (DownOn.refl hq))

theorem repair_must_change_edge (rho : PGraph A R)
    (hc : rho.Complete) (hn : ¬ rho.Universal) :
    ∃ a b, rho.par a = some b ∧
      (repaired (c := c) (d := d) (x := x) (n := n)).graph.par a ≠ some b :=
  complete_nonuniversal_changed_edge rho
    (repaired (c := c) (d := d) (x := x) (n := n)).graph hc hn
    ((PGraph.universal_iff_down_subset
      (repaired (c := c) (d := d) (x := x) (n := n)).graph).mpr
      (fun _ _ h => repaired_universal (c := c) (d := d) (x := x) (n := n) h))

end ExecutableRepair


theorem exists_complete_universal_repair (rho : PGraph A R) :
    ∃ beta : TermTargetedPGraph A R,
      beta.graph.Complete ∧ beta.Universal ∧
      rho.EqualityExtends beta.graph ∧
      RootStepsRepresented A R beta.graph := by
  classical
  letI : DecidableEq sigma := Classical.decEq sigma
  exact ⟨repaired (c := c) (d := d) (x := x) (n := n),
    repaired_complete (c := c) (d := d) (x := x) (n := n),
    repaired_universal (c := c) (d := d) (x := x) (n := n),
    repaired_preserves_eqv (c := c) (d := d) (x := x) (n := n) rho,
    repaired_rootStepsRepresented (c := c) (d := d) (x := x) (n := n)⟩

theorem exists_complete_nonuniversal (hn : 2 ≤ n) :
    ∃ rho : TermTargetedPGraph A R,
      rho.graph.Complete ∧ ¬ rho.Universal := by
  classical
  letI : DecidableEq sigma := Classical.decEq sigma
  have hv : ValidTarget n n := Or.inr ⟨by omega, le_rfl⟩
  have hpk : (targeted (c := c) (d := d) (x := x) (n := n) (k := n) hv).target.pick
      (t 1) = t n := by
    change (target (c := c) (d := d) (x := x) (n := n) (k := n) hv).pick
      (t 1) = t n
    rw [target_pick]
    exact pick_tower_positive (by omega) (by omega)
  refine ⟨targeted (c := c) (d := d) (x := x) (n := n) (k := n) hv, ?_, ?_⟩
  · exact graph_complete (c := c) (d := d) (x := x) (n := n) (k := n) hv
  · exact selected_high_not_universal
      (targeted (c := c) (d := d) (x := x) (n := n) (k := n) hv) hn le_rfl hpk

theorem exists_quotient_complete_nonuniversal (hn : 2 ≤ n) :
    ∃ rho : TargetedPGraph A R, rho.graph.Complete ∧ ¬ rho.graph.Universal := by
  classical
  letI : DecidableEq sigma := Classical.decEq sigma
  obtain ⟨rho, hc, hnu⟩ :=
    exists_complete_nonuniversal (c := c) (d := d) (x := x) (n := n) hn
  refine ⟨quotientGraph rho, ?_, ?_⟩
  · rw [quotientGraph_graph]
    exact hc
  · rw [quotientGraph_universal_iff]
    exact hnu

theorem chain_counterexample_and_repair (hn : 2 ≤ n) :
    Coalgebra A ∧ ConstructorRules R ∧ StronglyAlmostNonOmegaOverlapping R ∧
    ∃ bad good : TargetedPGraph A R,
      bad.graph.Complete ∧ ¬ bad.graph.Universal ∧
      good.graph.Complete ∧ good.graph.Universal ∧
      bad.graph.EqualityExtends good.graph ∧
      (∃ a b, bad.graph.par a = some b ∧ good.graph.par a ≠ some b) := by
  classical
  letI : DecidableEq sigma := Classical.decEq sigma
  have hvBad : ValidTarget n n := Or.inr ⟨by omega, le_rfl⟩
  have hpkBad : (targeted (c := c) (d := d) (x := x) (n := n) (k := n) hvBad).target.pick
      (t 1) = t n := by
    change (target (c := c) (d := d) (x := x) (n := n) (k := n) hvBad).pick
      (t 1) = t n
    rw [target_pick]
    exact pick_tower_positive (by omega) (by omega)
  have hnu : ¬ (targeted (c := c) (d := d) (x := x) (n := n) (k := n) hvBad).Universal :=
    selected_high_not_universal
      (targeted (c := c) (d := d) (x := x) (n := n) (k := n) hvBad) hn le_rfl hpkBad
  refine ⟨carrier_coalgebra, eraseRules_constructor, eraseRules_strong, ?_⟩
  refine ⟨quotientGraph (targeted (c := c) (d := d) (x := x) (n := n) (k := n) hvBad),
    quotientGraph (repaired (c := c) (d := d) (x := x) (n := n)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [quotientGraph_graph]
    exact graph_complete (c := c) (d := d) (x := x) (n := n) (k := n) hvBad
  · rw [quotientGraph_universal_iff]
    exact hnu
  · rw [quotientGraph_graph]
    exact repaired_complete (c := c) (d := d) (x := x) (n := n)
  · rw [quotientGraph_universal_iff]
    exact repaired_universal (c := c) (d := d) (x := x) (n := n)
  · rw [quotientGraph_graph, quotientGraph_graph]
    exact repaired_preserves_eqv (c := c) (d := d) (x := x) (n := n)
      (targeted (c := c) (d := d) (x := x) (n := n) (k := n) hvBad).graph
  · rw [quotientGraph_graph, quotientGraph_graph]
    exact repair_must_change_edge (c := c) (d := d) (x := x) (n := n)
      (targeted (c := c) (d := d) (x := x) (n := n) (k := n) hvBad).graph
      (graph_complete (c := c) (d := d) (x := x) (n := n) (k := n) hvBad)
      (fun h => hnu (fun {a b} hab =>
        ((PGraph.universal_iff_down_subset
          (targeted (c := c) (d := d) (x := x) (n := n) (k := n) hvBad).graph).mp h)
            a b hab))

theorem depth_zero_universal (rho : PGraph (carrier (nu := nu) c d 0) R) :
    rho.Universal := by
  rw [PGraph.universal_iff_down_subset]
  intro p q hdown
  have hp : p = t 0 := by
    obtain ⟨i, hi, hp⟩ := (mem_carrier_iff).mp hdown.mem.1
    have hi0 : i = 0 := by omega
    rw [hi0] at hp
    exact hp
  have hq : q = t 0 := by
    obtain ⟨i, hi, hq⟩ := (mem_carrier_iff).mp hdown.mem.2
    have hi0 : i = 0 := by omega
    rw [hi0] at hq
    exact hq
  rw [hp, hq]
  exact EqvOn.refl ((tower_mem_iff).mpr (Nat.zero_le 0))

theorem depth_one_complete_universal
    (rho : TermTargetedPGraph (carrier (nu := nu) c d 1) R)
    (hc : rho.graph.Complete) : rho.Universal := by
  obtain ⟨k, ⟨hk0, hk1, hpk⟩, _⟩ :=
    target_index_exists_unique (n := 1) (by omega) rho.target
  have hk : k = 1 := by omega
  subst hk
  rw [complete_target_universal_iff (n := 1) rho hc (by omega)]
  exact hpk

theorem depth_zero_targeted_universal
    (rho : TermTargetedPGraph (carrier (nu := nu) c d 0) R) : rho.Universal := by
  intro p q hdown
  have hp : p = t 0 := by
    obtain ⟨i, hi, hp⟩ := (mem_carrier_iff).mp hdown.mem.1
    have hi0 : i = 0 := by omega
    rw [hi0] at hp
    exact hp
  have hq : q = t 0 := by
    obtain ⟨i, hi, hq⟩ := (mem_carrier_iff).mp hdown.mem.2
    have hi0 : i = 0 := by omega
    rw [hi0] at hq
    exact hq
  rw [hp, hq]
  exact EqvOn.refl ((tower_mem_iff).mpr (Nat.zero_le 0))

theorem chain_bad_graph_exists_iff :
    (∃ rho : TermTargetedPGraph A R, rho.graph.Complete ∧ ¬ rho.Universal) ↔ 2 ≤ n := by
  classical
  letI : DecidableEq sigma := Classical.decEq sigma
  constructor
  · rintro ⟨rho, hc, hnu⟩
    by_contra hn2
    by_cases hn0 : n = 0
    · subst hn0
      exact hnu (depth_zero_targeted_universal rho)
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hpne : rho.target.pick (t 1) ≠ t 1 := by
        intro hp
        exact hnu ((complete_target_universal_iff (n := n) rho hc hnpos).mpr hp)
      obtain ⟨k, ⟨hk0, hkn, hpk⟩, _⟩ :=
        target_index_exists_unique (n := n) hnpos rho.target
      have hk2 : 2 ≤ k := by
        by_contra h
        have hk1 : k = 1 := by omega
        exact hpne (by rw [hpk, hk1])
      omega
  · intro hn
    exact exists_complete_nonuniversal (c := c) (d := d) (x := x) (n := n) hn


def emptyGraph : PGraph A R where
  par := fun _ => none
  mem_edge := by
    intro p q hpq
    cases hpq
  term := by
    refine WellFounded.intro (fun p => Acc.intro p ?_)
    intro q hq
    cases hq
  sub := by
    intro p q hpq
    obtain ⟨hp, hq, s, hps, hqs⟩ := hpq
    have hps' : p = s := by
      rcases hps.head_inv with h | ⟨u, hu, _⟩
      · exact h
      · cases hu
    have hqs' : q = s := by
      rcases hqs.head_inv with h | ⟨u, hu, _⟩
      · exact h
      · cases hu
    subst hps'
    subst hqs'
    exact DownOn.refl hp
  grey := by
    intro p q hpq
    cases hpq

theorem emptyGraph_par :
    (emptyGraph (c := c) (d := d) (x := x) (n := n)).par = fun _ => none := rfl

theorem emptyGraph_par_apply (w : CT sigma nu) :
    (emptyGraph (c := c) (d := d) (x := x) (n := n)).par w = none := rfl

theorem emptyGraph_not_universal (hn : 0 < n) :
    ¬ (emptyGraph (c := c) (d := d) (x := x) (n := n)).Universal := by
  intro hu
  have hdown : DownOn A R (t 1) (t 0) := down_tower_pair (by omega) (Nat.zero_le n)
  obtain ⟨_, _, s, h1s, h0s⟩ := (hu (t 1) (t 0)).mpr hdown
  have h1 : t 1 = s := by
    rcases h1s.head_inv with h | ⟨u, hu', _⟩
    · exact h
    · rw [emptyGraph_par_apply (c := c) (d := d) (x := x) (n := n)] at hu'
      cases hu'
  have h0 : t 0 = s := by
    rcases h0s.head_inv with h | ⟨u, hu', _⟩
    · exact h
    · rw [emptyGraph_par_apply (c := c) (d := d) (x := x) (n := n)] at hu'
      cases hu'
  have h10 : (1 : Nat) = 0 := (tower_eq_iff).mp (h1.trans h0.symm)
  omega

def emptyValid (hn : 0 < n) : ValidTarget n 1 := Or.inr ⟨by omega, hn⟩

noncomputable def emptyTargeted [DecidableEq sigma] (hn : 0 < n) :
    TermTargetedPGraph A R where
  graph := emptyGraph (c := c) (d := d) (x := x) (n := n)
  target := target (c := c) (d := d) (x := x) (n := n) (k := 1) (emptyValid hn)
  guided_or_nf := fun {_} _ => Or.inr rfl
  target_edge_exits_fiber := by
    intro w u _ hwu
    cases hwu

theorem emptyTargeted_pick [DecidableEq sigma] (hn : 0 < n) :
    (emptyTargeted (c := c) (d := d) (x := x) (n := n) hn).target.pick (t 1) = t 1 := by
  rw [show (emptyTargeted (c := c) (d := d) (x := x) (n := n) hn).target =
    target (c := c) (d := d) (x := x) (n := n) (k := 1) (emptyValid hn) from rfl]
  rw [target_pick]
  exact pick_tower_positive (by omega) (by omega)

theorem emptyTargeted_not_universal [DecidableEq sigma] (hn : 0 < n) :
    ¬ (emptyTargeted (c := c) (d := d) (x := x) (n := n) hn).Universal := by
  intro hu
  have hdown : DownOn A R (t 1) (t 0) := down_tower_pair (by omega) (Nat.zero_le n)
  obtain ⟨_, _, s, h1s, h0s⟩ := hu hdown
  change Reach (emptyGraph (c := c) (d := d) (x := x) (n := n)).par (t 1) s at h1s
  change Reach (emptyGraph (c := c) (d := d) (x := x) (n := n)).par (t 0) s at h0s
  have h1 : t 1 = s := by
    rcases h1s.head_inv with h | ⟨u, hu', _⟩
    · exact h
    · rw [emptyGraph_par_apply (c := c) (d := d) (x := x) (n := n)] at hu'
      cases hu'
  have h0 : t 0 = s := by
    rcases h0s.head_inv with h | ⟨u, hu', _⟩
    · exact h
    · rw [emptyGraph_par_apply (c := c) (d := d) (x := x) (n := n)] at hu'
      cases hu'
  have h10 : (1 : Nat) = 0 := (tower_eq_iff).mp (h1.trans h0.symm)
  omega

theorem emptyGraph_not_complete (hn : 0 < n) :
    ¬ (emptyGraph (c := c) (d := d) (x := x) (n := n)).Complete := by
  classical
  letI : DecidableEq sigma := Classical.decEq sigma
  intro hc
  have hp : (emptyTargeted (c := c) (d := d) (x := x) (n := n) hn).target.pick
      (t 1) = t 1 :=
    emptyTargeted_pick (c := c) (d := d) (x := x) (n := n) hn
  have huniv : (emptyTargeted (c := c) (d := d) (x := x) (n := n) hn).Universal :=
    (complete_target_universal_iff (n := n)
      (emptyTargeted (c := c) (d := d) (x := x) (n := n) hn) hc hn).mpr hp
  have hdown : DownOn A R (t 1) (t 0) := down_tower_pair (by omega) (Nat.zero_le n)
  obtain ⟨_, _, s, h1s, h0s⟩ := huniv hdown
  change Reach (emptyGraph (c := c) (d := d) (x := x) (n := n)).par (t 1) s at h1s
  change Reach (emptyGraph (c := c) (d := d) (x := x) (n := n)).par (t 0) s at h0s
  have h1 : t 1 = s := by
    rcases h1s.head_inv with h | ⟨u, hu', _⟩
    · exact h
    · rw [emptyGraph_par_apply (c := c) (d := d) (x := x) (n := n)] at hu'
      cases hu'
  have h0 : t 0 = s := by
    rcases h0s.head_inv with h | ⟨u, hu', _⟩
    · exact h
    · rw [emptyGraph_par_apply (c := c) (d := d) (x := x) (n := n)] at hu'
      cases hu'
  have h10 : (1 : Nat) = 0 := (tower_eq_iff).mp (h1.trans h0.symm)
  omega

theorem completeness_premise_necessary (hn : 0 < n) :
    ∃ rho : TermTargetedPGraph A R,
      rho.target.pick (t 1) = t 1 ∧ ¬ rho.Universal ∧ ¬ rho.graph.Complete := by
  classical
  letI : DecidableEq sigma := Classical.decEq sigma
  exact ⟨emptyTargeted (c := c) (d := d) (x := x) (n := n) hn,
    emptyTargeted_pick (c := c) (d := d) (x := x) (n := n) hn,
    emptyTargeted_not_universal (c := c) (d := d) (x := x) (n := n) hn,
    emptyGraph_not_complete (c := c) (d := d) (x := x) (n := n) hn⟩


theorem depth_two_carrier_membership (a : Section7Active.T) :
    a ∈ carrier () () 2 ↔ a ∈ Section7Active.terms := by
  rw [Section7Active.mem_terms]
  constructor
  · intro ha
    obtain ⟨i, hi, rfl⟩ := (mem_carrier_iff (a := a)).mp ha
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
  · rintro (rfl | rfl | rfl)
    · exact (mem_carrier_iff (a := Section7Active.twice)).mpr ⟨2, by decide, rfl⟩
    · exact (mem_carrier_iff (a := Section7Active.once)).mpr ⟨1, by decide, rfl⟩
    · exact (mem_carrier_iff (a := Section7Active.constant)).mpr ⟨0, by decide, rfl⟩

theorem depth_two_bad_parent :
    parent (nu := Unit) () () 2 2 = Section7Active.Trap.parent := by
  funext w
  by_cases h1 : w = Section7Active.once
  · subst h1
    rw [show (Section7Active.once : CT Unit Unit) = tower () () 1 from rfl]
    rw [parent_tower (i := 1) (by decide : 1 ≤ 2)]
    rfl
  by_cases h2 : w = Section7Active.twice
  · subst h2
    rw [show (Section7Active.twice : CT Unit Unit) = tower () () 2 from rfl]
    rw [parent_tower (i := 2) (by decide : 2 ≤ 2)]
    rfl
  by_cases h3 : w = Section7Active.constant
  · subst h3
    rw [show (Section7Active.constant : CT Unit Unit) = tower () () 0 from rfl]
    rw [parent_tower (i := 0) (by decide : 0 ≤ 2)]
    rfl
  · have hA : w ∉ carrier () () 2 := by
      intro hw
      obtain ⟨i, hi, hwi⟩ := (mem_carrier_iff (a := w)).mp hw
      have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hcases with rfl | rfl | rfl
      · exact h3 hwi
      · exact h1 hwi
      · exact h2 hwi
    rw [parent_outside hA]
    simp [Section7Active.Trap.parent, h1]

theorem depth_two_good_parent :
    parent (nu := Unit) () () 2 1 = Section7Active.parent := by
  funext w
  by_cases h2 : w = Section7Active.twice
  · subst h2
    rw [show (Section7Active.twice : CT Unit Unit) = tower () () 2 from rfl]
    rw [parent_tower (i := 2) (by decide : 2 ≤ 2)]
    rfl
  by_cases h1 : w = Section7Active.once
  · subst h1
    rw [show (Section7Active.once : CT Unit Unit) = tower () () 1 from rfl]
    rw [parent_tower (i := 1) (by decide : 1 ≤ 2)]
    rfl
  by_cases h3 : w = Section7Active.constant
  · subst h3
    rw [show (Section7Active.constant : CT Unit Unit) = tower () () 0 from rfl]
    rw [parent_tower (i := 0) (by decide : 0 ≤ 2)]
    rfl
  · have hA : w ∉ carrier () () 2 := by
      intro hw
      obtain ⟨i, hi, hwi⟩ := (mem_carrier_iff (a := w)).mp hw
      have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hcases with rfl | rfl | rfl
      · exact h3 hwi
      · exact h1 hwi
      · exact h2 hwi
    rw [parent_outside hA]
    simp [Section7Active.parent, h2, h1]

theorem towerTest_var_false [DecidableEq sigma] (y : nu) (i : Nat) :
    towerTest c d (.var y) i = false := by
  cases i <;> rfl

theorem towerTest_binary_false [DecidableEq sigma] (i : Nat) :
    towerTest c d (.app (.inr d) [a, b]) i = false := by
  cases i <;> rfl

theorem towerTest_constructor_arg_false [DecidableEq sigma] (i : Nat) :
    towerTest c d (.app (.inl c) [a]) i = false := by
  cases i <;> rfl

theorem depth_four_good_parent :
    parent (nu := Unit) () () 4 1 (tower () () 4) = some (tower () () 1) ∧
    parent (nu := Unit) () () 4 1 (tower () () 1) = some (tower () () 0) ∧
    parent (nu := Unit) () () 4 1 (tower () () 0) = none := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

theorem depth_four_bad_parent :
    parent (nu := Unit) () () 4 4 (tower () () 3) = some (tower () () 4) ∧
    parent (nu := Unit) () () 4 4 (tower () () 4) = none := by
  refine ⟨?_, ?_⟩ <;> rfl

end OperatorKO7.Meta.UniqueNormalization.ChainClassification

