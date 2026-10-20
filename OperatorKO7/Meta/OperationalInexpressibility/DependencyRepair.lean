import OperatorKO7.Meta.OperationalInexpressibility.DependencyLicense

/-!
# Subset repairs, consistent answers, and the error measures of a dependency

The maximal sets on which an observer licenses a target are the subset repairs of the
dependency. A state lies in every repair exactly when its fiber has one target value, and
the number of repairs is the product over realized fibers of the number of target values on the
fiber. The least number of deletions after which the dependency holds, divided by the number of
states, is the Bayes risk under the uniform law. The two other error measures of Kivinen and
Mannila count the states in a violating pair and the ordered violating pairs; all three vanish
exactly on licensed pairs.

Relation: equality of observations on a finite set of states.
Property: repairs, their count, certain answers, the measures g1, g2, g3.
Trust: kernel only; repairs and the largest licensed set use classical decidability.
Scope: arbitrary types for the answer theorems; finite states with decidable equality for counts.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.DependencyRepair

open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit
open OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery
open OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel
open OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse

universe u v w

section Answers

variable {X : Type u} {Q : Type v} {V : Type w}

/-- **Consistent answers.** A state lies in every subset repair exactly when every state of its
fiber has its target value. -/
theorem mem_every_repair_iff_fiber_constant (q : X → Q) (P : X → V) (x : X) :
    (∀ S : Set X, MaximalLicensedOn S q P → x ∈ S) ↔ ∀ y, q y = q x → P y = P x := by
  haveI : Nonempty V := ⟨P x⟩
  constructor
  · intro h y hy
    by_contra hne
    have hcol : OperationallyInexpressibleAt q P y x := ⟨hy, hne⟩
    obtain ⟨⟨S, hS, hyS, hxS⟩, _⟩ := maximal_refusals_of_collision hcol
    exact hxS (h S hS)
  · intro h S hS
    obtain ⟨d, hatt, rfl⟩ := (maximalLicensedOn_iff S q P).1 hS
    obtain ⟨y, hyq, hyP⟩ := hatt x
    show P x = d (q x)
    rw [← h y hyq, hyP]

/-- **Possible answers.** Every state lies in some subset repair. -/
theorem exists_repair_mem (q : X → Q) (P : X → V) (x : X) :
    ∃ S : Set X, MaximalLicensedOn S q P ∧ x ∈ S := by
  haveI : Nonempty V := ⟨P x⟩
  have hlic : LicensedOn ({x} : Set X) q P := by
    intro z hz w hw _
    rw [Set.mem_singleton_iff.1 hz, Set.mem_singleton_iff.1 hw]
  refine ⟨correctSet q P (retainedDecoder {x} q P),
    (maximalLicensedOn_iff _ q P).2 ⟨_, retainedDecoder_fiberAttained {x} q P, rfl⟩, ?_⟩
  exact retainedDecoder_of_mem hlic (Set.mem_singleton x)

end Answers

section Finite

variable {X : Type u} {Q : Type v} {V : Type w} [Fintype X] [DecidableEq X] [DecidableEq Q]
  [DecidableEq V]

open Classical in
/-- The subset repairs of the dependency `q → P`. -/
noncomputable def subsetRepairs (q : X → Q) (P : X → V) : Finset (Finset X) :=
  Finset.univ.filter fun S => MaximalLicensedOn (↑S : Set X) q P

section Decoders

variable {X : Type u} {Q : Type v} {V : Type w} [Fintype X] [DecidableEq Q]

open Classical in
/-- A decoder read off a menu choice on the realized fibers. -/
private noncomputable def decoderOfChoice [Nonempty V] (q : X → Q)
    (c : ∀ o : Q, o ∈ Finset.univ.image q → V) : Q → V :=
  fun o => if h : o ∈ Finset.univ.image q then c o h else Classical.arbitrary V

private theorem decoderOfChoice_apply [Nonempty V] (q : X → Q)
    (c : ∀ o : Q, o ∈ Finset.univ.image q → V) (o : Q)
    (h : o ∈ Finset.univ.image q) : decoderOfChoice q c o = c o h := by
  unfold decoderOfChoice
  rw [dif_pos h]

end Decoders

omit [DecidableEq X] in
private theorem card_subsetRepairs_nonempty [Nonempty V] (q : X → Q) (P : X → V) :
    (subsetRepairs q P).card = ∏ o ∈ Finset.univ.image q, (fiberVerdicts q P o).card := by
  classical
  rw [← Finset.card_pi]
  symm
  refine Finset.card_bij
    (fun c (_ : c ∈ (Finset.univ.image q).pi (fiberVerdicts q P)) =>
      Finset.univ.filter fun x =>
        P x = c (q x) (Finset.mem_image_of_mem q (Finset.mem_univ x))) ?_ ?_ ?_
  · intro c hc
    have hd : ∀ o (h : o ∈ Finset.univ.image q), decoderOfChoice q c o = c o h :=
      decoderOfChoice_apply q c
    have hAtt : FiberAttained q P (decoderOfChoice q c) := by
      intro x
      have hmemx : q x ∈ Finset.univ.image q := Finset.mem_image_of_mem q (Finset.mem_univ x)
      have hcx : c (q x) hmemx ∈ fiberVerdicts q P (q x) := (Finset.mem_pi.1 hc) (q x) hmemx
      obtain ⟨y, hyq, hyP⟩ := mem_fiberVerdicts.1 hcx
      exact ⟨y, hyq, by rw [hd (q x) hmemx]; exact hyP⟩
    have hcoe : (↑(Finset.univ.filter fun x =>
          P x = c (q x) (Finset.mem_image_of_mem q (Finset.mem_univ x))) : Set X) =
        correctSet q P (decoderOfChoice q c) := by
      ext x
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, correctSet,
        Set.mem_setOf_eq]
      rw [hd (q x) (Finset.mem_image_of_mem q (Finset.mem_univ x))]
    unfold subsetRepairs
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, (maximalLicensedOn_iff _ q P).2
      ⟨decoderOfChoice q c, hAtt, hcoe⟩⟩
  · intro c₁ hc₁ c₂ hc₂ heq
    have hd₁ : ∀ o (h : o ∈ Finset.univ.image q), decoderOfChoice q c₁ o = c₁ o h :=
      decoderOfChoice_apply q c₁
    have hd₂ : ∀ o (h : o ∈ Finset.univ.image q), decoderOfChoice q c₂ o = c₂ o h :=
      decoderOfChoice_apply q c₂
    have hcf₁ : (Finset.univ.filter fun x =>
          P x = c₁ (q x) (Finset.mem_image_of_mem q (Finset.mem_univ x))) =
        correctFinset q P (decoderOfChoice q c₁) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, correctFinset]
      rw [hd₁ (q x) (Finset.mem_image_of_mem q (Finset.mem_univ x))]
    have hcf₂ : (Finset.univ.filter fun x =>
          P x = c₂ (q x) (Finset.mem_image_of_mem q (Finset.mem_univ x))) =
        correctFinset q P (decoderOfChoice q c₂) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, correctFinset]
      rw [hd₂ (q x) (Finset.mem_image_of_mem q (Finset.mem_univ x))]
    have hd : decoderOfChoice q c₁ = decoderOfChoice q c₂ := by
      funext o
      by_cases ho : o ∈ Finset.univ.image q
      · have hc₁o : c₁ o ho ∈ fiberVerdicts q P o := (Finset.mem_pi.1 hc₁) o ho
        obtain ⟨z, hzq, hzP⟩ := mem_fiberVerdicts.1 hc₁o
        have hz₁ : z ∈ correctFinset q P (decoderOfChoice q c₁) := by
          simp only [correctFinset, Finset.mem_filter, Finset.mem_univ, true_and]
          show P z = decoderOfChoice q c₁ (q z)
          rw [hzq, hd₁ o ho]
          exact hzP
        have heq' : (Finset.univ.filter fun x =>
              P x = c₁ (q x) (Finset.mem_image_of_mem q (Finset.mem_univ x))) =
            (Finset.univ.filter fun x =>
              P x = c₂ (q x) (Finset.mem_image_of_mem q (Finset.mem_univ x))) := heq
        have hz₂ : z ∈ correctFinset q P (decoderOfChoice q c₂) := by
          have h₂ : z ∈ (Finset.univ.filter fun x =>
              P x = c₂ (q x) (Finset.mem_image_of_mem q (Finset.mem_univ x))) := by
            have h₁' : z ∈ (Finset.univ.filter fun x =>
                P x = c₁ (q x) (Finset.mem_image_of_mem q (Finset.mem_univ x))) := by
              rwa [← hcf₁] at hz₁
            exact heq' ▸ h₁'
          rwa [hcf₂] at h₂
        have hPz₂ : P z = decoderOfChoice q c₂ (q z) := by
          simpa only [correctFinset, Finset.mem_filter, Finset.mem_univ, true_and] using hz₂
        rw [hd₁ o ho, ← hzP, ← hzq]
        exact hPz₂
      · unfold decoderOfChoice
        rw [dif_neg ho, dif_neg ho]
    funext o ho
    rw [← hd₁ o ho, ← hd₂ o ho, hd]
  · intro S hS
    have hSmax : MaximalLicensedOn (↑S : Set X) q P := (Finset.mem_filter.1 hS).2
    obtain ⟨d, hAtt, hSd⟩ := (maximalLicensedOn_iff _ q P).1 hSmax
    refine ⟨fun o _ => d o, ?_, ?_⟩
    · rw [Finset.mem_pi]
      intro o ho
      obtain ⟨x, -, hxq⟩ := Finset.mem_image.1 ho
      obtain ⟨z, hzq, hzP⟩ := hAtt x
      exact mem_fiberVerdicts.2 ⟨z, by rw [hzq, hxq], by rw [hzP, hxq]⟩
    · have hcf : (Finset.univ.filter fun x =>
            P x = (fun o _ => d o) (q x) (Finset.mem_image_of_mem q (Finset.mem_univ x))) =
          correctFinset q P d := rfl
      show (Finset.univ.filter fun x =>
            P x = (fun o _ => d o) (q x) (Finset.mem_image_of_mem q (Finset.mem_univ x))) = S
      rw [hcf]
      apply Finset.coe_inj.1
      rw [coe_correctFinset]
      exact hSd.symm

omit [DecidableEq X] in
/-- **Repair count.** -/
theorem card_subsetRepairs (q : X → Q) (P : X → V) :
    (subsetRepairs q P).card = ∏ o ∈ Finset.univ.image q, (fiberVerdicts q P o).card := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · haveI : IsEmpty X := hX
    have hL : (subsetRepairs q P).card = 1 := by
      have hmax : MaximalLicensedOn (↑(∅ : Finset X) : Set X) q P := by
        refine ⟨?_, ?_⟩
        · exact fun x _ y _ _ => isEmptyElim x
        · intro T _ _
          ext w
          exact ⟨fun _ => isEmptyElim w, fun _ => isEmptyElim w⟩
      have huniq : subsetRepairs q P = {∅} := by
        ext S
        constructor
        · intro _
          have hS : S = ∅ := by
            ext z
            exact isEmptyElim z
          rw [hS]
          exact Finset.mem_singleton_self (∅ : Finset X)
        · intro hS
          rw [Finset.mem_singleton] at hS
          subst hS
          unfold subsetRepairs
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hmax⟩
      rw [huniq]
      simp
    have hR : (∏ o ∈ Finset.univ.image q, (fiberVerdicts q P o).card) = 1 := by
      rw [show (Finset.univ : Finset X) = ∅ from Finset.univ_eq_empty]
      simp
    rw [hL, hR]
  · haveI : Nonempty X := hX
    haveI : Nonempty V := ⟨P (Classical.arbitrary X)⟩
    exact card_subsetRepairs_nonempty q P

open Classical in
/-- The largest number of states on which `q` licenses `P`. -/
noncomputable def maxLicensedCard (q : X → Q) (P : X → V) : ℕ :=
  (Finset.univ.filter fun S : Finset X => LicensedOn (↑S : Set X) q P).sup Finset.card

/-- Number of states with observation `o`. -/
def fiberCount (q : X → Q) (o : Q) : ℕ :=
  (Finset.univ.filter fun x => q x = o).card

/-- Number of states with observation `o` and target `v`. -/
def cellCount (q : X → Q) (P : X → V) (o : Q) (v : V) : ℕ :=
  (Finset.univ.filter fun x => q x = o ∧ P x = v).card

/-- The measure `g₃` of Kivinen and Mannila as a count: the least number of deletions. -/
noncomputable def g3Count (q : X → Q) (P : X → V) : ℕ := Fintype.card X - maxLicensedCard q P

/-- The measure `g₂` as a count: states that belong to a violating pair. -/
def g2Count (q : X → Q) (P : X → V) : ℕ :=
  (Finset.univ.filter fun x => ∃ y, q y = q x ∧ P y ≠ P x).card

/-- The measure `g₁` as a count: ordered violating pairs. -/
def g1Count (q : X → Q) (P : X → V) : ℕ :=
  (Finset.univ.filter fun p : X × X => q p.1 = q p.2 ∧ P p.1 ≠ P p.2).card

noncomputable def g3 (q : X → Q) (P : X → V) : ℚ := (g3Count q P : ℚ) / Fintype.card X

noncomputable def g2 (q : X → Q) (P : X → V) : ℚ := (g2Count q P : ℚ) / Fintype.card X

noncomputable def g1 (q : X → Q) (P : X → V) : ℚ :=
  (g1Count q P : ℚ) / (Fintype.card X : ℚ) ^ 2

omit [DecidableEq X] [DecidableEq Q] [DecidableEq V] in
theorem maxLicensedCard_le_card (q : X → Q) (P : X → V) : maxLicensedCard q P ≤ Fintype.card X := by
  unfold maxLicensedCard
  exact Finset.sup_le fun S _ => Finset.card_le_univ S

omit [DecidableEq X] [DecidableEq Q] [DecidableEq V] in
theorem exists_licensedOn_card_eq_max (q : X → Q) (P : X → V) :
    ∃ S : Finset X, LicensedOn (↑S : Set X) q P ∧ S.card = maxLicensedCard q P := by
  classical
  obtain ⟨S, hS, hcard⟩ := Finset.exists_mem_eq_sup
    (Finset.univ.filter fun S : Finset X => LicensedOn (↑S : Set X) q P)
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, by intro x hx; simp at hx⟩⟩ Finset.card
  exact ⟨S, (Finset.mem_filter.1 hS).2, hcard.symm⟩

omit [DecidableEq X] in
/-- **Fiber formula.** A largest licensed set keeps a most frequent target value on each fiber. -/
theorem maxLicensedCard_eq_sum (q : X → Q) (P : X → V) :
    maxLicensedCard q P =
      ∑ o ∈ Finset.univ.image q, (fiberVerdicts q P o).sup (cellCount q P o) := by
  classical
  by_cases hX : Nonempty X
  · haveI : Nonempty V := ⟨P (Classical.arbitrary X)⟩
    obtain ⟨S, hSlic, hScard⟩ := exists_licensedOn_card_eq_max q P
    apply le_antisymm
    · rw [← hScard]
      have hfiber := Finset.card_eq_sum_card_fiberwise (s := S) (t := Finset.univ.image q) (f := q)
        (fun x _ => Finset.mem_image_of_mem q (Finset.mem_univ x))
      rw [hfiber]
      apply Finset.sum_le_sum
      intro o ho
      by_cases hpart : (S.filter fun x => q x = o).Nonempty
      · obtain ⟨x₀, hx₀⟩ := hpart
        have hx₀S : x₀ ∈ S := (Finset.mem_filter.1 hx₀).1
        have hx₀q : q x₀ = o := (Finset.mem_filter.1 hx₀).2
        have hcell : (S.filter fun x => q x = o).card ≤ cellCount q P o (P x₀) := by
          unfold cellCount
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_filter] at hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hx.2, hSlic x (Finset.mem_coe.2 hx.1) x₀ (Finset.mem_coe.2 hx₀S)
            (hx.2.trans hx₀q.symm)⟩
        have hmem : P x₀ ∈ fiberVerdicts q P o := mem_fiberVerdicts.2 ⟨x₀, hx₀q, rfl⟩
        exact hcell.trans (Finset.le_sup (f := cellCount q P o) hmem)
      · rw [Finset.not_nonempty_iff_eq_empty] at hpart
        rw [hpart]
        exact Nat.zero_le _
    · have hfvn : ∀ o, o ∈ Finset.univ.image q → (fiberVerdicts q P o).Nonempty := by
        intro o ho
        obtain ⟨x, -, hxq⟩ := Finset.mem_image.1 ho
        exact ⟨P x, mem_fiberVerdicts.2 ⟨x, hxq, rfl⟩⟩
      let v : Q → V := fun o => if h : o ∈ Finset.univ.image q then
          Classical.choose (Finset.exists_mem_eq_sup (fiberVerdicts q P o) (hfvn o h)
            (cellCount q P o))
        else Classical.arbitrary V
      have hv_spec : ∀ o (h : o ∈ Finset.univ.image q),
          cellCount q P o (v o) = (fiberVerdicts q P o).sup (cellCount q P o) := by
        intro o h
        unfold v
        rw [dif_pos h]
        exact (Classical.choose_spec (Finset.exists_mem_eq_sup (fiberVerdicts q P o) (hfvn o h)
          (cellCount q P o))).2.symm
      have hlic : LicensedOn (↑(correctFinset q P v) : Set X) q P := by
        rw [coe_correctFinset]
        exact licensedOn_correctSet q P v
      have hle : (correctFinset q P v).card ≤ maxLicensedCard q P :=
        Finset.le_sup (Finset.mem_filter.2 ⟨Finset.mem_univ _, hlic⟩)
      have hcard : (correctFinset q P v).card =
          ∑ o ∈ Finset.univ.image q, cellCount q P o (v o) := by
        have hfiber := Finset.card_eq_sum_card_fiberwise (s := correctFinset q P v)
          (t := Finset.univ.image q) (f := q)
          (fun x _ => Finset.mem_image_of_mem q (Finset.mem_univ x))
        rw [hfiber]
        apply Finset.sum_congr rfl
        intro o _
        have hpart : (correctFinset q P v).filter (fun x => q x = o) =
            Finset.univ.filter (fun x => q x = o ∧ P x = v o) := by
          ext x
          simp only [correctFinset, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hP, hq⟩
            exact ⟨hq, by rw [hP, hq]⟩
          · rintro ⟨hq, hP⟩
            exact ⟨by rw [hP, hq], hq⟩
        rw [hpart]
        rfl
      calc ∑ o ∈ Finset.univ.image q, (fiberVerdicts q P o).sup (cellCount q P o)
          = ∑ o ∈ Finset.univ.image q, cellCount q P o (v o) := by
            apply Finset.sum_congr rfl
            intro o ho
            rw [hv_spec o ho]
        _ = (correctFinset q P v).card := hcard.symm
        _ ≤ maxLicensedCard q P := hle
  · haveI : IsEmpty X := not_nonempty_iff.mp hX
    have hsum : (∑ o ∈ Finset.univ.image q, (fiberVerdicts q P o).sup (cellCount q P o)) = 0 := by
      simp
    rw [hsum]
    apply le_antisymm _ (Nat.zero_le _)
    apply Finset.sup_le
    intro S _
    have hS : S = ∅ := Finset.eq_empty_iff_forall_notMem.2 fun x _ => isEmptyElim x
    simp [hS]

/-- The uniform law on the states. -/
noncomputable def uniformPrior (X : Type u) [Fintype X] : X → ℚ := fun _ => 1 / Fintype.card X

omit [DecidableEq X] in
theorem uniformPrior_nonneg (x : X) : 0 ≤ uniformPrior X x := by
  unfold uniformPrior
  positivity

omit [DecidableEq X] in
theorem uniformPrior_sum [Nonempty X] : ∑ x, uniformPrior X x = 1 := by
  have hn : (Fintype.card X : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := X)
  unfold uniformPrior
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- The weight refused under the uniform law, as a count of dropped states. -/
theorem refusedMass_uniform (S : Finset X) :
    refusedMass (uniformPrior X) S =
      ((Fintype.card X - S.card : ℕ) : ℚ) / (Fintype.card X : ℚ) := by
  have h1 : (∑ x, if x ∈ S then (0 : ℚ) else (1 : ℚ) / (Fintype.card X : ℚ)) =
      ∑ x ∈ Finset.univ.filter (fun x => x ∉ S), ((1 : ℚ) / (Fintype.card X : ℚ)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ S <;> simp [hx]
  have hfilter : Finset.univ.filter (fun x => x ∉ S) = Sᶜ := by
    ext x
    simp
  unfold refusedMass uniformPrior
  rw [h1, hfilter, Finset.sum_const, nsmul_eq_mul, Finset.card_compl]
  ring

/-- **`g₃` is a Bayes risk.** -/
theorem g3_eq_bayesRisk_uniform [Nonempty X] [Fintype Q] (EV : Enumeration V) (q : X → Q)
    (P : X → V) :
    g3 q P = bayesRisk EV
      (deterministicModel (uniformPrior X) uniformPrior_nonneg uniformPrior_sum q) P := by
  classical
  have hβ : bayesRisk EV
        (deterministicModel (uniformPrior X) uniformPrior_nonneg uniformPrior_sum q) P =
      ((Fintype.card X - maxLicensedCard q P : ℕ) : ℚ) / (Fintype.card X) := by
    obtain ⟨S₀, hS₀lic, hS₀mass⟩ :=
      (least_refusal_eq_bayesRisk EV (uniformPrior X) uniformPrior_nonneg uniformPrior_sum q P).1
    have hβle : bayesRisk EV
          (deterministicModel (uniformPrior X) uniformPrior_nonneg uniformPrior_sum q) P ≤
        ((Fintype.card X - maxLicensedCard q P : ℕ) : ℚ) / (Fintype.card X) := by
      obtain ⟨Sstar, hSstarlic, hSstarcard⟩ := exists_licensedOn_card_eq_max q P
      have h := (least_refusal_eq_bayesRisk EV (uniformPrior X) uniformPrior_nonneg
        uniformPrior_sum q P).2 Sstar hSstarlic
      rwa [refusedMass_uniform Sstar, hSstarcard] at h
    have hS₀card : S₀.card ≤ maxLicensedCard q P :=
      Finset.le_sup (Finset.mem_filter.2 ⟨Finset.mem_univ _, hS₀lic⟩)
    have hβge : ((Fintype.card X - maxLicensedCard q P : ℕ) : ℚ) / (Fintype.card X) ≤
        bayesRisk EV
          (deterministicModel (uniformPrior X) uniformPrior_nonneg uniformPrior_sum q) P := by
      calc ((Fintype.card X - maxLicensedCard q P : ℕ) : ℚ) / (Fintype.card X)
          ≤ ((Fintype.card X - S₀.card : ℕ) : ℚ) / (Fintype.card X) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact_mod_cast Nat.sub_le_sub_left hS₀card (Fintype.card X)
        _ = refusedMass (uniformPrior X) S₀ := (refusedMass_uniform S₀).symm
        _ = bayesRisk EV
              (deterministicModel (uniformPrior X) uniformPrior_nonneg uniformPrior_sum q) P :=
            hS₀mass
    exact le_antisymm hβle hβge
  unfold g3 g3Count
  exact hβ.symm

open Classical in
theorem g2Count_eq_card_sub_certain [Nonempty V] (q : X → Q) (P : X → V) :
    g2Count q P = Fintype.card X -
      (Finset.univ.filter fun x => ∀ S : Set X, MaximalLicensedOn S q P → x ∈ S).card := by
  have hcertain : (Finset.univ.filter fun x => ∀ S : Set X, MaximalLicensedOn S q P → x ∈ S) =
      Finset.univ.filter fun x => ∀ y, q y = q x → P y = P x := by
    apply Finset.filter_congr
    intro x _
    exact mem_every_repair_iff_fiber_constant q P x
  have hcompl : (Finset.univ.filter fun x => ∃ y, q y = q x ∧ P y ≠ P x) =
      (Finset.univ.filter fun x => ∀ y, q y = q x → P y = P x)ᶜ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    constructor
    · rintro ⟨y, hy, hne⟩ h
      exact hne (h y hy)
    · intro h
      by_contra hne
      exact h fun y hy => by by_contra hPy; exact hne ⟨y, hy, hPy⟩
  unfold g2Count
  rw [hcompl, hcertain, Finset.card_compl]

theorem g3Count_le_g2Count (q : X → Q) (P : X → V) : g3Count q P ≤ g2Count q P := by
  classical
  let T := Finset.univ.filter fun x => ¬ ∃ y, q y = q x ∧ P y ≠ P x
  have hTlic : LicensedOn (↑T : Set X) q P := by
    intro x hx y hy hq
    by_contra hne
    have hcol : ∃ z, q z = q x ∧ P z ≠ P x := ⟨y, hq.symm, fun e => hne e.symm⟩
    exact (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2 hcol
  have hle : T.card ≤ maxLicensedCard q P :=
    Finset.le_sup (Finset.mem_filter.2 ⟨Finset.mem_univ _, hTlic⟩)
  have hTcard : T.card = Fintype.card X - g2Count q P := by
    have hcompl : T = (Finset.univ.filter fun x => ∃ y, q y = q x ∧ P y ≠ P x)ᶜ := by
      ext x
      simp [T]
    rw [hcompl, Finset.card_compl]
    rfl
  have hg2le : g2Count q P ≤ Fintype.card X := by
    unfold g2Count
    exact Finset.card_le_univ _
  unfold g3Count
  omega

omit [DecidableEq X] in
theorem g1Count_le_card_mul_g2Count (q : X → Q) (P : X → V) :
    g1Count q P ≤ Fintype.card X * g2Count q P := by
  have hsub : (Finset.univ.filter fun p : X × X => q p.1 = q p.2 ∧ P p.1 ≠ P p.2) ⊆
      (Finset.univ.filter fun x => ∃ y, q y = q x ∧ P y ≠ P x) ×ˢ (Finset.univ : Finset X) := by
    intro p hp
    rw [Finset.mem_product]
    refine ⟨?_, Finset.mem_univ _⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      ⟨p.2, (Finset.mem_filter.1 hp).2.1.symm, fun e => (Finset.mem_filter.1 hp).2.2 e.symm⟩⟩
  calc g1Count q P ≤ ((Finset.univ.filter fun x => ∃ y, q y = q x ∧ P y ≠ P x) ×ˢ
        (Finset.univ : Finset X)).card := Finset.card_le_card hsub
    _ = g2Count q P * Fintype.card X := by rw [Finset.card_product]; simp [g2Count]
    _ = Fintype.card X * g2Count q P := Nat.mul_comm _ _

omit [DecidableEq X] in
theorem g1_le_g2 [Nonempty X] (q : X → Q) (P : X → V) : g1 q P ≤ g2 q P := by
  have hn : (0 : ℚ) < Fintype.card X := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty X›
  have hcast : (g1Count q P : ℚ) ≤ (Fintype.card X : ℚ) * (g2Count q P : ℚ) := by
    exact_mod_cast g1Count_le_card_mul_g2Count q P
  unfold g1 g2
  exact (div_le_div_iff₀ (show (0 : ℚ) < (Fintype.card X : ℚ) ^ 2 by positivity) hn).mpr
    (by nlinarith [hcast, hn])

theorem g3_le_g2 (q : X → Q) (P : X → V) : g3 q P ≤ g2 q P := by
  unfold g3 g2
  apply div_le_div_of_nonneg_right
  · exact_mod_cast g3Count_le_g2Count q P
  · positivity

omit [DecidableEq X] in
/-- **`g₁` counts collisions.** -/
theorem g1Count_eq_sum_fiber [Fintype Q] [Fintype V] (q : X → Q) (P : X → V) :
    (g1Count q P : ℤ) = ∑ o, ((fiberCount q o : ℤ) ^ 2 - ∑ v, (cellCount q P o v : ℤ) ^ 2) := by
  classical
  have hsameQ : (Finset.univ.filter fun p : X × X => q p.1 = q p.2).card =
      ∑ o, fiberCount q o ^ 2 := by
    have hfiber := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun p : X × X => q p.1 = q p.2)
      (t := (Finset.univ : Finset Q)) (f := fun p : X × X => q p.1)
      (fun p _ => Finset.mem_univ _)
    rw [hfiber]
    apply Finset.sum_congr rfl
    intro o _
    have hpart : (Finset.univ.filter fun p : X × X => q p.1 = q p.2).filter
          (fun p => q p.1 = o) =
        (Finset.univ.filter fun x => q x = o) ×ˢ (Finset.univ.filter fun x => q x = o) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact ⟨h.2, h.1.symm.trans h.2⟩
      · intro h
        exact ⟨h.1.trans h.2.symm, h.1⟩
    rw [hpart, Finset.card_product, fiberCount, pow_two]
  have hsameQP : (Finset.univ.filter fun p : X × X => q p.1 = q p.2 ∧ P p.1 = P p.2).card =
      ∑ o, ∑ v, cellCount q P o v ^ 2 := by
    have hfiber := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun p : X × X => q p.1 = q p.2 ∧ P p.1 = P p.2)
      (t := (Finset.univ : Finset (Q × V))) (f := fun p : X × X => (q p.1, P p.1))
      (fun p _ => Finset.mem_univ _)
    rw [hfiber]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro o _
    apply Finset.sum_congr rfl
    intro v _
    have hpart : (Finset.univ.filter fun p : X × X => q p.1 = q p.2 ∧ P p.1 = P p.2).filter
          (fun p => (q p.1, P p.1) = (o, v)) =
        (Finset.univ.filter fun x => q x = o ∧ P x = v) ×ˢ
          (Finset.univ.filter fun x => q x = o ∧ P x = v) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
        Prod.mk.injEq]
      constructor
      · intro h
        exact ⟨⟨h.2.1, h.2.2⟩, ⟨h.1.1.symm.trans h.2.1, h.1.2.symm.trans h.2.2⟩⟩
      · intro h
        exact ⟨⟨h.1.1.trans h.2.1.symm, h.1.2.trans h.2.2.symm⟩, h.1.1, h.1.2⟩
    rw [hpart, Finset.card_product, cellCount, pow_two]
  have hsplit2 : (Finset.univ.filter fun p : X × X => q p.1 = q p.2 ∧ P p.1 ≠ P p.2).card +
      (Finset.univ.filter fun p : X × X => q p.1 = q p.2 ∧ P p.1 = P p.2).card =
      (Finset.univ.filter fun p : X × X => q p.1 = q p.2).card := by
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s := Finset.univ.filter fun p : X × X => q p.1 = q p.2)
      (p := fun p => P p.1 = P p.2)
    have hpos : (Finset.univ.filter fun p : X × X => q p.1 = q p.2).filter
          (fun p => P p.1 = P p.2) =
        Finset.univ.filter (fun p : X × X => q p.1 = q p.2 ∧ P p.1 = P p.2) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hneg : (Finset.univ.filter fun p : X × X => q p.1 = q p.2).filter
          (fun p => ¬ P p.1 = P p.2) =
        Finset.univ.filter (fun p : X × X => q p.1 = q p.2 ∧ P p.1 ≠ P p.2) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
    rw [hpos, hneg] at hsplit
    omega
  have hcast : (g1Count q P : ℤ) =
      (∑ o, (fiberCount q o : ℤ) ^ 2) - (∑ o, ∑ v, (cellCount q P o v : ℤ) ^ 2) := by
    unfold g1Count
    rw [show (Finset.univ.filter fun p : X × X => q p.1 = q p.2 ∧ P p.1 ≠ P p.2).card =
        (Finset.univ.filter fun p : X × X => q p.1 = q p.2).card -
          (Finset.univ.filter fun p : X × X => q p.1 = q p.2 ∧ P p.1 = P p.2).card
        from by omega]
    rw [Nat.cast_sub (show (Finset.univ.filter fun p : X × X =>
          q p.1 = q p.2 ∧ P p.1 = P p.2).card ≤
        (Finset.univ.filter fun p : X × X => q p.1 = q p.2).card from by omega)]
    rw [hsameQ, hsameQP]
    push_cast
    ring
  rw [hcast, Finset.sum_sub_distrib]

omit [DecidableEq X] in
theorem licensed_iff_g1Count_eq_zero (q : X → Q) (P : X → V) : Licensed q P ↔ g1Count q P = 0 := by
  constructor
  · intro h
    unfold g1Count
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _
    rintro ⟨hpq, hne⟩
    exact hne (h p.1 p.2 hpq)
  · intro h x y hxy
    by_contra hne
    have hmem : (x, y) ∈ Finset.univ.filter
        (fun p : X × X => q p.1 = q p.2 ∧ P p.1 ≠ P p.2) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hxy, hne⟩
    have hzero : (Finset.univ.filter
        (fun p : X × X => q p.1 = q p.2 ∧ P p.1 ≠ P p.2)).card = 0 := h
    have hempty : (Finset.univ.filter
        (fun p : X × X => q p.1 = q p.2 ∧ P p.1 ≠ P p.2)) = ∅ :=
      Finset.card_eq_zero.mp hzero
    rw [hempty] at hmem
    simp at hmem

omit [DecidableEq X] in
theorem licensed_iff_g2Count_eq_zero (q : X → Q) (P : X → V) : Licensed q P ↔ g2Count q P = 0 := by
  constructor
  · intro h
    unfold g2Count
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x _ hx
    exact hx.elim fun y hy => hy.2 (h x y hy.1.symm).symm
  · intro h x y hxy
    by_contra hne
    have hmem : x ∈ Finset.univ.filter (fun x => ∃ y, q y = q x ∧ P y ≠ P x) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨y, hxy.symm, fun e => hne e.symm⟩⟩
    have hzero : (Finset.univ.filter (fun x => ∃ y, q y = q x ∧ P y ≠ P x)).card = 0 := h
    have hempty : (Finset.univ.filter (fun x => ∃ y, q y = q x ∧ P y ≠ P x)) = ∅ :=
      Finset.card_eq_zero.mp hzero
    rw [hempty] at hmem
    simp at hmem

omit [DecidableEq X] [DecidableEq Q] [DecidableEq V] in
theorem licensed_iff_g3Count_eq_zero (q : X → Q) (P : X → V) : Licensed q P ↔ g3Count q P = 0 := by
  classical
  constructor
  · intro h
    have huniv : (Finset.univ : Finset X) ∈ Finset.univ.filter
        (fun S : Finset X => LicensedOn (↑S : Set X) q P) := by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [Finset.coe_univ]
      exact (licensedOn_univ_iff q P).2 h
    have hle : Fintype.card X ≤ maxLicensedCard q P := by
      calc Fintype.card X = (Finset.univ : Finset X).card := Finset.card_univ.symm
        _ ≤ maxLicensedCard q P := Finset.le_sup huniv
    unfold g3Count
    omega
  · intro h
    have hcard : maxLicensedCard q P = Fintype.card X := by
      have := maxLicensedCard_le_card q P
      unfold g3Count at h
      omega
    obtain ⟨S, hSlic, hScard⟩ := exists_licensedOn_card_eq_max q P
    have hSu : S = Finset.univ := Finset.eq_univ_of_card S (by rw [hScard, hcard])
    rw [hSu, Finset.coe_univ] at hSlic
    exact (licensedOn_univ_iff q P).1 hSlic

end Finite

/-! ## Fixtures -/

/-- Five tuples in two fibers: two target values on the first fiber, three on the second. -/
def repairFixtureObserver : Fin 5 → Fin 2 := ![0, 0, 1, 1, 1]

def repairFixtureTarget : Fin 5 → Fin 3 := ![0, 1, 0, 1, 2]

theorem repairFixture_card :
    (subsetRepairs repairFixtureObserver repairFixtureTarget).card = 6 := by
  rw [card_subsetRepairs]
  decide

theorem repairFixture_measures :
    g1Count repairFixtureObserver repairFixtureTarget = 8 ∧
      g2Count repairFixtureObserver repairFixtureTarget = 5 ∧
      g3Count repairFixtureObserver repairFixtureTarget = 3 := by
  refine ⟨by decide, by decide, ?_⟩
  unfold g3Count
  rw [maxLicensedCard_eq_sum]
  decide

/-- A third fiber with one tuple: the certain answers are exactly that tuple. -/
def answerFixtureObserver : Fin 3 → Fin 2 := ![0, 0, 1]

def answerFixtureTarget : Fin 3 → Fin 2 := ![0, 1, 0]

theorem answerFixture_certain (x : Fin 3) :
    (∀ S : Set (Fin 3), MaximalLicensedOn S answerFixtureObserver answerFixtureTarget → x ∈ S) ↔
      x = 2 := by
  rw [mem_every_repair_iff_fiber_constant]
  fin_cases x <;> decide

end OperatorKO7.Meta.OperationalInexpressibility.DependencyRepair
