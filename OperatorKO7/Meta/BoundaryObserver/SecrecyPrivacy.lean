import OperatorKO7.Meta.BoundaryObserver.BoundaryPrivacy
import OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy

set_option autoImplicit false

/-!
# Private readings and perfect secrecy

The three clauses of the secrecy-privacy theorem cover the zero-privacy pole,
adaptive information, the quadratic privacy cost, identical ciphertext rows,
and the Boolean pad with biased keys.
-/

namespace OperatorKO7.Meta.BoundaryObserver.SecrecyPrivacy

open scoped BigOperators
open ProtocolResolution BoundarySingularity BoundaryPrivacy BoundarySecrecy

noncomputable section

/-- The zero-ratio privacy condition forces two finite reading rows to have zero discrimination. -/
theorem privacy_zero_discrimination {Y : Type} [Fintype Y]
    (P Q : FiniteLaw Y) (h : IndistinguishableRows 0 P.mass Q.mass) :
    discrimination P.mass Q.mass = 0 := by
  have heq : P.mass = Q.mass := by
    funext y
    obtain ⟨hle, hge⟩ := h y
    apply le_antisymm
    · simpa using hle
    · simpa using hge
  exact (discrimination_eq_zero_iff P.mass Q.mass P.nonnegative Q.nonnegative).2 heq


/-- Zero-privacy readings give zero information at every stopped horizon and in the limit,
regardless of their nonnegative costs. -/
theorem privacy_zero_no_information {A Y : Type} [Fintype A] [Fintype Y]
    (p : FiniteProtocol Bool A Y)
    (hrows : ∀ h a, IndistinguishableRows 0
      (p.observation h a true).mass (p.observation h a false).mass) :
    (∀ n bank, HistoryBank n bank → terminalMI p n bank = 0) ∧
      informationLimit p = 0 := by
  have heq (h : List (A × Y)) (a : A) :
      (p.observation h a true).mass = (p.observation h a false).mass :=
    (discrimination_eq_zero_iff _ _ (p.observation h a true).nonnegative
      (p.observation h a false).nonnegative).mp
      (privacy_zero_discrimination _ _ (hrows h a))
  have hcap : LocalCapacityBound p 0 := by
    intro h a hw _ _
    have hs (b : Bool) :
        (p.observation h a b).mass = (p.observation h a true).mass := by
      cases b with
      | false => exact (heq h a).symm
      | true => rfl
    have hsource : (fun zy : Bool × Y =>
          posterior p h zy.1 * (p.observation h a zy.1).mass zy.2) =
        (fun zy : Bool × Y =>
          posterior p h zy.1 * (p.observation h a true).mass zy.2) := by
      funext zy
      rw [hs zy.1]
    have hz : localGain p h a = 0 := by
      unfold localGain
      rw [hsource]
      exact jointMI_product_zero (posterior p h) (p.observation h a true).mass
        (posterior_total p h hw) (p.observation h a true).total
    simpa only [hz, zero_mul] using (le_refl (0 : ℝ))
  refine ⟨?_, informationLimit_zero_capacity p hcap⟩
  intro n bank hb
  have hupper := terminalMI_le_expectedCost p 0 n bank hb hcap
  have hlower := terminalMI_nonnegative p n bank hb
  exact le_antisymm (by simpa only [zero_mul] using hupper) hlower


/-- A positive privacy parameter forces expected cost at least two times acquired
information in bits times log two divided by the squared parameter. -/
theorem privacy_cost_quadratic {A Y : Type} [Fintype A] [Fintype Y]
    (p : FiniteProtocol Bool A Y) (ε c : ℝ) (hε : 0 < ε)
    (hrows : ∀ h a, IndistinguishableRows ε
      (p.observation h a true).mass (p.observation h a false).mass)
    (hcost : ∀ h a, 1 ≤ p.cost h a) (n : ℕ)
    (bank : List (List (A × Y))) (hb : HistoryBank n bank)
    (hc : c ≤ terminalMI p n bank) :
    2 * c * Real.log 2 / ε ^ 2 ≤ expectedCost p n bank := by
  have hdisc (h : List (A × Y)) (a : A) :
      discrimination (p.observation h a true).mass
        (p.observation h a false).mass ≤ ε ^ 2 / 2 := by
    have hbound := privacyDiscriminationGoal Y
      (p.observation h a true) (p.observation h a false) ε hε.le (hrows h a)
    exact hbound.1.trans hbound.2
  have menu : PairMenu p (ε ^ 2 / 2) :=
    ⟨hdisc, hcost⟩
  have hδ : 0 < ε ^ 2 / 2 := by positivity
  have hbound := pairMenu_cost_lower_bound p (ε ^ 2 / 2) c menu hδ n bank hb hc
  calc
    2 * c * Real.log 2 / ε ^ 2 =
        c * Real.log 2 / (ε ^ 2 / 2) := by
      have hn : ε ^ 2 ≠ 0 := (pow_pos hε 2).ne'
      field_simp [hn]
      ring
    _ ≤ expectedCost p n bank := hbound


/-- All ciphertext-row discriminations vanish exactly when all message-conditional
ciphertext probabilities agree pointwise. -/
theorem secrecy_zero_iff_equal_rows {M C : Type} [Fintype M] [Fintype C]
    (E : M → FiniteLaw C) :
    (∀ m m', discrimination (E m).mass (E m').mass = 0) ↔
      ∀ m m' c, (E m).mass c = (E m').mass c := by
  constructor
  · intro hz m m' c
    have heq : (E m).mass = (E m').mass :=
      (discrimination_eq_zero_iff _ _ (E m).nonnegative
        (E m').nonnegative).mp (hz m m')
    exact congrFun heq c
  · intro heq m m'
    apply (discrimination_eq_zero_iff _ _ (E m).nonnegative
      (E m').nonnegative).mpr
    funext c
    exact heq m m' c


/-- Identical finite ciphertext rows are equivalent to zero mutual information for every
message prior, including priors with zero-mass messages. -/
theorem secrecy_equal_rows_iff_zero_information {M C : Type}
    [Fintype M] [Fintype C] (E : M → FiniteLaw C) :
    (∀ m m' c, (E m).mass c = (E m').mass c) ↔
      ∀ prior : FiniteLaw M,
        jointMI (fun mc : M × C => prior.mass mc.1 * (E mc.1).mass mc.2) = 0 := by
  classical
  constructor
  · intro heq prior
    by_cases hM : Nonempty M
    · obtain ⟨m₀⟩ := hM
      have hsource :
          (fun mc : M × C => prior.mass mc.1 * (E mc.1).mass mc.2) =
          (fun mc : M × C => prior.mass mc.1 * (E m₀).mass mc.2) := by
        funext ⟨m, c⟩
        rw [heq m m₀ c]
      rw [hsource]
      exact jointMI_product_zero prior.mass (E m₀).mass prior.total (E m₀).total
    · haveI : IsEmpty M := ⟨fun m => hM ⟨m⟩⟩
      have hbad := prior.total
      simp at hbad
  · intro hinfo m m' c
    haveI : Nonempty M := ⟨m⟩
    have hcard : (0 : ℝ) < (Fintype.card M : ℝ) := by
      exact_mod_cast Fintype.card_pos
    let q : FiniteLaw M := {
      mass := fun _ => 1 / (Fintype.card M : ℝ)
      nonnegative := by
        intro _
        exact (one_div_pos.mpr hcard).le
      total := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp [(ne_of_gt hcard)]
    }
    have hqpos (z : M) : 0 < q.mass z := by
      change 0 < (1 : ℝ) / (Fintype.card M : ℝ)
      exact one_div_pos.mpr hcard
    have hgap (y : C) :
        (∑ z, q.mass z * entropyTerm ((E z).mass y)) ≤
          entropyTerm (∑ z, q.mass z * (E z).mass y) := by
      have hj : (∑ z, q.mass z * Real.negMulLog ((E z).mass y)) ≤
          Real.negMulLog (∑ z, q.mass z * (E z).mass y) := by
        simpa only [smul_eq_mul] using
          (Real.concaveOn_negMulLog.le_map_sum
            (t := Finset.univ) (w := q.mass) (p := fun z => (E z).mass y)
            (fun z _ => q.nonnegative z) q.total
            (fun z _ => Set.mem_Ici.mpr ((E z).nonnegative y)))
      simpa only [entropyTerm, Finset.sum_div, mul_div_assoc] using
        (div_le_div_iff_of_pos_right (Real.log_pos one_lt_two)).mpr hj
    have hsum :
        (∑ y, (entropyTerm (∑ z, q.mass z * (E z).mass y) -
          ∑ z, q.mass z * entropyTerm ((E z).mass y))) =
        jointMI (fun mc : M × C => q.mass mc.1 * (E mc.1).mass mc.2) := by
      rw [jointMI_kernel q.mass (fun z => (E z).mass) (fun z => (E z).total)]
      simp only [Finset.sum_sub_distrib, entropy_eq_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
    have hzero :
        ∀ y ∈ (Finset.univ : Finset C),
          entropyTerm (∑ z, q.mass z * (E z).mass y) -
            ∑ z, q.mass z * entropyTerm ((E z).mass y) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun y _ => sub_nonneg.mpr (hgap y))).mp (hsum.trans (hinfo q))
    have hcell := sub_eq_zero.mp (hzero c (Finset.mem_univ c))
    have hdiv :
        Real.negMulLog (∑ z, q.mass z * (E z).mass c) / Real.log 2 =
          (∑ z, q.mass z * Real.negMulLog ((E z).mass c)) / Real.log 2 := by
      simpa only [entropyTerm, Finset.sum_div, mul_div_assoc] using hcell
    have hmul := congrArg (fun x : ℝ => x * Real.log 2) hdiv
    have hnum :
        Real.negMulLog (∑ z, q.mass z * (E z).mass c) =
          ∑ z, q.mass z * Real.negMulLog ((E z).mass c) := by
      field_simp [(Real.log_pos one_lt_two).ne'] at hmul
      exact hmul
    have hval :
        (∑ z, q.mass z • Real.negMulLog ((E z).mass c)) =
          Real.negMulLog (∑ z, q.mass z • (E z).mass c) := by
      simpa only [smul_eq_mul] using hnum.symm
    have hall := Real.strictConcaveOn_negMulLog.eq_of_map_sum_eq
      (t := (Finset.univ : Finset M)) (w := q.mass)
      (p := fun z => (E z).mass c)
      (fun z _ => hqpos z) q.total
      (fun z _ => Set.mem_Ici.mpr ((E z).nonnegative c))
      (le_of_eq hval.symm)
    exact hall (Finset.mem_univ m) (Finset.mem_univ m')


/-- A protocol that selects ciphertext rows of a perfectly secret reading, even with
history-dependent message choices, gains zero information at every horizon and in the limit. -/
theorem secrecy_protocol_zero {M A C : Type}
    [Fintype M] [Fintype A] [Fintype C]
    (E : M → FiniteLaw C)
    (hequal : ∀ m m' c, (E m).mass c = (E m').mass c)
    (p : FiniteProtocol Bool A C)
    (hreading : ∀ h a, ∃ m₀ m₁ : M,
      (p.observation h a true).mass = (E m₀).mass ∧
      (p.observation h a false).mass = (E m₁).mass) :
    (∀ n bank, HistoryBank n bank → terminalMI p n bank = 0) ∧
      informationLimit p = 0 := by
  apply privacy_zero_no_information p
  intro h a c
  obtain ⟨m₀, m₁, htrue, hfalse⟩ := hreading h a
  have heq :
      (p.observation h a true).mass c =
        (p.observation h a false).mass c := by
    calc
      (p.observation h a true).mass c = (E m₀).mass c := congrFun htrue c
      _ = (E m₁).mass c := hequal m₀ m₁ c
      _ = (p.observation h a false).mass c := (congrFun hfalse c).symm
  constructor
  · simpa only [Real.exp_zero, one_mul] using (le_of_eq heq)
  · simpa only [Real.exp_zero, one_mul] using (le_of_eq heq.symm)


/-- The two ciphertext rows of a Boolean one-time pad with key bias δ have
triangular discrimination exactly eight times δ squared. -/
theorem biased_pad_discrimination (key : FiniteLaw Bool) (δ : ℝ)
    (hfalse : key.mass false = 1 / 2 + δ)
    (htrue : key.mass true = 1 / 2 - δ) :
    discrimination (cipherLaw key (fun k m => xor k m) false)
      (cipherLaw key (fun k m => xor k m) true) = 8 * δ ^ 2 := by
  classical
  have hcfalse :
      cipherLaw key (fun k m => xor k m) false = binaryKernel δ false := by
    funext c
    cases c <;> simp [cipherLaw, binaryKernel, hfalse, htrue]
  have hctrue :
      cipherLaw key (fun k m => xor k m) true = binaryKernel δ true := by
    funext c
    cases c <;> simp [cipherLaw, binaryKernel, hfalse, htrue]
  have hswapfalse : binaryKernel δ false = binaryKernel (-δ) true := by
    funext c
    cases c <;> simp [binaryKernel, sub_eq_add_neg]
  have hswaptrue : binaryKernel δ true = binaryKernel (-δ) false := by
    funext c
    cases c <;> simp [binaryKernel, sub_eq_add_neg]
  rw [hcfalse, hctrue, hswapfalse, hswaptrue, discrimination_binaryKernel]
  ring

/-- The biased one-time pad has identical ciphertext rows exactly when its key is fair. -/
theorem biased_pad_secret_iff (key : FiniteLaw Bool) (δ : ℝ)
    (hfalse : key.mass false = 1 / 2 + δ)
    (htrue : key.mass true = 1 / 2 - δ) :
    discrimination (cipherLaw key (fun k m => xor k m) false)
      (cipherLaw key (fun k m => xor k m) true) = 0 ↔ δ = 0 := by
  rw [biased_pad_discrimination key δ hfalse htrue]
  constructor
  · intro h
    have hsq : δ * δ = 0 := by nlinarith
    exact (mul_self_eq_zero.mp hsq)
  · intro h
    rw [h]
    ring

/-! ## Conditional histories and the shared-key control, audit A6 -/

/-- Identical binary rows have zero local capacity independently of action cost. -/
theorem zero_privateRows_capacity {A Y : Type} [Fintype A] [Fintype Y]
    (p : FiniteProtocol Bool A Y)
    (hrows : ∀ h a, IndistinguishableRows 0
      (p.observation h a true).mass (p.observation h a false).mass) :
    LocalCapacityBound p 0 := by
  intro h a hw _ _
  have heq : (p.observation h a true).mass = (p.observation h a false).mass :=
    (discrimination_eq_zero_iff _ _ (p.observation h a true).nonnegative
      (p.observation h a false).nonnegative).mp
      (privacy_zero_discrimination _ _ (hrows h a))
  have hs (b : Bool) :
      (p.observation h a b).mass = (p.observation h a true).mass := by
    cases b with
    | false => exact heq.symm
    | true => rfl
  have hsource :
      (fun zy : Bool × Y => posterior p h zy.1 *
        (p.observation h a zy.1).mass zy.2) =
      (fun zy : Bool × Y => posterior p h zy.1 *
        (p.observation h a true).mass zy.2) := by
    funext zy
    rw [hs zy.1]
  have hz : localGain p h a = 0 := by
    unfold localGain
    rw [hsource]
    exact jointMI_product_zero (posterior p h) (p.observation h a true).mass
      (posterior_total p h hw) (p.observation h a true).total
  simp only [hz, zero_mul, le_refl]

/-- Zero conditional privacy gives zero acquired information at every stopped
horizon and in the limit. Initial information stays in the retained record;
no positive lower bound on reading costs is required. -/
theorem conditionalPrivacy_zero_information {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (p : ConditionalProtocol H0 Bool A Y)
    (hrows : ∀ u, 0 < p.initialRecord.mass u → ∀ h a,
      IndistinguishableRows 0 ((p.given u).observation h a true).mass
        ((p.given u).observation h a false).mass) :
    (∀ n bank, HistoryBank n bank → conditionalJointInfo p n bank = 0) ∧
      conditionalInformationLimit p = 0 := by
  have hc : ∀ u, 0 < p.initialRecord.mass u → LocalCapacityBound (p.given u) 0 :=
    fun u hu => zero_privateRows_capacity (p.given u) (hrows u hu)
  exact ⟨fun n bank hb => conditionalJointInfo_zero_capacity p n bank hb hc,
    conditionalInformationLimit_zero_capacity p hc⟩

/-- The actual private rows after each positive-mass initial record form a
conditional pair menu at the sharp hyperbolic-tangent discrimination bound. -/
theorem conditionalPrivacy_pairMenu {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (p : ConditionalProtocol H0 Bool A Y) (ε : ℝ) (hε : 0 ≤ ε)
    (hrows : ∀ u, 0 < p.initialRecord.mass u → ∀ h a,
      IndistinguishableRows ε ((p.given u).observation h a true).mass
        ((p.given u).observation h a false).mass)
    (hcost : ∀ u, 0 < p.initialRecord.mass u → ∀ h a, 1 ≤ (p.given u).cost h a) :
    ConditionalPairMenu p (2 * Real.tanh (ε / 2) ^ 2) := by
  refine ⟨fun u hu => ⟨?_, hcost u hu⟩⟩
  intro h a
  exact (privacyDiscriminationGoal Y ((p.given u).observation h a true)
    ((p.given u).observation h a false) ε hε (hrows u hu h a)).1

/-- The same conditional experiment also satisfies the quadratic row bound. -/
theorem conditionalPrivacy_quadratic_pairMenu {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (p : ConditionalProtocol H0 Bool A Y) (ε : ℝ) (hε : 0 ≤ ε)
    (hrows : ∀ u, 0 < p.initialRecord.mass u → ∀ h a,
      IndistinguishableRows ε ((p.given u).observation h a true).mass
        ((p.given u).observation h a false).mass)
    (hcost : ∀ u, 0 < p.initialRecord.mass u → ∀ h a, 1 ≤ (p.given u).cost h a) :
    ConditionalPairMenu p (ε ^ 2 / 2) := by
  refine ⟨fun u hu => ⟨?_, hcost u hu⟩⟩
  intro h a
  have hbound := privacyDiscriminationGoal Y ((p.given u).observation h a true)
    ((p.given u).observation h a false) ε hε (hrows u hu h a)
  exact hbound.1.trans hbound.2

/-- Positive privacy parameter gives both lower cost bounds for acquired
conditional information in the actual stopped experiment. -/
theorem conditionalPrivacy_finite_cost_bounds {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (p : ConditionalProtocol H0 Bool A Y) (ε c : ℝ) (hε : 0 < ε)
    (hrows : ∀ u, 0 < p.initialRecord.mass u → ∀ h a,
      IndistinguishableRows ε ((p.given u).observation h a true).mass
        ((p.given u).observation h a false).mass)
    (hcost : ∀ u, 0 < p.initialRecord.mass u → ∀ h a, 1 ≤ (p.given u).cost h a)
    (n : ℕ) (bank : List (List (A × Y))) (hb : HistoryBank n bank)
    (hc : c ≤ conditionalJointInfo p n bank) :
    c * Real.log 2 / (2 * Real.tanh (ε / 2) ^ 2) ≤ conditionalExpectedCost p n bank ∧
      2 * c * Real.log 2 / ε ^ 2 ≤ conditionalExpectedCost p n bank := by
  have ht : 0 < Real.tanh (ε / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  have hδ : 0 < 2 * Real.tanh (ε / 2) ^ 2 :=
    mul_pos (by norm_num) (pow_pos ht 2)
  refine ⟨conditionalPairMenu_cost_lower_bound p _ c
    (conditionalPrivacy_pairMenu p ε hε.le hrows hcost) hδ n bank hb hc, ?_⟩
  have hδ' : 0 < ε ^ 2 / 2 := by positivity
  have hbound := conditionalPairMenu_cost_lower_bound p _ c
    (conditionalPrivacy_quadratic_pairMenu p ε hε.le hrows hcost) hδ' n bank hb hc
  have heq : 2 * c * Real.log 2 / ε ^ 2 = c * Real.log 2 / (ε ^ 2 / 2) := by ring
  rw [heq]
  exact hbound

/-- The sharp conditional privacy bound holds for actual extended expected
cost, including experiments with infinite cost. -/
theorem conditionalPrivacy_limit_extended_bound {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (p : ConditionalProtocol H0 Bool A Y) (ε : ℝ) (hε : 0 ≤ ε)
    (hrows : ∀ u, 0 < p.initialRecord.mass u → ∀ h a,
      IndistinguishableRows ε ((p.given u).observation h a true).mass
        ((p.given u).observation h a false).mass)
    (hcost : ∀ u, 0 < p.initialRecord.mass u → ∀ h a, 1 ≤ (p.given u).cost h a) :
    ENNReal.ofReal (conditionalInformationLimit p) ≤
      ENNReal.ofReal ((2 * Real.tanh (ε / 2) ^ 2) / Real.log 2) *
        conditionalExtendedCost p := by
  exact conditionalPairMenu_limit_bound p _
    (conditionalPrivacy_pairMenu p ε hε hrows hcost)
    (mul_nonneg (by norm_num) (sq_nonneg _))

/-- A finite bound on the actual extended cost pays both conditional privacy
prices if the limiting acquired information reaches the target. -/
theorem conditionalPrivacy_limit_cost_bounds {H0 A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (p : ConditionalProtocol H0 Bool A Y) (ε c budget : ℝ) (hε : 0 < ε)
    (hrows : ∀ u, 0 < p.initialRecord.mass u → ∀ h a,
      IndistinguishableRows ε ((p.given u).observation h a true).mass
        ((p.given u).observation h a false).mass)
    (hcost : ∀ u, 0 < p.initialRecord.mass u → ∀ h a, 1 ≤ (p.given u).cost h a)
    (hb : 0 ≤ budget) (hc : c ≤ conditionalInformationLimit p)
    (hbudget : conditionalExtendedCost p ≤ ENNReal.ofReal budget) :
    c * Real.log 2 / (2 * Real.tanh (ε / 2) ^ 2) ≤ budget ∧
      2 * c * Real.log 2 / ε ^ 2 ≤ budget := by
  have ht : 0 < Real.tanh (ε / 2) := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr (by linarith)) (Real.cosh_pos _)
  have hδ : 0 < 2 * Real.tanh (ε / 2) ^ 2 :=
    mul_pos (by norm_num) (pow_pos ht 2)
  refine ⟨conditionalPairMenu_limit_cost_lower p _ c budget
    (conditionalPrivacy_pairMenu p ε hε.le hrows hcost) hδ hb hc hbudget, ?_⟩
  have hδ' : 0 < ε ^ 2 / 2 := by positivity
  have hbound := conditionalPairMenu_limit_cost_lower p _ c budget
    (conditionalPrivacy_quadratic_pairMenu p ε hε.le hrows hcost) hδ' hb hc hbudget
  have heq : 2 * c * Real.log 2 / ε ^ 2 = c * Real.log 2 / (ε ^ 2 / 2) := by ring
  rw [heq]
  exact hbound

/-- Equal ciphertext rows at every retained conditional history give zero
new information about a message pair. No claim is made from marginals alone. -/
theorem conditionalSecrecy_zero_information {H0 M A Y : Type}
    [Fintype H0] [Fintype A] [Fintype Y]
    (E : M → FiniteLaw Y) (hequal : ∀ m m' y, (E m).mass y = (E m').mass y)
    (p : ConditionalProtocol H0 Bool A Y)
    (hreading : ∀ u, 0 < p.initialRecord.mass u → ∀ h a, ∃ m₀ m₁ : M,
      ((p.given u).observation h a true).mass = (E m₀).mass ∧
      ((p.given u).observation h a false).mass = (E m₁).mass) :
    (∀ n bank, HistoryBank n bank → conditionalJointInfo p n bank = 0) ∧
      conditionalInformationLimit p = 0 := by
  apply conditionalPrivacy_zero_information p
  intro u hu h a y
  obtain ⟨m₀, m₁, htrue, hfalse⟩ := hreading u hu h a
  have heq : ((p.given u).observation h a true).mass y =
      ((p.given u).observation h a false).mass y :=
    (congrFun htrue y).trans ((hequal m₀ m₁ y).trans (congrFun hfalse y).symm)
  constructor
  · simpa only [Real.exp_zero, one_mul] using le_of_eq heq
  · simpa only [Real.exp_zero, one_mul] using le_of_eq heq.symm

/-- A fair key is emitted once, then reused to mask the label. -/
def reusedPadRow (b : Bool) (out : Bool × Bool) : ℝ :=
  if out.2 = xor out.1 b then 1 / 2 else 0

/-- The joint row is the actual pushforward of one fair key, not a product
of the two marginal ciphertext laws. -/
theorem reusedPadRow_source (b : Bool) (out : Bool × Bool) :
    reusedPadRow b out =
      ∑ k : Bool, if (k, xor k b) = out then (1 : ℝ) / 2 else 0 := by
  rcases out with ⟨l, r⟩
  cases b <;> cases l <;> cases r <;> norm_num [reusedPadRow, Fintype.sum_bool]

theorem reusedPadRow_nonnegative (b : Bool) (out : Bool × Bool) :
    0 ≤ reusedPadRow b out := by
  unfold reusedPadRow
  split <;> norm_num

/-- Each individual output is a fair coin under either label. -/
theorem reusedPadRow_marginals (b y : Bool) :
    (∑ z : Bool, reusedPadRow b (y, z)) = 1 / 2 ∧
      (∑ z : Bool, reusedPadRow b (z, y)) = 1 / 2 := by
  cases b <;> cases y <;> norm_num [reusedPadRow, Fintype.sum_bool]

/-- The joint output row is normalized for each label. -/
theorem reusedPadRow_total (b : Bool) :
    (∑ out : Bool × Bool, reusedPadRow b out) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [(reusedPadRow_marginals b _).1]
  norm_num

/-- The two outputs together recover the label without error. -/
theorem reusedPadRow_decodes (b : Bool) (out : Bool × Bool)
    (h : 0 < reusedPadRow b out) : xor out.1 out.2 = b := by
  rcases out with ⟨l, r⟩
  cases b <;> cases l <;> cases r <;> norm_num [reusedPadRow] at h ⊢

/-- Marginal secrecy does not imply equal joint rows under shared randomness. -/
theorem reusedPadRow_joint_not_secret : reusedPadRow false ≠ reusedPadRow true := by
  intro h
  have hcell := congrFun h (false, false)
  norm_num [reusedPadRow] at hcell

end

end OperatorKO7.Meta.BoundaryObserver.SecrecyPrivacy


