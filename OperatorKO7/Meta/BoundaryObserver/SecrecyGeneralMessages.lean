import OperatorKO7.Meta.BoundaryObserver.BoundarySingularity

set_option autoImplicit false

/-!
# Perfect secrecy on an arbitrary message set

Manuscript: clause (ii) of
`thm:secrecy-privacy` in the paper *Entangled Merged Pairs*.

For an arbitrary message type `M`, with no finiteness, and a finite ciphertext type `C`, a reading
`E : M → FiniteLaw C` has zero discrimination at every pair of messages iff its rows are equal, and its rows
are equal iff the message and the ciphertext carry zero information under every prior of finite support. A prior
of finite support is a finite set of messages with masses that add to one on the set and vanish off it; messages
of mass zero may lie in the set. Its information is the mutual information of the joint law of message and
ciphertext on the finite subtype of the set. Every protocol whose reading at each retained history has two rows of
a perfectly secret reading, the two messages chosen by the history, acquires zero information at every horizon and
in the limit.

A finite message type is the case of the support `univ`: `finite_zero_information_iff` identifies zero information
under every finite law with zero information under every prior of finite support, and
`finite_equal_rows_iff_zero_information` gives the finite equivalence as a special case of
`equal_rows_iff_zero_information`. The module imports `BoundarySingularity` alone; its finite lemmas are proved
here from `ProtocolResolution`, with no use of the module `SecrecyPrivacy`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.SecrecyGeneralMessages

open scoped BigOperators
open ProtocolResolution BoundarySingularity

noncomputable section

/-- A prior of finite support on a message type: nonnegative masses that vanish off a finite set of messages and
add to one on that set. Every message of positive mass lies in the set; messages of mass zero may lie in it. -/
structure FiniteSupportPrior (M : Type) where
  support : Finset M
  mass : M → ℝ
  nonnegative : ∀ m, 0 ≤ mass m
  zero_off : ∀ m, m ∉ support → mass m = 0
  total : ∑ m ∈ support, mass m = 1

/-- The support of a prior of finite support is nonempty, since its masses add to one. -/
theorem FiniteSupportPrior.support_nonempty {M : Type} (π : FiniteSupportPrior M) :
    π.support.Nonempty :=
  Finset.nonempty_of_sum_ne_zero (by rw [π.total]; exact one_ne_zero)

/-- The masses of a prior of finite support add to one over the finite subtype of its support. -/
theorem FiniteSupportPrior.total_subtype {M : Type} (π : FiniteSupportPrior M) :
    ∑ s : π.support, π.mass s = 1 := by
  rw [Finset.sum_coe_sort π.support π.mass]
  exact π.total

/-- The information, in bits, of the message and the ciphertext under a prior of finite support: the mutual
information of their joint law on the finite subtype of the support. -/
def supportInformation {M C : Type} [Fintype C] (E : M → FiniteLaw C) (π : FiniteSupportPrior M) : ℝ :=
  jointMI (fun sc : π.support × C => π.mass sc.1 * (E sc.1).mass sc.2)

/-- Zero discrimination at every pair of messages iff equal ciphertext rows, for an arbitrary message type. -/
theorem zero_discrimination_iff_equal_rows {M C : Type} [Fintype C] (E : M → FiniteLaw C) :
    (∀ m m', discrimination (E m).mass (E m').mass = 0) ↔
      ∀ m m' c, (E m).mass c = (E m').mass c := by
  constructor
  · intro hz m m' c
    have heq : (E m).mass = (E m').mass :=
      (discrimination_eq_zero_iff _ _ (E m).nonnegative (E m').nonnegative).mp (hz m m')
    exact congrFun heq c
  · intro heq m m'
    apply (discrimination_eq_zero_iff _ _ (E m).nonnegative (E m').nonnegative).mpr
    funext c
    exact heq m m' c

/-- Equal rows give zero information under every weighting of a finite type with weights adding to one: the joint
law is the product of the weights and one row. -/
theorem zero_information_of_equal_rows {Z C : Type} [Fintype Z] [Fintype C]
    (q : Z → ℝ) (hq1 : ∑ z, q z = 1) (K : Z → FiniteLaw C)
    (heq : ∀ z z' c, (K z).mass c = (K z').mass c) (z₀ : Z) :
    jointMI (fun zc : Z × C => q zc.1 * (K zc.1).mass zc.2) = 0 := by
  have hsource : (fun zc : Z × C => q zc.1 * (K zc.1).mass zc.2) =
      (fun zc : Z × C => q zc.1 * (K z₀).mass zc.2) := by
    funext zc
    rw [heq zc.1 z₀ zc.2]
  rw [hsource]
  exact jointMI_product_zero q (K z₀).mass hq1 (K z₀).total

/-- Under positive weights adding to one on a finite type, zero information forces equal rows: the information is a
sum of nonnegative concavity gaps of the entropy, and strict concavity makes each gap vanish only at equal rows. -/
theorem equal_rows_of_zero_information_of_pos {Z C : Type} [Fintype Z] [Fintype C]
    (q : Z → ℝ) (hq : ∀ z, 0 < q z) (hq1 : ∑ z, q z = 1) (K : Z → FiniteLaw C)
    (hinfo : jointMI (fun zc : Z × C => q zc.1 * (K zc.1).mass zc.2) = 0) :
    ∀ z z' c, (K z).mass c = (K z').mass c := by
  intro z z' c
  have hgap (y : C) :
      (∑ x, q x * entropyTerm ((K x).mass y)) ≤ entropyTerm (∑ x, q x * (K x).mass y) := by
    have hj : (∑ x, q x * Real.negMulLog ((K x).mass y)) ≤
        Real.negMulLog (∑ x, q x * (K x).mass y) := by
      simpa only [smul_eq_mul] using
        (Real.concaveOn_negMulLog.le_map_sum
          (t := Finset.univ) (w := q) (p := fun x => (K x).mass y)
          (fun x _ => (hq x).le) hq1
          (fun x _ => Set.mem_Ici.mpr ((K x).nonnegative y)))
    simpa only [entropyTerm, Finset.sum_div, mul_div_assoc] using
      (div_le_div_iff_of_pos_right (Real.log_pos one_lt_two)).mpr hj
  have hsum :
      (∑ y, (entropyTerm (∑ x, q x * (K x).mass y) -
        ∑ x, q x * entropyTerm ((K x).mass y))) =
        jointMI (fun zc : Z × C => q zc.1 * (K zc.1).mass zc.2) := by
    rw [jointMI_kernel q (fun x => (K x).mass) (fun x => (K x).total)]
    simp only [Finset.sum_sub_distrib, entropy_eq_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hzero :
      ∀ y ∈ (Finset.univ : Finset C),
        entropyTerm (∑ x, q x * (K x).mass y) - ∑ x, q x * entropyTerm ((K x).mass y) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => sub_nonneg.mpr (hgap y))).mp (hsum.trans hinfo)
  have hcell := sub_eq_zero.mp (hzero c (Finset.mem_univ c))
  have hdiv :
      Real.negMulLog (∑ x, q x * (K x).mass c) / Real.log 2 =
        (∑ x, q x * Real.negMulLog ((K x).mass c)) / Real.log 2 := by
    simpa only [entropyTerm, Finset.sum_div, mul_div_assoc] using hcell
  have hmul := congrArg (fun r : ℝ => r * Real.log 2) hdiv
  have hnum :
      Real.negMulLog (∑ x, q x * (K x).mass c) =
        ∑ x, q x * Real.negMulLog ((K x).mass c) := by
    field_simp [(Real.log_pos one_lt_two).ne'] at hmul
    exact hmul
  have hval :
      (∑ x, q x • Real.negMulLog ((K x).mass c)) =
        Real.negMulLog (∑ x, q x • (K x).mass c) := by
    simpa only [smul_eq_mul] using hnum.symm
  exact Real.strictConcaveOn_negMulLog.eq_of_map_sum_eq
    (t := (Finset.univ : Finset Z)) (w := q) (p := fun x => (K x).mass c)
    (fun x _ => hq x) hq1 (fun x _ => Set.mem_Ici.mpr ((K x).nonnegative c))
    (le_of_eq hval.symm) (Finset.mem_univ z) (Finset.mem_univ z')

open Classical in
/-- The uniform prior on two distinct messages: mass one half at each of the two messages and zero elsewhere. -/
def pairPrior {M : Type} (m m' : M) (h : m ≠ m') : FiniteSupportPrior M where
  support := {m, m'}
  mass x := if x ∈ ({m, m'} : Finset M) then 1 / 2 else 0
  nonnegative x := by split_ifs <;> norm_num
  zero_off x hx := if_neg hx
  total := by
    rw [Finset.sum_pair h]
    norm_num

open Classical in
/-- The mass of the pair prior is one half on its support and zero off it. -/
theorem pairPrior_mass {M : Type} (m m' : M) (h : m ≠ m') (x : M) :
    (pairPrior m m' h).mass x = if x ∈ (pairPrior m m' h).support then 1 / 2 else 0 :=
  rfl

/-- Each message in the support of the pair prior has positive mass. -/
theorem pairPrior_mass_pos {M : Type} (m m' : M) (h : m ≠ m') (x : M)
    (hx : x ∈ (pairPrior m m' h).support) : 0 < (pairPrior m m' h).mass x := by
  rw [pairPrior_mass, if_pos hx]
  norm_num

/-- The first message lies in the support of the pair prior. -/
theorem pairPrior_mem_left {M : Type} (m m' : M) (h : m ≠ m') : m ∈ (pairPrior m m' h).support := by
  simp [pairPrior]

/-- The second message lies in the support of the pair prior. -/
theorem pairPrior_mem_right {M : Type} (m m' : M) (h : m ≠ m') : m' ∈ (pairPrior m m' h).support := by
  simp [pairPrior]

/-- Perfect secrecy on an arbitrary message type, the information form.

Proves: for every message type `M`, with no finiteness, and every reading `E : M → FiniteLaw C` into a finite
ciphertext type, the rows of `E` agree at every pair of messages iff `supportInformation E π = 0` for every prior
`π` of finite support, messages of mass zero in the support included. The forward direction is the product form of
the joint law on the support; the converse reads the uniform prior on the two messages of a pair.
Does not prove: a statement for priors of infinite support.
Relation: the finite joint law of message and ciphertext on the support. Trust: kernel-only. -/
theorem equal_rows_iff_zero_information {M C : Type} [Fintype C] (E : M → FiniteLaw C) :
    (∀ m m' c, (E m).mass c = (E m').mass c) ↔
      ∀ π : FiniteSupportPrior M, supportInformation E π = 0 := by
  constructor
  · intro heq π
    obtain ⟨m₀, hm₀⟩ := π.support_nonempty
    exact zero_information_of_equal_rows (fun s : π.support => π.mass s) π.total_subtype
      (fun s : π.support => E s) (fun s s' c => heq s s' c) ⟨m₀, hm₀⟩
  · intro hinfo m m' c
    by_cases hmm : m = m'
    · rw [hmm]
    · have hrows := equal_rows_of_zero_information_of_pos
        (fun s : (pairPrior m m' hmm).support => (pairPrior m m' hmm).mass s)
        (fun s => pairPrior_mass_pos m m' hmm s s.2) (pairPrior m m' hmm).total_subtype
        (fun s : (pairPrior m m' hmm).support => E s) (hinfo (pairPrior m m' hmm))
      exact hrows ⟨m, pairPrior_mem_left m m' hmm⟩ ⟨m', pairPrior_mem_right m m' hmm⟩ c

/-- Perfect secrecy on an arbitrary message type, the three descriptions: zero discrimination at every pair of
messages, equal ciphertext rows, and zero information under every prior of finite support. -/
theorem perfect_secrecy_general {M C : Type} [Fintype C] (E : M → FiniteLaw C) :
    ((∀ m m', discrimination (E m).mass (E m').mass = 0) ↔
        ∀ m m' c, (E m).mass c = (E m').mass c) ∧
      ((∀ m m' c, (E m).mass c = (E m').mass c) ↔
        ∀ π : FiniteSupportPrior M, supportInformation E π = 0) :=
  ⟨zero_discrimination_iff_equal_rows E, equal_rows_iff_zero_information E⟩

/-- A finite law on a finite message type, read as a prior of finite support with support `univ`. -/
def FiniteSupportPrior.ofFiniteLaw {M : Type} [Fintype M] (prior : FiniteLaw M) :
    FiniteSupportPrior M where
  support := Finset.univ
  mass := prior.mass
  nonnegative := prior.nonnegative
  zero_off m hm := absurd (Finset.mem_univ m) hm
  total := prior.total

/-- On the support `univ`, the information of a finite law is the mutual information of the joint law on the whole
message type. -/
theorem supportInformation_ofFiniteLaw {M C : Type} [Fintype M] [Fintype C]
    (E : M → FiniteLaw C) (prior : FiniteLaw M) :
    supportInformation E (FiniteSupportPrior.ofFiniteLaw prior) =
      jointMI (fun mc : M × C => prior.mass mc.1 * (E mc.1).mass mc.2) :=
  (jointMI_reindex (Equiv.subtypeUnivEquiv Finset.mem_univ) (Equiv.refl C)
    (fun sc : {m // m ∈ (Finset.univ : Finset M)} × C => prior.mass sc.1 * (E sc.1).mass sc.2)
    (fun mc : M × C => prior.mass mc.1 * (E mc.1).mass mc.2) (fun _ _ => rfl)).symm

/-- On a finite message type, zero information under every finite law iff zero information under every prior of
finite support. -/
theorem finite_zero_information_iff {M C : Type} [Fintype M] [Fintype C] (E : M → FiniteLaw C) :
    (∀ prior : FiniteLaw M,
        jointMI (fun mc : M × C => prior.mass mc.1 * (E mc.1).mass mc.2) = 0) ↔
      ∀ π : FiniteSupportPrior M, supportInformation E π = 0 := by
  constructor
  · intro hfin
    apply (equal_rows_iff_zero_information E).mp
    intro m m' c
    haveI : Nonempty M := ⟨m⟩
    have hcard : (0 : ℝ) < (Fintype.card M : ℝ) := by
      exact_mod_cast Fintype.card_pos
    let u : FiniteLaw M := {
      mass := fun _ => 1 / (Fintype.card M : ℝ)
      nonnegative := fun _ => (one_div_pos.mpr hcard).le
      total := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp [(ne_of_gt hcard)] }
    exact equal_rows_of_zero_information_of_pos u.mass (fun _ => one_div_pos.mpr hcard) u.total
      E (hfin u) m m' c
  · intro hsupp prior
    rw [← supportInformation_ofFiniteLaw E prior]
    exact hsupp _

/-- The finite equivalence as the special case of a finite message type: equal rows iff zero information under
every finite law, derived from `equal_rows_iff_zero_information`. -/
theorem finite_equal_rows_iff_zero_information {M C : Type} [Fintype M] [Fintype C]
    (E : M → FiniteLaw C) :
    (∀ m m' c, (E m).mass c = (E m').mass c) ↔
      ∀ prior : FiniteLaw M,
        jointMI (fun mc : M × C => prior.mass mc.1 * (E mc.1).mass mc.2) = 0 :=
  (equal_rows_iff_zero_information E).trans (finite_zero_information_iff E).symm

/-- A protocol whose two rows agree at every retained history and every action acquires zero information at every
horizon and in the limit, whatever the costs of its readings: each local gain is the information of a product law. -/
theorem equal_rows_no_information {A Y : Type} [Fintype A] [Fintype Y]
    (p : FiniteProtocol Bool A Y)
    (heq : ∀ h a, (p.observation h a true).mass = (p.observation h a false).mass) :
    (∀ n bank, HistoryBank n bank → terminalMI p n bank = 0) ∧ informationLimit p = 0 := by
  have hcap : LocalCapacityBound p 0 := by
    intro h a hw _ _
    have hs (b : Bool) : (p.observation h a b).mass = (p.observation h a true).mass := by
      cases b with
      | false => exact (heq h a).symm
      | true => rfl
    have hsource :
        (fun zy : Bool × Y => posterior p h zy.1 * (p.observation h a zy.1).mass zy.2) =
          (fun zy : Bool × Y => posterior p h zy.1 * (p.observation h a true).mass zy.2) := by
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

/-- The protocol clause on an arbitrary message type.

Proves: if a reading `E : M → FiniteLaw C` on an arbitrary message type has equal rows, every protocol whose reading
at each retained history and action has two rows of `E` as its two rows, the two messages chosen by the history,
acquires zero information at every horizon and in the limit.
Does not prove: a statement about readings that share randomness across histories; given the history, such
readings need not have rows of `E`.
Relation: the stopped law of the protocol. Trust: kernel-only. -/
theorem secrecy_protocol_zero_general {M A C : Type} [Fintype A] [Fintype C]
    (E : M → FiniteLaw C) (hequal : ∀ m m' c, (E m).mass c = (E m').mass c)
    (p : FiniteProtocol Bool A C)
    (hreading : ∀ h a, ∃ m₀ m₁ : M,
      (p.observation h a true).mass = (E m₀).mass ∧
        (p.observation h a false).mass = (E m₁).mass) :
    (∀ n bank, HistoryBank n bank → terminalMI p n bank = 0) ∧ informationLimit p = 0 := by
  apply equal_rows_no_information p
  intro h a
  obtain ⟨m₀, m₁, htrue, hfalse⟩ := hreading h a
  funext c
  calc (p.observation h a true).mass c = (E m₀).mass c := congrFun htrue c
    _ = (E m₁).mass c := hequal m₀ m₁ c
    _ = (p.observation h a false).mass c := (congrFun hfalse c).symm

/-- The fair coin on the two ciphertexts. -/
def fairCoin : FiniteLaw Bool where
  mass _ := 1 / 2
  nonnegative _ := by norm_num
  total := by
    rw [Fintype.sum_bool]
    norm_num

/-- The parity reading of a natural-number message: its ciphertext is the bit `m % 2 = 0`, with chance one. -/
def parityReading (m : ℕ) : FiniteLaw Bool where
  mass b := if b = decide (m % 2 = 0) then 1 else 0
  nonnegative b := by split_ifs <;> norm_num
  total := by
    rw [Fintype.sum_bool]
    cases decide (m % 2 = 0) <;> simp

/-- On the natural numbers, the reading with the fair coin as every row has zero information under every prior of
finite support. -/
theorem constant_reading_zero_information (π : FiniteSupportPrior ℕ) :
    supportInformation (fun _ : ℕ => fairCoin) π = 0 :=
  (equal_rows_iff_zero_information (fun _ : ℕ => fairCoin)).mp (fun _ _ _ => rfl) π

/-- The parity reading has different rows at the messages `0` and `1`. -/
theorem parity_reading_rows_differ : (parityReading 0).mass true ≠ (parityReading 1).mass true := by
  simp [parityReading]

/-- The parity reading has a prior of finite support with nonzero information, so the equivalence of
`equal_rows_iff_zero_information` has instances on both sides on an infinite message type. -/
theorem parity_reading_informative :
    ∃ π : FiniteSupportPrior ℕ, supportInformation parityReading π ≠ 0 := by
  by_contra hno
  push_neg at hno
  exact parity_reading_rows_differ
    ((equal_rows_iff_zero_information parityReading).mpr hno 0 1 true)

end

end OperatorKO7.Meta.BoundaryObserver.SecrecyGeneralMessages
