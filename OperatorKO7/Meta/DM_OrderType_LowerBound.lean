import OperatorKO7.Meta.DM_OrderType
import Mathlib.Data.Multiset.Sort
import Mathlib.SetTheory.Ordinal.CantorNormalForm

namespace OperatorKO7.MetaDM

open Ordinal
open OperatorKO7.MetaCM

/-- Canonical finite CNF payload for ordinals below `ω^ω`: descending exponent list. -/
structure CNFωω where
  exponents : List Nat
  sorted : exponents.Sorted (· ≥ ·)

namespace CNFωω

/-- Forget coefficients into a multiset of exponents. -/
def toMultiset (c : CNFωω) : Multiset Nat :=
  (c.exponents : Multiset Nat)

/-- Canonical representative extracted from a multiset by descending sort. -/
def ofMultiset (m : Multiset Nat) : CNFωω :=
  ⟨Multiset.sort (· ≥ ·) m, Multiset.sort_sorted (r := (· ≥ ·)) m⟩

/-- Ordinal value of a CNF payload, via the mechanized DM embedding. -/
noncomputable def eval (c : CNFωω) : Ordinal :=
  dmOrdEmbed c.toMultiset

theorem eval_toMultiset (c : CNFωω) :
    dmOrdEmbed c.toMultiset = c.eval := rfl

@[simp] theorem toMultiset_ofMultiset (m : Multiset Nat) :
    (ofMultiset m).toMultiset = m := by
  simp [ofMultiset, toMultiset, Multiset.sort_eq]

@[simp] theorem eval_ofMultiset (m : Multiset Nat) :
    (ofMultiset m).eval = dmOrdEmbed m := by
  change dmOrdEmbed (ofMultiset m).toMultiset = dmOrdEmbed m
  exact congrArg dmOrdEmbed (toMultiset_ofMultiset m)

/-- Every multiset admits a canonical CNF representative with the same embedding value. -/
theorem exists_of_multiset (m : Multiset Nat) :
    ∃ c : CNFωω, c.eval = dmOrdEmbed m :=
  ⟨ofMultiset m, by simp⟩

/-- Phase-B upper bound restated on the CNF carrier. -/
theorem eval_lt_opow_omega (c : CNFωω) :
    c.eval < (ω : Ordinal) ^ (ω : Ordinal) := by
  simpa [eval] using
    (dmOrdEmbed_lt_opow_omega c.toMultiset :
      dmOrdEmbed c.toMultiset < (Ordinal.omega0 : Ordinal) ^ (Ordinal.omega0 : Ordinal))

/-- Sorting the multiset image of a canonical payload returns the original exponent list. -/
theorem sort_toMultiset (c : CNFωω) :
    Multiset.sort (· ≥ ·) c.toMultiset = c.exponents := by
  refine List.eq_of_perm_of_sorted (r := (· ≥ ·)) ?_ ?_ c.sorted
  · exact (Multiset.coe_eq_coe).1 (by
      simpa [toMultiset] using (Multiset.sort_eq (r := (· ≥ ·)) c.toMultiset))
  · exact Multiset.sort_sorted (r := (· ≥ ·)) c.toMultiset

@[simp] theorem ofMultiset_toMultiset (c : CNFωω) :
    ofMultiset c.toMultiset = c := by
  cases c with
  | mk ex hs =>
      simp [ofMultiset, toMultiset]
      refine List.eq_of_perm_of_sorted (r := (· ≥ ·)) ?_ ?_ hs
      · exact (Multiset.coe_eq_coe).1 (by simpa using (Multiset.sort_eq (r := (· ≥ ·)) (ex : Multiset Nat)))
      · exact Multiset.sort_sorted (r := (· ≥ ·)) (ex : Multiset Nat)

noncomputable def natOfLtOmega (o : Ordinal) (h : o < (ω : Ordinal)) : Nat :=
  Classical.choose (Ordinal.lt_omega0.1 h)

lemma natOfLtOmega_eq (o : Ordinal) (h : o < (ω : Ordinal)) :
    ((natOfLtOmega o h : Nat) : Ordinal) = o := by
  simpa [natOfLtOmega] using
    (Classical.choose_spec (Ordinal.lt_omega0.1 h)).symm

private theorem exists_multiset_eval_bounded :
    ∀ (b : Ordinal) (L : List (Ordinal × Ordinal)),
      (∀ p ∈ L, p.1 < b ∧ p.1 < (ω : Ordinal) ∧ p.2 < (ω : Ordinal)) →
      (L.map Prod.fst).Sorted (· > ·) →
      ∃ m : Multiset Nat,
        dmOrdEmbed m = L.foldr (fun p r ↦ (ω : Ordinal) ^ p.1 * p.2 + r) 0 ∧
          ∀ n ∈ m, (n : Ordinal) < b
  | b, [], _, _ =>
      ⟨0, by simp [dmOrdEmbed], by
        intro n hn
        simp at hn⟩
  | b, p :: ps, hBound, hSorted => by
      have hpBound : p.1 < b ∧ p.1 < (ω : Ordinal) ∧ p.2 < (ω : Ordinal) :=
        hBound p (by simp)
      have hSortedTail : (ps.map Prod.fst).Sorted (· > ·) := (List.sorted_cons.1 hSorted).2
      have hTailBound : ∀ q ∈ ps, q.1 < p.1 ∧ q.1 < (ω : Ordinal) ∧ q.2 < (ω : Ordinal) := by
        intro q hq
        have hqExp : q.1 < p.1 := by
          have hmem : q.1 ∈ ps.map Prod.fst := by
            exact List.mem_map.2 ⟨q, hq, rfl⟩
          exact (List.sorted_cons.1 hSorted).1 _ hmem
        exact ⟨hqExp, (hBound q (by simp [hq])).2.1, (hBound q (by simp [hq])).2.2⟩
      rcases exists_multiset_eval_bounded p.1 ps hTailBound hSortedTail with
        ⟨mTail, hmTailEval, hmTailLt⟩
      let e : Nat := natOfLtOmega p.1 hpBound.2.1
      let c : Nat := natOfLtOmega p.2 hpBound.2.2
      let m : Multiset Nat := Multiset.replicate c e + mTail
      have heEq : ((e : Nat) : Ordinal) = p.1 := by
        simpa [e] using natOfLtOmega_eq p.1 hpBound.2.1
      have hcEq : ((c : Nat) : Ordinal) = p.2 := by
        simpa [c] using natOfLtOmega_eq p.2 hpBound.2.2
      have hTailNatLt : ∀ n ∈ mTail, n < e := by
        intro n hn
        have hnOrd : (n : Ordinal) < p.1 := hmTailLt n hn
        have hnOrd' : (n : Ordinal) < (e : Ordinal) := by
          exact lt_of_lt_of_eq hnOrd heEq.symm
        exact (by exact_mod_cast hnOrd' : n < e)
      have hEval :
          dmOrdEmbed m =
            (ω : Ordinal) ^ p.1 * p.2 +
              ps.foldr (fun q r ↦ (ω : Ordinal) ^ q.1 * q.2 + r) 0 := by
        calc
          dmOrdEmbed m
              = dmOrdEmbed (Multiset.replicate c e + mTail) := rfl
          _ = (ω : Ordinal) ^ (e : Ordinal) * (c : Ordinal) + dmOrdEmbed mTail := by
                exact dmOrdEmbed_replicate_add_of_all_lt hTailNatLt
          _ = (ω : Ordinal) ^ p.1 * p.2 + dmOrdEmbed mTail := by
                simp [heEq, hcEq]
          _ = (ω : Ordinal) ^ p.1 * p.2 +
                ps.foldr (fun q r ↦ (ω : Ordinal) ^ q.1 * q.2 + r) 0 := by
                simp [hmTailEval]
      have hmLt : ∀ n ∈ m, (n : Ordinal) < b := by
        intro n hn
        rcases Multiset.mem_add.1 hn with hrep | htail
        · have hnEq : n = e := Multiset.eq_of_mem_replicate hrep
          subst hnEq
          exact lt_of_eq_of_lt heEq hpBound.1
        · exact (hmTailLt n htail).trans hpBound.1
      exact ⟨m, by simpa [m] using hEval, hmLt⟩

/--
Unconditional surjectivity of `dmOrdEmbed` below `ω^ω`, obtained from Mathlib's canonical
Cantor normal form decomposition.
-/
theorem dmOrdEmbed_surjective_lt_opow_omega :
    ∀ α < (ω : Ordinal) ^ (ω : Ordinal), ∃ m : Multiset Nat, dmOrdEmbed m = α := by
  intro α hα
  let L : List (Ordinal × Ordinal) := Ordinal.CNF (ω : Ordinal) α
  have hSorted : (L.map Prod.fst).Sorted (· > ·) := by
    simpa [L] using (Ordinal.CNF_sorted (ω : Ordinal) α)
  have hBound : ∀ p ∈ L, p.1 < (ω : Ordinal) ∧ p.1 < (ω : Ordinal) ∧ p.2 < (ω : Ordinal) := by
    intro p hp
    have hpL : p ∈ Ordinal.CNF (ω : Ordinal) α := by
      simpa [L] using hp
    have hSnd : p.2 < (ω : Ordinal) := by
      exact Ordinal.CNF_snd_lt (b := (ω : Ordinal)) (o := α)
        Ordinal.one_lt_omega0 hpL
    have hFst : p.1 < (ω : Ordinal) := by
      by_cases h0 : α = 0
      · subst h0
        exfalso
        simp [L, Ordinal.CNF_zero] at hp
      ·
        have hLog : Ordinal.log (ω : Ordinal) α < (ω : Ordinal) := by
          exact (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 h0).1 hα
        exact lt_of_le_of_lt
          (Ordinal.CNF_fst_le_log (b := (ω : Ordinal)) (o := α) (x := p)
            hpL)
          hLog
    exact ⟨hFst, hFst, hSnd⟩
  rcases exists_multiset_eval_bounded (ω : Ordinal) L hBound hSorted with ⟨m, hm, _⟩
  refine ⟨m, ?_⟩
  calc
    dmOrdEmbed m = L.foldr (fun p r ↦ (ω : Ordinal) ^ p.1 * p.2 + r) 0 := hm
    _ = α := by simpa [L] using (Ordinal.CNF_foldr (ω : Ordinal) α)

/-- Phase-B bridge: surjectivity of `dmOrdEmbed` below `ω^ω` (proved unconditionally). -/
def DmEmbedSurjBelowOmegaOmega : Prop :=
  ∀ α < (ω : Ordinal) ^ (ω : Ordinal), ∃ m : Multiset Nat, dmOrdEmbed m = α

theorem dmOrdEmbed_surjective_prop : DmEmbedSurjBelowOmegaOmega :=
  dmOrdEmbed_surjective_lt_opow_omega

/-- Order-reflection schema needed for a fully unconditional lower-bound bridge. -/
def DmEmbedReflects : Prop :=
  ∀ {m₁ m₂ : Multiset Nat}, dmOrdEmbed m₁ < dmOrdEmbed m₂ → DM m₁ m₂

/--
If `dmOrdEmbed` reflects strict order into `DM`, then the opposite rank bridge follows:
`dmOrdEmbed m ≤ dmRankOrd m`.

Together with the unconditional upper bridge `dmRankOrd m ≤ dmOrdEmbed m`, this yields equality.
-/
theorem dmOrdEmbed_le_dmRankOrd_of_reflect (hReflect : DmEmbedReflects) :
    ∀ m : Multiset Nat, dmOrdEmbed m ≤ dmRankOrd m := by
  let P : Ordinal → Prop := fun α =>
    ∀ m : Multiset Nat, dmOrdEmbed m = α → dmOrdEmbed m ≤ dmRankOrd m
  have hStep : ∀ α, (∀ β, β < α → P β) → P α := by
    intro α ih m hm
    refine le_of_forall_lt ?_
    intro β hβ
    have hβω : β < (ω : Ordinal) ^ (ω : Ordinal) := by
      exact lt_trans hβ (dmOrdEmbed_lt_opow_omega m)
    rcases dmOrdEmbed_surjective_lt_opow_omega β hβω with ⟨w, hw⟩
    have hDM : DM w m := hReflect (by simpa [hw] using hβ)
    have hRank : dmRankOrd w < dmRankOrd m := dmRankOrd_strictMono hDM
    have hβle : β ≤ dmRankOrd w := by
      have hβα : β < α := by simpa [hm] using hβ
      have hPw : P β := ih β hβα
      have hwLe : dmOrdEmbed w ≤ dmRankOrd w := hPw w hw
      simpa [hw] using hwLe
    exact lt_of_le_of_lt hβle hRank
  have hAll : ∀ α, P α := by
    intro α
    induction α using Ordinal.induction with
    | h α ih =>
        exact hStep α (fun β hβ => ih β hβ)
  intro m
  exact hAll (dmOrdEmbed m) m rfl

theorem dmOrdEmbed_eq_dmRankOrd_of_reflect
    (hReflect : DmEmbedReflects) (m : Multiset Nat) :
    dmOrdEmbed m = dmRankOrd m := by
  refine le_antisymm (dmOrdEmbed_le_dmRankOrd_of_reflect hReflect m) ?_
  exact dmRankOrd_le_dmOrdEmbed_of_strictMono (fun {_ _} hDM => dmOrdEmbed_strictMono hDM) m

theorem dmEmbedReflects : DmEmbedReflects := by
  intro m₁ m₂ hlt
  exact dmOrdEmbed_reflects hlt

theorem dmOrdEmbed_le_dmRankOrd (m : Multiset Nat) :
    dmOrdEmbed m ≤ dmRankOrd m :=
  dmOrdEmbed_le_dmRankOrd_of_reflect dmEmbedReflects m

theorem dmOrdEmbed_eq_dmRankOrd (m : Multiset Nat) :
    dmOrdEmbed m = dmRankOrd m :=
  dmOrdEmbed_eq_dmRankOrd_of_reflect dmEmbedReflects m

theorem dmRankOrd_surjective_lt_opow_omega :
    ∀ α < (ω : Ordinal) ^ (ω : Ordinal), ∃ m : Multiset Nat, dmRankOrd m = α := by
  intro α hα
  rcases dmOrdEmbed_surjective_lt_opow_omega α hα with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  calc
    dmRankOrd m = dmOrdEmbed m := (dmOrdEmbed_eq_dmRankOrd m).symm
    _ = α := hm

/--
If `dmOrdEmbed` is surjective on `< ω^ω`, then `CNFωω.eval` is also surjective on `< ω^ω`.
-/
theorem surj_lt_opow_omega_of_dmSurj
    (hSurj : DmEmbedSurjBelowOmegaOmega) :
    ∀ α < (ω : Ordinal) ^ (ω : Ordinal), ∃ c : CNFωω, c.eval = α := by
  intro α hα
  rcases hSurj α hα with ⟨m, hm⟩
  exact ⟨ofMultiset m, by simpa [eval] using hm⟩

/--
Choice-level constructor for values `< ω^ω`, parameterized by the surjectivity bridge.
-/
noncomputable def ofLtOpowOmega (hSurj : DmEmbedSurjBelowOmegaOmega)
    (a : {α : Ordinal // α < (ω : Ordinal) ^ (ω : Ordinal)}) : CNFωω :=
  ofMultiset (Classical.choose (hSurj a.1 a.2))

theorem eval_ofLtOpowOmega (hSurj : DmEmbedSurjBelowOmegaOmega)
    (a : {α : Ordinal // α < (ω : Ordinal) ^ (ω : Ordinal)}) :
    (ofLtOpowOmega hSurj a).eval = a.1 := by
  unfold ofLtOpowOmega
  simpa [eval] using (Classical.choose_spec (hSurj a.1 a.2))

/--
CNF-surjectivity below `ω^ω` is equivalent to DM-embedding surjectivity below `ω^ω`.
-/
theorem surj_lt_opow_omega_iff_dmSurj :
    (∀ α < (ω : Ordinal) ^ (ω : Ordinal), ∃ c : CNFωω, c.eval = α) ↔
      DmEmbedSurjBelowOmegaOmega := by
  constructor
  · intro h α hα
    rcases h α hα with ⟨c, hc⟩
    exact ⟨c.toMultiset, by simpa [eval] using hc⟩
  · intro h
    exact surj_lt_opow_omega_of_dmSurj h

theorem surj_lt_opow_omega :
    ∀ α < (ω : Ordinal) ^ (ω : Ordinal), ∃ c : CNFωω, c.eval = α :=
  surj_lt_opow_omega_of_dmSurj dmOrdEmbed_surjective_prop

noncomputable def ofLtOpowOmegaUncond
    (a : {α : Ordinal // α < (ω : Ordinal) ^ (ω : Ordinal)}) : CNFωω :=
  ofLtOpowOmega dmOrdEmbed_surjective_prop a

theorem eval_ofLtOpowOmegaUncond
    (a : {α : Ordinal // α < (ω : Ordinal) ^ (ω : Ordinal)}) :
    (ofLtOpowOmegaUncond a).eval = a.1 :=
  eval_ofLtOpowOmega dmOrdEmbed_surjective_prop a

end CNFωω

private lemma multiset_eq_replicate_count_add_filter_lt_of_all_le
    {m : Multiset Nat} {z : Nat} (hle : ∀ n ∈ m, n ≤ z) :
    m = Multiset.replicate (Multiset.count z m) z + m.filter (fun n => n < z) := by
  have hDecomp :
      m = m.filter (Eq z) + m.filter (fun n => ¬ z = n) := by
    simpa [add_comm] using (Multiset.filter_add_not (p := Eq z) m).symm
  have hNeEqLt :
      m.filter (fun n => ¬ z = n) = m.filter (fun n => n < z) := by
    refine Multiset.filter_congr ?_
    intro n hn
    constructor
    · intro hne
      exact lt_of_le_of_ne (hle n hn) (by simpa [eq_comm] using hne)
    · intro hlt
      exact (by simpa [eq_comm] using (ne_of_lt hlt))
  have hEqRep : m.filter (Eq z) = Multiset.replicate (Multiset.count z m) z := by
    simpa using (Multiset.filter_eq m z)
  calc
    m = m.filter (Eq z) + m.filter (fun n => ¬ z = n) := hDecomp
    _ = Multiset.replicate (Multiset.count z m) z + m.filter (fun n => n < z) := by
          rw [hEqRep, hNeEqLt]

private lemma dmOrdEmbed_eq_opow_mul_count_add_filter_lt_of_all_le
    {m : Multiset Nat} {z : Nat} (hle : ∀ n ∈ m, n ≤ z) :
    dmOrdEmbed m =
      (ω : Ordinal) ^ (z : Ordinal) * (Multiset.count z m : Ordinal) +
        dmOrdEmbed (m.filter (fun n => n < z)) := by
  have hsplit := multiset_eq_replicate_count_add_filter_lt_of_all_le hle
  have hLow : ∀ n ∈ m.filter (fun n => n < z), n < z := by
    intro n hn
    exact (Multiset.mem_filter.1 hn).2
  calc
    dmOrdEmbed m = dmOrdEmbed (Multiset.replicate (Multiset.count z m) z + m.filter (fun n => n < z)) := by
      simpa using congrArg dmOrdEmbed hsplit
    _ = (ω : Ordinal) ^ (z : Ordinal) * (Multiset.count z m : Ordinal) +
          dmOrdEmbed (m.filter (fun n => n < z)) :=
      dmOrdEmbed_replicate_add_of_all_lt hLow

private lemma dmOrdEmbed_lt_opow_of_forall_lt
    {m : Multiset Nat} {k : Nat} (h : ∀ n ∈ m, n < k) :
    dmOrdEmbed m < (ω : Ordinal) ^ (k : Ordinal) := by
  induction k generalizing m with
  | zero =>
      have hm : m = 0 := by
        apply Multiset.eq_zero_of_forall_notMem
        intro n hn
        exact Nat.not_lt_zero n (h n hn)
      simp [hm]
  | succ k ih =>
      have hle : ∀ n ∈ m, n ≤ k := by
        intro n hn
        exact Nat.lt_succ_iff.mp (h n hn)
      let tail : Multiset Nat := m.filter (fun n => n < k)
      have hTail : ∀ n ∈ tail, n < k := by
        intro n hn
        exact (Multiset.mem_filter.1 hn).2
      have hTailBound : dmOrdEmbed tail < (ω : Ordinal) ^ (k : Ordinal) :=
        ih hTail
      have hDecomp :
          dmOrdEmbed m = ((ω : Ordinal) ^ (k : Ordinal)) * (Multiset.count k m : Ordinal) + dmOrdEmbed tail := by
        simpa [tail] using dmOrdEmbed_eq_opow_mul_count_add_filter_lt_of_all_le hle
      have hCountLt : (Multiset.count k m : Ordinal) < (ω : Ordinal) := by
        simpa using (Ordinal.nat_lt_omega0 (Multiset.count k m))
      have hMain :
          ((ω : Ordinal) ^ (k : Ordinal)) * (Multiset.count k m : Ordinal) + dmOrdEmbed tail <
            (ω : Ordinal) ^ Order.succ (k : Ordinal) :=
        Ordinal.opow_mul_add_lt_opow_succ hCountLt hTailBound
      calc
        dmOrdEmbed m = ((ω : Ordinal) ^ (k : Ordinal)) * (Multiset.count k m : Ordinal) + dmOrdEmbed tail := hDecomp
        _ < (ω : Ordinal) ^ Order.succ (k : Ordinal) := hMain
        _ = (ω : Ordinal) ^ ((k + 1 : Nat) : Ordinal) := by
          simp

private theorem dmOrdEmbed_injective_bounded :
    ∀ k {m₁ m₂ : Multiset Nat},
      (∀ n ∈ m₁, n < k) →
      (∀ n ∈ m₂, n < k) →
      dmOrdEmbed m₁ = dmOrdEmbed m₂ →
      m₁ = m₂
  | 0, m₁, m₂, h₁, h₂, _ => by
      have hm₁ : m₁ = 0 := by
        apply Multiset.eq_zero_of_forall_notMem
        intro n hn
        exact Nat.not_lt_zero n (h₁ n hn)
      have hm₂ : m₂ = 0 := by
        apply Multiset.eq_zero_of_forall_notMem
        intro n hn
        exact Nat.not_lt_zero n (h₂ n hn)
      simp [hm₁, hm₂]
  | k + 1, m₁, m₂, h₁, h₂, hEq => by
      have h₁le : ∀ n ∈ m₁, n ≤ k := by
        intro n hn
        exact Nat.lt_succ_iff.mp (h₁ n hn)
      have h₂le : ∀ n ∈ m₂, n ≤ k := by
        intro n hn
        exact Nat.lt_succ_iff.mp (h₂ n hn)
      let tail₁ : Multiset Nat := m₁.filter (fun n => n < k)
      let tail₂ : Multiset Nat := m₂.filter (fun n => n < k)
      have hTail₁lt : ∀ n ∈ tail₁, n < k := by
        intro n hn
        exact (Multiset.mem_filter.1 hn).2
      have hTail₂lt : ∀ n ∈ tail₂, n < k := by
        intro n hn
        exact (Multiset.mem_filter.1 hn).2
      have hDecomp₁ := dmOrdEmbed_eq_opow_mul_count_add_filter_lt_of_all_le h₁le
      have hDecomp₂ := dmOrdEmbed_eq_opow_mul_count_add_filter_lt_of_all_le h₂le
      have hTail₁bound : dmOrdEmbed tail₁ < (ω : Ordinal) ^ (k : Ordinal) :=
        dmOrdEmbed_lt_opow_of_forall_lt hTail₁lt
      have hTail₂bound : dmOrdEmbed tail₂ < (ω : Ordinal) ^ (k : Ordinal) :=
        dmOrdEmbed_lt_opow_of_forall_lt hTail₂lt
      have hBaseNe : ((ω : Ordinal) ^ (k : Ordinal)) ≠ 0 :=
        Ordinal.opow_ne_zero _ Ordinal.omega0_pos.ne'
      have hDecomp₁' :
          dmOrdEmbed m₁ = ((ω : Ordinal) ^ (k : Ordinal)) * (Multiset.count k m₁ : Ordinal) + dmOrdEmbed tail₁ := by
        simpa [tail₁] using hDecomp₁
      have hDecomp₂' :
          dmOrdEmbed m₂ = ((ω : Ordinal) ^ (k : Ordinal)) * (Multiset.count k m₂ : Ordinal) + dmOrdEmbed tail₂ := by
        simpa [tail₂] using hDecomp₂
      have hCountEqOrd : (Multiset.count k m₁ : Ordinal) = (Multiset.count k m₂ : Ordinal) := by
        have hDiv₁ :
            dmOrdEmbed m₁ / ((ω : Ordinal) ^ (k : Ordinal)) = (Multiset.count k m₁ : Ordinal) := by
          calc
            dmOrdEmbed m₁ / ((ω : Ordinal) ^ (k : Ordinal)) =
                (((ω : Ordinal) ^ (k : Ordinal)) * (Multiset.count k m₁ : Ordinal) + dmOrdEmbed tail₁) /
                  ((ω : Ordinal) ^ (k : Ordinal)) := by rw [hDecomp₁']
            _ = (Multiset.count k m₁ : Ordinal) +
                  dmOrdEmbed tail₁ / ((ω : Ordinal) ^ (k : Ordinal)) :=
                Ordinal.mul_add_div _ hBaseNe _
            _ = (Multiset.count k m₁ : Ordinal) := by
                rw [Ordinal.div_eq_zero_of_lt hTail₁bound, add_zero]
        have hDiv₂ :
            dmOrdEmbed m₂ / ((ω : Ordinal) ^ (k : Ordinal)) = (Multiset.count k m₂ : Ordinal) := by
          calc
            dmOrdEmbed m₂ / ((ω : Ordinal) ^ (k : Ordinal)) =
                (((ω : Ordinal) ^ (k : Ordinal)) * (Multiset.count k m₂ : Ordinal) + dmOrdEmbed tail₂) /
                  ((ω : Ordinal) ^ (k : Ordinal)) := by rw [hDecomp₂']
            _ = (Multiset.count k m₂ : Ordinal) +
                  dmOrdEmbed tail₂ / ((ω : Ordinal) ^ (k : Ordinal)) :=
                Ordinal.mul_add_div _ hBaseNe _
            _ = (Multiset.count k m₂ : Ordinal) := by
                rw [Ordinal.div_eq_zero_of_lt hTail₂bound, add_zero]
        calc
          (Multiset.count k m₁ : Ordinal) = dmOrdEmbed m₁ / ((ω : Ordinal) ^ (k : Ordinal)) := hDiv₁.symm
          _ = dmOrdEmbed m₂ / ((ω : Ordinal) ^ (k : Ordinal)) := by rw [hEq]
          _ = (Multiset.count k m₂ : Ordinal) := hDiv₂
      have hCountEq : Multiset.count k m₁ = Multiset.count k m₂ := by
        exact_mod_cast hCountEqOrd
      have hTailEqEmbed : dmOrdEmbed tail₁ = dmOrdEmbed tail₂ := by
        have hMod₁ : dmOrdEmbed m₁ % ((ω : Ordinal) ^ (k : Ordinal)) = dmOrdEmbed tail₁ := by
          calc
            dmOrdEmbed m₁ % ((ω : Ordinal) ^ (k : Ordinal)) =
                ((((ω : Ordinal) ^ (k : Ordinal)) * (Multiset.count k m₁ : Ordinal)) + dmOrdEmbed tail₁) %
                  ((ω : Ordinal) ^ (k : Ordinal)) := by rw [hDecomp₁']
            _ = dmOrdEmbed tail₁ % ((ω : Ordinal) ^ (k : Ordinal)) :=
                Ordinal.mul_add_mod_self _ _ _
            _ = dmOrdEmbed tail₁ := Ordinal.mod_eq_of_lt hTail₁bound
        have hMod₂ : dmOrdEmbed m₂ % ((ω : Ordinal) ^ (k : Ordinal)) = dmOrdEmbed tail₂ := by
          calc
            dmOrdEmbed m₂ % ((ω : Ordinal) ^ (k : Ordinal)) =
                ((((ω : Ordinal) ^ (k : Ordinal)) * (Multiset.count k m₂ : Ordinal)) + dmOrdEmbed tail₂) %
                  ((ω : Ordinal) ^ (k : Ordinal)) := by rw [hDecomp₂']
            _ = dmOrdEmbed tail₂ % ((ω : Ordinal) ^ (k : Ordinal)) :=
                Ordinal.mul_add_mod_self _ _ _
            _ = dmOrdEmbed tail₂ := Ordinal.mod_eq_of_lt hTail₂bound
        calc
          dmOrdEmbed tail₁ = dmOrdEmbed m₁ % ((ω : Ordinal) ^ (k : Ordinal)) := hMod₁.symm
          _ = dmOrdEmbed m₂ % ((ω : Ordinal) ^ (k : Ordinal)) := by rw [hEq]
          _ = dmOrdEmbed tail₂ := hMod₂
      have hTailEq : tail₁ = tail₂ := dmOrdEmbed_injective_bounded k hTail₁lt hTail₂lt hTailEqEmbed
      have hSplit₁ := multiset_eq_replicate_count_add_filter_lt_of_all_le h₁le
      have hSplit₂ := multiset_eq_replicate_count_add_filter_lt_of_all_le h₂le
      calc
        m₁ = Multiset.replicate (Multiset.count k m₁) k + tail₁ := by simpa [tail₁] using hSplit₁
        _ = Multiset.replicate (Multiset.count k m₂) k + tail₂ := by rw [hCountEq, hTailEq]
        _ = m₂ := by simpa [tail₂] using hSplit₂.symm

/-- The DM ordinal embedding is injective on multisets of naturals. -/
theorem dmOrdEmbed_injective : Function.Injective dmOrdEmbed := by
  intro m₁ m₂ hEq
  by_cases hsum : m₁ + m₂ = 0
  · have hm₁ : m₁ = 0 := by
      apply Multiset.eq_zero_of_subset_zero
      intro n hn
      exact hsum.symm ▸ Multiset.mem_add.2 (Or.inl hn)
    have hm₂ : m₂ = 0 := by
      apply Multiset.eq_zero_of_subset_zero
      intro n hn
      exact hsum.symm ▸ Multiset.mem_add.2 (Or.inr hn)
    simp [hm₁, hm₂]
  · let s : Multiset Nat := m₁ + m₂
    let zMax : Nat := s.toFinset.max' (Multiset.toFinset_nonempty.2 hsum)
    have hzLe : ∀ z ∈ s, z ≤ zMax := by
      intro z hz
      exact Finset.le_max' _ _ ((Multiset.mem_toFinset).2 hz)
    have h₁lt : ∀ n ∈ m₁, n < zMax + 1 := by
      intro n hn
      exact Nat.lt_succ_of_le (hzLe n (Multiset.mem_add.2 (Or.inl hn)))
    have h₂lt : ∀ n ∈ m₂, n < zMax + 1 := by
      intro n hn
      exact Nat.lt_succ_of_le (hzLe n (Multiset.mem_add.2 (Or.inr hn)))
    exact dmOrdEmbed_injective_bounded (zMax + 1) h₁lt h₂lt hEq

/-- Equality of DM ordinal codes is equivalent to equality of multisets. -/
theorem dmOrdEmbed_eq_iff {m₁ m₂ : Multiset Nat} :
    dmOrdEmbed m₁ = dmOrdEmbed m₂ ↔ m₁ = m₂ :=
  ⟨fun h => dmOrdEmbed_injective h, fun h => by simp [h]⟩

/-! ### Order-type isomorphism: (Multiset Nat, DM) ≅ₒ (Iio ω^ω, <) -/

/-- Complete order-type characterization of the DM ordering on `Multiset Nat`.
The embedding `dmOrdEmbed` is an order isomorphism from `(Multiset Nat, DM)` to
`({α : Ordinal | α < ω^ω}, <)`:
1. **Bi-directional order**: `DM m₁ m₂ ↔ dmOrdEmbed m₁ < dmOrdEmbed m₂`
2. **Boundedness**: `dmOrdEmbed m < ω^ω` for all `m`
3. **Surjectivity**: every ordinal below `ω^ω` is hit

Together these imply the order type of `(Multiset Nat, DM)` is exactly `ω^ω`. -/
theorem dm_order_type_omega_omega :
    (∀ m₁ m₂ : Multiset Nat, DM m₁ m₂ ↔ dmOrdEmbed m₁ < dmOrdEmbed m₂) ∧
    (∀ m : Multiset Nat, dmOrdEmbed m < (ω : Ordinal) ^ (ω : Ordinal)) ∧
    (∀ α < (ω : Ordinal) ^ (ω : Ordinal), ∃ m : Multiset Nat, dmOrdEmbed m = α) :=
  ⟨fun _ _ => ⟨dmOrdEmbed_strictMono, dmOrdEmbed_reflects⟩,
   dmOrdEmbed_lt_opow_omega,
   CNFωω.dmOrdEmbed_surjective_lt_opow_omega⟩

/-- Phase-B CNF scaffold, stated as the exact `ω^ω` order-type package used in the paper. -/
theorem phaseB_cnf_scaffold_exact_order_type :
    (∀ m₁ m₂ : Multiset Nat, DM m₁ m₂ ↔ dmOrdEmbed m₁ < dmOrdEmbed m₂) ∧
    (∀ m : Multiset Nat, dmOrdEmbed m < (ω : Ordinal) ^ (ω : Ordinal)) ∧
    (∀ α < (ω : Ordinal) ^ (ω : Ordinal), ∃ m : Multiset Nat, dmOrdEmbed m = α) :=
  dm_order_type_omega_omega

/-- Phase-B cofinality restated on the reflected `dmRankOrd` image. -/
theorem phaseB_cnf_scaffold_cofinal :
    ∀ α < (ω : Ordinal) ^ (ω : Ordinal), ∃ m : Multiset Nat, dmRankOrd m = α :=
  CNFωω.dmRankOrd_surjective_lt_opow_omega

/-- `deltaFlag` is at most 1 for any trace (it is a binary phase indicator). -/
private lemma deltaFlag_le_one (t : Trace) : MetaSN_KO7.deltaFlag t ≤ 1 := by
  unfold MetaSN_KO7.deltaFlag
  split <;> omega

/-- The triple-lexicographic measure `Lex3c` for any `Trace` is bounded by `ω^ω · 2`.
This follows from the binary first component (`deltaFlag ≤ 1`) giving two blocks. -/
theorem lex3c_order_type_bound (t : Trace) :
    lex3cToOrd (mu3c t) < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat) := by
  apply lex3cToOrd_lt_opow_omega_mul_two
  exact deltaFlag_le_one t

end OperatorKO7.MetaDM
