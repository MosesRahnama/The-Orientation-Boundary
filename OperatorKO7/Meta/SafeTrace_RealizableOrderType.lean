import OperatorKO7.Meta.SafeTrace_TripleLexAmbientImage
import OperatorKO7.Meta.DM_OrderType_LowerBound
import Mathlib.Data.Multiset.Bind

/-!
# Exact order type of the trace-realizable carrier

The trace map is not surjective onto the calibrated carrier.  Its image nevertheless has the
same order type, `omega^omega * 2`.  The lower embedding realizes two full DM blocks by replacing
each exponent with its finite payload tower; the upper embedding is the calibrated code itself.
-/

namespace OperatorKO7.SafeTraceTripleLexExactness

open Ordinal
open OperatorKO7
open OperatorKO7.MetaCM
open OperatorKO7.MetaDM
open OperatorKO7.MetaDM.CNFωω
open OperatorKO7.Trace
open MetaSN_DM
open MetaSN_KO7

set_option autoImplicit false

/-- Replace every DM exponent by the prefix tower that the KO7 recursor realizes. -/
def towerClosure (m : Multiset Nat) : Multiset Nat :=
  m.bind kappaTower

/-- The largest member of `kappaTower n` is `n + 1`. -/
theorem succ_mem_kappaTower (n : Nat) : n + 1 ∈ kappaTower n := by
  induction n with
  | zero => simp [kappaTower]
  | succ n _ => simp [kappaTower]

/-- Every member of `kappaTower n` is at most its top member. -/
theorem mem_kappaTower_le {n k : Nat} (hk : k ∈ kappaTower n) : k ≤ n + 1 := by
  induction n with
  | zero =>
      simp [kappaTower] at hk
      omega
  | succ n ih =>
      simp [kappaTower] at hk
      rcases hk with rfl | hk
      · omega
      · exact (ih hk).trans (by omega)

theorem towerClosure_ne_zero {m : Multiset Nat} (hm : m ≠ 0) : towerClosure m ≠ 0 := by
  rcases Multiset.exists_mem_of_ne_zero hm with ⟨n, hn⟩
  have hmem : n + 1 ∈ towerClosure m :=
    Multiset.mem_bind.2 ⟨n, hn, succ_mem_kappaTower n⟩
  intro hzero
  rw [hzero] at hmem
  simp at hmem

/-- Prefix-tower closure preserves every strict Dershowitz--Manna comparison. -/
theorem towerClosure_preserves_dm {m₁ m₂ : Multiset Nat}
    (hDM : DM m₁ m₂) : DM (towerClosure m₁) (towerClosure m₂) := by
  rcases hDM with ⟨X, Y, Z, hZ, hm₁, hm₂, hDom⟩
  refine ⟨towerClosure X, towerClosure Y, towerClosure Z,
    towerClosure_ne_zero hZ, ?_, ?_, ?_⟩
  · simpa [towerClosure, Multiset.add_bind] using congrArg towerClosure hm₁
  · simpa [towerClosure, Multiset.add_bind] using congrArg towerClosure hm₂
  · intro y hy
    rcases Multiset.mem_bind.1 hy with ⟨i, hiY, hyTower⟩
    rcases hDom i hiY with ⟨j, hjZ, hij⟩
    refine ⟨j + 1, Multiset.mem_bind.2 ⟨j, hjZ, succ_mem_kappaTower j⟩, ?_⟩
    have hyLe : y ≤ i + 1 := mem_kappaTower_le hyTower
    omega

/-- A common multiset context preserves a strict DM comparison. -/
theorem dm_add_left (c : Multiset Nat) {m₁ m₂ : Multiset Nat}
    (hDM : DM m₁ m₂) : DM (c + m₁) (c + m₂) := by
  rcases hDM with ⟨X, Y, Z, hZ, hm₁, hm₂, hDom⟩
  refine ⟨c + X, Y, Z, hZ, ?_, ?_, hDom⟩
  · calc
      c + m₁ = c + (X + Y) := congrArg (c + ·) hm₁
      _ = (c + X) + Y := by simp [add_assoc]
  · calc
      c + m₂ = c + (X + Z) := congrArg (c + ·) hm₂
      _ = (c + X) + Z := by simp [add_assoc]

/-- Third argument whose recursor contribution is exactly `kappaTower n`. -/
def exponentSeed : Nat → Trace
  | 0 => void
  | n + 1 => payloadTower n

/-- Add one payload tower to the base trace. -/
def addTower (n : Nat) (b : Trace) : Trace :=
  recΔ b void (exponentSeed n)

@[simp] theorem kappaM_addTower (n : Nat) (b : Trace) :
    kappaM (addTower n b) = kappaTower n + kappaM b := by
  cases n with
  | zero => simp [addTower, exponentSeed, kappaTower, kappaM]
  | succ n =>
      simp [addTower, exponentSeed, kappaTower, kappaM,
        weight_payloadTower, kappaM_payloadTower]

@[simp] theorem deltaFlag_addTower (n : Nat) (b : Trace) :
    deltaFlag (addTower n b) = 0 := by
  cases n with
  | zero => rfl
  | succ n =>
      cases n <;> rfl

/-- Deterministic trace realization of a finite multiset of source exponents. -/
def towerTraceList : List Nat → Trace
  | [] => void
  | n :: ns => addTower n (towerTraceList ns)

@[simp] theorem kappaM_towerTraceList (l : List Nat) :
    kappaM (towerTraceList l) = (l : Multiset Nat).bind kappaTower := by
  induction l with
  | nil => simp [towerTraceList]
  | cons n ns ih =>
      simp only [towerTraceList, kappaM_addTower, ih]
      change kappaTower n + (ns : Multiset Nat).bind kappaTower =
        (n ::ₘ (ns : Multiset Nat)).bind kappaTower
      rw [Multiset.cons_bind]

@[simp] theorem deltaFlag_towerTraceList (l : List Nat) :
    deltaFlag (towerTraceList l) = 0 := by
  cases l with
  | nil => rfl
  | cons n ns =>
      change deltaFlag (addTower n (towerTraceList ns)) = 0
      exact deltaFlag_addTower n (towerTraceList ns)

/-- Canonical trace for a multiset, using descending sort only to choose syntax. -/
def towerTrace (m : Multiset Nat) : Trace :=
  towerTraceList (Multiset.sort (· ≥ ·) m)

@[simp] theorem kappaM_towerTrace (m : Multiset Nat) :
    kappaM (towerTrace m) = towerClosure m := by
  simp [towerTrace, towerClosure, Multiset.sort_eq]

@[simp] theorem deltaFlag_towerTrace (m : Multiset Nat) :
    deltaFlag (towerTrace m) = 0 := by
  unfold towerTrace
  exact deltaFlag_towerTraceList _

/-- Phase-one copy of the same tower-closed DM payload. -/
def flaggedTowerTrace (m : Multiset Nat) : Trace :=
  recΔ (towerTrace m) void (delta void)

@[simp] theorem kappaM_flaggedTowerTrace (m : Multiset Nat) :
    kappaM (flaggedTowerTrace m) = 1 ::ₘ towerClosure m := by
  simp [flaggedTowerTrace]

@[simp] theorem deltaFlag_flaggedTowerTrace (m : Multiset Nat) :
    deltaFlag (flaggedTowerTrace m) = 1 := by
  rfl

/-- Embed any concrete trace into the trace-realizable subtype. -/
def realizedCarrierOfTrace (t : Trace) : TraceRealizableCarrier :=
  ⟨traceToFullTripleLexCarrier t, ⟨t, rfl⟩⟩

def phaseZeroTowerCarrier (m : Multiset Nat) : TraceRealizableCarrier :=
  realizedCarrierOfTrace (towerTrace m)

def phaseOneTowerCarrier (m : Multiset Nat) : TraceRealizableCarrier :=
  realizedCarrierOfTrace (flaggedTowerTrace m)

/-- The phase-zero tower realization strictly preserves the full DM order. -/
theorem phaseZeroTowerCarrier_strict {m₁ m₂ : Multiset Nat} (hDM : DM m₁ m₂) :
    RealizableCarrierOrder (phaseZeroTowerCarrier m₁) (phaseZeroTowerCarrier m₂) := by
  have hClosed : DM (kappaM (towerTrace m₁)) (kappaM (towerTrace m₂)) := by
    simpa using towerClosure_preserves_dm hDM
  have hInner :
      LexDM_c (kappaM (towerTrace m₁), tau (towerTrace m₁))
        (kappaM (towerTrace m₂), tau (towerTrace m₂)) :=
    dm_to_LexDM_c_left hClosed
  have hLex : Lex3c (mu3c (towerTrace m₁)) (mu3c (towerTrace m₂)) := by
    simp only [mu3c, deltaFlag_towerTrace]
    exact Prod.Lex.right (α := Nat) (β := Multiset Nat × Nat)
      (ra := (· < ·)) (rb := LexDM_c) (0 : Nat) hInner
  change lex3cToOrd (mu3c (towerTrace m₁)) < lex3cToOrd (mu3c (towerTrace m₂))
  exact lex3cToOrd_strictMono hLex

/-- The phase-one tower realization strictly preserves the full DM order. -/
theorem phaseOneTowerCarrier_strict {m₁ m₂ : Multiset Nat} (hDM : DM m₁ m₂) :
    RealizableCarrierOrder (phaseOneTowerCarrier m₁) (phaseOneTowerCarrier m₂) := by
  have hClosed : DM (towerClosure m₁) (towerClosure m₂) :=
    towerClosure_preserves_dm hDM
  have hFlagged : DM (1 ::ₘ towerClosure m₁) (1 ::ₘ towerClosure m₂) := by
    simpa [Multiset.singleton_add] using dm_add_left ({1} : Multiset Nat) hClosed
  have hInner :
      LexDM_c (kappaM (flaggedTowerTrace m₁), tau (flaggedTowerTrace m₁))
        (kappaM (flaggedTowerTrace m₂), tau (flaggedTowerTrace m₂)) := by
    apply dm_to_LexDM_c_left
    simpa using hFlagged
  have hLex : Lex3c (mu3c (flaggedTowerTrace m₁)) (mu3c (flaggedTowerTrace m₂)) := by
    simp only [mu3c, deltaFlag_flaggedTowerTrace]
    exact Prod.Lex.right (α := Nat) (β := Multiset Nat × Nat)
      (ra := (· < ·)) (rb := LexDM_c) (1 : Nat) hInner
  change lex3cToOrd (mu3c (flaggedTowerTrace m₁)) <
    lex3cToOrd (mu3c (flaggedTowerTrace m₂))
  exact lex3cToOrd_strictMono hLex

/-- Every phase-zero tower point precedes every phase-one tower point. -/
theorem phaseZeroTowerCarrier_lt_phaseOneTowerCarrier (m₁ m₂ : Multiset Nat) :
    RealizableCarrierOrder (phaseZeroTowerCarrier m₁) (phaseOneTowerCarrier m₂) := by
  have hLex : Lex3c (mu3c (towerTrace m₁)) (mu3c (flaggedTowerTrace m₂)) := by
    simp only [mu3c, deltaFlag_towerTrace, deltaFlag_flaggedTowerTrace]
    exact Prod.Lex.left
      (kappaM (towerTrace m₁), tau (towerTrace m₁))
      (kappaM (flaggedTowerTrace m₂), tau (flaggedTowerTrace m₂))
      (by omega)
  change lex3cToOrd (mu3c (towerTrace m₁)) <
    lex3cToOrd (mu3c (flaggedTowerTrace m₂))
  exact lex3cToOrd_strictMono hLex

noncomputable def OmegaOmegaOrdinal : Ordinal.{0} :=
  (ω : Ordinal.{0}) ^ (ω : Ordinal.{0})

/-- Small canonical carrier of the ordinals below `omega^omega`.  `Ordinal.toType` keeps this
index in `Type 0`, so it can embed into the concrete trace carrier without a universe lift. -/
abbrev OmegaOmegaIndex := ((ω : Ordinal.{0}) ^ (ω : Ordinal.{0})).toType

/-- Canonical strict order on the small `omega^omega` carrier. -/
abbrev OmegaOmegaIndexOrder : OmegaOmegaIndex → OmegaOmegaIndex → Prop := (· < ·)

local instance omegaOmegaIndexOrder_isWellOrder :
    IsWellOrder OmegaOmegaIndex OmegaOmegaIndexOrder := by
  change IsWellOrder (((ω : Ordinal.{0}) ^ (ω : Ordinal.{0})).toType)
    (fun x y => x < y)
  infer_instance

/-- Ordinal represented by a point of the small `omega^omega` carrier. -/
noncomputable def omegaOmegaIndexCode (a : OmegaOmegaIndex) : Ordinal.{0} :=
  (Ordinal.typein OmegaOmegaIndexOrder).toRelEmbedding a

@[simp] theorem omegaOmegaIndexCode_lt (a : OmegaOmegaIndex) :
    omegaOmegaIndexCode a < OmegaOmegaOrdinal := by
  simpa [omegaOmegaIndexCode, OmegaOmegaOrdinal, OmegaOmegaIndexOrder] using
    (Ordinal.typein_lt_self a)

/-- Canonical preimage of a small index under the exact finite-CNF DM embedding. -/
noncomputable def dmPreimage (a : OmegaOmegaIndex) : Multiset Nat :=
  Classical.choose
    (CNFωω.dmOrdEmbed_surjective_lt_opow_omega
      (omegaOmegaIndexCode a) (omegaOmegaIndexCode_lt a))

@[simp] theorem dmOrdEmbed_dmPreimage (a : OmegaOmegaIndex) :
    dmOrdEmbed (dmPreimage a) = omegaOmegaIndexCode a :=
  Classical.choose_spec
    (CNFωω.dmOrdEmbed_surjective_lt_opow_omega
      (omegaOmegaIndexCode a) (omegaOmegaIndexCode_lt a))

noncomputable def phaseZeroIndexCarrier (a : OmegaOmegaIndex) : TraceRealizableCarrier :=
  phaseZeroTowerCarrier (dmPreimage a)

noncomputable def phaseOneIndexCarrier (a : OmegaOmegaIndex) : TraceRealizableCarrier :=
  phaseOneTowerCarrier (dmPreimage a)

theorem phaseZeroIndexCarrier_strict {a b : OmegaOmegaIndex} (h : a < b) :
    RealizableCarrierOrder (phaseZeroIndexCarrier a) (phaseZeroIndexCarrier b) := by
  apply phaseZeroTowerCarrier_strict
  apply dmOrdEmbed_reflects
  rw [dmOrdEmbed_dmPreimage, dmOrdEmbed_dmPreimage]
  simpa [omegaOmegaIndexCode, OmegaOmegaIndexOrder] using
    (Ordinal.typein_lt_typein OmegaOmegaIndexOrder).2 h

theorem phaseOneIndexCarrier_strict {a b : OmegaOmegaIndex} (h : a < b) :
    RealizableCarrierOrder (phaseOneIndexCarrier a) (phaseOneIndexCarrier b) := by
  apply phaseOneTowerCarrier_strict
  apply dmOrdEmbed_reflects
  rw [dmOrdEmbed_dmPreimage, dmOrdEmbed_dmPreimage]
  simpa [omegaOmegaIndexCode, OmegaOmegaIndexOrder] using
    (Ordinal.typein_lt_typein OmegaOmegaIndexOrder).2 h

abbrev TwoBlockIndex := Sum OmegaOmegaIndex OmegaOmegaIndex

abbrev TwoBlockIndexOrder : TwoBlockIndex → TwoBlockIndex → Prop :=
  Sum.Lex OmegaOmegaIndexOrder OmegaOmegaIndexOrder

local instance twoBlockIndexOrder_isWellOrder :
    IsWellOrder TwoBlockIndex TwoBlockIndexOrder := by
  infer_instance

local instance twoBlockIndexOrder_isTrichotomous :
    IsTrichotomous TwoBlockIndex TwoBlockIndexOrder := by
  infer_instance

noncomputable def twoBlockCarrier : TwoBlockIndex → TraceRealizableCarrier
  | Sum.inl a => phaseZeroIndexCarrier a
  | Sum.inr a => phaseOneIndexCarrier a

theorem twoBlockCarrier_strict {a b : TwoBlockIndex} (h : TwoBlockIndexOrder a b) :
    RealizableCarrierOrder (twoBlockCarrier a) (twoBlockCarrier b) := by
  change Sum.Lex OmegaOmegaIndexOrder OmegaOmegaIndexOrder a b at h
  cases h with
  | inl hab => exact phaseZeroIndexCarrier_strict hab
  | sep a b =>
      exact phaseZeroTowerCarrier_lt_phaseOneTowerCarrier (dmPreimage a) (dmPreimage b)
  | inr hab => exact phaseOneIndexCarrier_strict hab

/-- Two complete `omega^omega` blocks embed into the actual trace image. -/
noncomputable def twoBlockCarrierRelEmbedding :
    TwoBlockIndexOrder ↪r RealizableCarrierOrder :=
  RelEmbedding.ofMonotone twoBlockCarrier (fun _ _ h => twoBlockCarrier_strict h)

/-- Small code of a realizable carrier point inside `fullTripleLexBound.toType`. -/
noncomputable def realizableCarrierCodeSmall (x : TraceRealizableCarrier) :
    (fullTripleLexBound.{0}).toType :=
  Ordinal.enumIsoToType fullTripleLexBound.{0}
    ⟨traceRealizableCarrierRealization.code x,
      traceRealizableCarrier_image_upper_bound x⟩

/-- The code embeds the trace-realizable carrier into a same-universe carrier of the calibrated
ordinal interval.  This avoids the artificial universe jump of `Set.Iio fullTripleLexBound`. -/
noncomputable def realizableCarrierCodeRelEmbedding :
    RealizableCarrierOrder ↪r
      ((· < ·) : (fullTripleLexBound.{0}).toType →
        (fullTripleLexBound.{0}).toType → Prop) :=
  RelEmbedding.ofMonotone realizableCarrierCodeSmall (by
    intro a b h
    apply (Ordinal.enumIsoToType fullTripleLexBound.{0}).strictMono
    exact h)

theorem twoBlockIndex_order_type :
    @Ordinal.type TwoBlockIndex TwoBlockIndexOrder inferInstance = fullTripleLexBound.{0} := by
  change @Ordinal.type (Sum OmegaOmegaIndex OmegaOmegaIndex)
      (Sum.Lex OmegaOmegaIndexOrder OmegaOmegaIndexOrder) inferInstance =
        fullTripleLexBound.{0}
  calc
    @Ordinal.type (Sum OmegaOmegaIndex OmegaOmegaIndex)
        (Sum.Lex OmegaOmegaIndexOrder OmegaOmegaIndexOrder) inferInstance =
        @Ordinal.type OmegaOmegaIndex OmegaOmegaIndexOrder inferInstance +
          @Ordinal.type OmegaOmegaIndex OmegaOmegaIndexOrder inferInstance :=
      Ordinal.type_sum_lex OmegaOmegaIndexOrder OmegaOmegaIndexOrder
    _ = OmegaOmegaOrdinal + OmegaOmegaOrdinal := by
      simp [OmegaOmegaOrdinal, OmegaOmegaIndex]
    _ = fullTripleLexBound.{0} := by
      let a : Ordinal.{0} := (ω : Ordinal.{0}) ^ (ω : Ordinal.{0})
      change a + a = a * 2
      simpa [a] using (Ordinal.mul_succ a (1 : Ordinal.{0})).symm

/-- **Exact image theorem.**  Non-surjectivity removes carrier points, but it does not lower the
well-order type: the trace-realizable carrier still has order type `omega^omega * 2`. -/
theorem trace_realizable_carrier_order_type_eq_full :
    @Ordinal.type TraceRealizableCarrier RealizableCarrierOrder
        realizableCarrierOrder_isWellOrder = fullTripleLexBound.{0} := by
  apply le_antisymm
  · calc
      @Ordinal.type TraceRealizableCarrier RealizableCarrierOrder
          realizableCarrierOrder_isWellOrder ≤
          @Ordinal.type (fullTripleLexBound.{0}).toType
            ((· < ·) : (fullTripleLexBound.{0}).toType →
              (fullTripleLexBound.{0}).toType → Prop)
            inferInstance := realizableCarrierCodeRelEmbedding.ordinal_type_le
      _ = fullTripleLexBound.{0} := Ordinal.type_toType fullTripleLexBound.{0}
  · calc
      fullTripleLexBound.{0} = @Ordinal.type TwoBlockIndex TwoBlockIndexOrder inferInstance :=
        twoBlockIndex_order_type.symm
      _ ≤ @Ordinal.type TraceRealizableCarrier RealizableCarrierOrder
          realizableCarrierOrder_isWellOrder := twoBlockCarrierRelEmbedding.ordinal_type_le

/-- The ambient trace image has the full calibrated order type as well. -/
theorem ambient_trace_image_order_type_eq_full :
    @Ordinal.type AmbientTraceImage AmbientImageOrder ambientImageOrder_isWellOrder =
      fullTripleLexBound.{0} :=
  ambient_trace_image_order_type_eq_realizable.trans
    trace_realizable_carrier_order_type_eq_full

/-- Sharp package: exact image order type and proper inclusion in the calibrated carrier. -/
theorem ambient_trace_image_exact_and_proper :
    (@Ordinal.type AmbientTraceImage AmbientImageOrder ambientImageOrder_isWellOrder =
        fullTripleLexBound.{0}) ∧
      ¬ Function.Surjective traceToFullTripleLexCarrier :=
  ⟨ambient_trace_image_order_type_eq_full, traceToFullTripleLexCarrier_not_surjective⟩

end OperatorKO7.SafeTraceTripleLexExactness
