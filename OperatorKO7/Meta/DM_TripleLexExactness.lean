import OperatorKO7.Meta.DM_TripleLexImage

namespace OperatorKO7.MetaDM

open Ordinal
open OperatorKO7.MetaCM

/-- Every ordinal below `ω^ω * 2` appears in the calibrated binary-phase triple-lex image. -/
theorem full_triple_lex_image_surjective_lt_opow_omega_mul_two
    {α : Ordinal.{0}} (hα : α < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat)) :
    ∃ x : FullTripleLexCarrier, lex3cToOrd x.toLex3cTuple = α := by
  let δOrd : Ordinal := α / ((ω : Ordinal) ^ (ω : Ordinal))
  let inner : Ordinal := α % ((ω : Ordinal) ^ (ω : Ordinal))
  have hDivLe : ((ω : Ordinal) ^ (ω : Ordinal)) * δOrd ≤ α := by
    simpa [δOrd] using (Ordinal.mul_div_le α ((ω : Ordinal) ^ (ω : Ordinal)))
  have hδltTwo : δOrd < (2 : Ordinal) := by
    by_contra hNot
    have hTwoLe : (2 : Ordinal) ≤ δOrd := not_lt.1 hNot
    have hMulLe : ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Ordinal) ≤
        ((ω : Ordinal) ^ (ω : Ordinal)) * δOrd := by
      exact mul_le_mul_left' hTwoLe ((ω : Ordinal) ^ (ω : Ordinal))
    exact not_lt_of_ge (hMulLe.trans hDivLe) hα
  have hInner : inner < (ω : Ordinal) ^ (ω : Ordinal) := by
    exact Ordinal.mod_lt α (Ordinal.opow_ne_zero _ Ordinal.omega0_pos.ne')
  have hδltOmega : δOrd < (ω : Ordinal) := by
    exact lt_trans hδltTwo (by simpa using (Ordinal.nat_lt_omega0 2))
  obtain ⟨δ, hδEq⟩ := Ordinal.lt_omega0.1 hδltOmega
  have hδltTwoOrd : (δ : Ordinal.{0}) < (2 : Ordinal.{0}) := by
    simpa [hδEq] using hδltTwo
  have hδnotgeTwoNat : ¬ 2 ≤ δ := by
    intro hge
    have hgeOrd : (2 : Ordinal.{0}) ≤ (δ : Ordinal.{0}) := by
      exact_mod_cast hge
    exact not_lt_of_ge hgeOrd hδltTwoOrd
  have hδleOne : δ ≤ 1 := by
    exact Nat.le_of_lt_succ (Nat.lt_of_not_ge hδnotgeTwoNat)
  rcases lexDMToOrd_surjective_lt_opow_omega hInner with ⟨⟨κ, τ⟩, hInnerEq⟩
  refine ⟨{ phase := δ, dmComponent := κ, tauComponent := τ, phase_le_one := hδleOne }, ?_⟩
  calc
    lex3cToOrd
        (FullTripleLexCarrier.toLex3cTuple
          { phase := δ, dmComponent := κ, tauComponent := τ, phase_le_one := hδleOne })
        = ((ω : Ordinal) ^ (ω : Ordinal)) * (δ : Ordinal) + lexDMToOrd (κ, τ) := by
            rfl
    _ = ((ω : Ordinal) ^ (ω : Ordinal)) * δOrd + inner := by rw [hδEq, hInnerEq]
    _ = α := by
        simpa [δOrd, inner] using (Ordinal.div_add_mod α ((ω : Ordinal) ^ (ω : Ordinal)))

/-- Reflection boundary still needed for an unconditional exact order-type theorem. -/
def FullTripleLexOrderReflects : Prop :=
  ∀ {x y : FullTripleLexCarrier},
    lex3cToOrd x.toLex3cTuple < lex3cToOrd y.toLex3cTuple →
      Lex3c x.toLex3cTuple y.toLex3cTuple

/-- Exact inner blocker still needed to turn equal `dmOrdEmbed` codes back into equal multisets. -/
def DmOrdEmbedInjective : Prop :=
  ∀ {m₁ m₂ : Multiset Nat}, dmOrdEmbed m₁ = dmOrdEmbed m₂ → m₁ = m₂

/-- The lower-bound layer now supplies the missing DM-code injectivity theorem. -/
theorem dmOrdEmbedInjective : DmOrdEmbedInjective := by
  intro m₁ m₂ hEq
  exact dmOrdEmbed_injective hEq

/-- Inner reflection for `lexDMToOrd`, conditional on injectivity of the DM ordinal code. -/
theorem lexDMToOrd_reflects_of_dmOrdEmbedInjective
    (hInj : DmOrdEmbedInjective) {p q : Multiset Nat × Nat}
    (hlt : lexDMToOrd p < lexDMToOrd q) :
    LexDM_c p q := by
  rcases p with ⟨κ₁, τ₁⟩
  rcases q with ⟨κ₂, τ₂⟩
  rcases lt_trichotomy (dmOrdEmbed κ₁) (dmOrdEmbed κ₂) with hκ | hκ | hκ
  · exact
      Prod.Lex.left
        (α := Multiset Nat) (β := Nat)
        (ra := fun a b : Multiset Nat => DM a b) (rb := (· < ·))
        (a₁ := κ₁) (a₂ := κ₂) (b₁ := τ₁) (b₂ := τ₂)
        (dmOrdEmbed_reflects hκ)
  · have hκeq : κ₁ = κ₂ := hInj hκ
    have hτlt : τ₁ < τ₂ := by
      by_contra hτnot
      have hτge : τ₂ ≤ τ₁ := Nat.le_of_not_gt hτnot
      have hτgeOrd : (τ₂ : Ordinal) ≤ (τ₁ : Ordinal) := by
        exact_mod_cast hτge
      have hqle : lexDMToOrd (κ₂, τ₂) ≤ lexDMToOrd (κ₁, τ₁) := by
        simpa [lexDMToOrd, hκeq] using
          (add_le_add_left hτgeOrd ((ω : Ordinal) * dmOrdEmbed κ₁))
      exact (not_lt_of_ge hqle) hlt
    simpa [hκeq] using
      (Prod.Lex.right
        (α := Multiset Nat) (β := Nat)
        (ra := fun a b : Multiset Nat => DM a b) (rb := (· < ·))
        (a := κ₁) hτlt)
  · have hrevDM : DM κ₂ κ₁ := dmOrdEmbed_reflects hκ
    have hrev : lexDMToOrd (κ₂, τ₂) < lexDMToOrd (κ₁, τ₁) := by
      exact
        lexDMToOrd_strictMono
          (Prod.Lex.left
            (α := Multiset Nat) (β := Nat)
            (ra := fun a b : Multiset Nat => DM a b) (rb := (· < ·))
            (a₁ := κ₂) (a₂ := κ₁) (b₁ := τ₂) (b₂ := τ₁)
            hrevDM)
    exact (False.elim (lt_asymm hlt hrev))

/-- Conditional inner order equivalence for the `ω * dmOrdEmbed + τ` code. -/
theorem lexDMToOrd_order_iff_of_dmOrdEmbedInjective
    (hInj : DmOrdEmbedInjective) (p q : Multiset Nat × Nat) :
    LexDM_c p q ↔ lexDMToOrd p < lexDMToOrd q := by
  constructor
  · exact lexDMToOrd_strictMono
  · intro hlt
    exact lexDMToOrd_reflects_of_dmOrdEmbedInjective hInj hlt

/-- Unconditional inner reflection for `lexDMToOrd`. -/
theorem lexDMToOrd_reflects {p q : Multiset Nat × Nat}
    (hlt : lexDMToOrd p < lexDMToOrd q) :
    LexDM_c p q :=
  lexDMToOrd_reflects_of_dmOrdEmbedInjective dmOrdEmbedInjective hlt

/-- Unconditional inner order equivalence for the `ω * dmOrdEmbed + τ` code. -/
theorem lexDMToOrd_order_iff (p q : Multiset Nat × Nat) :
    LexDM_c p q ↔ lexDMToOrd p < lexDMToOrd q :=
  lexDMToOrd_order_iff_of_dmOrdEmbedInjective dmOrdEmbedInjective p q

/-- The `ω * dmOrdEmbed + τ` code is injective. -/
theorem lexDMToOrd_injective : Function.Injective lexDMToOrd := by
  intro p q hEq
  rcases p with ⟨κ₁, τ₁⟩
  rcases q with ⟨κ₂, τ₂⟩
  have hωNe : (ω : Ordinal) ≠ 0 := Ordinal.omega0_pos.ne'
  have hτ₁lt : (τ₁ : Ordinal) < (ω : Ordinal) := by
    simpa using (Ordinal.nat_lt_omega0 τ₁)
  have hτ₂lt : (τ₂ : Ordinal) < (ω : Ordinal) := by
    simpa using (Ordinal.nat_lt_omega0 τ₂)
  have hκCode : dmOrdEmbed κ₁ = dmOrdEmbed κ₂ := by
    have hDiv₁ : lexDMToOrd (κ₁, τ₁) / (ω : Ordinal) = dmOrdEmbed κ₁ := by
      rw [lexDMToOrd, Ordinal.mul_add_div _ hωNe, Ordinal.div_eq_zero_of_lt hτ₁lt, add_zero]
    have hDiv₂ : lexDMToOrd (κ₂, τ₂) / (ω : Ordinal) = dmOrdEmbed κ₂ := by
      rw [lexDMToOrd, Ordinal.mul_add_div _ hωNe, Ordinal.div_eq_zero_of_lt hτ₂lt, add_zero]
    calc
      dmOrdEmbed κ₁ = lexDMToOrd (κ₁, τ₁) / (ω : Ordinal) := hDiv₁.symm
      _ = lexDMToOrd (κ₂, τ₂) / (ω : Ordinal) := by rw [hEq]
      _ = dmOrdEmbed κ₂ := hDiv₂
  have hκ : κ₁ = κ₂ := dmOrdEmbedInjective hκCode
  have hτOrd : (τ₁ : Ordinal) = (τ₂ : Ordinal) := by
    have hMod₁ : lexDMToOrd (κ₁, τ₁) % (ω : Ordinal) = (τ₁ : Ordinal) := by
      rw [lexDMToOrd, Ordinal.mul_add_mod_self]
      exact Ordinal.mod_eq_of_lt hτ₁lt
    have hMod₂ : lexDMToOrd (κ₂, τ₂) % (ω : Ordinal) = (τ₂ : Ordinal) := by
      rw [lexDMToOrd, Ordinal.mul_add_mod_self]
      exact Ordinal.mod_eq_of_lt hτ₂lt
    calc
      (τ₁ : Ordinal) = lexDMToOrd (κ₁, τ₁) % (ω : Ordinal) := hMod₁.symm
      _ = lexDMToOrd (κ₂, τ₂) % (ω : Ordinal) := by rw [hEq]
      _ = (τ₂ : Ordinal) := hMod₂
  have hτ : τ₁ = τ₂ := by
    exact_mod_cast hτOrd
  rcases hκ
  rcases hτ
  rfl

/-- Equality for the `ω * dmOrdEmbed + τ` code is equivalent to equality of pairs. -/
theorem lexDMToOrd_eq_iff {p q : Multiset Nat × Nat} :
    lexDMToOrd p = lexDMToOrd q ↔ p = q :=
  ⟨fun h => lexDMToOrd_injective h, fun h => by simp [h]⟩

/-- Equal calibrated triple-lex codes on the full carrier have equal phase components. -/
theorem full_triple_lex_phase_eq_of_code_eq {x y : FullTripleLexCarrier}
    (hEq : lex3cToOrd x.toLex3cTuple = lex3cToOrd y.toLex3cTuple) :
    x.phase = y.phase := by
  let base : Ordinal := (ω : Ordinal) ^ (ω : Ordinal)
  have hBaseNe : base ≠ 0 := Ordinal.opow_ne_zero _ Ordinal.omega0_pos.ne'
  have hInnerX : lexDMToOrd (x.dmComponent, x.tauComponent) < base := by
    simpa [base] using lexDMToOrd_lt_opow_omega (x.dmComponent, x.tauComponent)
  have hInnerY : lexDMToOrd (y.dmComponent, y.tauComponent) < base := by
    simpa [base] using lexDMToOrd_lt_opow_omega (y.dmComponent, y.tauComponent)
  have hDivX : lex3cToOrd x.toLex3cTuple / base = (x.phase : Ordinal) := by
    rw [FullTripleLexCarrier.toLex3cTuple, lex3cToOrd,
      Ordinal.mul_add_div _ hBaseNe, Ordinal.div_eq_zero_of_lt hInnerX, add_zero]
  have hDivY : lex3cToOrd y.toLex3cTuple / base = (y.phase : Ordinal) := by
    rw [FullTripleLexCarrier.toLex3cTuple, lex3cToOrd,
      Ordinal.mul_add_div _ hBaseNe, Ordinal.div_eq_zero_of_lt hInnerY, add_zero]
  have hPhaseOrd : (x.phase : Ordinal) = (y.phase : Ordinal) := by
    calc
      (x.phase : Ordinal) = lex3cToOrd x.toLex3cTuple / base := hDivX.symm
      _ = lex3cToOrd y.toLex3cTuple / base := by rw [hEq]
      _ = (y.phase : Ordinal) := hDivY
  exact_mod_cast hPhaseOrd

/-- Equal calibrated triple-lex codes on the full carrier have equal inner pairs. -/
theorem full_triple_lex_inner_eq_of_code_eq {x y : FullTripleLexCarrier}
    (hEq : lex3cToOrd x.toLex3cTuple = lex3cToOrd y.toLex3cTuple) :
    (x.dmComponent, x.tauComponent) = (y.dmComponent, y.tauComponent) := by
  let base : Ordinal := (ω : Ordinal) ^ (ω : Ordinal)
  have hInnerX : lexDMToOrd (x.dmComponent, x.tauComponent) < base := by
    simpa [base] using lexDMToOrd_lt_opow_omega (x.dmComponent, x.tauComponent)
  have hInnerY : lexDMToOrd (y.dmComponent, y.tauComponent) < base := by
    simpa [base] using lexDMToOrd_lt_opow_omega (y.dmComponent, y.tauComponent)
  have hModX : lex3cToOrd x.toLex3cTuple % base = lexDMToOrd (x.dmComponent, x.tauComponent) := by
    rw [FullTripleLexCarrier.toLex3cTuple, lex3cToOrd, Ordinal.mul_add_mod_self]
    exact Ordinal.mod_eq_of_lt hInnerX
  have hModY : lex3cToOrd y.toLex3cTuple % base = lexDMToOrd (y.dmComponent, y.tauComponent) := by
    rw [FullTripleLexCarrier.toLex3cTuple, lex3cToOrd, Ordinal.mul_add_mod_self]
    exact Ordinal.mod_eq_of_lt hInnerY
  have hInnerCode :
      lexDMToOrd (x.dmComponent, x.tauComponent) = lexDMToOrd (y.dmComponent, y.tauComponent) := by
    calc
      lexDMToOrd (x.dmComponent, x.tauComponent) = lex3cToOrd x.toLex3cTuple % base := hModX.symm
      _ = lex3cToOrd y.toLex3cTuple % base := by rw [hEq]
      _ = lexDMToOrd (y.dmComponent, y.tauComponent) := hModY
  exact lexDMToOrd_injective hInnerCode

/-- The calibrated binary-phase carrier code is injective on the full carrier. -/
theorem lex3cToOrd_injective_on_fullCarrier :
    Function.Injective (fun x : FullTripleLexCarrier => lex3cToOrd x.toLex3cTuple) := by
  intro x y hEq
  cases x with
  | mk phaseX dmX tauX hPhaseX =>
      cases y with
      | mk phaseY dmY tauY hPhaseY =>
          have hPhase : phaseX = phaseY := full_triple_lex_phase_eq_of_code_eq hEq
          have hInner : (dmX, tauX) = (dmY, tauY) := full_triple_lex_inner_eq_of_code_eq hEq
          cases hPhase
          cases hInner
          simp

/-- Equality for the calibrated binary-phase carrier code is equivalent to carrier equality. -/
theorem lex3cToOrd_eq_iff_on_fullCarrier {x y : FullTripleLexCarrier} :
    lex3cToOrd x.toLex3cTuple = lex3cToOrd y.toLex3cTuple ↔ x = y :=
  ⟨fun h => lex3cToOrd_injective_on_fullCarrier h, fun h => by simp [h]⟩

/-- Triple reflection follows from inner reflection of the `lexDMToOrd` block. -/
theorem full_triple_lex_order_reflects_of_lexDMToOrd_reflects
    (hInnerReflect : ∀ {p q : Multiset Nat × Nat},
      lexDMToOrd p < lexDMToOrd q → LexDM_c p q) :
    FullTripleLexOrderReflects := by
  intro x y hlt
  rcases x with ⟨δ₁, κ₁, τ₁, hδ₁⟩
  rcases y with ⟨δ₂, κ₂, τ₂, hδ₂⟩
  rcases Nat.lt_trichotomy δ₁ δ₂ with hδ | hδ | hδ
  · simpa [FullTripleLexCarrier.toLex3cTuple] using
      (Prod.Lex.left
        (α := Nat) (β := (Multiset Nat × Nat))
        (ra := (· < ·)) (rb := LexDM_c)
        (a₁ := δ₁) (a₂ := δ₂) (b₁ := (κ₁, τ₁)) (b₂ := (κ₂, τ₂))
        hδ)
  · have hInner : lexDMToOrd (κ₁, τ₁) < lexDMToOrd (κ₂, τ₂) := by
      by_contra hInnerNot
      have hInnerGe : lexDMToOrd (κ₂, τ₂) ≤ lexDMToOrd (κ₁, τ₁) := not_lt.1 hInnerNot
      have hOuterGe :
          lex3cToOrd (δ₂, (κ₂, τ₂)) ≤ lex3cToOrd (δ₁, (κ₁, τ₁)) := by
        simpa [lex3cToOrd, hδ] using
          (add_le_add_left hInnerGe (((ω : Ordinal) ^ (ω : Ordinal)) * (δ₁ : Ordinal)))
      exact (not_lt_of_ge hOuterGe) hlt
    have hInnerLex : LexDM_c (κ₁, τ₁) (κ₂, τ₂) := hInnerReflect hInner
    have hcore : Lex3c (δ₁, (κ₁, τ₁)) (δ₁, (κ₂, τ₂)) :=
      (Prod.Lex.right
        (α := Nat) (β := (Multiset Nat × Nat))
        (ra := (· < ·)) (rb := LexDM_c)
        (a := δ₁) hInnerLex)
    simpa [FullTripleLexCarrier.toLex3cTuple, hδ] using hcore
  · have hrev : Lex3c (δ₂, (κ₂, τ₂)) (δ₁, (κ₁, τ₁)) :=
      Prod.Lex.left
        (α := Nat) (β := (Multiset Nat × Nat))
        (ra := (· < ·)) (rb := LexDM_c)
        (a₁ := δ₂) (a₂ := δ₁) (b₁ := (κ₂, τ₂)) (b₂ := (κ₁, τ₁))
        hδ
    exact (False.elim (lt_asymm hlt (lex3cToOrd_strictMono hrev)))

/-- Triple reflection closes once the DM ordinal embedding is injective. -/
theorem full_triple_lex_order_reflects_of_dmOrdEmbedInjective
    (hInj : DmOrdEmbedInjective) :
    FullTripleLexOrderReflects :=
  full_triple_lex_order_reflects_of_lexDMToOrd_reflects
    (fun {_ _} hlt => lexDMToOrd_reflects_of_dmOrdEmbedInjective hInj hlt)

/-- The calibrated binary-phase triple-lex surface now reflects order unconditionally. -/
theorem full_triple_lex_order_reflects : FullTripleLexOrderReflects :=
  full_triple_lex_order_reflects_of_dmOrdEmbedInjective dmOrdEmbedInjective

/-- Honest unconditional package for the calibrated binary-phase triple-lex image. -/
theorem full_triple_lex_image_surjective_package :
    (∀ x y : FullTripleLexCarrier,
      Lex3c x.toLex3cTuple y.toLex3cTuple →
        lex3cToOrd x.toLex3cTuple < lex3cToOrd y.toLex3cTuple) ∧
    (∀ x : FullTripleLexCarrier,
      lex3cToOrd x.toLex3cTuple < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat)) ∧
    (∀ α < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat),
      ∃ x : FullTripleLexCarrier, lex3cToOrd x.toLex3cTuple = α) := by
  refine ⟨?_, full_triple_lex_image_upper_bound, ?_⟩
  · intro x y h
    exact lex3cToOrd_strictMono h
  · intro α hα
    exact full_triple_lex_image_surjective_lt_opow_omega_mul_two hα

/-- Exact order type follows once the remaining order-reflection lemma is supplied. -/
theorem full_triple_lex_exactness_residual_boundary
    (hReflect : FullTripleLexOrderReflects) :
    (∀ x y : FullTripleLexCarrier,
      Lex3c x.toLex3cTuple y.toLex3cTuple ↔
        lex3cToOrd x.toLex3cTuple < lex3cToOrd y.toLex3cTuple) ∧
    (∀ x : FullTripleLexCarrier,
      lex3cToOrd x.toLex3cTuple < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat)) ∧
    (∀ α < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat),
      ∃ x : FullTripleLexCarrier, lex3cToOrd x.toLex3cTuple = α) := by
  refine ⟨?_, full_triple_lex_image_upper_bound, ?_⟩
  · intro x y
    constructor
    · intro h
      exact lex3cToOrd_strictMono h
    · intro h
      exact hReflect h
  · intro α hα
    exact full_triple_lex_image_surjective_lt_opow_omega_mul_two hα

/-- The exact order-type package closes under the sharper injectivity blocker. -/
theorem full_triple_lex_exact_order_type_of_dmOrdEmbedInjective
    (hInj : DmOrdEmbedInjective) :
    (∀ x y : FullTripleLexCarrier,
      Lex3c x.toLex3cTuple y.toLex3cTuple ↔
        lex3cToOrd x.toLex3cTuple < lex3cToOrd y.toLex3cTuple) ∧
    (∀ x : FullTripleLexCarrier,
      lex3cToOrd x.toLex3cTuple < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat)) ∧
    (∀ α < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat),
      ∃ x : FullTripleLexCarrier, lex3cToOrd x.toLex3cTuple = α) :=
  full_triple_lex_exactness_residual_boundary
    (full_triple_lex_order_reflects_of_dmOrdEmbedInjective hInj)

/-- The calibrated binary-phase triple-lex code realizes the exact order type of `ω^ω * 2`. -/
theorem full_triple_lex_exact_order_type :
    (∀ x y : FullTripleLexCarrier,
      Lex3c x.toLex3cTuple y.toLex3cTuple ↔
        lex3cToOrd x.toLex3cTuple < lex3cToOrd y.toLex3cTuple) ∧
    (∀ x : FullTripleLexCarrier,
      lex3cToOrd x.toLex3cTuple < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat)) ∧
    (∀ α < ((ω : Ordinal) ^ (ω : Ordinal)) * (2 : Nat),
      ∃ x : FullTripleLexCarrier, lex3cToOrd x.toLex3cTuple = α) :=
  full_triple_lex_exact_order_type_of_dmOrdEmbedInjective dmOrdEmbedInjective

end OperatorKO7.MetaDM
