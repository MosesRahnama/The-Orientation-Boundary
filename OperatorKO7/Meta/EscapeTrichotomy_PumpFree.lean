import OperatorKO7.Meta.EscapeTrichotomy
import OperatorKO7.Meta.BarrierPumpDischarge
import OperatorKO7.Meta.MatrixBarrierNatural

/-!
# Escape Trichotomy, Pump-Free

`Meta/EscapeTrichotomy.lean` states its universe over pumped families
(`AffineMeasureWithPump`, `QuadraticCounterMeasureWithPump`, and the rest),
because at the time each family's barrier carried a growth premise. The wrapper
positivity fields already force unbounded range, so the premises are redundant
and the universe can be stated over the plain families.

This module restates both trichotomies over the pump-free universes and proves
`pumpFree_of_withPump`, so the new universe provably contains the old one. The
original statements are untouched and remain citable.

## Formal Scope

Each trichotomy is a case split over the enumerated representability type shown
in its theorem. No classification of methods outside that type is implied.
-/

namespace OperatorKO7.EscapeTrichotomyPumpFree

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.MetaConjectureBoundary
open OperatorKO7.DepthBarrier
open OperatorKO7.PrecedenceBarrier
open OperatorKO7.EscapeTrichotomy

/-! ## The pump-free Nat-valued universe -/

/-- The Nat-valued direct universe with every growth premise discharged. The
affine, restricted-quadratic, and max-plus families are unconditional; the
cross-term, multilinear, and polynomial families keep only their base-point
dominance conditions, which are not growth premises. -/
inductive KO7NatDirectBarrierRepresentablePumpFree (μ : Trace → Nat) : Prop
  | additive (M : AdditiveCompositionalMeasure) (heval : M.eval = μ)
  | compositionalTransparent (CM : CompositionalMeasure)
      (htransparent : CM.c_delta CM.c_void = CM.c_void) (heval : CM.eval = μ)
  | affine (M : StepDuplicatingSchema.AffineMeasure ko7Schema)
      (heval : ∀ t : Trace, M.eval t = μ t)
  | quadratic (M : StepDuplicatingSchema.QuadraticCounterMeasure ko7Schema)
      (heval : ∀ t : Trace, M.eval t = μ t)
  | crossQuadraticBounded
      (M : StepDuplicatingSchema.CrossTermQuadraticMeasure ko7Schema)
      (hb : StepDuplicatingSchema.CrossTermBoundedAtBase M)
      (heval : ∀ t : Trace, M.eval t = μ t)
  | multilinearDominated
      (M : StepDuplicatingSchema.BoundedMultilinearMeasure ko7Schema)
      (hdom : StepDuplicatingSchema.MultilinearDominatedAtBase M)
      (heval : ∀ t : Trace, M.eval t = μ t)
  | polynomialDominated
      (M : StepDuplicatingSchema.BoundedPolynomialMeasure ko7Schema)
      (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase M)
      (heval : ∀ t : Trace, M.eval t = μ t)
  | max (M : StepDuplicatingSchema.MaxMeasure ko7Schema)
      (heval : ∀ t : Trace, M.eval t = μ t)
  | depth (M : MaxDepthMeasure) (heval : M.eval = μ)
  | precedence (M : HeadPrecedenceFamily) (heval : M.eval = μ)

/-- KO7 escape trichotomy over the pump-free Nat-valued universe. -/
theorem ko7_nat_direct_escape_trichotomy_pumpFree
    {μ : Trace → Nat}
    (horient : MetaConjectureBoundary.GlobalOrients μ (· < ·)) :
    ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema μ ∨
      ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema μ ∨
      ¬ KO7NatDirectBarrierRepresentablePumpFree μ := by
  classical
  by_cases hsub : StepDuplicatingSchema.WrapSubtermSensitive ko7Schema μ
  · by_cases htrans : StepDuplicatingSchema.TransparentAtBase ko7Schema μ
    · right
      right
      intro hrepr
      cases hrepr with
      | additive M heval =>
          subst heval
          exact (no_global_step_orientation_additive_compositional M) horient
      | compositionalTransparent CM htransparent heval =>
          subst heval
          exact
            (no_global_step_orientation_compositional_transparent_delta CM htransparent) horient
      | affine M heval =>
          have hrepr : M.eval = μ := by funext t; exact heval t
          subst hrepr
          exact
            (StepDuplicatingSchema.no_global_orients_affine (Sys := ko7System) M) horient
      | quadratic M heval =>
          have hrepr : M.eval = μ := by funext t; exact heval t
          subst hrepr
          exact (OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_quadratic M) horient
      | crossQuadraticBounded M hb heval =>
          have hrepr : M.eval = μ := by funext t; exact heval t
          subst hrepr
          exact
            (OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_cross_quadratic_of_bounded
              M hb) horient
      | multilinearDominated M hdom heval =>
          have hrepr : M.eval = μ := by funext t; exact heval t
          subst hrepr
          exact
            (OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_multilinear_of_dominated
              M hdom) horient
      | polynomialDominated M hdom heval =>
          have hrepr : M.eval = μ := by funext t; exact heval t
          subst hrepr
          exact
            (OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_polynomial_of_dominated
              M hdom) horient
      | max M heval =>
          have hrepr : M.eval = μ := by funext t; exact heval t
          subst hrepr
          exact (OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_max M) horient
      | depth M heval =>
          subst heval
          exact (no_global_step_orientation_maxDepth M) horient
      | precedence M heval =>
          subst heval
          exact (no_global_step_orientation_headPrecedenceFamily M) horient
    · right
      left
      exact htrans
  · left
    exact hsub

/-! ## The pump-free extended universe -/

/-- The explicit KO7 direct-orienter universe, widened with the two natural
matrix readings the certificate-free barrier covers. The componentwise and
Endrullis-Waldmann-Zantema constructors carry the tracked coordinate, because
the barrier for those orders is stated at a tracked coordinate and `Fin d` is
empty at `d = 0`. -/
inductive KO7DirectOrienterPumpFree where
  | nat (μ : Trace → Nat)
  | pairComponentwise (μ : Trace → StepDuplicatingSchema.Vec2)
  | pairLex (μ : Trace → StepDuplicatingSchema.Vec2)
  | vecComponentwise (d : Nat) (tracked : Fin d) (μ : Trace → Fin d → Nat)
  | vecEwz (d : Nat) (tracked : Fin d) (μ : Trace → Fin d → Nat)
  | vecLex (d : Nat) (μ : Trace → Fin (d + 1) → Nat)
  | vecPermLex (d : Nat) (σ : Equiv.Perm (Fin (d + 1))) (μ : Trace → Fin (d + 1) → Nat)

/-- The tracked primary scalar exposed by an orienter. -/
def KO7DirectOrienterPumpFree.primaryScalar : KO7DirectOrienterPumpFree → Trace → Nat
  | .nat μ => μ
  | .pairComponentwise μ => fun t => (μ t).1
  | .pairLex μ => fun t => (μ t).1
  | .vecComponentwise _ tracked μ => fun t => μ t tracked
  | .vecEwz _ tracked μ => fun t => μ t tracked
  | .vecLex d μ => fun t => μ t (StepDuplicatingSchema.primaryIdx d)
  | .vecPermLex _ σ μ => fun t => μ t (StepDuplicatingSchema.permPrimaryIdx σ)

/-- Orientation predicate for the widened orienter universe. -/
def KO7DirectOrienterPumpFree.Orients : KO7DirectOrienterPumpFree → Prop
  | .nat μ =>
      MetaConjectureBoundary.GlobalOrients μ (· < ·)
  | .pairComponentwise μ =>
      StepDuplicatingSchema.GlobalOrients ko7System μ StepDuplicatingSchema.PairLt
  | .pairLex μ =>
      StepDuplicatingSchema.GlobalOrients ko7System μ StepDuplicatingSchema.PairLexLt
  | .vecComponentwise _ _ μ =>
      StepDuplicatingSchema.GlobalOrients ko7System μ StepDuplicatingSchema.VecLt
  | .vecEwz _ tracked μ =>
      StepDuplicatingSchema.GlobalOrients ko7System μ
        (StepDuplicatingSchema.VecLeLt tracked)
  | .vecLex _ μ =>
      StepDuplicatingSchema.GlobalOrients ko7System μ StepDuplicatingSchema.VecLexLt
  | .vecPermLex _ σ μ =>
      StepDuplicatingSchema.GlobalOrients ko7System μ
        (StepDuplicatingSchema.VecPermLexLt σ)

/-- The pump-free extended universe: the ten scalar families, the two pair
families, the two lexicographic vector families, and the three natural matrix
readings that need no scalarization certificate. -/
inductive KO7DirectBarrierRepresentablePumpFree : KO7DirectOrienterPumpFree → Prop
  | additive (M : AdditiveCompositionalMeasure) :
      KO7DirectBarrierRepresentablePumpFree (.nat M.eval)
  | compositionalTransparent (CM : CompositionalMeasure)
      (htransparent : CM.c_delta CM.c_void = CM.c_void) :
      KO7DirectBarrierRepresentablePumpFree (.nat CM.eval)
  | affine (M : StepDuplicatingSchema.AffineMeasure ko7Schema) :
      KO7DirectBarrierRepresentablePumpFree (.nat M.eval)
  | quadratic (M : StepDuplicatingSchema.QuadraticCounterMeasure ko7Schema) :
      KO7DirectBarrierRepresentablePumpFree (.nat M.eval)
  | crossQuadraticBounded
      (M : StepDuplicatingSchema.CrossTermQuadraticMeasure ko7Schema)
      (hb : StepDuplicatingSchema.CrossTermBoundedAtBase M) :
      KO7DirectBarrierRepresentablePumpFree (.nat M.eval)
  | multilinearDominated
      (M : StepDuplicatingSchema.BoundedMultilinearMeasure ko7Schema)
      (hdom : StepDuplicatingSchema.MultilinearDominatedAtBase M) :
      KO7DirectBarrierRepresentablePumpFree (.nat M.eval)
  | polynomialDominated
      (M : StepDuplicatingSchema.BoundedPolynomialMeasure ko7Schema)
      (hdom : StepDuplicatingSchema.EventuallyDominatedAtBase M) :
      KO7DirectBarrierRepresentablePumpFree (.nat M.eval)
  | max (M : StepDuplicatingSchema.MaxMeasure ko7Schema) :
      KO7DirectBarrierRepresentablePumpFree (.nat M.eval)
  | depth (M : MaxDepthMeasure) :
      KO7DirectBarrierRepresentablePumpFree (.nat M.eval)
  | precedence (M : HeadPrecedenceFamily) :
      KO7DirectBarrierRepresentablePumpFree (.nat M.eval)
  | matrix2Componentwise (M : StepDuplicatingSchema.MatrixMeasure2 ko7Schema) :
      KO7DirectBarrierRepresentablePumpFree (.pairComponentwise M.eval)
  | matrix2LexOfFstPos (M : StepDuplicatingSchema.MatrixMeasure2 ko7Schema)
      (hpos : ∃ t : Trace, 1 ≤ (M.eval t).1) :
      KO7DirectBarrierRepresentablePumpFree (.pairLex M.eval)
  | matrixLexDOfPrimaryPos {d : Nat}
      (M : StepDuplicatingSchema.MatrixLexMeasureD ko7Schema d)
      (hpos : ∃ t : Trace, 1 ≤ M.eval t (StepDuplicatingSchema.primaryIdx d)) :
      KO7DirectBarrierRepresentablePumpFree (.vecLex d M.eval)
  | matrixLexPermDOfPrimaryPos {d : Nat}
      (M : StepDuplicatingSchema.MatrixLexPermMeasureD ko7Schema d)
      (hpos : ∃ t : Trace,
        1 ≤ M.eval t (StepDuplicatingSchema.permPrimaryIdx M.priority)) :
      KO7DirectBarrierRepresentablePumpFree (.vecPermLex d M.priority M.eval)
  | naturalMatrixComponentwise {d : Nat}
      (M : StepDuplicatingSchema.NatMatrixMeasure ko7Schema d) (i : Fin d)
      (hi : StepDuplicatingSchema.WrapDiagPositive M i) :
      KO7DirectBarrierRepresentablePumpFree (.vecComponentwise d i M.eval)
  | naturalMatrixEwz {d : Nat}
      (M : StepDuplicatingSchema.NatMatrixMeasure ko7Schema d) (tracked : Fin d)
      (hi : StepDuplicatingSchema.WrapDiagPositive M tracked) :
      KO7DirectBarrierRepresentablePumpFree (.vecEwz d tracked M.eval)
  | naturalMatrixLexDOfPrimaryPos {d : Nat}
      (M : StepDuplicatingSchema.NatMatrixMeasure ko7Schema (d + 1))
      (hi : StepDuplicatingSchema.WrapDiagPositive M
        (StepDuplicatingSchema.primaryIdx d))
      (hpos : ∃ t : Trace, 1 ≤ M.eval t (StepDuplicatingSchema.primaryIdx d)) :
      KO7DirectBarrierRepresentablePumpFree (.vecLex d M.eval)

/-- Extended KO7 escape trichotomy over the pump-free universe. -/
theorem ko7_direct_escape_trichotomy_pumpFree
    {O : KO7DirectOrienterPumpFree}
    (horient : O.Orients) :
    ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema O.primaryScalar ∨
      ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema O.primaryScalar ∨
      ¬ KO7DirectBarrierRepresentablePumpFree O := by
  classical
  by_cases hsub :
      StepDuplicatingSchema.WrapSubtermSensitive ko7Schema O.primaryScalar
  · by_cases htrans :
        StepDuplicatingSchema.TransparentAtBase ko7Schema O.primaryScalar
    · right
      right
      intro hrepr
      cases hrepr with
      | additive M =>
          exact (no_global_step_orientation_additive_compositional M) horient
      | compositionalTransparent CM htransparent =>
          exact
            (no_global_step_orientation_compositional_transparent_delta CM htransparent) horient
      | affine M =>
          exact
            (StepDuplicatingSchema.no_global_orients_affine (Sys := ko7System) M) horient
      | quadratic M =>
          exact (OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_quadratic M) horient
      | crossQuadraticBounded M hb =>
          exact
            (OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_cross_quadratic_of_bounded
              M hb) horient
      | multilinearDominated M hdom =>
          exact
            (OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_multilinear_of_dominated
              M hdom) horient
      | polynomialDominated M hdom =>
          exact
            (OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_polynomial_of_dominated
              M hdom) horient
      | max M =>
          exact (OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_max M) horient
      | depth M =>
          exact (no_global_step_orientation_maxDepth M) horient
      | precedence M =>
          exact (no_global_step_orientation_headPrecedenceFamily M) horient
      | matrix2Componentwise M =>
          exact (OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_matrix2 M) horient
      | matrix2LexOfFstPos M hpos =>
          exact
            (OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_matrix2_lex_of_fst_pos
              M hpos) horient
      | matrixLexDOfPrimaryPos M hpos =>
          exact
            (OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_matrixLexD_of_primary_pos
              M hpos) horient
      | matrixLexPermDOfPrimaryPos M hpos =>
          exact
            (OperatorKO7.BarrierPumpDischarge.no_global_step_orientation_matrixLexPermD_of_primary_pos
              M hpos) horient
      | naturalMatrixComponentwise M i hi =>
          exact
            (OperatorKO7.MatrixBarrierNatural.no_global_step_orientation_naturalMatrix_componentwise
              M hi) horient
      | naturalMatrixEwz M tracked hi =>
          exact
            (OperatorKO7.MatrixBarrierNatural.no_global_step_orientation_naturalMatrix_ewz M hi)
              horient
      | naturalMatrixLexDOfPrimaryPos M hi hpos =>
          exact
            (OperatorKO7.MatrixBarrierNatural.no_global_step_orientation_naturalMatrix_lexD_of_primary_pos
              M hi hpos) horient
    · right
      left
      exact htrans
  · left
    exact hsub

/-! ## The pump-free universe contains the pumped one -/

/-- Every pumped family is a plain family with its pump field forgotten, so the
pump-free universe of `ko7_nat_direct_escape_trichotomy_pumpFree` is provably at
least as wide as the pumped universe of `ko7_nat_direct_escape_trichotomy`. -/
theorem pumpFree_of_withPump {μ : Trace → Nat}
    (h : KO7NatDirectBarrierRepresentable μ) :
    KO7NatDirectBarrierRepresentablePumpFree μ := by
  cases h with
  | additive M heval =>
      exact .additive M heval
  | compositionalTransparent CM htransparent heval =>
      exact .compositionalTransparent CM htransparent heval
  | affineWithPump M heval =>
      exact .affine M.toAffineMeasure heval
  | quadraticWithPump M heval =>
      exact .quadratic M.toQuadraticCounterMeasure heval
  | crossQuadraticWithPump M heval =>
      exact .crossQuadraticBounded M.toCrossTermQuadraticMeasure M.h_bounded heval
  | multilinearWithPump M heval =>
      exact .multilinearDominated M.toBoundedMultilinearMeasure M.h_dominated heval
  | polynomialWithPump M heval =>
      exact .polynomialDominated M.toBoundedPolynomialMeasure M.h_dominated heval
  | maxWithPump M heval =>
      exact .max M.toMaxMeasure heval
  | depth M heval =>
      exact .depth M heval
  | precedence M heval =>
      exact .precedence M heval

end OperatorKO7.EscapeTrichotomyPumpFree
