import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Pointed
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.NormalVerdictBreaker

/-!
# Universal `Fork3` embedding for exact terminal diagonals

Every exact terminal equality-witness diagonal is a pointed nonjoinable fork;
initiality therefore supplies a canonical injective `Fork3` map. Under the
additional one-step determined hypothesis, the relation on the exact three-point
image is relation-isomorphic to `Fork3Step`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u v w

/-- A relation isomorphism packages a carrier equivalence and a two-sided edge theorem. -/
structure RelIso {A : Type u} {B : Type v}
    (RA : A → A → Prop) (RB : B → B → Prop) where
  toEquiv : A ≃ B
  map_rel_iff : ∀ {x y}, RA x y ↔ RB (toEquiv x) (toEquiv y)

/-- Reverse a relation isomorphism. -/
noncomputable def RelIso.symm {A : Type u} {B : Type v}
    {RA : A → A → Prop} {RB : B → B → Prop}
    (e : RelIso RA RB) : RelIso RB RA where
  toEquiv := e.toEquiv.symm
  map_rel_iff := by
    intro x y
    simpa using (e.map_rel_iff (x := e.toEquiv.symm x) (y := e.toEquiv.symm y)).symm

/-- Compose relation isomorphisms. -/
noncomputable def RelIso.trans {A : Type u} {B : Type v} {C : Type w}
    {RA : A → A → Prop} {RB : B → B → Prop} {RC : C → C → Prop}
    (e₁ : RelIso RA RB) (e₂ : RelIso RB RC) : RelIso RA RC where
  toEquiv := e₁.toEquiv.trans e₂.toEquiv
  map_rel_iff := by
    intro x y
    exact e₁.map_rel_iff.trans e₂.map_rel_iff

/-- Package one exact terminal diagonal as a pointed nonjoinable fork. -/
def schemaPointedFork {T : Type u}
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) : PointedFork where
  Carrier := T
  R := S.R
  source := S.E a a
  equal := S.Z
  different := S.D a a
  toEqual := S.refl_rule a
  toDifferent := S.diff_rule a a
  verdicts_unjoinable := terminalDiagonal_verdicts_unjoinable S a hterm

/-- The canonical `Fork3` morphism into a terminal diagonal. -/
def fork3Embedding {T : Type u}
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) :
    PointedForkHom fork3Pointed (schemaPointedFork S a hterm) :=
  canonicalHom _

@[simp] theorem fork3Embedding_source {T : Type u}
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) :
    (fork3Embedding S a hterm).toFun .source = S.E a a := rfl

@[simp] theorem fork3Embedding_equal {T : Type u}
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) :
    (fork3Embedding S a hterm).toFun .equal = S.Z := rfl

@[simp] theorem fork3Embedding_different {T : Type u}
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) :
    (fork3Embedding S a hterm).toFun .different = S.D a a := rfl

/-- Roadmap-stable name for the canonical pointed-fork embedding supplied by
initiality. -/
def fork3_embedding_of_terminalDiagonal {T : Type u}
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) :
    PointedForkHom fork3Pointed (schemaPointedFork S a hterm) :=
  fork3Embedding S a hterm

/-- Every exact terminal diagonal literally contains an injective copy of `Fork3`. -/
theorem fork3Embedding_injective {T : Type u}
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) :
    Function.Injective (fork3Embedding S a hterm).toFun :=
  canonicalHom_injective _

/-- The canonical embedding preserves every canonical fork edge. -/
theorem fork3Embedding_preserves {T : Type u}
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) {x y : Fork3}
    (hxy : Fork3Step x y) :
    S.R ((fork3Embedding S a hterm).toFun x)
      ((fork3Embedding S a hterm).toFun y) :=
  (fork3Embedding S a hterm).map_rel hxy

/-- Roadmap-stable embedding injectivity theorem. -/
theorem fork3_embedding_injective {T : Type u}
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) :
    Function.Injective (fork3_embedding_of_terminalDiagonal S a hterm).toFun :=
  fork3Embedding_injective S a hterm

/-- Roadmap-stable edge-preservation theorem. -/
theorem fork3_embedding_preserves_edges {T : Type u}
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) {x y : Fork3}
    (hxy : Fork3Step x y) :
    S.R ((fork3_embedding_of_terminalDiagonal S a hterm).toFun x)
      ((fork3_embedding_of_terminalDiagonal S a hterm).toFun y) :=
  fork3Embedding_preserves S a hterm hxy

/-- The exact three-point image of the canonical embedding. The existential
witness is a proposition; the inverse equivalence below chooses that witness and
then uses the proved injectivity to show it is unique. -/
def LocalConeCarrier {T : Type u}
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) :=
  {t : T // ∃ x : Fork3, (fork3Embedding S a hterm).toFun x = t}

/-- Relation inherited from the ambient exact schema on the marked local cone. -/
def LocalConeStep {T : Type u}
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) :
    LocalConeCarrier S a hterm → LocalConeCarrier S a hterm → Prop :=
  fun x y => S.R x.1 y.1

/-- The three canonical states are carrier-equivalent to their exact image. -/
noncomputable def fork3EquivLocalCone {T : Type u}
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) :
    Fork3 ≃ LocalConeCarrier S a hterm where
  toFun x := ⟨(fork3Embedding S a hterm).toFun x, ⟨x, rfl⟩⟩
  invFun t := Classical.choose t.2
  left_inv x := by
    apply fork3Embedding_injective S a hterm
    exact Classical.choose_spec (show
      ∃ z : Fork3, (fork3Embedding S a hterm).toFun z =
        (fork3Embedding S a hterm).toFun x from
      (show LocalConeCarrier S a hterm from
        ⟨(fork3Embedding S a hterm).toFun x, ⟨x, rfl⟩⟩).2)
  right_inv t := by
    apply Subtype.ext
    exact Classical.choose_spec t.2

/-- Under one-step determinedness, an ambient edge between canonical image points
reflects back to the unique canonical `Fork3Step`. -/
theorem localCone_reflects_fork3 {T : Type u}
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a)
    (hdet : DiagonalDetermined S a)
    {x y : Fork3}
    (hxy : LocalConeStep S a hterm
      (fork3EquivLocalCone S a hterm x)
      (fork3EquivLocalCone S a hterm y)) :
    Fork3Step x y := by
  cases x with
  | source =>
      have hout := hdet hxy
      rcases hout with hEq | hDiff
      · have hy : y = Fork3.equal := by
          apply fork3Embedding_injective S a hterm
          simpa using hEq
        subst y
        exact Fork3Step.toEqual
      · have hy : y = Fork3.different := by
          apply fork3Embedding_injective S a hterm
          simpa using hDiff
        subst y
        exact Fork3Step.toDifferent
  | equal =>
      exact False.elim (hterm.equal_normal _ (by simpa using hxy))
  | different =>
      exact False.elim (hterm.different_normal _ (by simpa using hxy))

/-- Roadmap-stable reflection theorem. One-step reflection requires the
explicit determined-diagonal hypothesis and therefore does not overclaim for
arbitrary terminal diagonals. -/
theorem fork3_embedding_reflects_edges_of_determined {T : Type u}
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a)
    (hdet : DiagonalDetermined S a)
    {x y : Fork3}
    (hxy : S.R ((fork3_embedding_of_terminalDiagonal S a hterm).toFun x)
      ((fork3_embedding_of_terminalDiagonal S a hterm).toFun y)) :
    Fork3Step x y := by
  exact localCone_reflects_fork3 S a hterm hdet hxy

/-- The canonical embedding preserves the inherited local-cone relation. -/
theorem localCone_preserves_fork3 {T : Type u}
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a)
    {x y : Fork3} (hxy : Fork3Step x y) :
    LocalConeStep S a hterm
      (fork3EquivLocalCone S a hterm x)
      (fork3EquivLocalCone S a hterm y) :=
  fork3Embedding_preserves S a hterm hxy

/-- A determined terminal diagonal has exactly the canonical marked local cone,
up to carrier and relation isomorphism. This does not claim the ambient carrier
itself has three elements. -/
noncomputable def determined_terminal_diagonal_localCone_equiv_fork3
    {T : Type u} (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a)
    (hdet : DiagonalDetermined S a) :
    RelIso Fork3Step (LocalConeStep S a hterm) where
  toEquiv := fork3EquivLocalCone S a hterm
  map_rel_iff := by
    intro x y
    exact ⟨localCone_preserves_fork3 S a hterm,
      localCone_reflects_fork3 S a hterm hdet⟩

/-- Finite ambient carriers supporting a terminal diagonal have at least three
states. This is inherited from the universal nonjoinable-peak lower bound. -/
theorem terminalDiagonal_card_ge_three {T : Type u}
    [Fintype T] [DecidableEq T]
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) :
    3 ≤ Fintype.card T :=
  nonjoinable_peak_card_ge_three (S.refl_rule a) (S.diff_rule a a)
    (terminalDiagonal_verdicts_unjoinable S a hterm)

/-- Roadmap-stable finite exact-schema lower-bound name. -/
theorem finite_exactSchema_card_ge_three {T : Type u}
    [Fintype T] [DecidableEq T]
    (S : ExactDiagonalForkSchema T) (a : T)
    (hterm : TerminalDiagonal S a) :
    3 ≤ Fintype.card T :=
  terminalDiagonal_card_ge_three S a hterm

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
