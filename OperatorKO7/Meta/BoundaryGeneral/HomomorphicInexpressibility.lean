import Mathlib

set_option autoImplicit false

/-!
# Homomorphic inexpressibility for finitary term languages

This module supplies the algebraic interface missing from the historical
collapse records.  A signature has explicitly finite arities, an algebra
interprets every operation, and an algebra homomorphism carries a proof that it
preserves every interpretation.  Evaluation is natural with respect to such a
homomorphism.

The obstruction theorem is interface-relative: if a homomorphism identifies a
pair on which a predicate holds, fixes the selected truth token, and the
predicate fails on the image pair, then no single term over the declared
signature defines that predicate by equality with the truth token.

Audit scope (LASOT): this is a theorem about free terms and algebra
homomorphisms, not a rewriting, normalization, termination, or confluence
statement.
-/

namespace OperatorKO7.Meta.BoundaryGeneral.HomomorphicInexpressibility

universe u v w x y z

/-- A single-sorted finitary signature. -/
structure FinitarySignature where
  Op : Type u
  arity : Op -> Nat

/-- An algebra for a finitary signature. -/
structure FinitaryAlgebra (S : FinitarySignature.{u}) where
  Carrier : Type v
  interp : (o : S.Op) -> (Fin (S.arity o) -> Carrier) -> Carrier

/-- A proof-carrying homomorphism between two algebras for the same signature. -/
structure AlgebraHom
    {S : FinitarySignature.{u}}
    (A : FinitaryAlgebra.{u, v} S)
    (B : FinitaryAlgebra.{u, w} S) where
  toFun : A.Carrier -> B.Carrier
  map_op : ∀ (o : S.Op) (args : Fin (S.arity o) -> A.Carrier),
    toFun (A.interp o args) =
      B.interp o (fun i => toFun (args i))

/-- Free terms over a finitary signature and a variable carrier. -/
inductive FreeTerm
    (S : FinitarySignature.{u}) (V : Type x) : Type (max u x) where
| var : V -> FreeTerm S V
| op : (o : S.Op) ->
    (Fin (S.arity o) -> FreeTerm S V) -> FreeTerm S V

namespace FreeTerm

/-- Evaluate a free term under a valuation into an algebra. -/
def eval
    {S : FinitarySignature.{u}}
    {V : Type x}
    (A : FinitaryAlgebra.{u, w} S)
    (rho : V -> A.Carrier) : FreeTerm S V -> A.Carrier
| .var x => rho x
| .op o args => A.interp o (fun i => eval A rho (args i))

/-- Simultaneous substitution of free terms for variables. -/
def bind
    {S : FinitarySignature.{u}}
    {V : Type x} {W : Type y}
    (sigma : V -> FreeTerm S W) : FreeTerm S V -> FreeTerm S W
  | .var x => sigma x
  | .op operation args =>
      .op operation (fun i => bind sigma (args i))

/-- Composition of two substitutions, stated pointwise. -/
def substitutionComposition
    {S : FinitarySignature.{u}}
    {V : Type x} {W : Type y} {U : Type z}
    (tau : W -> FreeTerm S U) (sigma : V -> FreeTerm S W) :
    V -> FreeTerm S U :=
  fun x => bind tau (sigma x)

/-- Substitution composition is represented by iterated `bind`. -/
theorem bind_bind
    {S : FinitarySignature.{u}}
    {V : Type x} {W : Type y} {U : Type z}
    (tau : W -> FreeTerm S U) (sigma : V -> FreeTerm S W)
    (t : FreeTerm S V) :
    bind tau (bind sigma t) =
      bind (substitutionComposition tau sigma) t := by
  induction t with
  | var x => rfl
  | op operation args ih =>
      apply congrArg (fun branches => FreeTerm.op operation branches)
      funext i
      exact ih i

/-- Evaluation after substitution equals evaluation under the induced
valuation. -/
theorem eval_bind
    {S : FinitarySignature.{u}}
    {V : Type x} {W : Type y}
    (A : FinitaryAlgebra.{u, w} S)
    (rho : W -> A.Carrier) (sigma : V -> FreeTerm S W)
    (t : FreeTerm S V) :
    eval A rho (bind sigma t) =
      eval A (fun x => eval A rho (sigma x)) t := by
  induction t with
  | var x => rfl
  | op operation args ih =>
      change
        A.interp operation
            (fun i => eval A rho (bind sigma (args i))) =
          A.interp operation
            (fun i =>
              eval A (fun x => eval A rho (sigma x))
                (args i))
      apply congrArg (A.interp operation)
      funext i
      exact ih i

/-- Evaluation commutes with every proof-carrying algebra homomorphism. -/
theorem eval_natural
    {S : FinitarySignature.{u}}
    {V : Type x}
    {A : FinitaryAlgebra.{u, v} S}
    {B : FinitaryAlgebra.{u, w} S}
    (h : AlgebraHom A B)
    (t : FreeTerm S V)
    (rho : V -> A.Carrier) :
    h.toFun (eval A rho t) =
      eval B (fun x => h.toFun (rho x)) t := by
  induction t with
  | var x => rfl
  | op o args ih =>
      change
        h.toFun (A.interp o (fun i => eval A rho (args i))) =
          B.interp o
            (fun i => eval B (fun x => h.toFun (rho x)) (args i))
      calc
        h.toFun (A.interp o (fun i => eval A rho (args i))) =
            B.interp o (fun i => h.toFun (eval A rho (args i))) :=
          h.map_op o (fun i => eval A rho (args i))
        _ = B.interp o
              (fun i => eval B (fun x => h.toFun (rho x)) (args i)) := by
          apply congrArg (B.interp o)
          funext i
          exact ih i

end FreeTerm

/-- The two variable positions of a binary term definition. -/
inductive BinaryVar where
| left
| right
deriving DecidableEq, Fintype, Repr

/-- Valuation assigning the two inputs to the two binary variable positions. -/
def binaryVal {A : Type v} (a b : A) : BinaryVar -> A
| .left => a
| .right => b

/-- A term defines a binary predicate when evaluation equals the declared truth
token exactly on the predicate's positive instances. -/
def TermDefinesBinaryPredicate
    {S : FinitarySignature.{u}}
    (A : FinitaryAlgebra.{u, v} S)
    (truth : A.Carrier)
    (P : A.Carrier -> A.Carrier -> Prop) : Prop :=
  ∃ t : FreeTerm S BinaryVar,
    ∀ a b : A.Carrier,
      FreeTerm.eval A (binaryVal a b) t = truth ↔ P a b

/-- Proof-carrying homomorphic obstruction for a binary predicate. The
operation-preservation laws are carried by `hom`; `distinct` records
non-vacuity independently of the predicate-separation fields. -/
structure HomomorphicPredicateObstruction
    {S : FinitarySignature.{u}}
    (A : FinitaryAlgebra.{u, v} S)
    (truth : A.Carrier)
    (P : A.Carrier -> A.Carrier -> Prop) where
  hom : AlgebraHom A A
  truth_fixed : hom.toFun truth = truth
  a : A.Carrier
  b : A.Carrier
  distinct : a ≠ b
  collapse : hom.toFun a = hom.toFun b
  target_at_pair : P a b
  target_fails_after_map : Not (P (hom.toFun a) (hom.toFun b))

/-- A projection factors through a homomorphism when a post-map reconstructs
the projection on every source element. This is a composition equation, not a
name-only factorization claim. -/
def ProjectionFactorsThrough
    {S : FinitarySignature.{u}}
    {A : FinitaryAlgebra.{u, v} S}
    {B : FinitaryAlgebra.{u, w} S}
    (h : AlgebraHom A B) {Z : Type x}
    (projection : A.Carrier -> Z) : Prop :=
  ∃ decode : B.Carrier -> Z,
    ∀ source, decode (h.toFun source) = projection source

/-- A pair identified by a genuine algebra homomorphism but separated by a
projection prevents that projection from factoring through the homomorphism. -/
theorem projection_not_factorsThrough_of_hom_collapse
    {S : FinitarySignature.{u}}
    {A : FinitaryAlgebra.{u, v} S}
    {B : FinitaryAlgebra.{u, w} S}
    {Z : Type x} {h : AlgebraHom A B}
    {projection : A.Carrier -> Z} {a b : A.Carrier}
    (collapse : h.toFun a = h.toFun b)
    (projection_separates : projection a ≠ projection b) :
    ¬ ProjectionFactorsThrough h projection := by
  rintro ⟨decode, hdecode⟩
  apply projection_separates
  calc
    projection a = decode (h.toFun a) := (hdecode a).symm
    _ = decode (h.toFun b) := congrArg decode collapse
    _ = projection b := hdecode b

/-- Generic homomorphic collapse criterion.  The theorem states all data that
perform work: a signature-preserving map, a fixed truth token, a positive source
pair, and failure of the predicate after applying the map. -/
theorem predicate_not_termDefinable_of_hom_collapse
    {S : FinitarySignature.{u}}
    {A : FinitaryAlgebra.{u, v} S}
    {truth : A.Carrier}
    {P : A.Carrier -> A.Carrier -> Prop}
    (h : AlgebraHom A A)
    (truth_fixed : h.toFun truth = truth)
    {a b : A.Carrier}
    (target_at_pair : P a b)
    (target_fails_after_map : ¬ P (h.toFun a) (h.toFun b)) :
    ¬ TermDefinesBinaryPredicate A truth P := by
  rintro ⟨t, ht⟩
  have hsource : FreeTerm.eval A (binaryVal a b) t = truth :=
    (ht a b).2 target_at_pair
  have hnatural := FreeTerm.eval_natural h t (binaryVal a b)
  have hvaluation :
      (fun x => h.toFun (binaryVal a b x)) =
        binaryVal (h.toFun a) (h.toFun b) := by
    funext x
    cases x <;> rfl
  rw [hvaluation] at hnatural
  have himage :
      FreeTerm.eval A (binaryVal (h.toFun a) (h.toFun b)) t = truth := by
    calc
      FreeTerm.eval A (binaryVal (h.toFun a) (h.toFun b)) t =
          h.toFun (FreeTerm.eval A (binaryVal a b) t) := hnatural.symm
      _ = h.toFun truth := congrArg h.toFun hsource
      _ = truth := truth_fixed
  exact target_fails_after_map ((ht (h.toFun a) (h.toFun b)).1 himage)

/-- Every proof-carrying obstruction rules out a term definition over its
declared signature and truth token. -/
theorem HomomorphicPredicateObstruction.not_termDefinable
    {S : FinitarySignature.{u}}
    {A : FinitaryAlgebra.{u, v} S}
    {truth : A.Carrier}
    {P : A.Carrier -> A.Carrier -> Prop}
    (O : HomomorphicPredicateObstruction A truth P) :
    Not (TermDefinesBinaryPredicate A truth P) :=
  predicate_not_termDefinable_of_hom_collapse
    O.hom O.truth_fixed O.target_at_pair O.target_fails_after_map

/-- Disequality specialization: a homomorphism that identifies a distinct pair
and fixes the truth token blocks term-definition of disequality. -/
theorem disequality_not_termDefinable_of_hom_collapse
    {S : FinitarySignature.{u}}
    {A : FinitaryAlgebra.{u, v} S}
    {truth : A.Carrier}
    (h : AlgebraHom A A)
    (truth_fixed : h.toFun truth = truth)
    {a b : A.Carrier}
    (a_ne_b : a ≠ b)
    (collapse : h.toFun a = h.toFun b) :
    ¬ TermDefinesBinaryPredicate A truth (fun x y => x ≠ y) :=
  predicate_not_termDefinable_of_hom_collapse h truth_fixed a_ne_b
    (fun hne => hne collapse)

end OperatorKO7.Meta.BoundaryGeneral.HomomorphicInexpressibility
