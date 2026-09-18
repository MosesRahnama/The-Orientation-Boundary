import OperatorKO7.Meta.DistinctionBoundary.GodelAcceptableNumbering

set_option autoImplicit false

/-!
# One-parameter specialization on the extended partial-code interpreter

The extended carrier `AccCode` already contains three pieces needed for a
Kleene-style specialization interface:

* `.cons a` builds the application pair `app a x`;
* `.apply` interprets an embedded `PartialCode` from such a pair;
* `.compose` composes these programs.

The compiler below specializes a binary `PartialCode e` at a fixed first Trace
argument `x`. Its generated `AccCode` maps `y` to the behavior of `e` on
`Trace.app x y`. This is a genuine semantic s-m-n theorem for the declared
interface `PartialCode × Trace → AccCode`; it does not claim a self-specializer
for arbitrary `AccCode` syntax.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelPartial

/-- Successful `AccCode` evaluation is monotone in the fuel budget. -/
theorem stepAcc_mono {n m : Nat} {c : AccCode} {x v : Trace}
    (hle : n ≤ m) (h : stepAcc n c x = some v) :
    stepAcc m c x = some v := by
  induction n generalizing m c x v with
  | zero => cases h
  | succ n ih =>
      cases m with
      | zero => exact (Nat.not_succ_le_zero n hle).elim
      | succ m =>
        have hnm : n ≤ m := Nat.le_of_succ_le_succ hle
        cases c with
        | embed c =>
            exact step_mono hle h
        | apply =>
            cases x with
            | app a b =>
                exact ih (m := m) (c := .embed (quote a)) (x := b)
                  (v := v) hnm h
            | void => cases h
            | delta _ => cases h
            | integrate _ => cases h
            | merge _ _ => cases h
            | recΔ _ _ _ => cases h
            | eqW _ _ => cases h
        | cons a => exact h
        | compose f g =>
            cases hg : stepAcc n g x with
            | none =>
                have h' : (stepAcc n g x).bind (stepAcc n f) = some v := h
                rw [hg] at h'
                cases h'
            | some u =>
                have hf : stepAcc n f u = some v := by
                  have h' : (stepAcc n g x).bind (stepAcc n f) = some v := h
                  rw [hg] at h'
                  exact h'
                have hg' : stepAcc m g x = some u := ih hnm hg
                have hf' : stepAcc m f u = some v := ih hnm hf
                change (stepAcc m g x).bind (stepAcc m f) = some v
                rw [hg']
                exact hf'

/-- The extended interpreter is deterministic at convergent outputs. -/
theorem convergesToAcc_unique {c : AccCode} {x v w : Trace}
    (hv : convergesToAcc c x v) (hw : convergesToAcc c x w) : v = w := by
  obtain ⟨n, hn⟩ := hv
  obtain ⟨m, hm⟩ := hw
  cases Nat.le_total n m with
  | inl hle =>
      have hn' := stepAcc_mono hle hn
      injection (hn'.symm.trans hm)
  | inr hle =>
      have hm' := stepAcc_mono hle hm
      injection (hn.symm.trans hm')

/-- Semantic composition rule for the extended code carrier. -/
theorem convergesToAcc_compose_iff (f g : AccCode) (x v : Trace) :
    convergesToAcc (.compose f g) x v ↔
      ∃ u : Trace, convergesToAcc g x u ∧ convergesToAcc f u v := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => cases hn
    | succ n =>
        change (stepAcc n g x).bind (stepAcc n f) = some v at hn
        cases hg : stepAcc n g x with
        | none => rw [hg] at hn; cases hn
        | some u =>
            rw [hg] at hn
            exact ⟨u, ⟨n, hg⟩, ⟨n, hn⟩⟩
  · rintro ⟨u, ⟨ng, hg⟩, ⟨nf, hf⟩⟩
    let n := max ng nf
    have hg' : stepAcc n g x = some u :=
      stepAcc_mono (Nat.le_max_left ng nf) hg
    have hf' : stepAcc n f u = some v :=
      stepAcc_mono (Nat.le_max_right ng nf) hf
    refine ⟨n + 1, ?_⟩
    change (stepAcc n g x).bind (stepAcc n f) = some v
    rw [hg']
    exact hf'

/-- Pair a fixed Trace with the future argument. -/
def pairFixedAcc (x : Trace) : AccCode := .cons x

/-- Specialize one argument of a partial code. The generated code performs
`y ↦ e (app x y)`. -/
def compile1 (e : PartialCode) (x : Trace) : AccCode :=
  .compose .apply (.compose (.cons (encode e)) (.cons x))

/-- First half of the specialization pipeline constructs the nested application
`app (encode e) (app x y)`. -/
theorem compile1_pair_stage (e : PartialCode) (x y : Trace) :
    convergesToAcc (.compose (.cons (encode e)) (.cons x)) y
      (Trace.app (encode e) (Trace.app x y)) := by
  rw [convergesToAcc_compose_iff]
  refine ⟨Trace.app x y, cons_pairs x y, ?_⟩
  exact cons_pairs (encode e) (Trace.app x y)

/-- Genuine one-parameter s-m-n theorem for the declared source/target
interface. -/
theorem compile1_smn (e : PartialCode) (x y v : Trace) :
    convergesToAcc (compile1 e x) y v ↔
      convergesTo e (Trace.app x y) v := by
  unfold compile1
  rw [convergesToAcc_compose_iff]
  constructor
  · rintro ⟨u, hu, happ⟩
    have hpair := compile1_pair_stage e x y
    have huEq : u = Trace.app (encode e) (Trace.app x y) :=
      convergesToAcc_unique hu hpair
    subst u
    exact (apply_is_universal e (Trace.app x y) v).1 happ
  · intro h
    refine ⟨Trace.app (encode e) (Trace.app x y),
      compile1_pair_stage e x y, ?_⟩
    exact (apply_is_universal e (Trace.app x y) v).2 h

/-- Acceptability of the declared relative numbering interface: a universal
interpreter for every `PartialCode` and a total one-parameter compiler into
`AccCode`. -/
structure AccCodeAcceptable : Prop where
  universal : InterpretsPartialCode .apply
  smn : ∀ e : PartialCode, ∀ x y v : Trace,
    convergesToAcc (compile1 e x) y v ↔
      convergesTo e (Trace.app x y) v

/-- The extended carrier is acceptable for the declared `PartialCode × Trace`
specialization interface. -/
theorem accCode_acceptable : AccCodeAcceptable where
  universal := apply_interprets_partialCode
  smn := compile1_smn

#check @stepAcc_mono
#check @convergesToAcc_unique
#check @convergesToAcc_compose_iff
#check @compile1
#check @compile1_pair_stage
#check @compile1_smn
#check @AccCodeAcceptable
#check @accCode_acceptable
#print axioms stepAcc_mono
#print axioms convergesToAcc_unique
#print axioms convergesToAcc_compose_iff
#print axioms compile1_pair_stage
#print axioms compile1_smn
#print axioms accCode_acceptable

end OperatorKO7.Meta.DistinctionBoundary.GodelPartial
