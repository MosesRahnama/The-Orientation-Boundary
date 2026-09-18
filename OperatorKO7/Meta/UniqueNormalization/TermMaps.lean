import OperatorKO7.Meta.Rewriting.Rewrite

/-!
# Renaming symbols and variables in first-order terms

Campaign: `Roadmaps\klop\ROADMAP.md`, shared infrastructure for WP-K1 and WP-K2.
Definition freeze: `Roadmaps\klop\definitions.md` (D7, Definition 8).

Two structural maps on `Term sigma nu`, both needed downstream:

* `Term.mapSym f`, relabelling of function symbols along `f : sigma -> tau`.
  This is the term map `T_f` induced by a signature morphism, and it carries the
  constructor translation of `definitions.md` D7.
* `Term.mapVar g`, renaming of variables along `g : nu -> mu`. Renaming apart is
  what makes the two-substitution form of omega-unifiability (D4) expressible on
  a single variable type.

## Fidelity block (frozen `definitions.md`, D7, Definition 8)

> "A signature morphism between signatures Sigma = (F_Sigma, #_Sigma) and
> Theta = (F_Theta, #_Theta) is a function f : F_Sigma -> F_Theta such that
> #_Theta(f(G)) = #_Sigma(G). Each signature morphism f : Sigma -> Theta induces
> a map T_f : Ter(Sigma, X) -> Ter(Theta, X) given as
> T_f(F(t_1, ..., t_n)) = f(F)(T_f(t_1), ..., T_f(t_n)) and T_f(x) = x for x in X."

`Term.app` stores an arbitrary argument list. `ArityCorrect` checks its length
against the symbol's assigned arity and checks every argument recursively.
Arity-preserving symbol maps preserve and reflect this property. The ranked
term maps also commute with substitution.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.Rewriting

universe u u' u'' v v'

namespace Term

variable {sigma : Type u} {tau : Type u'} {nu : Type v} {mu : Type v'}

/-! ## Relabelling function symbols -/

mutual
/-- Relabel every function symbol along `f`. This is the term map `T_f` induced
by a signature morphism (frozen `definitions.md` D7, Definition 8). Uses the
auxiliary `mapSymList` so the nested recursion through the argument list is
structural. -/
def mapSym (f : sigma → tau) : Term sigma nu → Term tau nu
  | .var x => .var x
  | .app g args => .app (f g) (mapSymList f args)
/-- `mapSym` across an argument list. -/
def mapSymList (f : sigma → tau) : List (Term sigma nu) → List (Term tau nu)
  | [] => []
  | a :: as => mapSym f a :: mapSymList f as
end

@[simp] theorem mapSym_var (f : sigma → tau) (x : nu) :
    mapSym (nu := nu) f (.var x) = .var x := rfl
@[simp] theorem mapSym_app (f : sigma → tau) (g : sigma) (args : List (Term sigma nu)) :
    mapSym f (.app g args) = .app (f g) (mapSymList f args) := rfl
@[simp] theorem mapSymList_nil (f : sigma → tau) :
    mapSymList (nu := nu) f [] = [] := rfl
@[simp] theorem mapSymList_cons (f : sigma → tau) (a : Term sigma nu)
    (as : List (Term sigma nu)) :
    mapSymList f (a :: as) = mapSym f a :: mapSymList f as := rfl

/-- `mapSymList` is the `List.map` of `mapSym`. -/
theorem mapSymList_eq_map (f : sigma → tau) (args : List (Term sigma nu)) :
    mapSymList f args = args.map (mapSym f) := by
  induction args with
  | nil => simp
  | cons a as ih => simp [ih]

/-- Relabelling along the identity is the identity. -/
@[simp] theorem mapSym_id (t : Term sigma nu) : mapSym (nu := nu) (fun s => s) t = t := by
  induction t using Term.rec' with
  | hvar x => rfl
  | happ g args ih =>
      simp only [mapSym_app, mapSymList_eq_map]
      congr 1
      exact (List.map_congr_left ih).trans (List.map_id'' (fun _ => rfl) ..)

/-- Relabelling is functorial. -/
theorem mapSym_mapSym {rho : Type u''} (f : sigma → tau) (h : tau → rho)
    (t : Term sigma nu) : mapSym h (mapSym f t) = mapSym (fun s => h (f s)) t := by
  induction t using Term.rec' with
  | hvar x => rfl
  | happ g args ih =>
      simp only [mapSym_app, mapSymList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left (fun a ha => ih a ha)

/-- The relabelled image of a substitution: apply `mapSym f` to every value. -/
def mapSubstSym (f : sigma → tau) (s : Subst sigma nu) : Subst tau nu :=
  fun x => mapSym f (s x)

/-- Relabelling commutes with substitution. This is the substitutivity fact that
every step-transfer lemma of the constructor translation rests on. -/
theorem mapSym_apply (f : sigma → tau) (s : Subst sigma nu) (t : Term sigma nu) :
    mapSym f (Subst.apply s t) = Subst.apply (mapSubstSym f s) (mapSym f t) := by
  induction t using Term.rec' with
  | hvar x => rfl
  | happ g args ih =>
      simp only [Subst.apply_app, mapSym_app, Subst.applyList_eq_map,
        mapSymList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left (fun a ha => ih a ha)

/-- Relabelling preserves the application/variable distinction. -/
@[simp] theorem isApp_mapSym (f : sigma → tau) (t : Term sigma nu) :
    (mapSym f t).isApp = t.isApp := by
  cases t <;> rfl

/-! ## Renaming variables -/

mutual
/-- Rename every variable along `g`, leaving function symbols alone. -/
def mapVar (g : nu → mu) : Term sigma nu → Term sigma mu
  | .var x => .var (g x)
  | .app f args => .app f (mapVarList g args)
/-- `mapVar` across an argument list. -/
def mapVarList (g : nu → mu) : List (Term sigma nu) → List (Term sigma mu)
  | [] => []
  | a :: as => mapVar g a :: mapVarList g as
end

@[simp] theorem mapVar_var (g : nu → mu) (x : nu) :
    mapVar (sigma := sigma) g (.var x) = .var (g x) := rfl
@[simp] theorem mapVar_app (g : nu → mu) (f : sigma) (args : List (Term sigma nu)) :
    mapVar g (.app f args) = .app f (mapVarList g args) := rfl
@[simp] theorem mapVarList_nil (g : nu → mu) :
    mapVarList (sigma := sigma) g [] = [] := rfl
@[simp] theorem mapVarList_cons (g : nu → mu) (a : Term sigma nu)
    (as : List (Term sigma nu)) :
    mapVarList g (a :: as) = mapVar g a :: mapVarList g as := rfl

/-- `mapVarList` is the `List.map` of `mapVar`. -/
theorem mapVarList_eq_map (g : nu → mu) (args : List (Term sigma nu)) :
    mapVarList g args = args.map (mapVar g) := by
  induction args with
  | nil => simp
  | cons a as ih => simp [ih]

/-- Renaming commutes with substitution, with the source renaming `g` and the
result renaming `h` allowed to differ. The two renamings differ exactly in the
rename-apart argument: the left copy of a term is tagged by `Sum.inl` and the
right copy by `Sum.inr`, while both unified images are tagged the same way. -/
theorem apply_mapVar_of {g h : nu → mu} {s : Subst sigma nu} {r : Subst sigma mu}
    (hcompat : ∀ x, r (g x) = mapVar h (s x)) (t : Term sigma nu) :
    Subst.apply r (mapVar g t) = mapVar h (Subst.apply s t) := by
  induction t using Term.rec' with
  | hvar x => simpa using hcompat x
  | happ f args ih =>
      simp only [mapVar_app, Subst.apply_app, Subst.applyList_eq_map,
        mapVarList_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left (fun a ha => ih a ha)

/-- An injective renaming is injective on terms. Renaming apart therefore loses
no information, which is what makes the shared-variable form of
omega-unifiability faithful to the two-substitution definition D4. -/
theorem mapVar_injective {g : nu → mu} (hg : Function.Injective g) :
    Function.Injective (mapVar (sigma := sigma) g) := by
  -- Pointwise injectivity on an argument list, given the induction hypothesis
  -- for each member of that list.
  have hlist : ∀ (as : List (Term sigma nu)),
      (∀ a ∈ as, ∀ u : Term sigma nu, mapVar (sigma := sigma) g a = mapVar g u → a = u) →
      ∀ bs : List (Term sigma nu),
        as.map (mapVar g) = bs.map (mapVar g) → as = bs := by
    intro as
    induction as with
    | nil =>
        intro _ bs h
        cases bs with
        | nil => rfl
        | cons b bs => simp at h
    | cons a as ih =>
        intro hmem bs h
        cases bs with
        | nil => simp at h
        | cons b bs =>
            simp only [List.map_cons, List.cons.injEq] at h
            have ha := hmem a (by simp) b h.1
            have has := ih (fun x hx => hmem x (by simp [hx])) bs h.2
            rw [ha, has]
  have key : ∀ (t : Term sigma nu) (u : Term sigma nu),
      mapVar (sigma := sigma) g t = mapVar g u → t = u := by
    intro t
    induction t using Term.rec' with
    | hvar x =>
        intro u h
        cases u with
        | var y => simpa using hg (by simpa using h)
        | app f args => simp at h
    | happ f args ih =>
        intro u h
        cases u with
        | var y => simp at h
        | app f' args' =>
            simp only [mapVar_app, mapVarList_eq_map, Term.app.injEq] at h
            obtain ⟨hf, hargs⟩ := h
            subst hf
            exact congrArg _ (hlist args ih args' hargs)
  exact fun a b h => key a b h


/-! ## Ranked signatures -/

/-- Every application has its symbol's declared arity, recursively. -/
inductive ArityCorrect (arity : sigma → Nat) : Term sigma nu → Prop
  | var (x : nu) : ArityCorrect arity (.var x)
  | app (f : sigma) (args : List (Term sigma nu))
      (length_eq : args.length = arity f)
      (arguments : ∀ a ∈ args, ArityCorrect arity a) :
      ArityCorrect arity (.app f args)

@[simp] theorem arityCorrect_var (arity : sigma → Nat) (x : nu) :
    ArityCorrect arity (.var x) := ArityCorrect.var x

@[simp] theorem arityCorrect_app_iff (arity : sigma → Nat) (f : sigma)
    (args : List (Term sigma nu)) :
    ArityCorrect arity (.app f args) ↔
      args.length = arity f ∧ ∀ a ∈ args, ArityCorrect arity a := by
  constructor
  · intro h
    cases h with
    | app _ _ hn ha => exact ⟨hn, ha⟩
  · rintro ⟨hn, ha⟩
    exact ArityCorrect.app f args hn ha

/-- Arity-preserving symbol maps also reflect well-formedness; injectivity is
unnecessary for this statement. -/
theorem arityCorrect_mapSym_iff (sourceArity : sigma → Nat) (targetArity : tau → Nat)
    (f : sigma → tau) (hf : ∀ s, targetArity (f s) = sourceArity s)
    (t : Term sigma nu) :
    ArityCorrect targetArity (mapSym f t) ↔ ArityCorrect sourceArity t := by
  induction t using Term.rec' with
  | hvar x => simp
  | happ s args ih =>
      simp only [mapSym_app, mapSymList_eq_map, arityCorrect_app_iff,
        List.length_map, hf]
      constructor
      · rintro ⟨hn, ha⟩
        exact ⟨hn, fun a hmem =>
          (ih a hmem).1 (ha (mapSym f a) (List.mem_map_of_mem (f := mapSym f) hmem))⟩
      · rintro ⟨hn, ha⟩
        refine ⟨hn, ?_⟩
        intro b hb
        obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hb
        exact (ih a hmem).2 (ha a hmem)

/-- Any variable renaming preserves and reflects well-formedness. -/
theorem arityCorrect_mapVar_iff (arity : sigma → Nat) (g : nu → mu)
    (t : Term sigma nu) :
    ArityCorrect arity (mapVar g t) ↔ ArityCorrect arity t := by
  induction t using Term.rec' with
  | hvar x => simp
  | happ f args ih =>
      simp only [mapVar_app, mapVarList_eq_map, arityCorrect_app_iff, List.length_map]
      constructor
      · rintro ⟨hn, ha⟩
        exact ⟨hn, fun a hmem =>
          (ih a hmem).1 (ha (mapVar g a) (List.mem_map_of_mem (f := mapVar g) hmem))⟩
      · rintro ⟨hn, ha⟩
        refine ⟨hn, ?_⟩
        intro b hb
        obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hb
        exact (ih a hmem).2 (ha a hmem)

/-- Substitution is well-formed exactly when the source term and the images
of its occurring variables are well-formed. -/
theorem arityCorrect_apply_iff [DecidableEq nu] (arity : sigma → Nat)
    (s : Subst sigma nu) (t : Term sigma nu) :
    ArityCorrect arity (Subst.apply s t) ↔
      ArityCorrect arity t ∧ ∀ x ∈ vars t, ArityCorrect arity (s x) := by
  induction t using Term.rec' with
  | hvar x =>
      simp only [Subst.apply_var, vars_var, Finset.mem_singleton]
      constructor
      · intro hx
        refine ⟨ArityCorrect.var x, ?_⟩
        intro y hy
        subst y
        exact hx
      · intro h
        exact h.2 x rfl
  | happ f args ih =>
      simp only [Subst.apply_app, Subst.applyList_eq_map, arityCorrect_app_iff,
        List.length_map, vars_app]
      constructor
      · rintro ⟨hn, ha⟩
        have hall : ∀ a ∈ args, ArityCorrect arity a ∧
            ∀ x ∈ vars a, ArityCorrect arity (s x) :=
          fun a hmem => (ih a hmem).1
            (ha (Subst.apply s a) (List.mem_map_of_mem (f := Subst.apply s) hmem))
        refine ⟨⟨hn, fun a hmem => (hall a hmem).1⟩, ?_⟩
        intro x hx
        obtain ⟨a, hmem, hxa⟩ := mem_varsList_iff.mp hx
        exact (hall a hmem).2 x hxa
      · rintro ⟨⟨hn, ha⟩, hs⟩
        refine ⟨hn, ?_⟩
        intro b hb
        obtain ⟨a, hmem, rfl⟩ := List.mem_map.mp hb
        exact (ih a hmem).2
          ⟨ha a hmem, fun x hx => hs x (mem_varsList_iff.mpr ⟨a, hmem, hx⟩)⟩

theorem ArityCorrect.apply {arity : sigma → Nat} {s : Subst sigma nu}
    {t : Term sigma nu} (ht : ArityCorrect arity t)
    (hs : ∀ x, ArityCorrect arity (s x)) : ArityCorrect arity (Subst.apply s t) := by
  classical
  exact (arityCorrect_apply_iff arity s t).2 ⟨ht, fun x _ => hs x⟩

/-- Substitution cannot repair an incorrect application arity in its source. -/
theorem ArityCorrect.of_apply {arity : sigma → Nat} {s : Subst sigma nu}
    {t : Term sigma nu} (h : ArityCorrect arity (Subst.apply s t)) :
    ArityCorrect arity t := by
  classical
  exact (arityCorrect_apply_iff arity s t).1 h |>.1

/-- One application tests the declared arity of a symbol. -/
def arityProbe (arity : sigma → Nat) (f : sigma) : Term sigma Unit :=
  .app f (List.replicate (arity f) (.var ()))

theorem arityProbe_correct (arity : sigma → Nat) (f : sigma) :
    ArityCorrect arity (arityProbe arity f) := by
  apply ArityCorrect.app
  · exact List.length_replicate
  · intro a ha
    have he : a = (Term.var () : Term sigma Unit) := (List.mem_replicate.mp ha).2
    subst a
    exact ArityCorrect.var ()

/-- Preservation on these one-level terms already forces the signature law. -/
theorem arity_preserving_iff_probes (sourceArity : sigma → Nat)
    (targetArity : tau → Nat) (f : sigma → tau) :
    (∀ s, targetArity (f s) = sourceArity s) ↔
      ∀ s, ArityCorrect targetArity (mapSym f (arityProbe sourceArity s)) := by
  constructor
  · intro hf s
    exact (arityCorrect_mapSym_iff sourceArity targetArity f hf _).2
      (arityProbe_correct sourceArity s)
  · intro h s
    have hn := (arityCorrect_app_iff targetArity (f s)
      (mapSymList f (List.replicate (sourceArity s) (.var ())))).1 (h s) |>.1
    simpa only [mapSymList_eq_map, List.length_map, List.length_replicate] using hn.symm

theorem arity_preserving_iff_all_terms (sourceArity : sigma → Nat)
    (targetArity : tau → Nat) (f : sigma → tau) :
    (∀ s, targetArity (f s) = sourceArity s) ↔
      ∀ t : Term sigma Unit, ArityCorrect sourceArity t →
        ArityCorrect targetArity (mapSym f t) := by
  constructor
  · intro hf t ht
    exact (arityCorrect_mapSym_iff sourceArity targetArity f hf t).2 ht
  · intro h
    apply (arity_preserving_iff_probes sourceArity targetArity f).2
    intro s
    exact h _ (arityProbe_correct sourceArity s)

/-- Terms carrying their recursive arity proof. -/
def Ranked (arity : sigma → Nat) : Type (max u v) :=
  {t : Term sigma nu // ArityCorrect arity t}

def mapRankedSym (sourceArity : sigma → Nat) (targetArity : tau → Nat)
    (f : sigma → tau) (hf : ∀ s, targetArity (f s) = sourceArity s)
    (t : Ranked (nu := nu) sourceArity) : Ranked (nu := nu) targetArity :=
  ⟨mapSym f t.1, (arityCorrect_mapSym_iff sourceArity targetArity f hf t.1).2 t.2⟩

def mapRankedVar (arity : sigma → Nat) (g : nu → mu)
    (t : Ranked (nu := nu) arity) : Ranked (nu := mu) arity :=
  ⟨mapVar g t.1, (arityCorrect_mapVar_iff arity g t.1).2 t.2⟩

def applyRanked (arity : sigma → Nat) (s : nu → Ranked (nu := nu) arity)
    (t : Ranked (nu := nu) arity) : Ranked (nu := nu) arity :=
  ⟨Subst.apply (fun x => (s x).1) t.1, t.2.apply (fun x => (s x).2)⟩

@[simp] theorem mapRankedSym_id (arity : sigma → Nat)
    (t : Ranked (nu := nu) arity) :
    mapRankedSym arity arity id (fun _ => rfl) t = t := by
  apply Subtype.ext
  exact mapSym_id t.1

theorem mapRankedSym_comp {rho : Type u''}
    (a : sigma → Nat) (b : tau → Nat) (c : rho → Nat)
    (f : sigma → tau) (g : tau → rho)
    (hf : ∀ s, b (f s) = a s) (hg : ∀ s, c (g s) = b s)
    (t : Ranked (nu := nu) a) :
    mapRankedSym b c g hg (mapRankedSym a b f hf t) =
      mapRankedSym a c (fun s => g (f s))
        (fun s => (hg (f s)).trans (hf s)) t := by
  apply Subtype.ext
  exact mapSym_mapSym f g t.1

theorem mapRankedSym_applyRanked (a : sigma → Nat) (b : tau → Nat)
    (f : sigma → tau) (hf : ∀ s, b (f s) = a s)
    (s : nu → Ranked (nu := nu) a) (t : Ranked (nu := nu) a) :
    mapRankedSym a b f hf (applyRanked a s t) =
      applyRanked b (fun x => mapRankedSym a b f hf (s x)) (mapRankedSym a b f hf t) := by
  apply Subtype.ext
  exact mapSym_apply f (fun x => (s x).1) t.1

/-- Equal argument-list lengths do not imply that symbol arities agree. -/
theorem list_length_preservation_not_arity_preservation :
    (mapSymList (id : Unit → Unit) ([] : List (Term Unit Unit))).length = 0 ∧
    ArityCorrect (fun _ : Unit => 0) (Term.app () [] : Term Unit Unit) ∧
    ¬ ArityCorrect (fun _ : Unit => 1)
      (mapSym (id : Unit → Unit) (Term.app () [] : Term Unit Unit)) := by
  refine ⟨rfl, ArityCorrect.app () [] rfl (by simp), ?_⟩
  intro h
  have hbad : (0 : Nat) = 1 := (arityCorrect_app_iff _ _ _).1 h |>.1
  omega

end Term

end OperatorKO7.Meta.Rewriting

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.Rewriting.Term.mapSym
#check @OperatorKO7.Meta.Rewriting.Term.mapVar
#check @OperatorKO7.Meta.Rewriting.Term.mapSubstSym

#print axioms OperatorKO7.Meta.Rewriting.Term.mapSym_id
#print axioms OperatorKO7.Meta.Rewriting.Term.mapSym_mapSym
#print axioms OperatorKO7.Meta.Rewriting.Term.mapSym_apply
#print axioms OperatorKO7.Meta.Rewriting.Term.mapSymList_eq_map
#print axioms OperatorKO7.Meta.Rewriting.Term.mapVarList_eq_map
