import OperatorKO7.Meta.UniqueNormalization.ProofGraph
import Mathlib.Data.Finset.Prod

/-!
# Lemma 52

Campaign: `Roadmaps\klop\ROADMAP.md`, wave 6. Source: Kahrs and Smith, FSCD 2016,
Lemma 52, transcribed in `Roadmaps\klop\definitions.md` at D14 with amendment A4.

## Fidelity block (frozen `definitions.md`, D14, Lemma 52)

> "Let rho be a proof graph. Let ->_beta subset of rho-grey such that ->_beta is
> deterministic and terminating, and let =_beta be the equivalence closure of
> ->_beta. Then =_beta subset of down_A."

> "Proof. If t =_beta u we must have an s in A with t ->*_beta s and u ->*_beta s,
> because ->_beta is deterministic and terminating. We prove this by induction on
> the number of ->_beta steps. Moreover, we strengthen the claim by requiring that
> if t hat-id_A t and u hat-id_A u then t hat-=_rho u."

The strengthened claim is the second component of `Lemma52Claim`. It carries the
constructor-tilde case, where there is no transitivity to appeal to: two
constructor-tilde steps compose into one because `=_rho` is transitive.

The case order is the source's. A root contraction or a destructor tilde out of
either endpoint is peeled first. Only when neither endpoint carries such an edge
are both endpoints constructor-topped, and that is what amendment A4 delivers.

Trust: kernel-only; no `sorry`, `admit`, `axiom`, `native_decide`, `partial`,
`unsafe`, or `opaque`. Axiom footprint reported at the end of the file.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u v

variable {sigma : Type u} {nu : Type v}

/-! ## Chain inversion and roots -/

theorem ReachN.zero_inv {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {a b : Term (sigma ⊕ sigma) nu} (h : ReachN g 0 a b) : a = b := by
  cases h with
  | refl => rfl

theorem ReachN.succ_inv {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {n : Nat} {a b : Term (sigma ⊕ sigma) nu} (h : ReachN g (n + 1) a b) :
    ∃ c, g a = some c ∧ ReachN g n c b := by
  cases h with
  | head hedge htail => exact ⟨_, hedge, htail⟩

/-- Termination gives every node a root. -/
theorem exists_root {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hwf : Terminating g) (x : Term (sigma ⊕ sigma) nu) :
    ∃ r, Reach g x r ∧ g r = none := by
  induction x using hwf.induction with
  | _ x ih =>
      cases hx : g x with
      | none => exact ⟨x, Reach.refl x, hx⟩
      | some y =>
          obtain ⟨r, hr, hnr⟩ := ih y hx
          exact ⟨r, Reach.head hx hr, hnr⟩

/-! ## The two halves of one peeling step -/

/-- A constructor tilde of a graph's equivalence is part of the invariant. -/
theorem downOn_of_hatEq {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (h : hatEq (EqvOn A rho.par) a b) : DownOn A R a b := by
  rcases h with ⟨x, rfl, rfl⟩ | ⟨f, as, bs, ⟨c, rfl⟩, rfl, rfl, hall⟩
  · exact DownOn.refl ha
  · exact DownOn.hatCl ha hb (forall₂_mono (fun _ _ hx => rho.sub hx) hall)

/-- Peeling a root contraction or a destructor tilde off the front of a chain. -/
theorem downOn_peel {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {p c q : Term (sigma ⊕ sigma) nu} (hp : p ∈ A) (hc : c ∈ A)
    (hkind : rootStep R p c ∨ barRel (DownOn A R) p c)
    (hcq : DownOn A R c q) : DownOn A R p q := by
  rcases hkind with hroot | hbar
  · exact DownOn.rootComp hp hc hroot hcq
  · obtain ⟨f, as, cs, ⟨d, rfl⟩, rfl, rfl, hall⟩ := hbar
    exact DownOn.barComp hp hall hcq

/-- Such an edge has a destructor-headed source, so the strengthened claim is
vacuous there. -/
theorem not_conTopped_peel {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {p c : Term (sigma ⊕ sigma) nu}
    (hkind : rootStep R p c ∨ barRel (DownOn A R) p c) : ¬ ConTopped p := by
  rcases hkind with hroot | hbar
  · obtain ⟨d, args, rfl⟩ := rootStep_source_destructor hR hroot
    exact not_conTopped_destructor args
  · obtain ⟨f, as, cs, ⟨d, rfl⟩, rfl, -, -⟩ := hbar
    exact not_conTopped_destructor as

/-- The claim on the diagonal. -/
theorem lemma52_diag {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R)
    {x : Term (sigma ⊕ sigma) nu} (hx : x ∈ A) :
    DownOn A R x x ∧
      (ConTopped x → ConTopped x → hatEq (EqvOn A rho.par) x x) := by
  refine ⟨DownOn.refl hx, fun hcx _ => ?_⟩
  rcases hcx with ⟨z, hz⟩ | ⟨f, args, hf⟩
  · exact Or.inl ⟨z, hz, hz⟩
  · subst hf
    refine Or.inr ⟨.inl f, args, args, ⟨f, rfl⟩, rfl, rfl, forall₂_self_of ?_⟩
    intro z hz
    exact EqvOn.refl (Coalgebra.arg hA hx hz)

/-! ## Lemma 52 -/

/-- **Lemma 52.** A deterministic terminating subrelation of the grey edges has
its equivalence closure inside the invariant, and its constructor-topped pairs
inside the constructor tilde of the graph's own equivalence. -/
theorem lemma52 {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R) (rho : PGraph A R)
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hgterm : Terminating g)
    (hgmem : ∀ {a b : Term (sigma ⊕ sigma) nu}, g a = some b → a ∈ A ∧ b ∈ A)
    (hgrey : ∀ {a b : Term (sigma ⊕ sigma) nu}, g a = some b →
      Grey A R (EqvOn A rho.par) a b)
    {t u : Term (sigma ⊕ sigma) nu} (h : EqvOn A g t u) :
    DownOn A R t u ∧
      (ConTopped t → ConTopped u → hatEq (EqvOn A rho.par) t u) := by
  classical
  obtain ⟨htA, huA, s₀, hts₀, hus₀⟩ := h
  obtain ⟨s, hs₀s, hsroot⟩ := exists_root hgterm s₀
  obtain ⟨m, hm⟩ := (hts₀.trans hs₀s).toReachN
  obtain ⟨n, hn⟩ := (hus₀.trans hs₀s).toReachN
  have key : ∀ N : Nat, ∀ (i j : Nat) (x y : Term (sigma ⊕ sigma) nu),
      i + j ≤ N → x ∈ A → y ∈ A → ReachN g i x s → ReachN g j y s →
      DownOn A R x y ∧
        (ConTopped x → ConTopped y → hatEq (EqvOn A rho.par) x y) := by
    intro N
    induction N with
    | zero =>
        intro i j x y hle hx hy hix hjy
        have hi : i = 0 := by omega
        have hj : j = 0 := by omega
        subst hi; subst hj
        have hxs : x = s := hix.zero_inv
        have hys : y = s := hjy.zero_inv
        subst hxs
        subst hys
        exact lemma52_diag hA rho hx
    | succ N ih =>
        intro i j x y hle hx hy hix hjy
        have swap : ∀ p q : Term (sigma ⊕ sigma) nu,
            (DownOn A R p q ∧ (ConTopped p → ConTopped q →
              hatEq (EqvOn A rho.par) p q)) →
            (DownOn A R q p ∧ (ConTopped q → ConTopped p →
              hatEq (EqvOn A rho.par) q p)) :=
          fun p q hpq => ⟨DownOn.symm hpq.1, fun hq hp =>
            hatEq.symm (fun _ _ hxy => EqvOn.symm hxy) (hpq.2 hp hq)⟩
        -- a node with a peelable edge has a nonzero chain to the root
        have nonzero : ∀ (k : Nat) (p c : Term (sigma ⊕ sigma) nu),
            ReachN g k p s → g p = some c → ∃ k', k = k' + 1 := by
          intro k p c hkp hpc
          cases k with
          | zero =>
              rw [hkp.zero_inv] at hpc
              rw [hsroot] at hpc
              exact absurd hpc (by simp)
          | succ k' => exact ⟨k', rfl⟩
        by_cases hpx : ∃ c, g x = some c ∧ (rootStep R x c ∨ barRel (DownOn A R) x c)
        · obtain ⟨c, hxc, hkind⟩ := hpx
          obtain ⟨i', rfl⟩ := nonzero i x c hix hxc
          obtain ⟨c', hxc', htail⟩ := hix.succ_inv
          have hcc : c = c' := Option.some.inj (hxc.symm.trans hxc')
          subst hcc
          have hcA : c ∈ A := (hgmem hxc).2
          have hrec := ih i' j c y (by omega) hcA hy htail hjy
          exact ⟨downOn_peel hx hcA hkind hrec.1,
            fun hcx _ => absurd hcx (not_conTopped_peel hR hkind)⟩
        · by_cases hpy : ∃ c, g y = some c ∧ (rootStep R y c ∨ barRel (DownOn A R) y c)
          · obtain ⟨c, hyc, hkind⟩ := hpy
            obtain ⟨j', rfl⟩ := nonzero j y c hjy hyc
            obtain ⟨c', hyc', htail⟩ := hjy.succ_inv
            have hcc : c = c' := Option.some.inj (hyc.symm.trans hyc')
            subst hcc
            have hcA : c ∈ A := (hgmem hyc).2
            have hrec := ih i j' x c (by omega) hx hcA hix htail
            refine swap y x ⟨downOn_peel hy hcA hkind (swap x c hrec).1,
              fun hcy _ => absurd hcy (not_conTopped_peel hR hkind)⟩
          · -- both endpoints carry only constructor-tilde edges
            have htr : ∀ p q r : Term (sigma ⊕ sigma) nu,
                EqvOn A rho.par p q → EqvOn A rho.par q r → EqvOn A rho.par p r :=
              fun _ _ _ h₁ h₂ => EqvOn.trans h₁ h₂
            have hatx : ∀ c, g x = some c → hatEq (EqvOn A rho.par) x c := by
              intro c hxc
              rcases hgrey hxc with hroot | hbar | hhat
              · exact absurd ⟨c, hxc, Or.inl hroot⟩ hpx
              · exact absurd ⟨c, hxc, Or.inr hbar⟩ hpx
              · exact hhat
            have haty : ∀ c, g y = some c → hatEq (EqvOn A rho.par) y c := by
              intro c hyc
              rcases hgrey hyc with hroot | hbar | hhat
              · exact absurd ⟨c, hyc, Or.inl hroot⟩ hpy
              · exact absurd ⟨c, hyc, Or.inr hbar⟩ hpy
              · exact hhat
            have hgreyAll : ∀ {a b : Term (sigma ⊕ sigma) nu}, g a = some b →
                Grey A R (EqvOn A rho.par) a b := fun hab => hgrey hab
            cases i with
            | zero =>
                cases j with
                | zero =>
                    have hxs : x = s := hix.zero_inv
                    have hys : y = s := hjy.zero_inv
                    subst hxs
                    subst hys
                    exact lemma52_diag hA rho hx
                | succ j' =>
                    obtain ⟨c, hyc, htail⟩ := hjy.succ_inv
                    have hhy := haty c hyc
                    have hcy : ConTopped y := ConTopped.of_hatEq hhy
                    have hxs : x = s := hix.zero_inv
                    have hcx : ConTopped x := by
                      rw [hxs]
                      exact conTopped_of_reach hR hgreyAll hjy.toReach hcy
                    have hcA : c ∈ A := (hgmem hyc).2
                    have hrec := ih 0 j' x c (by omega) hx hcA hix htail
                    have hxc : hatEq (EqvOn A rho.par) x c :=
                      hrec.2 hcx (ConTopped.of_hatEq_right hhy)
                    have hcyy : hatEq (EqvOn A rho.par) c y :=
                      hatEq.symm (E := EqvOn A rho.par)
                        (fun _ _ hxy => EqvOn.symm hxy) hhy
                    have hfull : hatEq (EqvOn A rho.par) x y :=
                      hatEq.trans (E := EqvOn A rho.par) htr hxc hcyy
                    exact ⟨downOn_of_hatEq rho hx hy hfull, fun _ _ => hfull⟩
            | succ i' =>
                obtain ⟨c, hxc, htail⟩ := hix.succ_inv
                have hhx := hatx c hxc
                have hcx : ConTopped x := ConTopped.of_hatEq hhx
                have hcy : ConTopped y := by
                  cases j with
                  | zero =>
                      have hys : y = s := hjy.zero_inv
                      rw [hys]
                      exact conTopped_of_reach hR hgreyAll hix.toReach hcx
                  | succ j' =>
                      obtain ⟨c₂, hyc₂, -⟩ := hjy.succ_inv
                      exact ConTopped.of_hatEq (haty c₂ hyc₂)
                have hcA : c ∈ A := (hgmem hxc).2
                have hrec := ih i' j c y (by omega) hcA hy htail hjy
                have hcyy : hatEq (EqvOn A rho.par) c y :=
                  hrec.2 (ConTopped.of_hatEq_right hhx) hcy
                have hfull : hatEq (EqvOn A rho.par) x y :=
                  hatEq.trans (E := EqvOn A rho.par) htr hhx hcyy
                exact ⟨downOn_of_hatEq rho hx hy hfull, fun _ _ => hfull⟩
  exact key (m + n) m n t u (le_refl _) htA huA hm hn

/-! ## Corollary 53: one-edge proof-graph extension -/

/-- Corollary 53 with the exact new parent function exposed. -/
theorem PGraph.extend_one_exact {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R) (rho : PGraph A R)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hnf : rho.NF a) (hne : ¬ EqvOn A rho.par a b)
    (hgrey : Grey A R (EqvOn A rho.par) a b) :
    ∃ beta : PGraph A R, beta.par = extendPar rho.par a b ∧
      rho.Extends beta ∧ beta.par a = some b := by
  classical
  let g := extendPar rho.par a b
  have hnr : ¬ Reach rho.par b a := by
    intro hba
    exact hne (EqvOn.symm (EqvOn.of_reach hb ha hba))
  have hgterm : Terminating g := by
    simpa [g] using terminating_extendPar rho.term hnf hnr
  have hold : ∀ ⦃x y : Term (sigma ⊕ sigma) nu⦄,
      rho.par x = some y → g x = some y := by
    intro x y hxy
    have hxa : x ≠ a := by
      intro hEq
      subst hEq
      rw [hnf] at hxy
      contradiction
    simpa [g] using (extendPar_of_ne (g := rho.par) (a := a) (b := b) hxa ▸ hxy)
  have hgmem : ∀ ⦃x y : Term (sigma ⊕ sigma) nu⦄,
      g x = some y → x ∈ A ∧ y ∈ A := by
    intro x y hxy
    rcases extendPar_edge (g := rho.par) (a := a) (b := b) hxy with ⟨rfl, rfl⟩ | holdEdge
    · exact ⟨ha, hb⟩
    · exact rho.mem_edge holdEdge
  have hgGreyOld : ∀ ⦃x y : Term (sigma ⊕ sigma) nu⦄,
      g x = some y → Grey A R (EqvOn A rho.par) x y := by
    intro x y hxy
    rcases extendPar_edge (g := rho.par) (a := a) (b := b) hxy with ⟨rfl, rfl⟩ | holdEdge
    · exact hgrey
    · exact rho.grey holdEdge
  have heqMono : ∀ x y, EqvOn A rho.par x y → EqvOn A g x y :=
    fun _ _ hxy => EqvOn.mono hold hxy
  have hgsub : ∀ ⦃x y : Term (sigma ⊕ sigma) nu⦄,
      EqvOn A g x y → DownOn A R x y := by
    intro x y hxy
    exact (lemma52 hA hR rho hgterm (fun h => hgmem h) (fun h => hgGreyOld h) hxy).1
  have hgGrey : ∀ ⦃x y : Term (sigma ⊕ sigma) nu⦄,
      g x = some y → Grey A R (EqvOn A g) x y := by
    intro x y hxy
    exact Grey.mono heqMono (hgGreyOld hxy)
  let beta : PGraph A R :=
    { par := g
      mem_edge := fun h => hgmem h
      term := hgterm
      sub := fun h => hgsub h
      grey := fun h => hgGrey h }
  refine ⟨beta, rfl, ?_, ?_⟩
  · intro x y hxy
    simpa [beta] using hold hxy
  · simp [beta, g, extendPar_self]

/-- A grey edge from a graph normal form into a distinct represented class
can be added with every old edge retained. The original interface is unchanged. -/
theorem PGraph.extend_one {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R) (rho : PGraph A R)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hnf : rho.NF a) (hne : ¬ EqvOn A rho.par a b)
    (hgrey : Grey A R (EqvOn A rho.par) a b) :
    ∃ beta : PGraph A R, rho.Extends beta ∧ beta.par a = some b := by
  obtain ⟨beta, _, hExt, hedge⟩ := rho.extend_one_exact hA hR ha hb hnf hne hgrey
  exact ⟨beta, hExt, hedge⟩

/-! ## Lemma 56: constructor closure of a complete proof graph -/

/-- The endpoint of a proof-graph parent chain remains in the coalgebra. -/
theorem PGraph.mem_of_reach_right {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (h : Reach rho.par a b) : b ∈ A := by
  induction h with
  | refl => exact ha
  | @head x y z hxy hyz ih =>
      exact ih (rho.mem_edge hxy).2

/-- **Lemma 56.** The equivalence represented by a complete proof graph is
closed under the constructor subsignature on the strongly finite coalgebra.
Variables are treated as frozen nullary constructors through `hatEq`. -/
theorem PGraph.constructorClosed_of_complete {A : List (Term (sigma ⊕ sigma) nu)}
    (hA : Coalgebra A) {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : PGraph A R) (hcomplete : rho.Complete)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hhat : hatEq (EqvOn A rho.par) a b) : EqvOn A rho.par a b := by
  obtain ⟨s, has, hsnf⟩ := exists_root rho.term a
  have hsA : s ∈ A := rho.mem_of_reach_right ha has
  have hasEq : EqvOn A rho.par a s := EqvOn.of_reach ha hsA has
  have hca : ConTopped a := ConTopped.of_hatEq hhat
  have hcs : ConTopped s := conTopped_of_reach hR (fun h => rho.grey h) has hca
  have hasHat : hatEq (EqvOn A rho.par) a s :=
    rho.constructorCompatible hA hR hca hcs hasEq
  have hsbHat : hatEq (EqvOn A rho.par) s b :=
    hatEq.trans (E := EqvOn A rho.par) (fun _ _ _ h1 h2 => EqvOn.trans h1 h2)
      (hatEq.symm (E := EqvOn A rho.par) (fun _ _ hxy => EqvOn.symm hxy) hasHat) hhat
  by_cases hsb : EqvOn A rho.par s b
  · exact EqvOn.trans hasEq hsb
  · have hgrey : Grey A R (EqvOn A rho.par) s b := Or.inr (Or.inr hsbHat)
    obtain ⟨beta, hExt, hedge⟩ := rho.extend_one hA hR hsA hb hsnf hsb hgrey
    have hBack : beta.Extends rho := hcomplete beta hExt
    have hOld : rho.par s = some b := hBack hedge
    rw [hsnf] at hOld
    contradiction

/-! ## Definitions 57--60: targeted proof graphs -/

/-- **Definition 57, destructor step on the finite coalgebra.** This is the rendered
`\bar{\Downarrow_A}` relation, including endpoint membership explicitly. -/
def BarStepOn (A : List (Term (sigma ⊕ sigma) nu)) (R : TRS (sigma ⊕ sigma) nu) :
    CRel sigma nu :=
  fun a b => a ∈ A ∧ b ∈ A ∧ barRel (DownOn A R) a b

/-- The destructor-step relation is symmetric because `DownOn` is symmetric. -/
theorem BarStepOn.symm {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : BarStepOn A R a b) : BarStepOn A R b a := by
  refine ⟨h.2.1, h.1, ?_⟩
  have hflip : barRel (fun x y => DownOn A R y x) a b :=
    tildeOn_mono (fun _ _ hxy => DownOn.symm hxy) h.2.2
  exact tildeOn_flip hflip

/-- **Definition 57.** `BarReachOn A R t u` is the rendered
` t (\bar{\Downarrow_A})* u`. -/
inductive BarReachOn (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) : CRel sigma nu
  | refl (a : Term (sigma ⊕ sigma) nu) : BarReachOn A R a a
  | head {a b c : Term (sigma ⊕ sigma) nu} :
      BarStepOn A R a b → BarReachOn A R b c → BarReachOn A R a c

theorem BarReachOn.trans {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {a b c : Term (sigma ⊕ sigma) nu}
    (hab : BarReachOn A R a b) (hbc : BarReachOn A R b c) : BarReachOn A R a c := by
  induction hab with
  | refl => exact hbc
  | head hstep _ ih => exact BarReachOn.head hstep (ih hbc)

/-- The class relation of Definition 57 is symmetric. -/
theorem BarReachOn.symm {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : BarReachOn A R a b) : BarReachOn A R b a := by
  induction h with
  | refl => exact BarReachOn.refl _
  | @head a b c hab _ ih =>
      exact ih.trans (BarReachOn.head hab.symm (BarReachOn.refl a))

/-- A destructor-class path carrying its exact number of edges. -/
inductive BarReachN (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) :
    Nat → Term (sigma ⊕ sigma) nu → Term (sigma ⊕ sigma) nu → Prop
  | refl (a : Term (sigma ⊕ sigma) nu) : BarReachN A R 0 a a
  | head {n : Nat} {a b c : Term (sigma ⊕ sigma) nu} :
      BarStepOn A R a b → BarReachN A R n b c → BarReachN A R (n + 1) a c

/-- Forget the length of a destructor-class path. -/
theorem BarReachN.toBarReach {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {n : Nat} {a b : Term (sigma ⊕ sigma) nu}
    (h : BarReachN A R n a b) : BarReachOn A R a b := by
  induction h with
  | refl => exact BarReachOn.refl _
  | head hstep _ ih => exact BarReachOn.head hstep ih

/-- Every destructor-class path has a finite edge count. -/
theorem BarReachOn.toBarReachN {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : BarReachOn A R a b) : ∃ n, BarReachN A R n a b := by
  induction h with
  | refl => exact ⟨0, BarReachN.refl _⟩
  | head hstep _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, BarReachN.head hstep hn⟩

theorem BarReachN.zero_inv {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {a b : Term (sigma ⊕ sigma) nu}
    (h : BarReachN A R 0 a b) : a = b := by
  cases h with
  | refl => rfl

theorem BarReachN.succ_inv {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {n : Nat} {a c : Term (sigma ⊕ sigma) nu}
    (h : BarReachN A R (n + 1) a c) :
    ∃ b, BarStepOn A R a b ∧ BarReachN A R n b c := by
  cases h with
  | head hstep htail => exact ⟨_, hstep, htail⟩

/-- The destructor-tilde equivalence classes `D_A` from Definition 57. -/
def barClassSetoid (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) : Setoid {t // t ∈ A} where
  r x y := BarReachOn A R x.1 y.1
  iseqv := ⟨fun x => BarReachOn.refl x.1,
    fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The carrier `D_A` of destructor-tilde equivalence classes. -/
abbrev BarClass (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) := Quotient (barClassSetoid A R)

/-- The class `E_t` of Definition 57. -/
def barClassOf (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) (t : Term (sigma ⊕ sigma) nu) (ht : t ∈ A) :
    BarClass A R := Quotient.mk (barClassSetoid A R) ⟨t, ht⟩

/-- `R_t`: the class of `t` contains a root redex. -/
def RedexClass (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) (t : Term (sigma ⊕ sigma) nu) : Prop :=
  ∃ u, u ∈ A ∧ BarReachOn A R t u ∧ ∃ v, v ∈ A ∧ rootStep R u v

/-- **Definition 58.** A target selects one member of each destructor class and selects
a redex whenever that class contains a redex. Using the quotient makes the source's
`D_A → A` typing literal rather than representative-dependent. -/
structure Target (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) where
  pick : BarClass A R → Term (sigma ⊕ sigma) nu
  pick_mem : ∀ C, pick C ∈ A
  inFiber : ∀ (t : Term (sigma ⊕ sigma) nu) (ht : t ∈ A),
    BarReachOn A R t (pick (barClassOf A R t ht))
  redexPriority : ∀ (t : Term (sigma ⊕ sigma) nu) (ht : t ∈ A),
    RedexClass A R t →
      ∃ v, v ∈ A ∧ rootStep R (pick (barClassOf A R t ht)) v

/-- A quotient class contains a root redex. -/
def ClassHasRedex (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) (C : BarClass A R) : Prop :=
  ∃ u, ∃ hu : u ∈ A, barClassOf A R u hu = C ∧
    ∃ v, v ∈ A ∧ rootStep R u v

/-- `R_t ≠ ∅` is exactly a redex-bearing quotient class. -/
theorem classHasRedex_of_redexClass {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {t : Term (sigma ⊕ sigma) nu} (ht : t ∈ A)
    (h : RedexClass A R t) : ClassHasRedex A R (barClassOf A R t ht) := by
  obtain ⟨u, hu, htu, v, hv, hroot⟩ := h
  refine ⟨u, hu, ?_, v, hv, hroot⟩
  exact Quotient.sound htu.symm

/-- Every destructor class has a representative, and if the class contains a redex then it
has a redex representative. This is the choice principle behind Definition 58. -/
theorem exists_targetRepresentative (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) (C : BarClass A R) :
    ∃ u, ∃ hu : u ∈ A, barClassOf A R u hu = C ∧
      (ClassHasRedex A R C → ∃ v, v ∈ A ∧ rootStep R u v) := by
  classical
  by_cases hred : ClassHasRedex A R C
  · obtain ⟨u, hu, hclass, v, hv, hroot⟩ := hred
    exact ⟨u, hu, hclass, fun _ => ⟨v, hv, hroot⟩⟩
  · obtain ⟨z, hz⟩ := Quotient.exists_rep C
    refine ⟨z.1, z.2, ?_, fun h => False.elim (hred h)⟩
    exact hz

/-- A selected source-faithful target representative for one class. -/
noncomputable def targetRepresentative (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) (C : BarClass A R) : Term (sigma ⊕ sigma) nu :=
  Classical.choose (exists_targetRepresentative A R C)

theorem targetRepresentative_spec (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) (C : BarClass A R) :
    ∃ hu : targetRepresentative A R C ∈ A,
      barClassOf A R (targetRepresentative A R C) hu = C ∧
        (ClassHasRedex A R C →
          ∃ v, v ∈ A ∧ rootStep R (targetRepresentative A R C) v) := by
  classical
  exact Classical.choose_spec (exists_targetRepresentative A R C)

/-- **Definition 58 is inhabited on every finite coalgebra.** Classical choice selects one
representative of each `E_t`, preferring a redex exactly when `R_t` is nonempty. -/
noncomputable def canonicalTarget (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) : Target A R where
  pick := targetRepresentative A R
  pick_mem := fun C => Classical.choose (targetRepresentative_spec A R C)
  inFiber := by
    intro t ht
    let C := barClassOf A R t ht
    let hp : targetRepresentative A R C ∈ A :=
      Classical.choose (targetRepresentative_spec A R C)
    have hclass : barClassOf A R (targetRepresentative A R C) hp = C :=
      (Classical.choose_spec (targetRepresentative_spec A R C)).1
    have hrel : BarReachOn A R (targetRepresentative A R C) t :=
      Quotient.exact (hclass.trans rfl)
    exact hrel.symm
  redexPriority := by
    intro t ht hred
    let C := barClassOf A R t ht
    have hc : ClassHasRedex A R C := classHasRedex_of_redexClass ht hred
    exact (Classical.choose_spec (targetRepresentative_spec A R C)).2 hc

/-- A target is literally constant on one `E_t` class. -/
theorem Target.pick_eq_of_barReach {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (target : Target A R)
    {t u : Term (sigma ⊕ sigma) nu} (ht : t ∈ A) (hu : u ∈ A)
    (h : BarReachOn A R t u) :
    target.pick (barClassOf A R t ht) = target.pick (barClassOf A R u hu) := by
  apply congrArg target.pick
  exact Quotient.sound h

/-! ### A canonical well-founded forest inside every destructor class -/

/-- Minimal destructor-class distance from `t` to the selected target of `E_t`. -/
noncomputable def Target.distance {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (target : Target A R)
    (t : Term (sigma ⊕ sigma) nu) : Nat := by
  classical
  by_cases ht : t ∈ A
  · exact Nat.find (target.inFiber t ht).toBarReachN
  · exact 0

/-- The minimal-distance path actually reaches the selected target. -/
theorem Target.distance_spec {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (target : Target A R)
    (t : Term (sigma ⊕ sigma) nu) (ht : t ∈ A) :
    BarReachN A R (target.distance t) t (target.pick (barClassOf A R t ht)) := by
  classical
  simp only [Target.distance, dif_pos ht]
  exact Nat.find_spec (target.inFiber t ht).toBarReachN

/-- Distance zero means that the node itself is the selected target. -/
theorem Target.eq_target_of_distance_zero {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (target : Target A R)
    {t : Term (sigma ⊕ sigma) nu} (ht : t ∈ A) (hzero : target.distance t = 0) :
    t = target.pick (barClassOf A R t ht) := by
  have h := target.distance_spec t ht
  rw [hzero] at h
  exact h.zero_inv

/-- If a node is not the selected target, one destructor step strictly decreases the
minimal target distance. -/
theorem Target.exists_distance_decreasing_step
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (target : Target A R) {t : Term (sigma ⊕ sigma) nu} (ht : t ∈ A)
    (hne : t ≠ target.pick (barClassOf A R t ht)) :
    ∃ b, BarStepOn A R t b ∧ target.distance b < target.distance t := by
  classical
  have hpos : 0 < target.distance t := by
    by_contra h
    have hz : target.distance t = 0 := by omega
    exact hne (target.eq_target_of_distance_zero ht hz)
  obtain ⟨n, hd⟩ : ∃ n, target.distance t = n + 1 := by
    exact ⟨target.distance t - 1, by omega⟩
  have hpath := target.distance_spec t ht
  rw [hd] at hpath
  obtain ⟨b, htb, htail⟩ := hpath.succ_inv
  have hb : b ∈ A := htb.2.1
  have hclass : BarReachOn A R t b :=
    BarReachOn.head htb (BarReachOn.refl b)
  have hpick := target.pick_eq_of_barReach ht hb hclass
  have hcand : BarReachN A R n b (target.pick (barClassOf A R b hb)) := by
    rw [← hpick]
    exact htail
  have hle : target.distance b ≤ n := by
    simp only [Target.distance, dif_pos hb]
    exact Nat.find_min' (target.inFiber b hb).toBarReachN hcand
  exact ⟨b, htb, by omega⟩

/-- The chosen next node on a shortest target path. -/
noncomputable def Target.next {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (target : Target A R)
    (t : Term (sigma ⊕ sigma) nu) (ht : t ∈ A)
    (hne : t ≠ target.pick (barClassOf A R t ht)) : Term (sigma ⊕ sigma) nu :=
  Classical.choose (target.exists_distance_decreasing_step ht hne)

/-- The selected next node is a destructor neighbor and strictly closer to the target. -/
theorem Target.next_spec {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (target : Target A R)
    (t : Term (sigma ⊕ sigma) nu) (ht : t ∈ A)
    (hne : t ≠ target.pick (barClassOf A R t ht)) :
    BarStepOn A R t (target.next t ht hne) ∧
      target.distance (target.next t ht hne) < target.distance t :=
  Classical.choose_spec (target.exists_distance_decreasing_step ht hne)

/-- Parent function of the canonical destructor-class spanning forest. -/
noncomputable def Target.parent {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (target : Target A R) :
    Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu) := by
  classical
  intro t
  by_cases ht : t ∈ A
  · by_cases htarget : t = target.pick (barClassOf A R t ht)
    · exact none
    · exact some (target.next t ht htarget)
  · exact none

/-- A non-target member points to the selected next node. -/
theorem Target.parent_eq_some_next {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (target : Target A R)
    {t : Term (sigma ⊕ sigma) nu} (ht : t ∈ A)
    (hne : t ≠ target.pick (barClassOf A R t ht)) :
    target.parent t = some (target.next t ht hne) := by
  classical
  rw [Target.parent]
  simp only [dif_pos ht, dif_neg hne]

/-- Every parent edge is exactly a shortest-distance destructor edge. -/
theorem Target.parent_edge {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (target : Target A R)
    {t b : Term (sigma ⊕ sigma) nu} (h : target.parent t = some b) :
    t ∈ A ∧ b ∈ A ∧ BarStepOn A R t b ∧ target.distance b < target.distance t := by
  classical
  unfold Target.parent at h
  split at h <;> rename_i ht
  · split at h <;> rename_i htarget
    · simp at h
    · have hbEq : target.next t ht htarget = b := Option.some.inj h
      subst b
      have hs := target.next_spec t ht htarget
      exact ⟨ht, hs.1.2.1, hs.1, hs.2⟩
  · simp at h

/-- The target forest is terminating by strict descent of target distance. -/
theorem Target.parent_terminating {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (target : Target A R) : Terminating target.parent := by
  have hwf : WellFounded (fun x y : Term (sigma ⊕ sigma) nu =>
      target.distance x < target.distance y) :=
    InvImage.wf (f := target.distance) Nat.lt_wfRel.wf
  have hsub : Subrelation
      (fun x y : Term (sigma ⊕ sigma) nu => target.parent y = some x)
      (fun x y : Term (sigma ⊕ sigma) nu => target.distance x < target.distance y) := by
    intro x y hxy
    exact (target.parent_edge hxy).2.2.2
  exact Subrelation.wf hsub hwf

/-- A selected target has no parent in the canonical destructor forest. -/
theorem Target.parent_eq_none_of_target {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (target : Target A R)
    {t : Term (sigma ⊕ sigma) nu} (ht : t ∈ A)
    (heq : t = target.pick (barClassOf A R t ht)) : target.parent t = none := by
  classical
  rw [Target.parent]
  simp only [dif_pos ht]
  rw [dif_pos heq]

/-- The empty proof graph. It is the seed relation used to certify the destructor spanning
forest through Lemma 52 without presupposing transitivity of `DownOn`. -/
def PGraph.empty (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) : PGraph A R where
  par := fun _ => none
  mem_edge := by
    intro a b h
    simp at h
  term := by
    refine ⟨fun a => Acc.intro a ?_⟩
    intro b h
    simp at h
  sub := by
    intro a b h
    obtain ⟨ha, hb, s, has, hbs⟩ := h
    have hasEq : a = s := by
      cases has with
      | refl => rfl
      | head hedge _ => simp at hedge
    have hbsEq : b = s := by
      cases hbs with
      | refl => rfl
      | head hedge _ => simp at hedge
    have hab : a = b := hasEq.trans hbsEq.symm
    rw [← hab]
    exact DownOn.refl ha
  grey := by
    intro a b h
    simp at h

/-- The shortest-path destructor forest is a proof graph. Lemma 52 supplies its invariant
containment, so no transitivity of `DownOn` is used in this construction. -/
noncomputable def Target.baseGraph {A : List (Term (sigma ⊕ sigma) nu)}
    (hA : Coalgebra A) {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (target : Target A R) : PGraph A R := by
  let seed := PGraph.empty A R
  have hmem : ∀ {a b : Term (sigma ⊕ sigma) nu}, target.parent a = some b →
      a ∈ A ∧ b ∈ A := by
    intro a b hab
    have hs := target.parent_edge hab
    exact ⟨hs.1, hs.2.1⟩
  have hgreySeed : ∀ {a b : Term (sigma ⊕ sigma) nu}, target.parent a = some b →
      Grey A R (EqvOn A seed.par) a b := by
    intro a b hab
    exact Or.inr (Or.inl (target.parent_edge hab).2.2.1.2.2)
  have hsub : ∀ {a b : Term (sigma ⊕ sigma) nu}, EqvOn A target.parent a b →
      DownOn A R a b := by
    intro a b hab
    exact (lemma52 hA hR seed target.parent_terminating hmem hgreySeed hab).1
  exact
    { par := target.parent
      mem_edge := hmem
      term := target.parent_terminating
      sub := hsub
      grey := by
        intro a b hab
        exact Or.inr (Or.inl (target.parent_edge hab).2.2.1.2.2) }

@[simp] theorem Target.baseGraph_par {A : List (Term (sigma ⊕ sigma) nu)}
    (hA : Coalgebra A) {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (target : Target A R) : (target.baseGraph hA hR).par = target.parent := rfl

/-- A parent chain in the shortest-path forest stays inside one destructor class. -/
theorem Target.barReach_of_parentReach {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (target : Target A R)
    {a b : Term (sigma ⊕ sigma) nu} (h : Reach target.parent a b) :
    BarReachOn A R a b := by
  induction h with
  | refl => exact BarReachOn.refl _
  | head hedge _ ih =>
      exact BarReachOn.head (target.parent_edge hedge).2.2.1 ih

/-- A parent edge used by Definition 59: it is simultaneously a proof-graph edge and a
rendered destructor-tilde edge. -/
def GuidedParentStep {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R) : CRel sigma nu :=
  fun a b => rho.par a = some b ∧ BarStepOn A R a b

/-- The reflexive-transitive `(\bar{\Downarrow_A} ∩ →_rho)*` path in Definition 59. -/
def GuidedReach {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R) : CRel sigma nu :=
  Relation.ReflTransGen (GuidedParentStep rho)

/-- A guided path is a proof-graph parent path. -/
theorem GuidedReach.toReach {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {rho : PGraph A R}
    {a b : Term (sigma ⊕ sigma) nu} (h : GuidedReach rho a b) : Reach rho.par a b := by
  induction h with
  | refl => exact Reach.refl _
  | tail _ hlast ih =>
      exact ih.trans (Reach.head hlast.1 (Reach.refl _))

/-- A guided path stays in one destructor class. -/
theorem GuidedReach.toBarReach {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {rho : PGraph A R}
    {a b : Term (sigma ⊕ sigma) nu} (h : GuidedReach rho a b) : BarReachOn A R a b := by
  induction h with
  | refl => exact BarReachOn.refl _
  | tail _ hlast ih =>
      exact ih.trans (BarReachOn.head hlast.2 (BarReachOn.refl _))

/-- A parent chain in the shortest-path forest is a guided path in the base graph. -/
theorem Target.guidedReach_baseGraph_of_parentReach
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (target : Target A R) {a b : Term (sigma ⊕ sigma) nu}
    (h : Reach target.parent a b) : GuidedReach (target.baseGraph hA hR) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b c hab _ ih =>
      have hedge : GuidedParentStep (target.baseGraph hA hR) a b := by
        refine ⟨?_, (target.parent_edge hab).2.2.1⟩
        simpa using hab
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hedge) ih

/-- Every coalgebra member follows the canonical destructor forest to the selected target of
its class. This is the strong targeting property needed before applying Proposition 55. -/
theorem Target.guidedReach_baseGraph
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (target : Target A R) (t : Term (sigma ⊕ sigma) nu) (ht : t ∈ A) :
    GuidedReach (target.baseGraph hA hR) t (target.pick (barClassOf A R t ht)) := by
  obtain ⟨r, htr, hrnone⟩ := exists_root target.parent_terminating t
  have htrGraph : Reach (target.baseGraph hA hR).par t r := by
    simpa using htr
  have hrA : r ∈ A := (target.baseGraph hA hR).mem_of_reach_right ht htrGraph
  have hbar : BarReachOn A R t r := target.barReach_of_parentReach htr
  have hpick : target.pick (barClassOf A R t ht) =
      target.pick (barClassOf A R r hrA) := target.pick_eq_of_barReach ht hrA hbar
  have hrTarget : r = target.pick (barClassOf A R t ht) := by
    by_contra hne
    have hne' : r ≠ target.pick (barClassOf A R r hrA) := by
      intro heq
      apply hne
      exact heq.trans hpick.symm
    have hsome := target.parent_eq_some_next hrA hne'
    rw [hrnone] at hsome
    contradiction
  have hg : GuidedReach (target.baseGraph hA hR) t r :=
    target.guidedReach_baseGraph_of_parentReach hA hR htr
  simpa [hrTarget] using hg

/-- Guided reachability is monotone under proof-graph extension. -/
theorem GuidedReach.mono {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {alpha beta : PGraph A R}
    (hExt : alpha.Extends beta) {a b : Term (sigma ⊕ sigma) nu}
    (h : GuidedReach alpha a b) : GuidedReach beta a b := by
  exact Relation.ReflTransGen.mono
    (fun _ _ hxy => ⟨hExt hxy.1, hxy.2⟩) h

/-- A parent chain, read backwards, is a chain in the well-founded parent relation. -/
theorem Reach.toReflTransGenRev
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    {a b : Term (sigma ⊕ sigma) nu} (h : Reach g a b) :
    Relation.ReflTransGen (fun y x => g x = some y) b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | head hab _ ih => exact Relation.ReflTransGen.tail ih hab

/-- A terminating parent function cannot contain an edge whose target reaches back to its
source. -/
theorem Terminating.no_parent_cycle
    {g : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hwf : Terminating g) {a b : Term (sigma ⊕ sigma) nu}
    (hab : g a = some b) (hba : Reach g b a) : False := by
  let r : Term (sigma ⊕ sigma) nu → Term (sigma ⊕ sigma) nu → Prop :=
    fun y x => g x = some y
  have hrev : Relation.ReflTransGen r a b := hba.toReflTransGenRev
  have hback : Relation.TransGen r b a := Relation.TransGen.single hab
  rcases (Relation.reflTransGen_iff_eq_or_transGen).1 hrev with hEq | hforward
  · subst b
    exact hwf.transGen.asymmetric a a hback hback
  · exact hwf.transGen.asymmetric a b hforward hback

/-- **Definition 59.** A targeted proof graph. The disjunction in `guided_or_nf` is
kept exactly as in the rendered source; it is not silently strengthened to require every
node to reach its target. -/
structure TargetedPGraph (A : List (Term (sigma ⊕ sigma) nu))
    (R : TRS (sigma ⊕ sigma) nu) where
  graph : PGraph A R
  target : Target A R
  guided_or_nf : ∀ (t : Term (sigma ⊕ sigma) nu) (ht : t ∈ A),
    GuidedReach graph t (target.pick (barClassOf A R t ht)) ∨ graph.NF t
  target_exit : ∀ (t : Term (sigma ⊕ sigma) nu) (ht : t ∈ A)
      (u : Term (sigma ⊕ sigma) nu),
    graph.par (target.pick (barClassOf A R t ht)) = some u →
      ¬ BarReachOn A R t u

/-- **Definition 60.** A targeted extension retains every graph edge of the old proof graph. -/
def TargetedPGraph.Extends {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (alpha beta : TargetedPGraph A R) : Prop :=
  alpha.graph.Extends beta.graph

/-- The canonical destructor spanning forest is already a targeted proof graph, and in fact
all of its nodes are guided to their selected target. -/
noncomputable def Target.baseTargeted {A : List (Term (sigma ⊕ sigma) nu)}
    (hA : Coalgebra A) {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (target : Target A R) : TargetedPGraph A R where
  graph := target.baseGraph hA hR
  target := target
  guided_or_nf := fun t ht => Or.inl (target.guidedReach_baseGraph hA hR t ht)
  target_exit := by
    intro t ht u hedge _
    have hpA : target.pick (barClassOf A R t ht) ∈ A := target.pick_mem _
    have hclass : BarReachOn A R t (target.pick (barClassOf A R t ht)) :=
      target.inFiber t ht
    have hpick : target.pick (barClassOf A R t ht) =
        target.pick (barClassOf A R (target.pick (barClassOf A R t ht)) hpA) :=
      target.pick_eq_of_barReach ht hpA hclass
    have hnone := target.parent_eq_none_of_target hpA hpick
    change target.parent (target.pick (barClassOf A R t ht)) = some u at hedge
    rw [hnone] at hedge
    contradiction

/-- All nodes are already linked to their target. This is the strengthened state reached
by the completion construction and consumed by Lemma 62. -/
def TargetedPGraph.AllGuided {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : TargetedPGraph A R) : Prop :=
  ∀ (t : Term (sigma ⊕ sigma) nu) (ht : t ∈ A),
    GuidedReach rho.graph t (rho.target.pick (barClassOf A R t ht))

/-- The base targeted forest is all-guided. -/
theorem Target.baseTargeted_allGuided {A : List (Term (sigma ⊕ sigma) nu)}
    (hA : Coalgebra A) {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (target : Target A R) : (target.baseTargeted hA hR).AllGuided := by
  intro t ht
  exact target.guidedReach_baseGraph hA hR t ht

/-- **Section-7 complete-targeted existence theorem.** Every source-faithful target function
admits a complete targeted proof graph. This is the existence consequence needed downstream,
but it is deliberately not named as the full source Lemma 61: the source states the stronger
extension theorem that every already-targeted graph has a complete targeted extension.
We span every destructor class by shortest target paths, then apply Proposition 55. Retained
target paths give Definition 59(i); termination prevents a new edge out of a selected target
from returning to its own class, giving Definition 59(ii). The resulting graph is all-guided,
which is stronger than the disjunctive targeting clause. -/
theorem Target.exists_complete_targeted
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (target : Target A R) :
    ∃ rho : TargetedPGraph A R, rho.graph.Complete ∧ rho.AllGuided := by
  let rho0 : TargetedPGraph A R := target.baseTargeted hA hR
  obtain ⟨beta, hExt, hcomplete⟩ := rho0.graph.exists_complete_extension
  let rho : TargetedPGraph A R :=
    { graph := beta
      target := target
      guided_or_nf := by
        intro t ht
        exact Or.inl ((target.guidedReach_baseGraph hA hR t ht).mono hExt)
      target_exit := by
        intro t ht u hedge htu
        have huA : u ∈ A := (beta.mem_edge hedge).2
        have hpick : target.pick (barClassOf A R t ht) =
            target.pick (barClassOf A R u huA) :=
          target.pick_eq_of_barReach ht huA htu
        have hgu : GuidedReach rho0.graph u
            (target.pick (barClassOf A R u huA)) :=
          target.guidedReach_baseGraph hA hR u huA
        rw [← hpick] at hgu
        have hguBeta : GuidedReach beta u (target.pick (barClassOf A R t ht)) :=
          hgu.mono hExt
        exact beta.term.no_parent_cycle hedge hguBeta.toReach }
  refine ⟨rho, hcomplete, ?_⟩
  intro t ht
  exact (target.guidedReach_baseGraph hA hR t ht).mono hExt

/-- Every strongly finite coalgebra has a complete targeted proof graph for the canonical
redex-priority target selection. -/
theorem exists_complete_targeted
    (A : List (Term (sigma ⊕ sigma) nu)) (hA : Coalgebra A)
    (R : TRS (sigma ⊕ sigma) nu) (hR : ConstructorRules R) :
    ∃ rho : TargetedPGraph A R, rho.graph.Complete ∧ rho.AllGuided :=
  (canonicalTarget A R).exists_complete_targeted hA hR

/-- Local `Σ`-closure on the finite coalgebra. The repository-wide `SigmaClosed` ranges over
all terms, whereas Section 7's relation is explicitly relativized to `A`. -/
def SigmaClosedOn (A : List (Term (sigma ⊕ sigma) nu)) (E : CRel sigma nu) : Prop :=
  ∀ t u, t ∈ A → u ∈ A → tildeAll E t u → E t u

/-- **Lemma 62, all-guided core.** If a targeted graph is graph-complete and every node is
already linked to its target, its represented equivalence is `Σ`-closed on `A`. -/
theorem TargetedPGraph.sigmaClosedOn_of_all_guided
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : TargetedPGraph A R) (hcomplete : rho.graph.Complete)
    (hall : rho.AllGuided) : SigmaClosedOn A (EqvOn A rho.graph.par) := by
  intro t u ht hu htilde
  rcases hatRel_or_barRel_of_tildeAll htilde with hhat | hbar
  · exact rho.graph.constructorClosed_of_complete hA hR hcomplete ht hu (Or.inr hhat)
  · have hbarDown : barRel (DownOn A R) t u :=
      tildeOn_mono (fun _ _ hxy => rho.graph.sub hxy) hbar
    have hclass : BarReachOn A R t u :=
      BarReachOn.head ⟨ht, hu, hbarDown⟩ (BarReachOn.refl u)
    have hpick := rho.target.pick_eq_of_barReach ht hu hclass
    have htg : Reach rho.graph.par t
        (rho.target.pick (barClassOf A R t ht)) := (hall t ht).toReach
    have hug : Reach rho.graph.par u
        (rho.target.pick (barClassOf A R u hu)) := (hall u hu).toReach
    rw [← hpick] at hug
    exact ⟨ht, hu, rho.target.pick (barClassOf A R t ht), htg, hug⟩

/-- **Lemma 62.** Every complete targeted proof graph is `Σ`-closed on its strongly finite
coalgebra. The normal-form cases are discharged directly by Corollary 53: a direct
destructor-tilde edge between two distinct represented classes would be a proper proof-graph
extension, contradicting completeness. Thus no prior strengthening of Definition 59 is used. -/
theorem TargetedPGraph.sigmaClosedOn_of_complete
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : TargetedPGraph A R) (hcomplete : rho.graph.Complete) :
    SigmaClosedOn A (EqvOn A rho.graph.par) := by
  intro t u ht hu htilde
  rcases hatRel_or_barRel_of_tildeAll htilde with hhat | hbar
  · exact rho.graph.constructorClosed_of_complete hA hR hcomplete ht hu (Or.inr hhat)
  · have hbarDown : barRel (DownOn A R) t u :=
      tildeOn_mono (fun _ _ hxy => rho.graph.sub hxy) hbar
    have htuClass : BarReachOn A R t u :=
      BarReachOn.head ⟨ht, hu, hbarDown⟩ (BarReachOn.refl u)
    have hpick := rho.target.pick_eq_of_barReach ht hu htuClass
    rcases rho.guided_or_nf t ht with htguided | htnf
    · rcases rho.guided_or_nf u hu with huguided | hunf
      · have htr : Reach rho.graph.par t
            (rho.target.pick (barClassOf A R t ht)) := htguided.toReach
        have hur : Reach rho.graph.par u
            (rho.target.pick (barClassOf A R u hu)) := huguided.toReach
        rw [← hpick] at hur
        exact ⟨ht, hu, rho.target.pick (barClassOf A R t ht), htr, hur⟩
      · by_cases heq : EqvOn A rho.graph.par t u
        · exact heq
        · have hne : ¬ EqvOn A rho.graph.par u t := fun hut => heq hut.symm
          have hgrey : Grey A R (EqvOn A rho.graph.par) u t :=
            Or.inr (Or.inl (BarStepOn.symm ⟨ht, hu, hbarDown⟩).2.2)
          obtain ⟨beta, hExt, hedge⟩ :=
            rho.graph.extend_one hA hR hu ht hunf hne hgrey
          have hBack : beta.Extends rho.graph := hcomplete beta hExt
          have hOld : rho.graph.par u = some t := hBack hedge
          rw [hunf] at hOld
          contradiction
    · by_cases heq : EqvOn A rho.graph.par t u
      · exact heq
      · have hgrey : Grey A R (EqvOn A rho.graph.par) t u :=
          Or.inr (Or.inl hbarDown)
        obtain ⟨beta, hExt, hedge⟩ :=
          rho.graph.extend_one hA hR ht hu htnf heq hgrey
        have hBack : beta.Extends rho.graph := hcomplete beta hExt
        have hOld : rho.graph.par t = some u := hBack hedge
        rw [htnf] at hOld
        contradiction

/-! ## Definition 63 and the exact reduction of Lemma 64 -/

/-- **Definition 63.** A proof graph is universal when its represented equivalence is exactly
the relativized invariant on the coalgebra. -/
def PGraph.Universal {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R) : Prop :=
  ∀ a b, EqvOn A rho.par a b ↔ DownOn A R a b

/-- Since every proof graph already satisfies `=_rho ⊆ DownOn`, universality is equivalent
to the one missing inclusion. -/
theorem PGraph.universal_iff_down_subset {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R) :
    rho.Universal ↔ ∀ a b, DownOn A R a b → EqvOn A rho.par a b := by
  constructor
  · intro h a b hab
    exact (h a b).2 hab
  · intro h a b
    exact ⟨fun heq => rho.sub heq, h a b⟩

/-- **Lemma-64 reduction.** For a complete targeted graph, the entire universality proof
reduces to closure under coalgebra root contractions. Every other clause of the least-fixed-
point operator is discharged by the induction hypothesis and Lemma 62's local Sigma closure.
This theorem isolates the exact obligation that the published term-structure induction was
trying to establish. -/
theorem TargetedPGraph.universal_of_complete_of_rootClosure
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (rho : TargetedPGraph A R) (hcomplete : rho.graph.Complete)
    (hroot : ∀ {a b : Term (sigma ⊕ sigma) nu}, a ∈ A → b ∈ A →
      rootStep R a b → EqvOn A rho.graph.par a b) :
    rho.graph.Universal := by
  rw [rho.graph.universal_iff_down_subset]
  intro a b hab
  have hsigma : SigmaClosedOn A (EqvOn A rho.graph.par) :=
    rho.sigmaClosedOn_of_complete hA hR hcomplete
  refine DownOn.induction
    (P := fun x y => EqvOn A rho.graph.par x y) ?_ hab
  intro p q hpq
  obtain ⟨hp, hq, hbody⟩ := hpq
  rcases hbody with heq | hinv | ⟨c, hc, hpc, hcq⟩ |
      ⟨d, as, cs, hpApp, hall, hcApp, hcq⟩ | hhat | hbar
  · subst q
    exact EqvOn.refl hp
  · exact EqvOn.symm hinv.2
  · exact EqvOn.trans (hroot hp hc hpc) hcq.2
  · have hallEq : List.Forall₂ (EqvOn A rho.graph.par) as cs :=
      forall₂_mono (fun _ _ hxy => hxy.2) hall
    have hbarEq : barRel (EqvOn A rho.graph.par)
        (.app (Sum.inr d) as) (.app (Sum.inr d) cs) :=
      ⟨.inr d, as, cs, ⟨d, rfl⟩, rfl, rfl, hallEq⟩
    have htilde : tildeAll (EqvOn A rho.graph.par) p (.app (Sum.inr d) cs) := by
      subst hpApp
      exact tildeAll_of_barRel hbarEq
    have hfirst : EqvOn A rho.graph.par p (.app (Sum.inr d) cs) :=
      hsigma p (.app (Sum.inr d) cs) hp hcApp htilde
    exact EqvOn.trans hfirst hcq.2
  · have hhatEq : hatRel (EqvOn A rho.graph.par) p q :=
      tildeOn_mono (fun _ _ hxy => hxy.2) hhat
    exact hsigma p q hp hq (tildeAll_of_hatRel hhatEq)
  · have hbarEq : barRel (EqvOn A rho.graph.par) p q :=
      tildeOn_mono (fun _ _ hxy => hxy.2) hbar
    exact hsigma p q hp hq (tildeAll_of_barRel hbarEq)


/-! ## Reorienting proof-graph roots without losing represented equalities -/

/-- Representing each old edge as a new equality preserves every old equality. -/
theorem EqvOn.mono_of_parent_eqv {A : List (Term (sigma ⊕ sigma) nu)}
    {g h : Term (sigma ⊕ sigma) nu → Option (Term (sigma ⊕ sigma) nu)}
    (hedge : ∀ {x y}, g x = some y → EqvOn A h x y)
    {x y : Term (sigma ⊕ sigma) nu} (hxy : EqvOn A g x y) : EqvOn A h x y := by
  have lift : ∀ {a b}, Reach g a b → a ∈ A → EqvOn A h a b := by
    intro a b hab
    induction hab with
    | refl a => exact EqvOn.refl
    | @head a b c he hbc ih =>
        intro _
        exact EqvOn.trans (hedge he) (ih (hedge he).2.1)
  obtain ⟨hx, hy, z, hxz, hyz⟩ := hxy
  exact EqvOn.trans (lift hxz hx) (EqvOn.symm (lift hyz hy))

/-- Reverse one parent edge into a graph root and make its former source the
root. All represented equalities are preserved in both directions. -/
theorem PGraph.reroot_one {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R)
    {a b : Term (sigma ⊕ sigma) nu} (hab : rho.par a = some b)
    (hbnf : rho.NF b) (hreverse : Grey A R (EqvOn A rho.par) b a) :
    ∃ beta : PGraph A R,
      beta.par = extendPar (ParentReplacement.cut rho.par a) b a ∧
      beta.NF a ∧ beta.par b = some a ∧
      (∀ x y, EqvOn A beta.par x y ↔ EqvOn A rho.par x y) ∧
      ∀ x, x ≠ a → x ≠ b → beta.par x = rho.par x := by
  classical
  have haA := (rho.mem_edge hab).1
  have hbA := (rho.mem_edge hab).2
  have hne : a ≠ b := by
    intro heq
    subst a
    rw [hbnf] at hab
    cases hab
  let cut := ParentReplacement.cut rho.par a
  let g := extendPar cut b a
  have hcutA : cut a = none := by simp [cut, ParentReplacement.cut]
  have hcutSub : Subrelation (fun y x => cut x = some y)
      (fun y x => rho.par x = some y) := by
    intro x y he
    exact (ParentReplacement.cut_edge he).2
  have hcutTerm : Terminating cut := Subrelation.wf hcutSub rho.term
  have hnoReturn : ¬ Reach cut a b := by
    intro hp
    exact hne (hp.toParentPath.eq_of_none hcutA)
  have hgTerm : Terminating g :=
    terminating_extendPar_of_no_return hcutTerm hnoReturn
  have hgA : g a = none := by
    simp [g, extendPar, hne, cut, ParentReplacement.cut]
  have hgB : g b = some a := extendPar_self cut b a
  have hgUnchanged : ∀ x, x ≠ a → x ≠ b → g x = rho.par x := by
    intro x hxa hxb
    simp [g, extendPar, hxb, cut, ParentReplacement.cut, hxa]
  have hgEdge : ∀ {x y}, g x = some y →
      (x = b ∧ y = a) ∨ (x ≠ a ∧ rho.par x = some y) := by
    intro x y he
    rcases extendPar_edge he with hnew | hold
    · exact Or.inl hnew
    · exact Or.inr (ParentReplacement.cut_edge hold)
  have hgMem : ∀ {x y}, g x = some y → x ∈ A ∧ y ∈ A := by
    intro x y he
    rcases hgEdge he with ⟨rfl, rfl⟩ | ⟨_, hold⟩
    · exact ⟨hbA, haA⟩
    · exact rho.mem_edge hold
  have holdNew : ∀ {x y}, EqvOn A rho.par x y → EqvOn A g x y := by
    apply EqvOn.mono_of_parent_eqv
    intro x y he
    by_cases hxa : x = a
    · subst x
      have hy : y = b := Option.some.inj (he.symm.trans hab)
      subst y
      exact EqvOn.symm (EqvOn.of_reach hbA haA (Reach.head hgB (Reach.refl a)))
    · have hxb : x ≠ b := by
        intro hxb
        subst x
        rw [hbnf] at he
        cases he
      exact EqvOn.of_reach (rho.mem_edge he).1 (rho.mem_edge he).2
        (Reach.head ((hgUnchanged x hxa hxb).trans he) (Reach.refl y))
  have hnewOld : ∀ {x y}, EqvOn A g x y → EqvOn A rho.par x y := by
    apply EqvOn.mono_of_parent_eqv
    intro x y he
    rcases hgEdge he with ⟨rfl, rfl⟩ | ⟨_, hold⟩
    · exact EqvOn.symm (EqvOn.of_reach haA hbA (Reach.head hab (Reach.refl _)))
    · exact EqvOn.of_reach (rho.mem_edge hold).1 (rho.mem_edge hold).2
        (Reach.head hold (Reach.refl y))
  have hgGreyOld : ∀ {x y}, g x = some y → Grey A R (EqvOn A rho.par) x y := by
    intro x y he
    rcases hgEdge he with ⟨rfl, rfl⟩ | ⟨_, hold⟩
    · exact hreverse
    · exact rho.grey hold
  let beta : PGraph A R :=
    { par := g
      mem_edge := fun he => hgMem he
      term := hgTerm
      sub := fun he => rho.sub (hnewOld he)
      grey := fun he => Grey.mono (fun _ _ h => holdNew h) (hgGreyOld he) }
  refine ⟨beta, rfl, hgA, hgB, ?_, hgUnchanged⟩
  intro x y
  exact ⟨hnewOld, holdNew⟩

/-- A parent path whose reversed edges are legal in the original graph. -/
inductive ReversibleReach {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R) :
    Term (sigma ⊕ sigma) nu → Term (sigma ⊕ sigma) nu → Prop
  | refl (a) : ReversibleReach rho a a
  | head {a b c} : rho.par a = some b →
      Grey A R (EqvOn A rho.par) b a → ReversibleReach rho b c →
      ReversibleReach rho a c

theorem ReversibleReach.toReach {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {rho : PGraph A R}
    {a b : Term (sigma ⊕ sigma) nu} (h : ReversibleReach rho a b) :
    Reach rho.par a b := by
  induction h with
  | refl a => exact Reach.refl a
  | head he _ _ ih => exact Reach.head he ih

theorem ReversibleReach.trans {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {rho : PGraph A R}
    {a b c : Term (sigma ⊕ sigma) nu}
    (hab : ReversibleReach rho a b) (hbc : ReversibleReach rho b c) :
    ReversibleReach rho a c := by
  induction hab with
  | refl _ => exact hbc
  | head he hr _ ih => exact ReversibleReach.head he hr (ih hbc)

/-- Reversing an arbitrary finite legal parent path relocates its root,
preserves exactly the same equality relation, and changes no parent off that path. -/
theorem PGraph.reroot_reversible {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R)
    {a r : Term (sigma ⊕ sigma) nu} (hpath : ReversibleReach rho a r)
    (hr : rho.NF r) :
    ∃ beta : PGraph A R, beta.NF a ∧
      (∀ x y, EqvOn A beta.par x y ↔ EqvOn A rho.par x y) ∧
      ∀ x, ¬ Reach rho.par a x → beta.par x = rho.par x := by
  revert hr
  induction hpath with
  | refl a =>
      intro ha
      exact ⟨rho, ha, fun _ _ => Iff.rfl, fun _ _ => rfl⟩
  | @head a b r hab hreverse hbr ih =>
      intro hr
      obtain ⟨beta, hbnf, heq, hoff⟩ := ih hr
      have hnoBack : ¬ Reach rho.par b a := fun h => rho.term.no_parent_cycle hab h
      have hbetaAB : beta.par a = some b := (hoff a hnoBack).trans hab
      have hreverseBeta : Grey A R (EqvOn A beta.par) b a :=
        Grey.mono (fun x y h => (heq x y).mpr h) hreverse
      obtain ⟨gamma, _, hgnf, _, hgeq, hgoff⟩ :=
        beta.reroot_one hbetaAB hbnf hreverseBeta
      refine ⟨gamma, hgnf, fun x y => (hgeq x y).trans (heq x y), ?_⟩
      intro x hx
      have hxa : x ≠ a := by
        intro hxa
        subst x
        exact hx (Reach.refl a)
      have hxb : x ≠ b := by
        intro hxb
        subst x
        exact hx (Reach.head hab (Reach.refl b))
      exact (hgoff x hxa hxb).trans
        (hoff x (fun hbx => hx (Reach.head hab hbx)))

/-- Every destructor-guided parent path has legal reversed edges. -/
theorem GuidedReach.reversible {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {rho : PGraph A R}
    {a b : Term (sigma ⊕ sigma) nu} (h : GuidedReach rho a b) :
    ReversibleReach rho a b := by
  induction h with
  | refl => exact ReversibleReach.refl a
  | @tail b c hprev hstep ih =>
      exact ih.trans (ReversibleReach.head hstep.1
        (Or.inr (Or.inl hstep.2.symm.2.2)) (ReversibleReach.refl c))

/-- Rerooting a reversible path followed by a legal edge into another equality
class produces a proof graph containing every old equality and the new edge. -/
theorem PGraph.repair_along_reversible_path
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R) (rho : PGraph A R)
    {a r b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hpath : ReversibleReach rho a r) (hr : rho.NF r)
    (hne : ¬ EqvOn A rho.par a b) (hgrey : Grey A R (EqvOn A rho.par) a b) :
    ∃ beta : PGraph A R, beta.par a = some b ∧
      (∀ x y, EqvOn A rho.par x y → EqvOn A beta.par x y) ∧
      EqvOn A beta.par a b := by
  obtain ⟨gamma, hgnf, heq, _⟩ := rho.reroot_reversible hpath hr
  have hneGamma : ¬ EqvOn A gamma.par a b := fun h => hne ((heq a b).mp h)
  have hgreyGamma : Grey A R (EqvOn A gamma.par) a b :=
    Grey.mono (fun x y h => (heq x y).mpr h) hgrey
  obtain ⟨beta, hext, hedge⟩ := gamma.extend_one hA hR ha hb hgnf hneGamma hgreyGamma
  refine ⟨beta, hedge, ?_, EqvOn.of_reach ha hb (Reach.head hedge (Reach.refl b))⟩
  intro x y hxy
  exact EqvOn.mono hext ((heq x y).mpr hxy)

/-- A root rewrite can be represented after any destructor-guided path to a
graph root, without discarding a previously represented equality. -/
theorem PGraph.repair_rootStep_along_guided_path
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R) (rho : PGraph A R)
    {a r b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hpath : GuidedReach rho a r) (hr : rho.NF r)
    (hne : ¬ EqvOn A rho.par a b) (hroot : rootStep R a b) :
    ∃ beta : PGraph A R, beta.par a = some b ∧
      (∀ x y, EqvOn A rho.par x y → EqvOn A beta.par x y) ∧
      EqvOn A beta.par a b :=
  rho.repair_along_reversible_path hA hR ha hb hpath.reversible hr hne (Or.inl hroot)

/-! ## Completion by represented equalities -/

/-- Equality extension retains every represented pair, but may replace parent edges. -/
def PGraph.EqualityExtends {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (alpha beta : PGraph A R) : Prop :=
  ∀ ⦃x y⦄, EqvOn A alpha.par x y → EqvOn A beta.par x y

theorem PGraph.EqualityExtends.refl {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R) : rho.EqualityExtends rho := by
  intro x y h
  exact h

theorem PGraph.EqualityExtends.trans {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} {alpha beta gamma : PGraph A R}
    (hab : alpha.EqualityExtends beta) (hbc : beta.EqualityExtends gamma) :
    alpha.EqualityExtends gamma := by
  intro x y h
  exact hbc (hab h)

/-- No proof graph represents a strict superset of these equalities. -/
def PGraph.EqualityComplete {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R) : Prop :=
  ∀ beta : PGraph A R, rho.EqualityExtends beta → beta.EqualityExtends rho

noncomputable def PGraph.eqvPairs {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R) :
    Finset (Term (sigma ⊕ sigma) nu × Term (sigma ⊕ sigma) nu) := by
  classical
  exact (A.toFinset ×ˢ A.toFinset).filter (fun p => EqvOn A rho.par p.1 p.2)

theorem PGraph.mem_eqvPairs {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R)
    (x y : Term (sigma ⊕ sigma) nu) :
    (x, y) ∈ rho.eqvPairs ↔ EqvOn A rho.par x y := by
  classical
  simp only [PGraph.eqvPairs, Finset.mem_filter, Finset.mem_product, List.mem_toFinset]
  exact ⟨fun h => h.2, fun h => ⟨⟨h.1, h.2.1⟩, h⟩⟩

theorem PGraph.eqvPairs_subset_iff {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (alpha beta : PGraph A R) :
    alpha.eqvPairs ⊆ beta.eqvPairs ↔ alpha.EqualityExtends beta := by
  constructor
  · intro h x y hxy
    exact (beta.mem_eqvPairs x y).mp (h ((alpha.mem_eqvPairs x y).mpr hxy))
  · intro h p hp
    exact (beta.mem_eqvPairs p.1 p.2).mpr (h ((alpha.mem_eqvPairs p.1 p.2).mp hp))

/-- The finite number of currently unrepresented ordered pairs. -/
noncomputable def PGraph.eqvGap {A : List (Term (sigma ⊕ sigma) nu)}
    {R : TRS (sigma ⊕ sigma) nu} (rho : PGraph A R) : Nat := by
  classical
  exact (A.toFinset ×ˢ A.toFinset).card - rho.eqvPairs.card

theorem PGraph.eqvGap_lt_of_strict_equality_extension
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {alpha beta : PGraph A R} (hab : alpha.EqualityExtends beta)
    (hba : ¬ beta.EqualityExtends alpha) : beta.eqvGap < alpha.eqvGap := by
  classical
  have hstrict : alpha.eqvPairs ⊂ beta.eqvPairs :=
    ⟨(alpha.eqvPairs_subset_iff beta).mpr hab,
      fun h => hba ((beta.eqvPairs_subset_iff alpha).mp h)⟩
  have hlt := Finset.card_lt_card hstrict
  have hbound : beta.eqvPairs.card ≤ (A.toFinset ×ˢ A.toFinset).card :=
    Finset.card_le_card (by
      change (A.toFinset ×ˢ A.toFinset).filter _ ⊆ A.toFinset ×ˢ A.toFinset
      exact Finset.filter_subset _ _)
  unfold PGraph.eqvGap
  omega

/-- Every proof graph has an equality-complete replacement. Each strict
improvement decreases a finite natural count; no transitivity of DownOn is assumed. -/
theorem PGraph.exists_equalityComplete
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) :
    ∃ beta : PGraph A R, rho.EqualityExtends beta ∧ beta.EqualityComplete := by
  classical
  have main : ∀ n : Nat, ∀ alpha : PGraph A R, alpha.eqvGap = n →
      ∃ beta : PGraph A R, alpha.EqualityExtends beta ∧ beta.EqualityComplete := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro alpha hn
        by_cases hcomplete : alpha.EqualityComplete
        · exact ⟨alpha, PGraph.EqualityExtends.refl alpha, hcomplete⟩
        · have hnext : ∃ beta : PGraph A R,
              alpha.EqualityExtends beta ∧ ¬ beta.EqualityExtends alpha := by
            by_contra hnone
            apply hcomplete
            intro beta hab
            by_contra hba
            exact hnone ⟨beta, hab, hba⟩
          obtain ⟨beta, hab, hba⟩ := hnext
          have hlt : beta.eqvGap < n := by
            rw [← hn]
            exact PGraph.eqvGap_lt_of_strict_equality_extension hab hba
          obtain ⟨gamma, hbg, hgc⟩ := ih beta.eqvGap hlt beta rfl
          exact ⟨gamma, hab.trans hbg, hgc⟩
  exact main rho.eqvGap rho rfl

/-- Equality completion implies the existing edge-extension completeness. -/
theorem PGraph.EqualityComplete.complete
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hcomplete : rho.EqualityComplete) : rho.Complete := by
  intro beta hext x y hedge
  cases hx : rho.par x with
  | some z =>
      have hzy : z = y := Option.some.inj ((hext hx).symm.trans hedge)
      exact congrArg some hzy
  | none =>
      have hmono : rho.EqualityExtends beta := by
        intro a b h
        exact EqvOn.mono hext h
      have hxy : EqvOn A rho.par x y := hcomplete beta hmono
        (EqvOn.of_reach (beta.mem_edge hedge).1 (beta.mem_edge hedge).2
          (Reach.head hedge (Reach.refl y)))
      obtain ⟨_, _, z, hxz, hyz⟩ := hxy
      have hxzEq : x = z := hxz.toParentPath.eq_of_none hx
      subst z
      exact (beta.term.no_parent_cycle hedge (hyz.mono hext)).elim

/-- Any strict equality-improvement sequence has length bounded by its initial
number of unrepresented pairs. -/
theorem equality_extension_chain_length_le
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (graphs : Nat → PGraph A R) (n : Nat)
    (hstep : ∀ i < n, (graphs i).EqualityExtends (graphs (i + 1)) ∧
      ¬ (graphs (i + 1)).EqualityExtends (graphs i)) :
    n ≤ (graphs 0).eqvGap := by
  have hbound : ∀ k ≤ n, (graphs k).eqvGap + k ≤ (graphs 0).eqvGap := by
    intro k
    induction k with
    | zero => intro _; omega
    | succ k ih =>
        intro hkn
        have hk : k < n := by omega
        have hprev := ih (by omega)
        have hdrop := PGraph.eqvGap_lt_of_strict_equality_extension
          (hstep k hk).1 (hstep k hk).2
        omega
  have h := hbound n le_rfl
  omega

theorem PGraph.EqualityComplete.grey_of_reversible_to_root
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {rho : PGraph A R} (hcomplete : rho.EqualityComplete)
    {a r b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hpath : ReversibleReach rho a r) (hr : rho.NF r)
    (hgrey : Grey A R (EqvOn A rho.par) a b) : EqvOn A rho.par a b := by
  classical
  by_contra hne
  obtain ⟨beta, _, hmono, hnew⟩ :=
    rho.repair_along_reversible_path hA hR ha hb hpath hr hne hgrey
  have hmono' : rho.EqualityExtends beta := by
    intro x y h
    exact hmono x y h
  exact hne (hcomplete beta hmono' hnew)

theorem PGraph.EqualityComplete.rootStep_of_guided_to_root
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    {rho : PGraph A R} (hcomplete : rho.EqualityComplete)
    {a r b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hpath : GuidedReach rho a r) (hr : rho.NF r)
    (hroot : rootStep R a b) : EqvOn A rho.par a b :=
  hcomplete.grey_of_reversible_to_root hA hR ha hb hpath.reversible hr (Or.inl hroot)

/-- The equality-complete graph exists on every finite constructor coalgebra
and represents every root rewrite whose source has a guided path to a graph root. -/
theorem exists_equalityComplete_with_guided_rootClosure
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R) :
    ∃ rho : PGraph A R, rho.EqualityComplete ∧ rho.Complete ∧
      ∀ a r b, a ∈ A → b ∈ A → GuidedReach rho a r → rho.NF r →
        rootStep R a b → EqvOn A rho.par a b := by
  obtain ⟨rho, _, hmax⟩ := (PGraph.empty A R).exists_equalityComplete
  exact ⟨rho, hmax, hmax.complete, fun _ _ _ ha hb hp hr hs =>
    hmax.rootStep_of_guided_to_root hA hR ha hb hp hr hs⟩

/-! ## Normal roots and shortest routes between destructor fibers -/

/-- The normal root reached by the existing parent function. -/
noncomputable def PGraph.normalRoot
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (a : Term (sigma ⊕ sigma) nu) :
    Term (sigma ⊕ sigma) nu :=
  Classical.choose (exists_root rho.term a)

theorem PGraph.normalRoot_spec
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (a : Term (sigma ⊕ sigma) nu) :
    Reach rho.par a (rho.normalRoot a) ∧ rho.NF (rho.normalRoot a) :=
  Classical.choose_spec (exists_root rho.term a)

theorem PGraph.normalRoot_mem
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {a : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) :
    rho.normalRoot a ∈ A :=
  rho.mem_of_reach_right ha (rho.normalRoot_spec a).1

theorem PGraph.normalRoot_eq_of_reach
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {a b : Term (sigma ⊕ sigma) nu}
    (h : Reach rho.par a b) : rho.normalRoot a = rho.normalRoot b := by
  rcases (rho.normalRoot_spec a).1.comparable
      (h.trans (rho.normalRoot_spec b).1) with hp | hp
  · exact hp.toParentPath.eq_of_none (rho.normalRoot_spec a).2
  · exact (hp.toParentPath.eq_of_none (rho.normalRoot_spec b).2).symm

theorem PGraph.eqvOn_iff_normalRoot_eq
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A) :
    EqvOn A rho.par a b ↔ rho.normalRoot a = rho.normalRoot b := by
  constructor
  · rintro ⟨_, _, z, haz, hbz⟩
    exact (rho.normalRoot_eq_of_reach haz).trans (rho.normalRoot_eq_of_reach hbz).symm
  · intro heq
    refine ⟨ha, hb, rho.normalRoot a, (rho.normalRoot_spec a).1, ?_⟩
    rw [heq]
    exact (rho.normalRoot_spec b).1

/-- Every destructor-fiber edge is represented by the graph equality. -/
def PGraph.BarClosed
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) : Prop :=
  ∀ ⦃a b⦄, BarStepOn A R a b → EqvOn A rho.par a b

theorem PGraph.BarClosed.eqv_of_barReach
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A)
    (h : BarReachOn A R a b) : EqvOn A rho.par a b := by
  revert ha
  induction h with
  | refl a => intro ha; exact EqvOn.refl ha
  | head he _ ih => intro _; exact EqvOn.trans (hclosed he) (ih he.2.1)

theorem PGraph.BarClosed.normalRoot_eq_of_barReach
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A)
    (h : BarReachOn A R a b) : rho.normalRoot a = rho.normalRoot b := by
  have heq := hclosed.eqv_of_barReach ha h
  exact (rho.eqvOn_iff_normalRoot_eq heq.1 heq.2.1).mp heq

theorem Target.baseGraph_barClosed
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R)
    (target : Target A R) : (target.baseGraph hA hR).BarClosed := by
  intro a b hbar
  have hpick := target.pick_eq_of_barReach hbar.1 hbar.2.1
    (BarReachOn.head hbar (BarReachOn.refl b))
  refine ⟨hbar.1, hbar.2.1, target.pick (barClassOf A R a hbar.1),
    (target.guidedReach_baseGraph hA hR a hbar.1).toReach, ?_⟩
  rw [hpick]
  exact (target.guidedReach_baseGraph hA hR b hbar.2.1).toReach

theorem PGraph.BarClosed.mono
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {alpha beta : PGraph A R} (hclosed : alpha.BarClosed)
    (hext : alpha.EqualityExtends beta) : beta.BarClosed := by
  intro a b h
  exact hext (hclosed h)

/-- Equality completion above the destructor spanning forest retains every
destructor-fiber equality. -/
theorem exists_equalityComplete_barClosed
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R) :
    ∃ rho : PGraph A R, rho.EqualityComplete ∧ rho.BarClosed := by
  let target := canonicalTarget A R
  obtain ⟨rho, hext, hmax⟩ := (target.baseGraph hA hR).exists_equalityComplete
  exact ⟨rho, hmax, (target.baseGraph_barClosed hA hR).mono hext⟩

/-- A route uses free destructor-fiber paths and counts actual old parent edges. -/
inductive FiberRouteN
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) :
    Nat → Term (sigma ⊕ sigma) nu → Term (sigma ⊕ sigma) nu → Prop
  | zero {a r} : BarReachOn A R a r → FiberRouteN rho 0 a r
  | head {n a u v r} : BarReachOn A R a u → rho.par u = some v →
      FiberRouteN rho n v r → FiberRouteN rho (n + 1) a r

theorem FiberRouteN.prepend_bar
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {n : Nat} {a b r : Term (sigma ⊕ sigma) nu}
    (hab : BarReachOn A R a b) (h : FiberRouteN rho n b r) :
    FiberRouteN rho n a r := by
  cases h with
  | zero hbr => exact FiberRouteN.zero (hab.trans hbr)
  | head hbu he htail => exact FiberRouteN.head (hab.trans hbu) he htail

theorem FiberRouteN.zero_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {a r : Term (sigma ⊕ sigma) nu} :
    FiberRouteN rho 0 a r ↔ BarReachOn A R a r := by
  constructor
  · intro h; cases h with | zero h => exact h
  · exact FiberRouteN.zero


theorem FiberRouteN.succ_inv
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {n : Nat} {a r : Term (sigma ⊕ sigma) nu}
    (h : FiberRouteN rho (n + 1) a r) :
    ∃ u v, BarReachOn A R a u ∧ rho.par u = some v ∧ FiberRouteN rho n v r := by
  cases h with
  | head hbar he htail => exact ⟨_, _, hbar, he, htail⟩

theorem Reach.toFiberRouteN
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {a r : Term (sigma ⊕ sigma) nu}
    (h : Reach rho.par a r) : ∃ n, FiberRouteN rho n a r := by
  induction h with
  | refl a => exact ⟨0, FiberRouteN.zero (BarReachOn.refl a)⟩
  | @head a b c he hbc ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, FiberRouteN.head (BarReachOn.refl a) he hn⟩

noncomputable def PGraph.fiberDistance
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (a : Term (sigma ⊕ sigma) nu) : Nat := by
  classical
  exact Nat.find (rho.normalRoot_spec a).1.toFiberRouteN

theorem PGraph.fiberDistance_spec
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (a : Term (sigma ⊕ sigma) nu) :
    FiberRouteN rho (rho.fiberDistance a) a (rho.normalRoot a) := by
  classical
  exact Nat.find_spec (rho.normalRoot_spec a).1.toFiberRouteN

theorem PGraph.fiberDistance_le
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) {n : Nat} {a : Term (sigma ⊕ sigma) nu}
    (h : FiberRouteN rho n a (rho.normalRoot a)) : rho.fiberDistance a ≤ n := by
  classical
  exact Nat.find_min' (rho.normalRoot_spec a).1.toFiberRouteN h

theorem PGraph.fiberDistance_zero_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (a : Term (sigma ⊕ sigma) nu) :
    rho.fiberDistance a = 0 ↔ BarReachOn A R a (rho.normalRoot a) := by
  constructor
  · intro hzero
    have hs := rho.fiberDistance_spec a
    rw [hzero] at hs
    exact FiberRouteN.zero_iff.mp hs
  · intro hbar
    exact Nat.eq_zero_of_le_zero (rho.fiberDistance_le (FiberRouteN.zero hbar))

theorem PGraph.BarClosed.fiberDistance_eq_of_barReach
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (_hb : b ∈ A)
    (hbar : BarReachOn A R a b) : rho.fiberDistance a = rho.fiberDistance b := by
  have hr := hclosed.normalRoot_eq_of_barReach ha hbar
  apply Nat.le_antisymm
  · apply rho.fiberDistance_le
    rw [hr]
    exact (rho.fiberDistance_spec b).prepend_bar hbar
  · apply rho.fiberDistance_le
    rw [← hr]
    exact (rho.fiberDistance_spec a).prepend_bar hbar.symm

/-- Every positive minimum is attained by an old parent edge leaving its fiber
and strictly decreasing the minimum. -/
theorem PGraph.BarClosed.exists_distance_decreasing_exit
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed)
    {a : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hpos : rho.fiberDistance a ≠ 0) :
    ∃ u v, u ∈ A ∧ v ∈ A ∧ BarReachOn A R a u ∧ rho.par u = some v ∧
      rho.fiberDistance u = rho.fiberDistance a ∧
      rho.fiberDistance v < rho.fiberDistance a ∧ ¬ BarReachOn A R u v := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hs := rho.fiberDistance_spec a
  rw [hn] at hs
  obtain ⟨u, v, hbar, he, htail⟩ := FiberRouteN.succ_inv hs
  have hu := (rho.mem_edge he).1
  have hv := (rho.mem_edge he).2
  have hau := hclosed.eqv_of_barReach ha hbar
  have huv := EqvOn.of_reach hu hv (Reach.head he (Reach.refl v))
  have hav := EqvOn.trans hau huv
  have hr := (rho.eqvOn_iff_normalRoot_eq ha hv).mp hav
  have hvle : rho.fiberDistance v ≤ n := by
    apply rho.fiberDistance_le
    rw [← hr]
    exact htail
  have huEq := hclosed.fiberDistance_eq_of_barReach ha hu hbar
  have hvlt : rho.fiberDistance v < rho.fiberDistance a := by omega
  refine ⟨u, v, hu, hv, hbar, he, huEq.symm, hvlt, ?_⟩
  intro huvbar
  have hsame := hclosed.fiberDistance_eq_of_barReach hu hv huvbar
  omega

/-- Fiber paths preserve the old normal root even for reflexive paths outside A. -/
theorem PGraph.BarClosed.normalRoot_eq_of_barReach_all
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed)
    {a b : Term (sigma ⊕ sigma) nu} (hbar : BarReachOn A R a b) :
    rho.normalRoot a = rho.normalRoot b := by
  induction hbar with
  | refl a => rfl
  | head he _ ih =>
      exact ((rho.eqvOn_iff_normalRoot_eq he.1 he.2.1).mp (hclosed he)).trans ih

theorem PGraph.BarClosed.fiberDistance_eq_of_barReach_all
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed)
    {a b : Term (sigma ⊕ sigma) nu} (hbar : BarReachOn A R a b) :
    rho.fiberDistance a = rho.fiberDistance b := by
  have hr := hclosed.normalRoot_eq_of_barReach_all hbar
  apply Nat.le_antisymm
  · apply rho.fiberDistance_le
    rw [hr]
    exact (rho.fiberDistance_spec b).prepend_bar hbar
  · apply rho.fiberDistance_le
    rw [← hr]
    exact (rho.fiberDistance_spec a).prepend_bar hbar.symm


/-! ## Selecting targets from attained exits -/

/-- An exit consists of an actual old edge with the attained distance laws. -/
structure FiberExit
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (rho : PGraph A R) (a : Term (sigma ⊕ sigma) nu) where
  src : Term (sigma ⊕ sigma) nu
  dst : Term (sigma ⊕ sigma) nu
  src_mem : src ∈ A
  dst_mem : dst ∈ A
  sameFiber : BarReachOn A R a src
  edge : rho.par src = some dst
  distance_src : rho.fiberDistance src = rho.fiberDistance a
  distance_drop : rho.fiberDistance dst < rho.fiberDistance a
  exits : ¬ BarReachOn A R src dst

noncomputable def PGraph.BarClosed.exitChoice
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed)
    {a : Term (sigma ⊕ sigma) nu} (ha : a ∈ A)
    (hpos : rho.fiberDistance a ≠ 0) : FiberExit rho a :=
  Classical.choice (by
    obtain ⟨u, v, hu, hv, hbar, he, heq, hlt, hout⟩ :=
      hclosed.exists_distance_decreasing_exit ha hpos
    exact ⟨⟨u, v, hu, hv, hbar, he, heq, hlt, hout⟩⟩)

/-- A destructor class containing a root redex has no constructor-topped member. -/
theorem RedexClass.not_conTopped_source
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (hR : ConstructorRules R) {a : Term (sigma ⊕ sigma) nu}
    (hred : RedexClass A R a) : ¬ ConTopped a := by
  obtain ⟨u, _, hbar, v, _, hroot⟩ := hred
  cases hbar with
  | refl =>
      obtain ⟨d, args, rfl⟩ := rootStep_source_destructor hR hroot
      exact not_conTopped_destructor args
  | head hstep _ =>
      obtain ⟨f, as, bs, ⟨d, rfl⟩, rfl, _, _⟩ := hstep.2.2
      exact not_conTopped_destructor as

/-- The selected exit is a root rewrite whenever its fiber contains a redex. -/
theorem FiberExit.rootStep_of_redexClass
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} {a : Term (sigma ⊕ sigma) nu}
    (exit : FiberExit rho a) (hR : ConstructorRules R)
    (hred : RedexClass A R a) : rootStep R exit.src exit.dst := by
  have hredSrc : RedexClass A R exit.src := by
    obtain ⟨u, hu, hau, v, hv, hroot⟩ := hred
    exact ⟨u, hu, exit.sameFiber.symm.trans hau, v, hv, hroot⟩
  rcases rho.grey exit.edge with hroot | hbar | hhat
  · exact hroot
  · exact (exit.exits (BarReachOn.head ⟨exit.src_mem, exit.dst_mem, hbar⟩
      (BarReachOn.refl exit.dst))).elim
  · exact (RedexClass.not_conTopped_source hR hredSrc (ConTopped.of_hatEq hhat)).elim

noncomputable def PGraph.BarClosed.retargetPick
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (C : BarClass A R) :
    Term (sigma ⊕ sigma) nu := by
  classical
  let seed := canonicalTarget A R
  exact if hpos : rho.fiberDistance (seed.pick C) ≠ 0 then
    (hclosed.exitChoice (seed.pick_mem C) hpos).src else seed.pick C

noncomputable def PGraph.BarClosed.retargetExit
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (C : BarClass A R) :
    Option (Term (sigma ⊕ sigma) nu) := by
  classical
  let seed := canonicalTarget A R
  exact if hpos : rho.fiberDistance (seed.pick C) ≠ 0 then
    some (hclosed.exitChoice (seed.pick_mem C) hpos).dst else none

theorem PGraph.BarClosed.retargetPick_mem
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (C : BarClass A R) :
    hclosed.retargetPick C ∈ A := by
  classical
  unfold PGraph.BarClosed.retargetPick
  dsimp only
  split
  · exact (hclosed.exitChoice _ _).src_mem
  · exact (canonicalTarget A R).pick_mem C

theorem PGraph.BarClosed.retargetPick_inFiber
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (C : BarClass A R) :
    BarReachOn A R ((canonicalTarget A R).pick C) (hclosed.retargetPick C) := by
  classical
  unfold PGraph.BarClosed.retargetPick
  dsimp only
  split
  · exact (hclosed.exitChoice _ _).sameFiber
  · exact BarReachOn.refl _

theorem PGraph.BarClosed.retargetPick_distance
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (C : BarClass A R) :
    rho.fiberDistance (hclosed.retargetPick C) =
      rho.fiberDistance ((canonicalTarget A R).pick C) :=
  (hclosed.fiberDistance_eq_of_barReach ((canonicalTarget A R).pick_mem C)
    (hclosed.retargetPick_mem C) (hclosed.retargetPick_inFiber C)).symm

theorem PGraph.BarClosed.retargetExit_spec
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) {C : BarClass A R}
    {v : Term (sigma ⊕ sigma) nu} (he : hclosed.retargetExit C = some v) :
    rho.par (hclosed.retargetPick C) = some v ∧ v ∈ A ∧
      rho.fiberDistance v < rho.fiberDistance (hclosed.retargetPick C) := by
  classical
  unfold PGraph.BarClosed.retargetExit at he
  dsimp only at he
  split at he
  · rename_i hpos
    have hv := Option.some.inj he
    subst v
    rw [PGraph.BarClosed.retargetPick]
    rw [dif_pos hpos]
    exact ⟨(hclosed.exitChoice _ hpos).edge,
      (hclosed.exitChoice _ hpos).dst_mem,
      by rw [(hclosed.exitChoice _ hpos).distance_src]
         exact (hclosed.exitChoice _ hpos).distance_drop⟩
  · contradiction

theorem PGraph.BarClosed.retargetExit_none_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (C : BarClass A R) :
    hclosed.retargetExit C = none ↔ rho.fiberDistance (hclosed.retargetPick C) = 0 := by
  classical
  rw [hclosed.retargetPick_distance C]
  unfold PGraph.BarClosed.retargetExit
  dsimp only
  by_cases hp : rho.fiberDistance ((canonicalTarget A R).pick C) ≠ 0
  · simp [hp]
  · simp [not_not.mp hp]

/-- Positive-distance fibers select an actual decreasing exit source;
zero-distance fibers retain the existing redex-priority representative. -/
noncomputable def PGraph.BarClosed.retarget
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R) :
    Target A R where
  pick := hclosed.retargetPick
  pick_mem := hclosed.retargetPick_mem
  inFiber := by
    intro t ht
    exact ((canonicalTarget A R).inFiber t ht).trans
      (hclosed.retargetPick_inFiber (barClassOf A R t ht))
  redexPriority := by
    intro t ht hred
    classical
    let C := barClassOf A R t ht
    let seed := canonicalTarget A R
    have hredSeed : RedexClass A R (seed.pick C) := by
      obtain ⟨u, hu, htu, v, hv, huv⟩ := hred
      exact ⟨u, hu, (seed.inFiber t ht).symm.trans htu, v, hv, huv⟩
    change ∃ v, v ∈ A ∧ rootStep R (hclosed.retargetPick C) v
    unfold PGraph.BarClosed.retargetPick
    dsimp only
    by_cases hp : rho.fiberDistance (seed.pick C) ≠ 0
    · rw [dif_pos hp]
      exact ⟨(hclosed.exitChoice (seed.pick_mem C) hp).dst,
        (hclosed.exitChoice (seed.pick_mem C) hp).dst_mem,
        (hclosed.exitChoice (seed.pick_mem C) hp).rootStep_of_redexClass hR hredSeed⟩
    · rw [dif_neg hp]
      exact seed.redexPriority t ht hred

theorem PGraph.BarClosed.retarget_pick_distance
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R)
    {t : Term (sigma ⊕ sigma) nu} (ht : t ∈ A) :
    rho.fiberDistance ((hclosed.retarget hR).pick (barClassOf A R t ht)) =
      rho.fiberDistance t :=
  (hclosed.fiberDistance_eq_of_barReach ht ((hclosed.retarget hR).pick_mem _)
    ((hclosed.retarget hR).inFiber t ht)).symm

/-! ## Reconstructed parents and exact equality transport -/

noncomputable def PGraph.BarClosed.retargetParent
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R)
    (t : Term (sigma ⊕ sigma) nu) : Option (Term (sigma ⊕ sigma) nu) := by
  classical
  let target := hclosed.retarget hR
  exact if ht : t ∈ A then
    if t = target.pick (barClassOf A R t ht) then
      hclosed.retargetExit (barClassOf A R t ht)
    else target.parent t
  else none

theorem PGraph.BarClosed.retargetParent_of_target
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R)
    {t : Term (sigma ⊕ sigma) nu} (ht : t ∈ A)
    (heq : t = (hclosed.retarget hR).pick (barClassOf A R t ht)) :
    hclosed.retargetParent hR t = hclosed.retargetExit (barClassOf A R t ht) := by
  classical
  unfold PGraph.BarClosed.retargetParent
  dsimp only
  rw [dif_pos ht, if_pos heq]

theorem PGraph.BarClosed.retargetParent_of_nontarget
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R)
    {t : Term (sigma ⊕ sigma) nu} (ht : t ∈ A)
    (hne : t ≠ (hclosed.retarget hR).pick (barClassOf A R t ht)) :
    hclosed.retargetParent hR t = (hclosed.retarget hR).parent t := by
  classical
  unfold PGraph.BarClosed.retargetParent
  dsimp only
  rw [dif_pos ht, if_neg hne]

/-- Each changed parent is either a distance-decreasing destructor edge or an
actual old edge that decreases the distance between fibers. -/
theorem PGraph.BarClosed.retargetParent_edge
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R)
    {a b : Term (sigma ⊕ sigma) nu} (he : hclosed.retargetParent hR a = some b) :
    a ∈ A ∧ b ∈ A ∧
      ((BarStepOn A R a b ∧
          (hclosed.retarget hR).distance b < (hclosed.retarget hR).distance a) ∨
        (rho.par a = some b ∧ rho.fiberDistance b < rho.fiberDistance a)) := by
  classical
  unfold PGraph.BarClosed.retargetParent at he
  dsimp only at he
  split at he
  · rename_i ha
    split at he
    · rename_i hpick
      have hs := hclosed.retargetExit_spec he
      refine ⟨ha, hs.2.1, Or.inr ?_⟩
      have hpar : rho.par a = some b := by rw [hpick]; exact hs.1
      have hdrop : rho.fiberDistance b < rho.fiberDistance a := by
        rw [hpick]
        exact hs.2.2
      exact ⟨hpar, hdrop⟩
    · have hs := (hclosed.retarget hR).parent_edge he
      exact ⟨hs.1, hs.2.1, Or.inl ⟨hs.2.2.1, hs.2.2.2⟩⟩
  · contradiction

theorem PGraph.BarClosed.retargetParent_decreases
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R)
    {a b : Term (sigma ⊕ sigma) nu} (he : hclosed.retargetParent hR a = some b) :
    rho.fiberDistance b < rho.fiberDistance a ∨
      (rho.fiberDistance b = rho.fiberDistance a ∧
        (hclosed.retarget hR).distance b < (hclosed.retarget hR).distance a) := by
  rcases (hclosed.retargetParent_edge hR he).2.2 with ⟨hbar, hdist⟩ | ⟨_, hdist⟩
  · exact Or.inr ⟨(hclosed.fiberDistance_eq_of_barReach_all
      (BarReachOn.head hbar (BarReachOn.refl b))).symm, hdist⟩
  · exact Or.inl hdist

/-- Termination uses the actual changed parents and the two natural distances. -/
theorem PGraph.BarClosed.retargetParent_terminating
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R) :
    Terminating (hclosed.retargetParent hR) := by
  let rel := fun b a => hclosed.retargetParent hR a = some b
  have main : ∀ i j : Nat, ∀ t : Term (sigma ⊕ sigma) nu,
      rho.fiberDistance t = i → (hclosed.retarget hR).distance t = j → Acc rel t := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
        intro j
        induction j using Nat.strong_induction_on with
        | h j jh =>
            intro t hi hj
            refine Acc.intro t ?_
            intro b he
            rcases hclosed.retargetParent_decreases hR he with hd | ⟨hiEq, hd⟩
            · exact ih (rho.fiberDistance b) (by omega)
                ((hclosed.retarget hR).distance b) b rfl rfl
            · exact jh ((hclosed.retarget hR).distance b) (by omega) b
                (by omega) rfl
  exact ⟨fun t => main (rho.fiberDistance t) ((hclosed.retarget hR).distance t) t rfl rfl⟩

theorem PGraph.BarClosed.retargetParent_extends_target
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R)
    {a b : Term (sigma ⊕ sigma) nu} (he : (hclosed.retarget hR).parent a = some b) :
    hclosed.retargetParent hR a = some b := by
  have ha := ((hclosed.retarget hR).parent_edge he).1
  have hne : a ≠ (hclosed.retarget hR).pick (barClassOf A R a ha) := by
    intro hp
    have hn := (hclosed.retarget hR).parent_eq_none_of_target ha hp
    rw [hn] at he
    contradiction
  exact (hclosed.retargetParent_of_nontarget hR ha hne).trans he

theorem PGraph.BarClosed.retargetParent_old_eqv
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R)
    {a b : Term (sigma ⊕ sigma) nu} (he : hclosed.retargetParent hR a = some b) :
    EqvOn A rho.par a b := by
  obtain ⟨ha, hb, hcase⟩ := hclosed.retargetParent_edge hR he
  rcases hcase with ⟨hbar, _⟩ | ⟨hpar, _⟩
  · exact hclosed hbar
  · exact EqvOn.of_reach ha hb (Reach.head hpar (Reach.refl b))

theorem PGraph.BarClosed.retargetParent_normalRoot_eq
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R)
    {a b : Term (sigma ⊕ sigma) nu} (h : Reach (hclosed.retargetParent hR) a b) :
    rho.normalRoot a = rho.normalRoot b := by
  induction h with
  | refl a => rfl
  | head he _ ih =>
      have hxy := hclosed.retargetParent_old_eqv hR he
      exact ((rho.eqvOn_iff_normalRoot_eq hxy.1 hxy.2.1).mp hxy).trans ih

theorem PGraph.BarClosed.retargetParent_mem_reach
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R)
    {a b : Term (sigma ⊕ sigma) nu} (h : Reach (hclosed.retargetParent hR) a b)
    (ha : a ∈ A) : b ∈ A := by
  revert ha
  induction h with
  | refl a => exact id
  | head he _ ih => intro _; exact ih (hclosed.retargetParent_edge hR he).2.1

noncomputable def PGraph.BarClosed.retargetSink
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R)
    (a : Term (sigma ⊕ sigma) nu) (ha : a ∈ A) : Term (sigma ⊕ sigma) nu :=
  (hclosed.retarget hR).pick (barClassOf A R (rho.normalRoot a) (rho.normalRoot_mem ha))

theorem PGraph.BarClosed.retargetSink_eq_of_normalRoot_eq
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R)
    {a b : Term (sigma ⊕ sigma) nu} (ha : a ∈ A) (hb : b ∈ A)
    (hr : rho.normalRoot a = rho.normalRoot b) :
    hclosed.retargetSink hR a ha = hclosed.retargetSink hR b hb := by
  unfold PGraph.BarClosed.retargetSink
  apply congrArg (hclosed.retarget hR).pick
  apply Quotient.sound
  change BarReachOn A R (rho.normalRoot a) (rho.normalRoot b)
  rw [hr]
  exact BarReachOn.refl _

theorem PGraph.BarClosed.retargetParent_terminal_eq_sink
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R)
    {a : Term (sigma ⊕ sigma) nu} (ha : a ∈ A)
    (hn : hclosed.retargetParent hR a = none) :
    a = hclosed.retargetSink hR a ha := by
  classical
  have hp : a = (hclosed.retarget hR).pick (barClassOf A R a ha) := by
    by_contra hne
    have hs := (hclosed.retarget hR).parent_eq_some_next ha hne
    have hs' := hclosed.retargetParent_extends_target hR hs
    rw [hn] at hs'
    contradiction
  have hexit : hclosed.retargetExit (barClassOf A R a ha) = none :=
    (hclosed.retargetParent_of_target hR ha hp).symm.trans hn
  have hz : rho.fiberDistance a = 0 := by
    rw [hp]
    exact (hclosed.retargetExit_none_iff _).mp hexit
  have hbar := (rho.fiberDistance_zero_iff a).mp hz
  have hpick := (hclosed.retarget hR).pick_eq_of_barReach ha (rho.normalRoot_mem ha) hbar
  exact hp.trans hpick

/-- Every old equality class reaches one actual new root. -/
theorem PGraph.BarClosed.retargetParent_reaches_sink
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R)
    (a : Term (sigma ⊕ sigma) nu) (ha : a ∈ A) :
    Reach (hclosed.retargetParent hR) a (hclosed.retargetSink hR a ha) := by
  obtain ⟨r, har, hr⟩ := exists_root (hclosed.retargetParent_terminating hR) a
  have hrA := hclosed.retargetParent_mem_reach hR har ha
  have hterminal := hclosed.retargetParent_terminal_eq_sink hR hrA hr
  have hsinks := hclosed.retargetSink_eq_of_normalRoot_eq hR ha hrA
    (hclosed.retargetParent_normalRoot_eq hR har)
  have hrEq : r = hclosed.retargetSink hR a ha := hterminal.trans hsinks.symm
  simpa only [hrEq] using har

theorem PGraph.BarClosed.retargetParent_eqv_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R)
    (a b : Term (sigma ⊕ sigma) nu) :
    EqvOn A (hclosed.retargetParent hR) a b ↔ EqvOn A rho.par a b := by
  constructor
  · exact EqvOn.mono_of_parent_eqv (by
      intro x y he
      exact hclosed.retargetParent_old_eqv hR he)
  · intro hab
    have hsinks := hclosed.retargetSink_eq_of_normalRoot_eq hR hab.1 hab.2.1
      ((rho.eqvOn_iff_normalRoot_eq hab.1 hab.2.1).mp hab)
    refine ⟨hab.1, hab.2.1, hclosed.retargetSink hR a hab.1,
      hclosed.retargetParent_reaches_sink hR a hab.1, ?_⟩
    rw [hsinks]
    exact hclosed.retargetParent_reaches_sink hR b hab.2.1

/-- The reconstructed graph has the same equality relation, not an assumed
equality certificate supplied by a caller. -/
noncomputable def PGraph.BarClosed.retargetGraph
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R) :
    PGraph A R where
  par := hclosed.retargetParent hR
  mem_edge := by
    intro a b he
    have hs := hclosed.retargetParent_edge hR he
    exact ⟨hs.1, hs.2.1⟩
  term := hclosed.retargetParent_terminating hR
  sub := by
    intro a b he
    exact rho.sub ((hclosed.retargetParent_eqv_iff hR a b).mp he)
  grey := by
    intro a b he
    rcases (hclosed.retargetParent_edge hR he).2.2 with ⟨hbar, _⟩ | ⟨hold, _⟩
    · exact Or.inr (Or.inl hbar.2.2)
    · exact Grey.mono (fun x y h => (hclosed.retargetParent_eqv_iff hR x y).mpr h)
        (rho.grey hold)

theorem PGraph.BarClosed.retargetGraph_eqv_iff
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R)
    (a b : Term (sigma ⊕ sigma) nu) :
    EqvOn A (hclosed.retargetGraph hR).par a b ↔ EqvOn A rho.par a b :=
  hclosed.retargetParent_eqv_iff hR a b

/-- Retaining the target-distance forest gives guided paths without a coalgebra
or overlap premise. -/
theorem Target.guidedReach_of_parent_extension
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    (target : Target A R) (rho : PGraph A R)
    (hext : ∀ {a b}, target.parent a = some b → rho.par a = some b)
    (t : Term (sigma ⊕ sigma) nu) (ht : t ∈ A) :
    GuidedReach rho t (target.pick (barClassOf A R t ht)) := by
  have hwf : WellFounded (fun x y : Term (sigma ⊕ sigma) nu =>
      target.distance x < target.distance y) :=
    InvImage.wf (f := target.distance) Nat.lt_wfRel.wf
  revert ht
  induction t using hwf.induction with
  | _ t ih =>
      intro ht
      by_cases heq : t = target.pick (barClassOf A R t ht)
      · rw [← heq]
        exact Relation.ReflTransGen.refl
      · have hs := target.next_spec t ht heq
        have hnextMem := hs.1.2.1
        have htail := ih (target.next t ht heq) hs.2 hnextMem
        have hpick := target.pick_eq_of_barReach ht hnextMem
          (BarReachOn.head hs.1 (BarReachOn.refl _))
        rw [← hpick] at htail
        exact Relation.ReflTransGen.head
          ⟨hext (target.parent_eq_some_next ht heq), hs.1⟩ htail

noncomputable def PGraph.BarClosed.retargeted
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R) :
    TargetedPGraph A R where
  graph := hclosed.retargetGraph hR
  target := hclosed.retarget hR
  guided_or_nf := by
    intro t ht
    exact Or.inl ((hclosed.retarget hR).guidedReach_of_parent_extension
      (hclosed.retargetGraph hR) (by
        intro a b he
        exact hclosed.retargetParent_extends_target hR he) t ht)
  target_exit := by
    intro t ht u he hbar
    have hu := ((hclosed.retargetGraph hR).mem_edge he).2
    have hpick := (hclosed.retarget hR).pick_eq_of_barReach ht hu hbar
    have hreturn := (hclosed.retarget hR).guidedReach_of_parent_extension
      (hclosed.retargetGraph hR) (by
        intro a b h
        exact hclosed.retargetParent_extends_target hR h) u hu
    rw [← hpick] at hreturn
    exact (hclosed.retargetGraph hR).term.no_parent_cycle he hreturn.toReach

theorem PGraph.BarClosed.retargeted_allGuided
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R) :
    (hclosed.retargeted hR).AllGuided := by
  intro t ht
  exact (hclosed.retarget hR).guidedReach_of_parent_extension
    (hclosed.retargetGraph hR) (by
      intro a b he
      exact hclosed.retargetParent_extends_target hR he) t ht

theorem PGraph.BarClosed.retargeted_equalityComplete
    {A : List (Term (sigma ⊕ sigma) nu)} {R : TRS (sigma ⊕ sigma) nu}
    {rho : PGraph A R} (hclosed : rho.BarClosed) (hR : ConstructorRules R)
    (hmax : rho.EqualityComplete) : (hclosed.retargeted hR).graph.EqualityComplete := by
  intro gamma hnew x y hxy
  have hrhoGamma : rho.EqualityExtends gamma := by
    intro a b h
    exact hnew ((hclosed.retargetGraph_eqv_iff hR a b).mpr h)
  have hold := hmax gamma hrhoGamma hxy
  exact (hclosed.retargetGraph_eqv_iff hR x y).mpr hold

/-- Every finite constructor coalgebra admits an equality-maximal, all-guided
targeted graph with the actual target and parent laws proved above. -/
theorem exists_equalityComplete_targeted
    {A : List (Term (sigma ⊕ sigma) nu)} (hA : Coalgebra A)
    {R : TRS (sigma ⊕ sigma) nu} (hR : ConstructorRules R) :
    ∃ rho : TargetedPGraph A R, rho.graph.EqualityComplete ∧
      rho.graph.Complete ∧ rho.AllGuided := by
  obtain ⟨rho, hmax, hbar⟩ := exists_equalityComplete_barClosed hA hR
  have hmaxNew := hbar.retargeted_equalityComplete hR hmax
  exact ⟨hbar.retargeted hR, hmaxNew, hmaxNew.complete, hbar.retargeted_allGuided hR⟩

end OperatorKO7.Meta.UniqueNormalization

/-! ## Reach and axiom audit -/

#check @OperatorKO7.Meta.UniqueNormalization.lemma52
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.extend_one
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.mem_of_reach_right
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.constructorClosed_of_complete

#print axioms OperatorKO7.Meta.UniqueNormalization.exists_root
#print axioms OperatorKO7.Meta.UniqueNormalization.downOn_peel
#print axioms OperatorKO7.Meta.UniqueNormalization.lemma52_diag
#print axioms OperatorKO7.Meta.UniqueNormalization.lemma52
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.extend_one
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.mem_of_reach_right
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.constructorClosed_of_complete
