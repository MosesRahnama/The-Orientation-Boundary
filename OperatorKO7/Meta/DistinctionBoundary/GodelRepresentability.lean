import OperatorKO7.Meta.DistinctionBoundary.GodelArithmetization

set_option autoImplicit false

/-!
# Hilbert sequences and ProofTree flattening

A Hilbert sequence is a finite list of formulas in which every line is
an axiom, the conclusion of MP from earlier lines, a generalization of
an earlier line, or a closed instantiation of an earlier universal.
Every checked `ProofTree` flattens to such a sequence.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

def HilbertJust (seq : List Formula) (i : Nat) : Prop :=
  i < seq.length ∧
    ((∃ φ, seq[i]? = some φ ∧ isAxiom φ = true) ∨
      (∃ j k a b, j < i ∧ k < i ∧
        seq[j]? = some (Formula.imp a b) ∧ seq[k]? = some a ∧ seq[i]? = some b) ∨
      (∃ j x φ, j < i ∧ seq[j]? = some φ ∧ seq[i]? = some (Formula.all x φ)) ∨
      (∃ j x t φ, j < i ∧ isClosedTerm t = true ∧
        seq[j]? = some (Formula.all x φ) ∧ seq[i]? = some (substForm x t φ)))

def HilbertSeq (seq : List Formula) : Prop :=
  ∀ i, i < seq.length → HilbertJust seq i

def HilbertProvable (φ : Formula) : Prop :=
  ∃ seq : List Formula, seq.getLast? = some φ ∧ seq ≠ [] ∧ HilbertSeq seq

def flattenProof : ProofTree → List Formula
  | .ax φ => [φ]
  | .mp p q =>
    flattenProof p ++ flattenProof q ++
      match check p with
      | some (Formula.imp _ b) => [b]
      | _ => []
  | .gen x p =>
    flattenProof p ++
      match check p with
      | some φ => [Formula.all x φ]
      | none => []
  | .spec x t p =>
    flattenProof p ++
      match check p with
      | some (Formula.all y φ) =>
          if decide (x = y) && isClosedTerm t then [substForm x t φ] else []
      | _ => []

theorem getLast?_concat {α : Type} (l : List α) (a : α) :
    (l ++ [a]).getLast? = some a := by
  induction l with
  | nil => rfl
  | cons _ _ ih =>
    simpa [List.getLast?] using ih

theorem flatten_last_of_check :
    ∀ p : ProofTree, ∀ φ : Formula, check p = some φ →
      (flattenProof p).getLast? = some φ
  | .ax ψ, φ, h => by
    simp [check] at h
    rcases h with ⟨_, rfl⟩
    rfl
  | .mp p q, φ, h => by
    cases hp : check p with
    | none => simp [check, hp] at h
    | some a =>
      cases hq : check q with
      | none => simp [check, hp, hq] at h
      | some c =>
        simp [check, hp, hq] at h
        cases a with
        | imp u v =>
          simp at h
          rcases h with ⟨rfl, rfl⟩
          simp [flattenProof, hp, getLast?_concat]
        | eq _ _ => simp at h
        | not _ => simp at h
        | all _ _ => simp at h
  | .gen x p, φ, h => by
    cases hp : check p with
    | none => simp [check, hp] at h
    | some ψ =>
      simp [check, hp] at h
      cases h
      simp [flattenProof, hp, getLast?_concat]
  | .spec x t p, φ, h => by
    cases hp : check p with
    | none => simp [check, hp] at h
    | some a =>
      simp [check, hp] at h
      cases a with
      | all y ψ =>
        simp at h
        rcases h with ⟨⟨rfl, ht⟩, rfl⟩
        simp [flattenProof, hp, ht, getLast?_concat]
      | eq _ _ => simp at h
      | not _ => simp at h
      | imp _ _ => simp at h

theorem flatten_ne_nil_of_check {p : ProofTree} {φ : Formula}
    (h : check p = some φ) : flattenProof p ≠ [] := by
  intro hempty
  have := flatten_last_of_check p φ h
  simp [hempty] at this

theorem hilbert_just_prefix (pre suf : List Formula) {i : Nat}
    (h : HilbertJust pre i) : HilbertJust (pre ++ suf) i := by
  rcases h with ⟨hi, hjust⟩
  have hi' : i < (pre ++ suf).length := by
    simp [List.length_append]
    omega
  refine ⟨hi', ?_⟩
  have hget : ∀ j, j < pre.length → (pre ++ suf)[j]? = pre[j]? := by
    intro j hj
    simp [List.getElem?_append_left hj]
  rcases hjust with ⟨φ, hφ, hax⟩ | ⟨j, k, a, b, hj, hk, himp, ha, hb⟩ |
    ⟨j, x, φ, hj, hbody, hall⟩ | ⟨j, x, t, φ, hj, ht, huni, hsub⟩
  · exact Or.inl ⟨φ, (hget i hi).trans hφ, hax⟩
  · exact Or.inr (Or.inl ⟨j, k, a, b, hj, hk,
      (hget j (Nat.lt_trans hj hi)).trans himp,
      (hget k (Nat.lt_trans hk hi)).trans ha,
      (hget i hi).trans hb⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨j, x, φ, hj,
      (hget j (Nat.lt_trans hj hi)).trans hbody,
      (hget i hi).trans hall⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨j, x, t, φ, hj, ht,
      (hget j (Nat.lt_trans hj hi)).trans huni,
      (hget i hi).trans hsub⟩))

theorem hilbert_seq_prefix (pre suf : List Formula) (h : HilbertSeq pre) :
    ∀ i, i < pre.length → HilbertJust (pre ++ suf) i :=
  fun i hi => hilbert_just_prefix pre suf (h i hi)

theorem hilbert_just_shift (pre suf : List Formula) {i : Nat}
    (h : HilbertJust suf i) : HilbertJust (pre ++ suf) (pre.length + i) := by
  rcases h with ⟨hi, hjust⟩
  have hi' : pre.length + i < (pre ++ suf).length := by
    simp [List.length_append]
    omega
  refine ⟨hi', ?_⟩
  have hget : ∀ j, j < suf.length →
      (pre ++ suf)[pre.length + j]? = suf[j]? := by
    intro j hj
    rw [List.getElem?_append_right (by omega)]
    simp
  rcases hjust with ⟨φ, hφ, hax⟩ | ⟨j, k, a, b, hj, hk, himp, ha, hb⟩ |
    ⟨j, x, φ, hj, hbody, hall⟩ | ⟨j, x, t, φ, hj, ht, huni, hsub⟩
  · exact Or.inl ⟨φ, (hget i hi).trans hφ, hax⟩
  · exact Or.inr (Or.inl ⟨pre.length + j, pre.length + k, a, b,
      Nat.add_lt_add_left hj _, Nat.add_lt_add_left hk _,
      (hget j (Nat.lt_trans hj hi)).trans himp,
      (hget k (Nat.lt_trans hk hi)).trans ha,
      (hget i hi).trans hb⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨pre.length + j, x, φ,
      Nat.add_lt_add_left hj _,
      (hget j (Nat.lt_trans hj hi)).trans hbody,
      (hget i hi).trans hall⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨pre.length + j, x, t, φ,
      Nat.add_lt_add_left hj _, ht,
      (hget j (Nat.lt_trans hj hi)).trans huni,
      (hget i hi).trans hsub⟩))

theorem hilbert_append (pre suf : List Formula)
    (hpre : HilbertSeq pre) (hsuf : HilbertSeq suf) :
    HilbertSeq (pre ++ suf) := by
  intro i hi
  by_cases hlt : i < pre.length
  · exact hilbert_seq_prefix pre suf hpre i hlt
  · have hle : pre.length ≤ i := Nat.le_of_not_lt hlt
    have hi' : i - pre.length < suf.length := by
      simp [List.length_append] at hi
      omega
    have hshift := hilbert_just_shift pre suf (hsuf (i - pre.length) hi')
    have heq : pre.length + (i - pre.length) = i := Nat.add_sub_of_le hle
    rw [heq] at hshift
    exact hshift

theorem hilbert_singleton {φ : Formula} (hax : isAxiom φ = true) :
    HilbertSeq [φ] := by
  intro i hi
  have : i = 0 := by simp at hi; omega
  subst this
  exact ⟨Nat.zero_lt_succ _, Or.inl ⟨φ, rfl, hax⟩⟩

theorem getLast?_some_getElem? {α : Type} :
    ∀ {l : List α} {a : α}, l.getLast? = some a → l ≠ [] →
      l[l.length - 1]? = some a
  | [], _, h, hne => (hne rfl).elim
  | [x], a, h, _ => by simpa using h
  | x :: y :: xs, a, h, _ => by
    have hsuf : (y :: xs).getLast? = some a := by
      simpa [List.getLast?] using h
    have ih := getLast?_some_getElem? hsuf (List.cons_ne_nil _ _)
    simpa [List.length_cons] using ih

theorem hilbert_snoc_mp (seq : List Formula) (a b : Formula)
    (hseq : HilbertSeq seq) (hne : seq ≠ [])
    (himp : seq.getLast? = some (Formula.imp a b))
    (pre : List Formula) (hpre : HilbertSeq pre) (hnepre : pre ≠ [])
    (ha : pre.getLast? = some a) :
    HilbertSeq (seq ++ pre ++ [b]) := by
  have happ := hilbert_append seq pre hseq hpre
  intro i hi
  by_cases hlt : i < (seq ++ pre).length
  · exact hilbert_just_prefix (seq ++ pre) [b] (happ i hlt)
  · have : i = (seq ++ pre).length :=
      Nat.eq_of_lt_succ_of_not_lt (by simpa [List.length_append] using hi) hlt
    subst this
    have hlenSeq : 0 < seq.length := List.length_pos_iff.mpr hne
    have hlenPre : 0 < pre.length := List.length_pos_iff.mpr hnepre
    refine ⟨by simp [List.length_append], Or.inr (Or.inl ?_)⟩
    refine ⟨seq.length - 1, seq.length + (pre.length - 1), a, b, ?_, ?_, ?_, ?_, ?_⟩
    · simp [List.length_append]; omega
    · simp [List.length_append]; omega
    · have hidx : seq.length - 1 < seq.length := Nat.pred_lt hlenSeq.ne'
      have : (seq ++ pre ++ [b])[seq.length - 1]? = seq[seq.length - 1]? := by
        rw [List.getElem?_append_left (by simp [List.length_append]; omega)]
        rw [List.getElem?_append_left hidx]
      rw [this]
      exact getLast?_some_getElem? himp hne
    · have hidx : pre.length - 1 < pre.length := Nat.pred_lt hlenPre.ne'
      have : (seq ++ pre ++ [b])[seq.length + (pre.length - 1)]? = pre[pre.length - 1]? := by
        have hlt : seq.length + (pre.length - 1) < (seq ++ pre).length := by
          simp [List.length_append]; omega
        rw [List.getElem?_append_left (by simp [List.length_append]; omega)]
        rw [List.getElem?_append_right (by omega)]
        simp
      rw [this]
      exact getLast?_some_getElem? ha hnepre
    · have : (seq ++ pre ++ [b])[(seq ++ pre).length]? = some b := by
        simp [List.getElem?_append_right]
      simpa [List.length_append] using this

theorem hilbert_snoc_gen (seq : List Formula) (x : Nat) (φ : Formula)
    (hseq : HilbertSeq seq) (hne : seq ≠ [])
    (hφ : seq.getLast? = some φ) :
    HilbertSeq (seq ++ [Formula.all x φ]) := by
  intro i hi
  by_cases hlt : i < seq.length
  · exact hilbert_just_prefix seq [Formula.all x φ] (hseq i hlt)
  · have : i = seq.length := by
      simp [List.length_append] at hi hlt
      omega
    subst this
    refine ⟨by simp [List.length_append], Or.inr (Or.inr (Or.inl ?_))⟩
    refine ⟨seq.length - 1, x, φ,
      Nat.pred_lt (List.length_pos_iff.mpr hne).ne', ?_, ?_⟩
    · have : (seq ++ [Formula.all x φ])[seq.length - 1]? = seq[seq.length - 1]? := by
        have hidx : seq.length - 1 < seq.length :=
          Nat.pred_lt (List.length_pos_iff.mpr hne).ne'
        rw [List.getElem?_append_left hidx]
      rw [this]
      exact getLast?_some_getElem? hφ hne
    · simp [List.getElem?_append_right]

theorem hilbert_snoc_spec (seq : List Formula) (x : Nat) (t : Term) (φ : Formula)
    (hseq : HilbertSeq seq) (hne : seq ≠ [])
    (hφ : seq.getLast? = some (Formula.all x φ))
    (ht : isClosedTerm t = true) :
    HilbertSeq (seq ++ [substForm x t φ]) := by
  intro i hi
  by_cases hlt : i < seq.length
  · exact hilbert_just_prefix seq [substForm x t φ] (hseq i hlt)
  · have : i = seq.length := by
      simp [List.length_append] at hi hlt
      omega
    subst this
    refine ⟨by simp [List.length_append], Or.inr (Or.inr (Or.inr ?_))⟩
    refine ⟨seq.length - 1, x, t, φ,
      Nat.pred_lt (List.length_pos_iff.mpr hne).ne', ht, ?_, ?_⟩
    · have : (seq ++ [substForm x t φ])[seq.length - 1]? = seq[seq.length - 1]? := by
        have hidx : seq.length - 1 < seq.length :=
          Nat.pred_lt (List.length_pos_iff.mpr hne).ne'
        rw [List.getElem?_append_left hidx]
      rw [this]
      exact getLast?_some_getElem? hφ hne
    · simp [List.getElem?_append_right]

theorem flatten_hilbert :
    ∀ p : ProofTree, ∀ φ : Formula, check p = some φ →
      HilbertSeq (flattenProof p)
  | .ax ψ, φ, h => by
    simp [check] at h
    rcases h with ⟨hax, rfl⟩
    exact hilbert_singleton hax
  | .mp p q, φ, h => by
    cases hp : check p with
    | none => simp [check, hp] at h
    | some a =>
      cases hq : check q with
      | none => simp [check, hp, hq] at h
      | some c =>
        simp [check, hp, hq] at h
        cases a with
        | imp u v =>
          simp at h
          rcases h with ⟨rfl, rfl⟩
          have ihp := flatten_hilbert p (Formula.imp u v) hp
          have ihq := flatten_hilbert q u hq
          simp [flattenProof, hp]
          rw [← List.append_assoc]
          exact hilbert_snoc_mp (flattenProof p) u v ihp
            (flatten_ne_nil_of_check hp) (flatten_last_of_check p _ hp)
            (flattenProof q) ihq (flatten_ne_nil_of_check hq)
            (flatten_last_of_check q _ hq)
        | eq _ _ => simp at h
        | not _ => simp at h
        | all _ _ => simp at h
  | .gen x p, φ, h => by
    cases hp : check p with
    | none => simp [check, hp] at h
    | some ψ =>
      simp [check, hp] at h
      cases h
      simp [flattenProof, hp]
      exact hilbert_snoc_gen (flattenProof p) x ψ
        (flatten_hilbert p ψ hp) (flatten_ne_nil_of_check hp)
        (flatten_last_of_check p ψ hp)
  | .spec x t p, φ, h => by
    cases hp : check p with
    | none => simp [check, hp] at h
    | some a =>
      simp [check, hp] at h
      cases a with
      | all y ψ =>
        simp at h
        rcases h with ⟨⟨rfl, ht⟩, rfl⟩
        simp [flattenProof, hp, ht]
        exact hilbert_snoc_spec (flattenProof p) x t ψ
          (flatten_hilbert p (Formula.all x ψ) hp) (flatten_ne_nil_of_check hp)
          (flatten_last_of_check p _ hp) ht
      | eq _ _ => simp at h
      | not _ => simp at h
      | imp _ _ => simp at h

theorem provable_implies_hilbert {φ : Formula} (h : Provable φ) :
    HilbertProvable φ := by
  rcases h with ⟨p, hp⟩
  exact ⟨flattenProof p, flatten_last_of_check p φ hp,
    flatten_ne_nil_of_check hp, flatten_hilbert p φ hp⟩

theorem line_provable (seq : List Formula) (hseq : HilbertSeq seq) :
    ∀ i, i < seq.length → ∀ φ, seq[i]? = some φ → Provable φ := by
  intro i
  induction i using Nat.strongRecOn with
  | ind i ih =>
    intro hi φ hφ
    have hjust := (hseq i hi).2
    rcases hjust with ⟨ψ, hψ, hax⟩ | ⟨j, k, a, b, hj, hk, himp, ha, hb⟩ |
      ⟨j, x, ψ, hj, hbody, hall⟩ | ⟨j, x, t, ψ, hj, ht, huni, hsub⟩
    · have hψφ : ψ = φ := Option.some.inj (hψ.symm.trans hφ)
      have haxφ : isAxiom φ = true := hψφ ▸ hax
      refine ⟨ProofTree.ax φ, ?_⟩
      simp [ValidProof, check, haxφ]
    · have hbφ : b = φ := Option.some.inj (hb.symm.trans hφ)
      subst hbφ
      have hj' : j < seq.length := Nat.lt_trans hj hi
      have hk' : k < seq.length := Nat.lt_trans hk hi
      obtain ⟨p, hp⟩ := ih j hj hj' (Formula.imp a b) himp
      obtain ⟨q, hq⟩ := ih k hk hk' a ha
      have hp' : check p = some (Formula.imp a b) := hp
      have hq' : check q = some a := hq
      refine ⟨ProofTree.mp p q, ?_⟩
      simp [ValidProof, check, hp', hq']
    · have hallφ : Formula.all x ψ = φ := Option.some.inj (hall.symm.trans hφ)
      subst hallφ
      have hj' : j < seq.length := Nat.lt_trans hj hi
      obtain ⟨p, hp⟩ := ih j hj hj' ψ hbody
      have hp' : check p = some ψ := hp
      refine ⟨ProofTree.gen x p, ?_⟩
      simp [ValidProof, check, hp']
    · have hsubφ : substForm x t ψ = φ := Option.some.inj (hsub.symm.trans hφ)
      subst hsubφ
      have hj' : j < seq.length := Nat.lt_trans hj hi
      obtain ⟨p, hp⟩ := ih j hj hj' (Formula.all x ψ) huni
      have hp' : check p = some (Formula.all x ψ) := hp
      refine ⟨ProofTree.spec x t p, ?_⟩
      simp [ValidProof, check, hp', ht]

theorem getLast?_some_of_ne_nil {α : Type} {l : List α} {a : α}
    (h : l.getLast? = some a) :
    ∃ n, n < l.length ∧ l[n]? = some a := by
  have hne : l ≠ [] := by
    intro hempty
    subst hempty
    simp at h
  refine ⟨l.length - 1, Nat.pred_lt (List.length_pos_iff.mpr hne).ne', ?_⟩
  exact getLast?_some_getElem? h hne

theorem hilbert_implies_provable {φ : Formula} (h : HilbertProvable φ) :
    Provable φ := by
  rcases h with ⟨seq, hlast, hne, hseq⟩
  rcases getLast?_some_of_ne_nil hlast with ⟨n, hn, hnφ⟩
  exact line_provable seq hseq n hn φ hnφ

theorem hilbertProvable_iff_provable (φ : Formula) :
    HilbertProvable φ ↔ Provable φ :=
  ⟨hilbert_implies_provable, provable_implies_hilbert⟩

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
