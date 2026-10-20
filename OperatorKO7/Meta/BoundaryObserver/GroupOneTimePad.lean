import OperatorKO7.Meta.BoundaryObserver.BoundarySecrecy

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.GroupOneTimePad

open scoped BigOperators


/-- Every key of a finite nonempty type has mass one over the size of that type. -/
noncomputable def uniformKey (G : Type) [Fintype G] [Nonempty G] :
    ProtocolResolution.FiniteLaw G where
  mass := fun _ => 1 / Fintype.card G
  nonnegative := by
    intro _
    positivity
  total := by
    classical
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (Fintype.card G : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp [hc]

/-- Encryption adds the key on the left in an arbitrary additive group. -/
def groupEnc {G : Type} [AddGroup G] (k m : G) : G := k + m

/-- Decryption adds the inverse of the key on the left. -/
def groupDec {G : Type} [AddGroup G] (k c : G) : G := -k + c

/-- Left subtraction by the key undoes left encryption in every additive group. -/
theorem groupDec_groupEnc {G : Type} [AddGroup G] (k m : G) :
    groupDec k (groupEnc k m) = m := by
  simp [groupDec, groupEnc, ← add_assoc]

/-- A uniform left-additive pad assigns each ciphertext mass one over the group size. -/
theorem groupPad_cipherLaw {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]
    [Nonempty G] (m c : G) :
    BoundarySecrecy.cipherLaw (uniformKey G) groupEnc m c = 1 / Fintype.card G := by
  have hkey (k : G) : groupEnc k m = c ↔ k = c + -m := by
    constructor
    · intro hk
      calc
        k = (k + m) + -m := by simp [add_assoc]
        _ = c + -m := by simpa [groupEnc] using congrArg (fun x : G => x + -m) hk
    · intro hk
      rw [hk]
      simp [groupEnc, add_assoc]
  simp [BoundarySecrecy.cipherLaw, hkey, uniformKey]

/-- The ciphertext mass does not depend on the message for a uniform group key. -/
theorem groupPad_perfectSecrecy {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]
    [Nonempty G] (m m' c : G) :
    BoundarySecrecy.cipherLaw (uniformKey G) groupEnc m c =
      BoundarySecrecy.cipherLaw (uniformKey G) groupEnc m' c := by
  rw [groupPad_cipherLaw, groupPad_cipherLaw]

/-- Two message-conditioned group-pad ciphertext laws have zero triangular discrimination. -/
theorem groupPad_pole {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]
    [Nonempty G] (m m' : G) :
    BoundarySingularity.discrimination (BoundarySecrecy.cipherLaw (uniformKey G) groupEnc m)
      (BoundarySecrecy.cipherLaw (uniformKey G) groupEnc m') = 0 := by
  apply BoundarySecrecy.perfectSecrecyPoleGoal G G G (uniformKey G) groupEnc m m'
  intro c
  exact groupPad_perfectSecrecy m m' c

/-- Every key in a finite nonempty type has positive mass under the uniform law. -/
theorem groupPad_positive_keys {G : Type} [Fintype G] [Nonempty G] :
    (Finset.univ.filter (fun k => 0 < (uniformKey G).mass k)).card = Fintype.card G := by
  classical
  have hpos (k : G) : 0 < (uniformKey G).mass k := by
    change (0 : ℝ) < 1 / (Fintype.card G : ℝ)
    have hc : (0 : ℝ) < Fintype.card G := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
    positivity
  simp [hpos]

/-- A uniform group pad decrypts, conceals messages, and attains the positive-key bound. -/
theorem groupPad_attains_key_bound {G : Type} [AddGroup G] [Fintype G] [DecidableEq G]
    [Nonempty G] :
    (∀ k m : G, groupDec k (groupEnc k m) = m) ∧
    (∀ m m' c : G, BoundarySecrecy.cipherLaw (uniformKey G) groupEnc m c =
        BoundarySecrecy.cipherLaw (uniformKey G) groupEnc m' c) ∧
    Fintype.card G = (Finset.univ.filter (fun k => 0 < (uniformKey G).mass k)).card := by
  refine ⟨fun k m => groupDec_groupEnc k m, fun m m' c => groupPad_perfectSecrecy m m' c, ?_⟩
  have hbound : Fintype.card G ≤
      (Finset.univ.filter (fun k => 0 < (uniformKey G).mass k)).card :=
    BoundarySecrecy.shannonKeyGoal G G G (uniformKey G) groupEnc groupDec
      (fun k m => groupDec_groupEnc k m)
      (fun m m' c => groupPad_perfectSecrecy m m' c)
  exact Nat.le_antisymm hbound (groupPad_positive_keys (G := G)).le

/-- In the two-element additive group, every ciphertext has mass one half under every message. -/
theorem zmodTwo_pad_cipherLaw (m c : ZMod 2) :
    BoundarySecrecy.cipherLaw (uniformKey (ZMod 2)) groupEnc m c = 1 / 2 := by
  simpa using (groupPad_cipherLaw (G := ZMod 2) m c)


end OperatorKO7.Meta.BoundaryObserver.GroupOneTimePad
