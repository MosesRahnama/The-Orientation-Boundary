import Mathlib

/-!
# Product-valued boundary obstruction profiles

Relation: coordinatewise comparison of product-valued obstruction profiles.
Closure: finite natural-number coordinates only.
Trust: PROVEN-IN-LEAN, baseline arithmetic and product reasoning.
Scope: common quantitative substrate for Orientation, Distinction, QEC, PRT,
and RH-facing boundary transactions. It deliberately does not collapse the
coordinates into a single scalar.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryQuantitative

/-- Product-valued obstruction profile. The coordinates are intentionally
separate: carrier burden, branch excess, repair-cover burden, and witness
rank need not agree numerically. -/
structure ObstructionProfile where
  carrierBurden : Nat
  branchExcess : Nat
  repairCover : Nat
  witnessRank : Nat
deriving Repr, DecidableEq

/-- Coordinatewise order: `p ≤q q` means `p` is no worse than `q` in every
obstruction coordinate. -/
def CoordinateLe (p q : ObstructionProfile) : Prop :=
  p.carrierBurden <= q.carrierBurden
    /\ p.branchExcess <= q.branchExcess
    /\ p.repairCover <= q.repairCover
    /\ p.witnessRank <= q.witnessRank

/-- A strict licensed reduction: coordinatewise no worse, and strictly better
in at least one obstruction coordinate. -/
def StrictlyReduces (after before : ObstructionProfile) : Prop :=
  CoordinateLe after before
    /\ (after.carrierBurden < before.carrierBurden
      \/ after.branchExcess < before.branchExcess
      \/ after.repairCover < before.repairCover
      \/ after.witnessRank < before.witnessRank)

/-- The zero obstruction profile. -/
def zeroProfile : ObstructionProfile where
  carrierBurden := 0
  branchExcess := 0
  repairCover := 0
  witnessRank := 0

theorem coordinateLe_refl (p : ObstructionProfile) : CoordinateLe p p := by
  exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

theorem coordinateLe_trans {p q r : ObstructionProfile}
    (hpq : CoordinateLe p q) (hqr : CoordinateLe q r) :
    CoordinateLe p r := by
  exact
    ⟨hpq.1.trans hqr.1,
      hpq.2.1.trans hqr.2.1,
      hpq.2.2.1.trans hqr.2.2.1,
      hpq.2.2.2.trans hqr.2.2.2⟩

theorem zeroProfile_le (p : ObstructionProfile) : CoordinateLe zeroProfile p := by
  exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

/-- Projection to the carrier coordinate. -/
def carrierCoordinate (p : ObstructionProfile) : Nat := p.carrierBurden

/-- Projection to the branch-excess coordinate. -/
def branchCoordinate (p : ObstructionProfile) : Nat := p.branchExcess

/-- Projection to the repair-cover coordinate. -/
def repairCoordinate (p : ObstructionProfile) : Nat := p.repairCover

/-- Projection to the witness-rank coordinate. -/
def witnessCoordinate (p : ObstructionProfile) : Nat := p.witnessRank

theorem coordinateLe_carrier {p q : ObstructionProfile}
    (h : CoordinateLe p q) : carrierCoordinate p <= carrierCoordinate q := h.1

theorem coordinateLe_branch {p q : ObstructionProfile}
    (h : CoordinateLe p q) : branchCoordinate p <= branchCoordinate q := h.2.1

theorem coordinateLe_repair {p q : ObstructionProfile}
    (h : CoordinateLe p q) : repairCoordinate p <= repairCoordinate q := h.2.2.1

theorem coordinateLe_witness {p q : ObstructionProfile}
    (h : CoordinateLe p q) : witnessCoordinate p <= witnessCoordinate q := h.2.2.2

/-- Non-vacuity fixture: a profile reduced on three coordinates. -/
def sampleRawProfile : ObstructionProfile where
  carrierBurden := 9
  branchExcess := 2
  repairCover := 2
  witnessRank := 1

/-- Non-vacuity fixture: licensed image of `sampleRawProfile`. -/
def sampleLicensedProfile : ObstructionProfile where
  carrierBurden := 3
  branchExcess := 0
  repairCover := 1
  witnessRank := 1

theorem sampleLicensedProfile_reduces :
    StrictlyReduces sampleLicensedProfile sampleRawProfile := by
  unfold StrictlyReduces CoordinateLe sampleLicensedProfile sampleRawProfile
  exact ⟨⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, Or.inl (by norm_num)⟩

#print axioms coordinateLe_refl
#print axioms coordinateLe_trans
#print axioms zeroProfile_le
#print axioms coordinateLe_carrier
#print axioms coordinateLe_branch
#print axioms coordinateLe_repair
#print axioms coordinateLe_witness
#print axioms sampleLicensedProfile_reduces

end OperatorKO7.Meta.BoundaryQuantitative
