import YM.Comparison.RG02.Bulk.Sequence
import YM.FullVolume.Cross

/-! Bind the independent formal Wilson prescription to the already retained
Run. Every field is taken from that Run's directed construction; no path,
stationary chart, covariance convention or cost sheet is selected anew. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.RunFormalChain

open Lattice RG RG.Supply Precision Input Org
open PhysicalNext.Repeat.Legato

variable {G : Gauge}

/-- The actual Run supplies the complete formal-chain input independently of
perturbative order, marker load and period. This is a data/receipt adapter,
not a local approximation or a change of perturbative prescription. -/
def fromRun (R : Run G) : Comparison.RG02.Bulk.Chain R.family.path where
  preCosts := R.metals.p
  lengths := R.rolls
  post := R.alloy.post
  horizon := R.alloy.B.M
  O := R.metals.O
  receipt := R.alloy.B.ratio
  kin := R.alloy.B.kin
  planned := R.alloy.B.support
  selected N p m hm := by
    have h := ((R.T.sticks N p).prices m (Nat.zero_le _) hm).1.path
    exact h.trans (congrArg (fun f => f N m) R.alloy.B.bases)
  clips N p m hm := ((R.T.sticks N p).prices m (Nat.zero_le _) hm).1.clip

@[simp] theorem chart_eq (R : Run G) : (fromRun R).O = R.metals.O := rfl

@[simp] theorem kinetic_eq (R : Run G) : (fromRun R).kin = R.alloy.B.kin := rfl

@[simp] theorem alpha_eq (R : Run G) (N m : ℕ) :
    (fromRun R).kin.alpha N m = R.alloy.B.kin.alpha N m := rfl

/-- The step's stationary map is the very map of the actual Kin, for every
forest. It does not vary with later formal-order or marker choices. -/
@[simp] theorem step_stationary (R : Run G) (N m p : ℕ) (hm : m < N) :
    ((fromRun R).step N m p hm).b = R.alloy.B.kin.stationary N m p := rfl

end YM.Integration.RunFormalChain
