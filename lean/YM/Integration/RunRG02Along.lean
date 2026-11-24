import YM.FullVolume.Cross
import YM.RG02.Actual.Setup

/-!
The native RG02 Along record on the literal retained Run.

Every construction field comes from R. No calibration witness is selected
again, and no additional purchase or physical family is introduced. The
incoming extra/source stencil Supplies and their raw-germ handwriting and
exposure identities remain separate inputs to the native forecast theorem.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.CommonConstruction

open PhysicalNext.Repeat.Legato
open scoped Classical

variable {G : Gauge}

def runAlong (R : Run G) : RG02.Along R.family.path where
  s := R.metals.p
  q := R.rolls
  η := R.metals.O
  X := R.metals.K
  prices := R.alloy.post
  M := R.alloy.B.M
  V := R.alloy.B.kin
  receipt := R.alloy.B.ratio
  suffice := R.alloy.B.plan
  paid := R.alloy.B.support
  reads N m p hm :=
    ((R.T.sticks N p).prices m (Nat.zero_le m) hm).1.path.trans
      (congrFun (congrFun R.alloy.B.bases N) m)
  angle N m p hm := (R.T.moves N m p hm).δ

theorem runAlong_fields (R : Run G) :
    (runAlong R).η = R.metals.O ∧
    (runAlong R).X = R.metals.K ∧
    (runAlong R).prices = R.alloy.post ∧
    (runAlong R).M = R.alloy.B.M ∧
    (runAlong R).V = R.alloy.B.kin :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem runAlong_actual_path (R : Run G) (N m p : ℕ) (hm : m ≤ N) :
    (R.family.path.rep N p m).path = R.alloy.B.kin.path N m :=
  (runAlong R).reads N m p hm

end YM.Integration.CommonConstruction
