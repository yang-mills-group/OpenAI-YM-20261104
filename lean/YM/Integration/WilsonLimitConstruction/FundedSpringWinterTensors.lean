import YM.Integration.RunFormalChain
import YM.WilsonCoeffUV.Kinetic.Alpha
import YM.WilsonCoeffUV.Winding.Gazette

/-! The finite original Wilson coefficient program and its selected physical
kinetic path have the same leading tensor at every actual cutoff, period,
and surviving adjacent step. The intrinsic finite-temperature correction is
kept at its original coefficient and spatial rate. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedSpringWinterTensors

open Function Filter Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Precision Gauge
open Work.F08 PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic Asymptotics Stationary
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} (R : Run G)
local notation "A" => R.family.path.levels
local notation "O" => R.metals.O
local notation "P" => R.alloy.B.kin
local notation "post" => R.alloy.post

def actual (N m p : ℕ) := hazeM A N m P ((A).S.side m p)
def source (N m p : ℕ) := unripe A O N m (hazeM A N (m+1) P) ((A).S.side m p)
def finite (N m p : ℕ) := Winding.coil0 A O m N ((A).S.side m p)

/-- The complete issuer's finite source, including its actual quartic
thermal correction and the original side-volume factors. -/
theorem issued (hG : G.Simple) (N m p : ℕ) (hm : m<N) :
    (∀ i≤2, source R N m p i (2+i)=actual R N m p i (2+i)) ∧
    ∀ x, ‖source R N m p 2 2 x-((P).alpha N m • actual R N m p 0 2 x+actual R N m p 2 2 x)‖ ≤
      (1/2:ℝ)*(Fintype.card (Site ((A).S.side m p)):ℝ)^2*
        ((Fintype.card (Site ((A).S.side m p)):ℝ)*(post).Γ ((A).clock.J (m+1))*(A).clock.loopCap (m+1)*
          Real.exp (-((post).c ((A).clock.J (m+1)))*((A).S.side m p).val)) :=
  Mosaic.wagerYear hG R.alloy.B.ratio R.alloy.B.support hm
    (Mosaic.alpha_stable hG R.alloy.B.ratio R.alloy.B.support (Nat.succ_le_of_lt hm)).1 p

/-- The native first Gaussian coefficient is independent of which local
interacting packet was retained, before any thermodynamic limit. -/
theorem baseline (N m : ℕ) (n : Side) (W W' : Crude G) :
    unripe A O N m W n 0=unripe A O N m W' n 0 := by
  have base (X : Crude G) : unripe A O N m X n 0 =
      shine (orbQ (precisionC G n (freeForms A N m))) :=
    winter_calm (mStep A n m) (repeatF (mStep A n m)) (freeForms A N (m+1))
      (freeForms A N m) (roam A N m n) R.alloy.B.ratio
  exact (base W).trans (base W').symm

/-- The *same-tag finite reference that receives the winding payment*
reads the actual finite path quadratic in all original ordered positions. -/
theorem leading (hG : G.Simple) (N m p : ℕ) (hm : m<N) :
    finite R N m p 0 2 =
      rye (intended (R.family.path.rep N p m).clip (R.family.path.rep N p m).path
        (m:=(A).S.side m p)) 2 := by
  have b : finite R N m p 0=source R N m p 0 :=
    baseline R N m ((A).S.side m p) _ _
  have f := (issued R hG N m p hm).1 0 (by omega)
  have bg := R.alloy.B.support.cap N m hm.le
  rw [(RunFormalChain.fromRun R).selected N p m hm.le,
    (RunFormalChain.fromRun R).clips N p m hm.le]
  calc
    finite R N m p 0 2 = source R N m p 0 2 := congrFun b 2
    _ = actual R N m p 0 2 := f
    _ = _ := Mosaic.front_paths bg ((A).S.side m p) 0

theorem top (hG : G.Simple) (N m p : ℕ) (hm : m<N) (i : ℕ) (hi : i≤2) :
    source R N m p i (2+i) =
      rye (intended (R.family.path.rep N p m).clip (R.family.path.rep N p m).path
        (m:=(A).S.side m p)) (2+i) := by
  rw [(RunFormalChain.fromRun R).selected N p m hm.le,
    (RunFormalChain.fromRun R).clips N p m hm.le]
  exact ((issued R hG N m p hm).1 i hi).trans
    (Mosaic.front_paths (R.alloy.B.support.cap N m hm.le) ((A).S.side m p) i)

end YM.Integration.WilsonLimitConstruction.FundedSpringWinterTensors
