import YM.Integration.WilsonSingleHardStep

/-! The full previously pushed field and the newly filed true exceptional source
are compared after one more normalized Wilson integration. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSingleHardRadius
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {N per i:ℕ}
local notation "V" j:max => Config G (R.family.side j per)
local notation "vac" j:max U:max => (R.family.path.rep N per j).eval U
local notation "ker" => (R.family.path.levels.clock.op i per).push (R.family.path.β N per (i+1))
variable {J:Census (Fin 1)}
local notation "fire" => J.fire 0

theorem exact_scalar (live:i<N) (f:V (i+1)→ℂ) (U:V i) :
    actualAverage R.family (N:=N) (fun W=>(vac (i+1) W)⁻¹ • f W) U=(vac i U)⁻¹ • (ker f U) := by
  rw [actualAverage_push]
  apply congrArg ((vac i U)⁻¹ • ·)
  apply congrArg (fun z=>ker z U)
  funext W
  have pos : (vac (i+1) W)≠0 := (Multi.AxisShift.chosen_positive R.makes.wilson live W).ne'
  rw [smul_smul,mul_inv_cancel₀ pos,one_smul]

/-- Error propagation for the actual complete earlier field, prior to any absolute
value of an exceptional inventory. -/
theorem propagate (live:i<N) (f:V (i+1)→ℂ) (h:V (i+1)→Poly J) (r k:V i→ℂ)
    (fs:Integrable f (prior G _)) (hs:Integrable h (prior G _)) (C z:ℝ)
    (prev:∀W,‖(vac (i+1) W)⁻¹ • f W-(vac (i+1) W)⁻¹ • (h W).part fire‖≤C)
    (paid:∀U,‖r U‖≤z)
    (step:∀U,(LocalComparison.actualPush R.family N per i h U).part fire=
      ((vac i U):ℂ)*r U+k U) (U:V i) :
    ‖(vac i U)⁻¹ • (ker f U)-(vac i U)⁻¹ • k U‖≤C+z := by
  have hj:Integrable (fun W=>(h W).part fire) (prior G _):=(Poly.get fire).integrable_comp hs
  have approx:=difference R live f (fun W=>(h W).part fire) fs hj C prev U
  have pos : (vac i U)≠0 := (Multi.AxisShift.chosen_positive R.makes.wilson live.le U).ne'
  rw [exact_scalar R live f U,marginal R live h hs fire U,step U] at approx
  have split : (vac i U)⁻¹ • (((vac i U):ℂ)*r U+k U) = r U+(vac i U)⁻¹ • k U := by
    rw [smul_add,←Complex.real_smul,smul_smul,inv_mul_cancel₀ pos,one_smul]
  rw [split] at approx
  calc
    _=‖((vac i U)⁻¹ • (ker f U)-(r U+(vac i U)⁻¹ • k U))+r U‖ := by congr 1; abel
    _≤_ := (norm_add_le ..).trans (add_le_add approx (paid U))

end YM.Integration.WilsonSingleHardRadius
