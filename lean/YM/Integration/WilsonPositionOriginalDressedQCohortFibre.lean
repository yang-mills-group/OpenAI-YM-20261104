import YM.Integration.WilsonPositionOriginalDressedQFibre
import YM.Integration.ActualOriginalQInput
import YM.Extra.MULTISOURCE_TRAJECTORIES.Initial

/-! The entire physical push of a filed source has the genuine normalized
Wilson conditional law. Finite mode projections are integrated only after
this common denominator is installed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQCohortFibre
open Filter Set Function MeasureTheory Lattice Wilson RG Marker Cells OPE.Therm
open Push.GridApprox PhysicalNext.Repeat.Legato
open QLocalPhysicalPathKernel WilsonMacroscopicForwardTransfer
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){N p i:ℕ}
local notation "upper" => (R.family.path.rep N p (i+1))
local notation "lower" => (R.family.path.rep N p i)
local notation "S" => (R.family.path.levels.clock.op i p)

theorem measured {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
    (hi:i<N)(F:Config G (R.family.side (i+1) p)→E)(W:Config G (R.family.side i p)):
    (S).push (upper).beta (fun U=>(upper).eval U • F U) W =
      (lower).eval W • (∫U,F U ∂next R.family N p i W):=by
  have positive:(R.family.path.rep N p i).eval W≠0:=(Multi.AxisShift.chosen_positive R.makes.wilson hi.le W).ne'
  rw [held R.family R.makes hi,ActualWilsonConditionalRoots.average R.family R.makes hi]
  unfold StepData.push actualAverage
  rw [←integral_smul]
  apply integral_congr_ae
  filter_upwards [] with U
  rw [smul_smul,smul_smul]
  congr 1
  unfold actualConditionalDensity
  change _=(lower).eval W*((S).density (upper).beta U W*(upper).eval U/(lower).eval W)
  field_simp [positive]

variable {V:Type}[DecidableEq V]{Γ:Census V}
theorem coefficient (hi:i<N)(F:Config G (R.family.side (i+1) p)→Poly Γ)(s:Γ.Mode)
    (W:Config G (R.family.side i p))(good:Integrable F (next R.family N p i W)):
    ((S).push (upper).beta (fun U=>(upper).eval U • F U) W).part s =
      ((lower).eval W:ℂ)*exterior (C:=R.family) (N:=N) (Nat.le_succ i) (fun U=>(F U).part s) W:=by
  rw [measured R hi,←WilsonPositionOriginalDressedQFibre.measured R hi]
  have get:=((Poly.get s).restrictScalars ℝ).integral_comp_comm good
  change (Poly.get s) ((lower).eval W • ∫U,F U ∂next R.family N p i W)=_
  rw [show ∀a:ℝ,∀ y:Poly Γ,(Poly.get s) (a•y)=a•(Poly.get s) y from
    fun a y=>((Poly.get s).restrictScalars ℝ).map_smul a y]
  rw [show (Poly.get s) (∫U,F U ∂next R.family N p i W) =
      ∫U,(F U).part s ∂next R.family N p i W from get.symm]
  rfl

end YM.Integration.WilsonPositionOriginalDressedQCohortFibre
