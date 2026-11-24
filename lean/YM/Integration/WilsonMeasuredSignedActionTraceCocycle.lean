import YM.Integration.WilsonMeasuredSignedActionEngineering
import YM.Integration.WilsonMeasuredSignedActionTraceRatio

noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonMeasuredSignedActionTraceCocycle
open Filter Set Spec Table Extraction OPE OPE.Orbits Climb PhysMS
open Lattice RG Wilson Extra.Histories Trace Trace.Physical Trace.Terrace Trace.Pilot
open Function Next.UVStress Work.A01 Maxwell UVNext.FreeStress Spin StressFlux TraceExtension MergeProof.East Next.Rank
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawCompactNative (positive)
open scoped Topology
variable [Win:RangeSpec] {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(J:ℝ→tower S){b g:ℝ→ℝ}

theorem original (simple:G.Simple)(cal:TendC F (fun r=>J r 4) b)(heat:Coupling G g):
    ∀ᶠ z:ℝ×Ratio in sweep, 0<b z.1/b (z.2.val*z.1) ∧
      Frame.cocycle 4 J z.1 z.2.val (positive z.2) (stepField C)=
        ((b z.1/b (z.2.val*z.1):ℝ):ℂ) • stepField C:=by
  filter_upwards [WilsonMeasuredSignedActionTraceRatio.original F J simple cal heat] with z row
  refine ⟨row.1,?_⟩
  apply (Pert.Scale.gearIso C.labels 4 z.2.val (positive z.2)).injective
  apply (J z.1 4).injective
  change J z.1 4 (Pert.Scale.gear C.labels 4 z.2.val
    (Frame.cocycle 4 J z.1 z.2.val (positive z.2) (stepField C)))=
    J z.1 4 (Pert.Scale.gear C.labels 4 z.2.val _)
  rw [Frame.cocycle_value]
  rw [map_smul,WilsonMeasuredSignedActionEngineering.original,map_smul,map_smul,smul_smul,row.2]
  rw [← Complex.coe_smul (z.2.val^4*(b z.1/b (z.2.val*z.1)))]
  push_cast
  rw [mul_comm]

end YM.Integration.WilsonMeasuredSignedActionTraceCocycle
end
