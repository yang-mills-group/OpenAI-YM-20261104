import YM.Integration.WilsonCapturedPrimaryWardAppointment
import YM.Integration.WilsonThermometerUnitFilingReturn
import YM.Integration.WilsonGeometricSignedCoveredReturn

/-! Every homogeneous mode of the original Ward gallery and its next physical push. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerWardCutoffIncome
open Lattice Wilson RG Source Labels Marker OPE RG16.Literal MergeProof MergeProof.Accent
open Function MeasureTheory Finset Next.UVStress PhysicalNext.Repeat.Legato Push.GridApprox RG05Readout.Records
open WilsonCapturedPrimaryWardAppointment Extra.Trajectories
open private scalar_push from YM.Integration.WilsonThermometerUnitFilingReturn
open scoped Classical BigOperators
variable {G : Gauge} (R:Run G) {N per:ℕ} (d:Fin 3→ℕ) (o:Fin 3→Site (R.family.side N per))
  (v:(j:Fin 3)→R.family.label (d j))
local notation "C" => R.family
local notation "J" => Stock.census (Fin 3)
local notation "H" s:max => (fun U=>∏j∈(s).val,(C).O N per (v j) (o j) U)
local notation "raw" => WilsonCapturedPrimaryWardAppointment.input R d o v (J)

theorem deposited {i:ℕ} (live:i≤N) (s:(J).Mode) :
    (fun U=>(gust (C).path N per N raw i live U).part s)=credit (C) N per 0 (H s) i live:=by
  rw [pushpart live raw s (WilsonCapturedPrimaryWardAppointment.paid R d o v (J)),scalar_push R]
  have heads (U): (raw U).part s=(((C).path.rep N per N).eval U:ℂ)*(H s) U:=by
    simp only [input,birth,Mach,Poly.part_smul,pass_fire]
  simp_rw [heads]
  rw [(show ((C).path.rep N per N).eval=bare ((C).beta N per) from (R.makes.wilson.starts N per).2)]
  simp [credit]

theorem next {i:ℕ} (cut:i<N) (physical:Config G ((C).side (i+1) per)→Poly J)
    (issued:physical=gust (C).path N per N raw (i+1) cut) (s:(J).Mode) :
    (fun U=>(LocalComparison.actualPush (C) N per i physical U).part s)=
      credit (C) N per 0 (H s) i cut.le :=by
  rw [issued]
  change (fun U=>(((C).path.levels.clock.op i per).push ((C).path.β N per (i+1))
    (gust (C).path N per N raw (i+1) cut) U).part s)=_
  rw [←gust_step (C).path N per N raw cut]
  exact deposited R d o v cut.le s

end YM.Integration.WilsonThermometerWardCutoffIncome
