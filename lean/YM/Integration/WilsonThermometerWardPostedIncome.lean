import YM.Integration.WilsonThermometerWardCutoffIncome

/-! Carry the actual fixed bare charges through every source mode on its original quiet trajectory. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerWardPostedIncome
open Lattice Wilson RG Source Labels Marker MeasureTheory RG16.Literal MergeProof MergeProof.Accent
open PhysicalNext.Repeat.Legato WilsonCapturedPrimaryWardAppointment Next.UVStress Push.GridApprox RG05Readout.Records Extra.Histories
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N per i:ℕ} (d:Fin 3→ℕ) (o:Fin 3→Site (R.family.side N per))
  (v:(j:Fin 3)→R.family.label (d j))
local notation "C" => R.family
local notation "J" => Stock.census (Fin 3)
local notation "H" s:max => (fun U=>∏j∈(s).val,(C).O N per (v j) (o j) U)
local notation "raw" => WilsonCapturedPrimaryWardAppointment.input R d o v (J)

theorem posted (cut:i<N) (tape:Config G ((C).side N per)→Poly J) (bought:Integrable tape (prior G _))
    (physical:Config G ((C).side (i+1) per)→Poly J)
    (issued:physical=gust (C).path N per N tape (i+1) cut) (s:(J).Mode) (a:ℂ)
    (initial:(fun U=>(tape U).part s)=a • (fun U=>(raw U).part s)):
    (fun U=>(LocalComparison.actualPush (C) N per i physical U).part s)=
      a • credit (C) N per 0 (H s) i cut.le:=by
  rw [issued]
  change (fun U=>(((C).path.levels.clock.op i per).push ((C).path.β N per (i+1))
    (gust (C).path N per N tape (i+1) cut) U).part s)=_
  rw [←gust_step (C).path N per N tape cut,←WilsonThermometerWardCutoffIncome.deposited R d o v cut.le s]
  exact WilsonThermometerMarchFaceTransport.restored (C) tape raw s a bought
    (WilsonCapturedPrimaryWardAppointment.paid R d o v (J)) initial cut.le

end YM.Integration.WilsonThermometerWardPostedIncome
