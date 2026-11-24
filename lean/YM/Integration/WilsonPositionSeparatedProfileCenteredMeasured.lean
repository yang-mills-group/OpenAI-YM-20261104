import YM.Integration.WilsonPositionSeparatedProfileCenteredReadout
import YM.Integration.WilsonReportHarvestReadmittedSource

/-! Complete signed cutoff reading on the original numbered continuum
layout, with its authentic independently submitted microscopic columns. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileCenteredMeasured
open Function Set MeasureTheory Finset Lattice Wilson RG Source Labels
open RG05Readout Address Native Pulse Flatten MergeProof Accent Extra.Histories
open RG05Readout.Harvest RG05Readout.Many RG05Readout.Records PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Legato.Bandage RG05Readout.Velvet
open Extraction Spec RG12 RG17
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {order:Extraction.Order} {table:Table R.family.book} {F:Final R.family order table} (L:Layout F)
variable {v n m N per u:ℕ} (s:Fin v→ℕ) (w:(i:Fin v)→R.family.label (s i))

def upper (r:ℝ) (N per:ℕ) (i:Fin v):Palette R.family (s i):=
  chunk (WilsonReportingUnitOrbit.primary (s i)) ((R.family.factory (s i) N per).terminal.symm (atRef L (s i) r (N,per) (w i)))

theorem original (Y:∀d,(ℕ×ℕ)→Address.Emblems R.family d) {budget:ℕ→ℕ→ℝ} {start:ℕ→ℕ}
    (rows:Chalice.Anchored R.doors budget R.makes start Y) (r:ℝ) (Ψ:Wave (Fin v)) {cap:ℝ}
    (rp:0<r) (enclosed:∀z∈tsupport Ψ.val,∀i,‖z i‖≤cap) (room:r*cap+2*R.family.S.a u<R.family.S.radius per)
    (first:start 0≤u) (live:m≤N) (date:u≤N) {M:Palette R.family 0}
    (heard:hears Ψ s (fun i=>WilsonReportHarvestReadmittedSource.filed L (s i) r (w i) (Y (s i) (N,per)) m N per) Y n m u 0 N per r M):
    val M (Suede.mother R.family)=dyes R.family u N per date (constellation s (upper R L s w r N per) r Ψ date m (Native.line Suede.pip)) 1/liftVac R.family.path N per u 1:=by
  let x (i:Fin v):=WilsonReportHarvestReadmittedSource.filed L (s i) r (w i) (Y (s i) (N,per)) m N per
  have stock:WilsonPositionSeparatedProfileCenteredReadout.enrolled R s Y x m N per=upper R L s w r N per:=by
    funext i;exact WilsonReportHarvestReadmittedSource.carried L (s i) r (w i) (Y (s i) (N,per)) m N per live
  rw [WilsonPositionSeparatedProfileCenteredReadout.original R s Y rows x r Ψ rp enclosed room first live heard,
    WilsonPositionSeparatedProfileCenteredReadout.value,dif_pos date,stock]

end YM.Integration.WilsonPositionSeparatedProfileCenteredMeasured
