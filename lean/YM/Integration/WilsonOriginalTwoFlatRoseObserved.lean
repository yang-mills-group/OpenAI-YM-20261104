import YM.Integration.WilsonOriginalTwoFlatRoseCentered
import YM.Integration.WilsonOriginalTwoFlatRosePhysical

/-! The finite centered cofactor in the Wilson two-stop estimate has the original
unrestricted, connected, smooth-position measurement as its physical limit. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseObserved
open Function Filter Finset Set Metric MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits Climb Trace Trace.Pilot RG12 RG17 Next.UVStress PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose Cells Push.GridApprox WilsonPositionThermometerReading
open WilsonThermometerUnitFilingFourSquare
open WilsonOriginalTwoFlatRoseFaceLimits (raw result)
open WilsonNeutralOffsetCutoff (named)
open WilsonPositionThermometerGradedSource (grade)
open WilsonPositionThermometerConnected (value)
open scoped Topology Classical BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(A:WilsonPositionThermometerCapStation.Group R.family 6)
    {Y:Ultrafilter (ℕ×ℕ)}
local notation "d" => fun i:Fin 3=>(grade i).val
local notation "E" => Finset (Fin 3)

def observed (r:ℝ)(φ:Test 3)(z:UVIndex):ℂ:=
  ∑y:Site (R.family.side z.1 z.2)×Site (R.family.side z.1 z.2),
    WilsonThermometerAlignedCells.mass (R:=R) r z φ y*
      WilsonMaxwellThermometerNominatedCofactor.reading R A z.1 z.2 y
        (WilsonMaxwellThermometerNominatedCofactor.native R A z.1 z.2 y 0)

include F in
theorem original (hG:G.Simple)(hl:(Y:Filter _)≤f.fuse)(r:ℝ)(rp:0<r)(φ:Test 3)
    (v:(i:Fin 3)→S.Field (d i))(arms:(i:Fin 3)→Arm R.family S (Y:Filter _) (d i) (v i))
    (same:∀z i,(arms i).source z=named R A z.1 z.2 i):
    Tendsto (observed R A r φ) (Y:Filter _)
      (𝓝 (φ.applyTo (fun x=>value (result R r v x)))):=by
  have underlying:=WilsonOriginalTwoFlatRosePhysical.original R F A v arms same hG hl r rp φ
  apply underlying.congr'
  have ready:∀ᶠ z:UVIndex in (Y:Filter _),∀i:Fin 3,R.family.ref (d i)≤z.1:=
    Filter.eventually_all.mpr (fun i=>(large_mesh f (R.family.ref (d i))).filter_mono hl)
  filter_upwards [ready] with z live
  obtain ⟨N,per⟩:=z
  have cofactor:=WilsonOriginalTwoFlatRoseCentered.connected R A N per r live φ
    (fun _ _=>0)
  have blank:value (fun _=>0)=0:=by simp [WilsonPositionThermometerConnected.value]
  have eqn(x:Points 3):WilsonOriginalTwoFlatRoseFaceLimits.raw R A r (N,per) x=
      WilsonOriginalTwoFlatRoseCentered.ordinary R A N per
        (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (N,per) x):=by
    funext s
    rfl
  simpa only [blank,sub_zero,observed,eqn] using cofactor

end YM.Integration.WilsonOriginalTwoFlatRoseObserved
end
