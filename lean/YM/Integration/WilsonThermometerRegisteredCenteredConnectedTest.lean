import YM.Integration.WilsonThermometerRegisteredCenteredInvoice
import YM.Integration.WilsonThermometerRegisteredAncestralProperTest

/-! The full physical connected thermometer minus its fixed ordinary prediction at
the original cutoff and period, as two centered tests on the earlier Wilson law. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCenteredConnectedTest
open Filter Finset MeasureTheory Table Spec Lattice Wilson RG Source Marker Extraction Climb Trace.Pilot
open Next.UVStress Next.Rank RG12 RG17 PhysMS PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent MergeProof.East
open FVA1 OriginalForcedAddresses XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox OPE.Therm
open WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource WilsonPositionThermometerCapStation
open WilsonThermometerCenteredAlgebra WilsonThermometerFiniteConnectedCells WilsonThermometerAlignedCells
open WilsonThermometerCenteredScalar
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (A:Group R.family 6) (simple:G.Simple)
local notation "J" => Stock.census (Fin 3)
local notation "places" z:max => Fin 3→Site (R.family.side (z:UVIndex).1 z.2)
local notation "ν" z:max i:max => OPE.Therm.scene R.family.path (z:UVIndex).1 z.2 i
local notation "source₀" age:max z:max x:max => WilsonThermometerCourseResidual.table R A simple age
  (placement R z (atOrigin (offsets x)))
local notation "χ" r:max z:max => WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z
local notation "W" φ:max r:max z:max => WilsonSeparatedOriginalThermometerCells.weight φ (χ r z)
local notation "damp" w:max F:max Q:max => WilsonThermometerRegisteredCenteredInvoice.restoration w F Q
local notation "comp" w:max F:max Q:max => WilsonThermometerRegisteredCenteredInvoice.tested w F Q

theorem measured_unit {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}
    (checked:A.station.checked f H A.horizon) (unit:∀j,A.change j ((Bel R.family.book).unit j)=(Bel R.family.book).unit j)
    (z:UVIndex) (late:A.station.k<z.1) (refs:∀v:Fin 3,R.family.ref (index A (grade v))≤z.1) (x:places z):
    (measured R A z x).part (J).quiet=1:=by
  change R.family.omega z.1 z.2 (WilsonPositionThermometerJointFaces.submitted A z x ∅)=1
  have actual:=WilsonThermometerRegisteredMeasuredStation.submitted_at R A checked unit z late refs (placement R z x) ∅
  have blank:WilsonPositionThermometerJointFaces.submitted A z x ∅=fun _=>1:=by simpa only [WilsonThermometerFiniteConnectedCells.placement,Finset.prod_empty] using actual
  rw [blank];simp [Family.omega,Wilson.moment]

theorem original {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}
    (checked:A.station.checked f H A.horizon) (unit:∀j,A.change j ((Bel R.family.book).unit j)=(Bel R.family.book).unit j)
    (z:UVIndex) (late:A.station.k<z.1) (refs:∀v:Fin 3,R.family.ref (index A (grade v))≤z.1)
    (i:ℕ) (age:i ≤ z.1) (r:ℝ) (φ:Test 3) (Q:places z→Poly J) (qu:∀x,(Q x).part (J).quiet=1)
    (w:places z→Fin 3→ℝ) (wallet:∀x v,0<w x v):
    let M:=measured R A z
    let d:=fun x=>damp (w x) (M x) (Q x)
    let paid:=fun x=>comp (w x) (M x) (Q x)
    let price:=fun (x:places z) (B:Poly J)=>
      (∫U,(total ((source₀ age z x) U) B).part full ∂ν z i)-(total (Q x) B).part full
    φ.applyTo (WilsonPositionThermometerGradedReading.full r A z)-
      WilsonThermometerFiniteConnectedCells.reference R z r φ Q=
      ∑x,(W φ r z) x*((d x:ℂ)*price x (paid x)+(1-(d x:ℂ))*price x 1):=by
  intro M d paid price
  let trueVal (x:places z):=WilsonPositionThermometerConnected.value (WilsonPositionThermometerGradedReading.row A z x)
  let specVal (x:places z):=WilsonPositionThermometerConnected.value (read (Q x))
  have each (x:places z):trueVal x-specVal x=(d x:ℂ)*price x (paid x)+(1-(d x:ℂ))*price x 1:=by
    have mu:=measured_unit R A checked unit z late refs x
    have truth:read (Extra.Trajectories.connected (M x)) univ=trueVal x:=WilsonThermometerCenteredScalar.three _ mu
    have spec:read (Extra.Trajectories.connected (Q x)) univ=specVal x:=WilsonThermometerCenteredScalar.three _ (qu x)
    have density (B:Poly J):(total (M x-Q x) B).part full=price x B:=by
      have hear:=WilsonThermometerRegisteredMeasuredStation.original R A simple checked unit z late refs i age (atOrigin (offsets x)) B full
      have trans:=WilsonThermometerRegisteredAncestralProperTest.translated_table (N:=z.1) (per:=z.2) R A refs x
      have declared:(total (M x) B).part full=∫U,(total ((source₀ age z x) U) B).part full ∂ν z i:=by
        change (total (measured R A z x) B).part full=_
        rw [trans];exact hear.2
      calc
        _=(total (M x) B).part full-(total (Q x) B).part full:=by unfold total;rw [sub_mul];rfl
        _=price x B:=by rw [declared]
    rw [←truth,←spec,WilsonThermometerRegisteredCenteredInvoice.original (w x) (M x) (Q x) (wallet x) mu (qu x),density,density]
  have integrate:=WilsonSeparatedOriginalThermometerCells.tested φ (χ r z)
    (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)
  change φ.applyTo (fun p=>trueVal ((χ r z) p))-φ.applyTo (fun p=>specVal ((χ r z) p))=_
  rw [integrate trueVal,integrate specVal,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [←mul_sub,each]

end YM.Integration.WilsonThermometerRegisteredCenteredConnectedTest
