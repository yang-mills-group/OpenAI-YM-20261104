import YM.Integration.WilsonPositionScaleLawMeasuredCut
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredDatum
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionCapTransport
open WilsonPositionProgramTrialPublicJointPivotOriginalArms (ordinary)
open WilsonPhysicalStationMixedWickPositionedMeter (moved)
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{o:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family o S)(J:ℝ→tower S) (Z:WilsonPrescription G)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{B n:ℕ}
local notation "posed" => WilsonPositionPrescribedFrame.positioned F J Z.store
open WilsonPositionScaleLawMeasuredCut (bag)
def filed (A:Group R.family B)(j:Fin (B+1))(six:6≤B){r:ℝ}(rp:0<r)(z:ℕ×ℕ) : MoveSpace G j×ℝ :=
  ((Z.store.survey j).itinerary (bag F J Z A j rp z,0),WilsonPositionScaleLawMeasuredCut.reading F J Z A six r z)
theorem original (lead:Leading F J)(simple:G.Simple)(prior:(l:Filter _)≤o.fuse)(A:ℝ→Group R.family B)
    (paid:Book (f:=o) (l:=l) (H:=H) A J) (six:6≤B) :
    ∀ᶠr in trail,∀rp:0<r,∀j:Fin (B+1),Tendsto (filed F J Z (A r) j six rp) (l:Filter _)
      (𝓝 (WilsonPositionScaleLawMeasuredBank.fixed Z j,WilsonPositionHomogeneousFrame.reading F J Z r)) := by
  filter_upwards [WilsonPositionScaleLawMeasuredCut.menu F J Z prior A paid,
    WilsonPositionScaleLawMeasuredCut.sensor F J Z simple prior A paid six,
    eventually_all.mpr (fun j:Fin (B+1)=>WilsonPositionScaleLawMeasuredOriginal.position Z F J lead j)] with r menus sensor eq rp j
  let P:=WilsonPositionPrescribedScreen.hierarchy F posed j r
  let D:=Z.store.survey j
  have unchanged : recruit (Fray.box (0:MoveSpace G j)) P=P := by
    simpa only [Fray.box,map_zero,stand0] using Screen.recruit_one P
  have landed : D.itinerary (D.purse P,0)=WilsonPositionScaleLawMeasuredBank.fixed Z j := by
    rw [D.way,unchanged]
    exact congrArg (guide G j) (eq j)
  have xs : Tendsto (fun z=>D.itinerary (bag F J Z (A r) j rp z,0)) (l:Filter _)
      (𝓝 (D.itinerary (D.purse P,0))) :=
    D.fair.continuous.continuousAt.tendsto.comp ((menus rp j).prodMk_nhds tendsto_const_nhds)
  rw [landed] at xs
  exact xs.prodMk_nhds (sensor rp)
end YM.Integration.WilsonPositionScaleLawMeasuredDatum
