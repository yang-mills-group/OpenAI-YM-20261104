import YM.Integration.WilsonThermometerPepperCapture
import YM.Integration.WilsonThermometerClusterOlderReading
import YM.Integration.WilsonThermometerWeakMixedCapture

/- The original final two transfers read each scalar-shifted captured face on
   its genuine older Wilson history at the same native radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPepperLastRead
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu MergeProof.Ribbons
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Records Harvest Copper
open PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi Extra.Trajectories
open MergeProof.Float
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Records Harvest Copper
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi Extra.Trajectories
open ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus MergeProof.Float
open scoped Topology BigOperators Classical
 MergeProof.Ribbon Pressure
open WilsonMixedTaggedRoster WilsonMixedTaggedOutput WilsonMixedTaggedPrice
open scoped Topology BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge} {n:Side} {I J:Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable (R:Run G)
local notation "A" => R.family.path.levels
local notation "C" => R.family
open MergeProof.Float
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Records Harvest Copper
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi Extra.Trajectories
open ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus MergeProof.Float
open scoped Topology BigOperators Classical


open Trace.Physical.GermGraph WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFeed

theorem original (simple:G.Simple) (cater:Cater R.family R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A)) (wage:WilsonReportLampForecast.Ready (A)):
    ∀ᶠ j:ℕ in atTop,∀ N p (edge:j+1<N) (L:Fibers I J) (H l:ℕ),0<H →
    (∀v,(L.contents v).card≤H) →
    let top:=(C).path.rep N p (j+2)
    let middle:=(C).path.rep N p (j+1)
    let step:=(A).clock.op (j+1) p
    ∀ (raw:I→Three G ((C).side (j+2) p)) (down:I→Three G ((C).side (j+1) p))
      (o:I→Site ((C).side (j+2) p)) (w cost:I→ℝ) (F:Config G ((C).side (j+2) p)→Poly (Stock.census I)),
    ∀ a:ℝ, MenuBoard top raw F o w a 1 → ((A).budget (j+2)).supportExponent-4 ≤ a →
    (∀i,0<w i) → (∀i,Ride step (o i) (step.ratio.parent (o i)) (R.doors N p (j+1) edge)
      1 (raw i) (down i) (cost i)) →
    Occupancy o (apron (A) (j+1)) → Occupancy (step.ratio.parent ∘ o) (apron (A) (j+1)) →
    (∀i,2*w i*cost i≤1) →
    (∀i,coverNumber middle.p.B ({step.ratio.parent (o (L.twig (L.bunch i))),step.ratio.parent (o i)}:
       Support ((C).side (j+1) p))≤l) →
    ∀ direction:I→ℂ,(∀i,renal (A) (j+1)*w i*‖direction i‖≤1/2) →
    let sites:=step.ratio.parent ∘ o ∘ L.twig
    let fees:=WilsonThermometerWeakMixedGrouping.radius L middle H l (renal (A) (j+1))
      (fun i=>renal (A) (j+1)*w i)
    let filed:=fun U=>Fibers.reap L (Poly.pass (Mach (Stock.census I) direction)*step.push top.beta F U)
    ∀v,((A).clock.op j p).ratio.parent (sites v)=0 →
      ∀u:ℕ,(C).ref 0 ≤ u → ∀ uj:u≤j, Opened (C) 0 u p → Opened (C) 0 j p →
      ‖reading R (N:=N) (p:=p) (((A).clock.op j p).push middle.beta
          (fun U=>(filed U).part ((Stock.census J).fire v))) u uj‖ ≤
        (25+24*((A).params j).columns)*((A).clock.hatBeta j)^4*(4*(1/fees v)) := by
  filter_upwards [WilsonThermometerClusterOlderReading.original (I:=J) R simple cater bank wage]
    with j read N p edge L H l hH bound
  dsimp only
  intro raw down o w cost F a board wide pos rides upper lower capacity close direction affordable
  let middle:=(C).path.rep N p (j+1)
  let step:=(A).clock.op (j+1) p
  obtain ⟨a,t,course,bars⟩:=cater.tiers (j+1) N p edge
  obtain ⟨_,_,prev,_⟩:=cater.tiers j N p (show j<N by omega)
  have law:=R.makes.wilson
  have good:=law.represents N p (j+1) edge.le
  have next:=course.plates law edge board wide (ν:=fun _=>1) (fun _=>by simp)
    pos rides upper lower capacity
  simp only [inv_one,one_smul] at next
  have fee:=bars
  unfold Ribbons.scurry at fee
  have equal:middle.p=(A).budget (j+1):=good.vac
  rw [←equal] at fee
  obtain ⟨g,K,menu,blade⟩:=WilsonThermometerPepperCapture.grouped L _ next
    prev.publishes.contact good.good.labels (fun U=>(Tour.bright (C).path law N p _ edge.le U).ne')
    (fun i=>mul_pos course.poses.hats.1 (pos i)) lower hH bound close course.poses.hats.1 course.poses.hats.2 fee direction affordable
  intro v home
  have raised:=StepData.push_integrable ((A).transition_mass (j+1) p ((C).path.rep N p (j+2)).beta) _ board.cleared
  let shift:Poly (Stock.census I) →ₗ[ℂ] Poly (Stock.census I):=
    Algebra.lmul ℂ _ (Poly.pass (Mach (Stock.census I) direction))
  have provision:=((LinearMap.toContinuousLinearMap shift).restrictScalars ℝ).integrable_comp raised
  have seen:=((Fibers.reap L).restrictScalars ℝ).integrable_comp provision
  have cash:0<WilsonThermometerWeakMixedGrouping.radius L middle H l (renal (A) (j+1))
      (fun i=>renal (A) (j+1)*w i) v := by
    unfold WilsonThermometerWeakMixedGrouping.radius
    apply Finset.prod_pos
    intro i _
    have wage':0<(H:ℝ):=by exact_mod_cast hH
    have α:=course.poses.hats.1
    have ω:=pos i
    unfold Fibers.Salt.tow
    positivity
  exact read N p (show j<N by omega) _ _ _ _ _ menu blade seen v cash home
end YM.Integration.WilsonThermometerPepperLastRead
end
