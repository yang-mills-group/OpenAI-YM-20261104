import YM.Integration.WilsonThermometerPepperFace
import YM.Integration.WilsonThermometerPepperLastRead
import YM.Integration.WilsonThermometerPepperDifference
import YM.Integration.WilsonThermometerCorridorLastRead

/- The cubic face and its three proper pairs on one true earlier filing, at
   the physical compact housing even when the observed pair omits the origin. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCorridorFourFaces
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

open WilsonThermometerPepperFace

theorem original (simple:G.Simple)(cater:Cater R.family R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A))(wage:WilsonReportLampForecast.Ready (A)):
    ∀ᶠ j:ℕ in atTop,∀ N p (edge:j+1<N) (anchor:I) (l:ℕ),
    let top:=(C).path.rep N p (j+2)
    let middle:=(C).path.rep N p (j+1)
    let step:=(A).clock.op (j+1) p
    ∀ (raw:I→Three G ((C).side (j+2) p)) (down:I→Three G ((C).side (j+1) p))
      (o:I→Site ((C).side (j+2) p)) (w cost:I→ℝ) (F:Config G ((C).side (j+2) p)→Poly (Stock.census I)),
    ∀ a:ℝ,MenuBoard top raw F o w a 1 → ((A).budget (j+2)).supportExponent-4 ≤ a →
    (∀i,0<w i) → (∀i,Ride step (o i) (step.ratio.parent (o i)) (R.doors N p (j+1) edge)
      1 (raw i) (down i) (cost i)) →
    Occupancy o (apron (A) (j+1)) → Occupancy (step.ratio.parent ∘ o) (apron (A) (j+1)) →
    (∀i,2*w i*cost i≤1) →
    (∀i,coverNumber middle.p.B ({step.ratio.parent (o anchor),step.ratio.parent (o i)}:
       Support ((C).side (j+1) p))≤l) →
    ((A).clock.op j p).ratio.parent (step.ratio.parent (o anchor))=0 →
    ∀u:ℕ,(C).ref 0 ≤ u → ∀ uj:u≤j,Opened (C) 0 u p → Opened (C) 0 j p →
    let wallet:=fun i=>renal (A) (j+1)*w i
    let fees:=WilsonThermometerWeakMixedGrouping.radius (atSite anchor) middle (Fintype.card I) l
      (renal (A) (j+1)) wallet
    let bill:=(25+24*((A).params j).columns)*((A).clock.hatBeta j)^4*(4*(1/fees ()))
    let seen:=fun s:(Stock.census I).Mode=>WilsonThermometerUnitFilingCoarse.reading R (N:=N) (p:=p) (((A).clock.op j p).push middle.beta
      (fun U=>(step.push top.beta F U).part s)) u uj
    ‖seen (whole I)‖ ≤ bill ∧
      ∀i,‖seen (rest ((Stock.census I).fire i))‖≤4*wallet i*bill:=by
  filter_upwards [WilsonThermometerCorridorLastRead.original (I:=I) (J:=Unit) R simple cater bank wage,
    WilsonThermometerPepperLastRead.original (I:=I) (J:=Unit) R simple cater bank wage]
    with j plain shifted N p edge anchor l
  dsimp only
  intro raw down o w cost F a board wide pos rides upper lower cash close origin u ref uj ou oj
  let step:=(A).clock.op (j+1) p
  let top:=(C).path.rep N p (j+2)
  let middle:=(C).path.rep N p (j+1)
  let wallet:=fun i=>renal (A) (j+1)*w i
  obtain ⟨_,_,course,_⟩:=cater.tiers (j+1) N p edge
  have living (i:I):0<wallet i:=mul_pos course.poses.hats.1 (pos i)
  have load:0<Fintype.card I:=Fintype.card_pos_iff.mpr ⟨anchor⟩
  have count (v:Unit):((atSite anchor).contents v).card≤Fintype.card I:=Finset.card_le_univ _
  have bare:=plain N p edge (atSite anchor) (Fintype.card I) l load count raw down o w cost F a board
    wide pos rides upper lower cash close () origin u ref uj ou oj
  simp only [home] at bare
  refine ⟨bare,?_⟩
  intro i
  let direction:=scalar i ((2*wallet i)⁻¹:ℝ)
  have tapped:=shifted N p edge (atSite anchor) (Fintype.card I) l load count raw down o w cost F a board
    wide pos rides upper lower cash close direction (affordable wallet living i) () origin u ref uj ou oj
  simp only [home,direction,WilsonThermometerPepperFace.reading] at tapped
  have raised:=StepData.push_integrable ((A).transition_mass (j+1) p top.beta) F board.cleared
  exact WilsonThermometerPepperDifference.pair R (N:=N) uj (wallet i) _ (living i)
    _ _ ((Poly.get (whole I)).integrable_comp raised)
    ((Poly.get (rest ((Stock.census I).fire i))).integrable_comp raised) bare tapped

end YM.Integration.WilsonThermometerCorridorFourFaces
end
