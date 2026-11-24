import YM.Integration.WilsonThermometerPepperTwice
import YM.Integration.WilsonThermometerCorridorFourFaces
/- The cubic face and its three proper pairs on one true earlier filing, at
   the physical compact housing even when the observed pair omits the origin. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerCorridorTwoShifts
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
    ∀a b:I,b≠a → ‖seen (WilsonThermometerPepperTwice.stripped (rest ((Stock.census I).fire a)) b)‖≤
      4*wallet b*(4*wallet a*bill):=by
  filter_upwards [WilsonThermometerCorridorFourFaces.original (I:=I) R simple cater bank wage,
    WilsonThermometerPepperLastRead.original (I:=I) (J:=Unit) R simple cater bank wage]
    with j plain shifted N p edge anchor l
  dsimp only
  intro raw down o w cost F width board wide pos rides upper lower cash close origin u ref uj ou oj a b diff
  let step:=(A).clock.op (j+1) p
  let top:=(C).path.rep N p (j+2)
  let mid:=(C).path.rep N p (j+1)
  let wallet:=fun i=>renal (A) (j+1)*w i
  obtain ⟨_,_,course,_⟩:=cater.tiers (j+1) N p edge
  have living (i:I):0<wallet i:=mul_pos course.poses.hats.1 (pos i)
  have load:0<Fintype.card I:=Fintype.card_pos_iff.mpr ⟨anchor⟩
  have count (v:Unit):((atSite anchor).contents v).card≤Fintype.card I:=card_le_univ _
  let ca:ℂ:=((2*wallet a)⁻¹:ℝ)
  let cb:ℂ:=((2*wallet b)⁻¹:ℝ)
  have base:=(plain N p edge anchor l raw down o w cost F width board wide pos rides upper lower cash close origin u ref uj ou oj).2 a
  have filed:=shifted N p edge (atSite anchor) (Fintype.card I) l load count raw down o w cost F width board
    wide pos rides upper lower cash close
  have single:=filed (scalar b cb) (WilsonThermometerPepperFace.affordable wallet living b) () origin u ref uj ou oj
  simp only [home,WilsonThermometerPepperFace.reading] at single
  have double:=filed (WilsonThermometerPepperTwice.joined a b ca cb)
    (WilsonThermometerPepperTwice.affordable a b diff wallet living) () origin u ref uj ou oj
  simp only [home,WilsonThermometerPepperTwice.together a b diff] at double
  let cost₀:=(25+24*((A).params j).columns:ℝ)*((A).clock.hatBeta j)^4*
    (4*(1/WilsonThermometerWeakMixedGrouping.radius (atSite anchor) mid (Fintype.card I) l
      (renal (A) (j+1)) wallet ()))
  let X:=step.push top.beta F
  have hx:=StepData.push_integrable ((A).transition_mass (j+1) p top.beta) F board.cleared
  let get:=fun (s:(Stock.census I).Mode) (U:Config G ((C).side (j+1) p))=>(X U).part s
  have cash₀ (s):Integrable (get s) (prior G _):=(Poly.get s).integrable_comp hx
  let sA:=rest ((Stock.census I).fire a)
  let sB:=rest ((Stock.census I).fire b)
  let sC:=WilsonThermometerPepperTwice.stripped sA b
  have first:=WilsonThermometerPepperDifference.pair R (N:=N) uj (wallet a) cost₀ (living a)
    (get (whole I)+cb • get sB) (get sA+cb • get sC)
    ((cash₀ _).add ((cash₀ _).smul cb)) ((cash₀ _).add ((cash₀ _).smul cb)) single double
  exact WilsonThermometerPepperDifference.pair R (N:=N) uj (wallet b) _ (living b)
    (get sA) (get sC) (cash₀ _) (cash₀ _) base first
end YM.Integration.WilsonThermometerCorridorTwoShifts
end
