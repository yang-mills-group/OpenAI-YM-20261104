import YM.Integration.WilsonThermometerClusterSourceReturn
import YM.Integration.WilsonThermometerReopenedFare
import YM.Integration.WilsonThermometerUnitNames

noncomputable section
namespace YM.Integration.WilsonThermometerMixedBooked
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
open WilsonMixedTaggedRoster WilsonMixedTaggedOutput WilsonMixedTaggedPrice
open scoped Topology BigOperators Classical
open MergeProof.Float
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Records Harvest Copper
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Motion Bandage Extra.Multi Extra.Trajectories
open ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus MergeProof.Float
open scoped Topology BigOperators Classical
open RG05Readout.Pantry
open Planned.GuardedAtom Guard MergeProof.Accent MergeProof.Ribbon MergeProof.Menu PhysicalNext.Repeat.Mallow
set_option quotPrecheck false
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] [DecidableEq I]
local notation "A" => R.family.path.levels
local notation "C" => R.family
local notation "β" => (A).clock.hatBeta
local notation "Y" => Stock.census (Unit×I)
set_option quotPrecheck false

def nextRadius (j:ℕ) (w:Unit×I→ℝ) (i:Unit×I):ℝ:=
  renal (A) j*(renal (A) j*w i)/Real.exp (((A).budget j).supportExponent+1/2)

/-- Advance every occupied component through the same Wilson kernel and reopen its original support. -/
theorem original (cater:Cater R.family R.doors) {j N p:ℕ} (edge:j+1<N) (d:ℝ) :
    let top:=(C).path.rep N p (j+2)
    let middle:=(C).path.rep N p (j+1)
    let step:=(A).clock.op (j+1) p
    ∀ (raw:Unit×I→Three G ((C).side (j+2) p)) (down:Unit×I→Three G ((C).side (j+1) p))
      (o:Unit×I→Site ((C).side (j+2) p)) (w cost:Unit×I→ℝ)
      (F:Config G ((C).side (j+2) p)→Poly (Y)),
    MenuBoard top raw F o w d 1 → ((A).budget (j+2)).supportExponent-4≤d →
    (∀i,0<w i) → (∀i,Ride step (o i) (step.ratio.parent (o i)) (R.doors N p (j+1) edge)
      1 (raw i) (down i) (cost i)) →
    Occupancy o (apron (A) (j+1)) → Occupancy (step.ratio.parent ∘ o) (apron (A) (j+1)) →
    (∀i,2*w i*cost i≤1) →
      MenuBoard middle down (step.push top.beta F) (step.ratio.parent ∘ o) (nextRadius R (j+1) w)
        (((A).budget (j+1)).supportExponent-2) 1 ∧
      ∀i,(nextRadius R (j+1) w i)⁻¹ ≤ (β (j+2))^6*(w i)⁻¹:=by
  intro top middle step raw down o w cost F board wide pos rides upper lower capacity
  obtain ⟨a,t,course,sale⟩:=cater.tiers (j+1) N p edge
  obtain ⟨_,_,prev,_⟩:=cater.tiers j N p (show j<N by omega)
  have law:=R.makes.wilson
  have good:=law.represents N p (j+1) edge.le
  have book:=course.plates law edge board wide (ν:=fun _=>1) (fun _=>by simp)
    pos rides upper lower capacity
  simp only [inv_one,one_smul] at book
  have integrable:=StepData.push_integrable ((A).transition_mass (j+1) p top.beta) _ board.cleared
  have equal:middle.p=(A).budget (j+1):=good.vac
  obtain ⟨again,fee⟩:=WilsonThermometerReopenedFare.original (C).path course equal sale book
    prev.publishes.contact good.good.labels (fun U=>(Tour.bright (C).path law N p _ edge.le U).ne')
    integrable lower (fun i=>mul_pos course.poses.hats.1 (pos i))
  constructor
  · unfold nextRadius;rw [←equal];exact again
  · intro i
    have bound:=fee i
    change (renal (A) (j+1)*(renal (A) (j+1)*w i)/Real.exp (middle.p.supportExponent+1/2))⁻¹ ≤ _ at bound
    unfold nextRadius;rw [←equal]
    apply bound.trans
    have hot:0 < β (j+2):=zero_lt_one.trans ((A).fits.delayed _)
    have one:renal (A) (j+1)=((β (j+2))^2)⁻¹:=by
      unfold renal probe
      rw [Real.rpow_neg hot.le]
      norm_num
    apply le_of_eq
    rw [one,mul_inv_rev,inv_inv]
    ring
end YM.Integration.WilsonThermometerMixedBooked
end
