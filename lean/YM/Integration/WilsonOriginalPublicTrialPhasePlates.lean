import YM.Integration.WilsonOriginalPublicTrialPhaseLanding
import YM.RG05Readout.Capture.Fronds

/-! The elected original course issues a groupable capture at an arbitrary interior birth. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhasePlates
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu Marker
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many RG05Readout.Pantry
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open WilsonOriginalPublicTrialPhaseLanding
open private smaller from YM.Integration.WilsonOriginalPublicTrialPhaseLanding
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}(R:Run G){N m per:ℕ}{I:Type}[Fintype I][DecidableEq I]{Z:Census I}
local notation "C" => R.family
local notation "H" => (C).path
local notation "P" => (H).rep N per (m+1)
local notation "Q" => (H).rep N per m
local notation "O" => (H).levels.clock.op m per
local notation "δ" => Bandage.renal (H).levels m
local notation "slots" => apron (H).levels m

set_option maxHeartbeats 900000 in
theorem original (cater:Cater (C) R.doors)(hm:m<N)(hmpos : 1 ≤ m)
    (o:I→Site ((C).side (m+1) per))(w l:I→ℝ)(ν:I→ℂ)
    (X:I→Three G ((C).side (m+1) per))(Y:I→Three G ((C).side m per))
    (M:Config G ((C).side (m+1) per)→Poly Z)(pos:∀i,0<w i)(large:∀i,1≤‖ν i‖)
    (e:ℝ)(pitch:((P).p.supportExponent)-4≤e)(started:MenuBoard (P) X M o w e 1)
    (rides:∀i,Ride (O) (o i) ((O).ratio.parent (o i)) (R.doors N per m hm) (ν i) (X i) (Y i) (l i))
    (near:Occupancy o slots)(parents:Occupancy ((O).ratio.parent ∘ o) slots):
    let w':=fun i=>δ*first (w i) (l i)
    let M':=(O).push (P).beta M
    (∀i,0<w' i) ∧ Integrable M' (prior G _) ∧ Arsenal (Q) ∧
    ∃t:ℝ,Furls (H).levels m t ∧
      Alcove (Q) (fun i=>(ν i)⁻¹ • Y i) M' ((O).ratio.parent ∘ o) w' t δ (1/2):=by
  intro w' M'
  obtain ⟨a,t,course,hG,hA⟩:=cater.tiers m N per hm
  have hr i:=limits (pos i) (l i)
  have positive i:0<w' i:=mul_pos course.poses.hats.1 (hr i).1
  have paid:=smaller started pos (fun i=>(hr i).1) (fun i=>(hr i).2.1)
  have eqPitch:(P).p.supportExponent=((H).levels.budget (m+1)).supportExponent:=
    congrArg BudgetPoint.supportExponent (R.makes.wilson.represents N per (m+1) hm).vac
  have hx:((H).levels.budget (m+1)).supportExponent-4≤e:=by rw [← eqPitch];exact pitch
  have hB:=course.plates R.makes.wilson hm paid hx large (fun i=>(hr i).1) rides near parents
    (fun i=>(hr i).2.2)
  have hJ:Arsenal (Q):=by
    cases m with
    | zero=>omega
    | succ m=>
      obtain ⟨_,_,priorCourse,_,_⟩:=cater.tiers m N per (Nat.lt_of_succ_lt hm)
      exact priorCourse.publishes.contact
  have positive_t:0≤t:=by
    obtain ⟨_,_,_,_,_,hK,_⟩:=hB.chamber
    obtain ⟨_,_,h,_⟩:=hK
    exact (tsum_nonneg (h 0).1).trans (h 0).2.2
  exact ⟨positive,StepData.push_integrable ((H).levels.transition_mass ..) _ started.cleared,
    hJ,t,⟨positive_t,course.poses.hats.1,course.poses.hats.2,course.poses.exp.1,
      course.poses.stakes.1,hG,hA⟩,hB⟩

end YM.Integration.WilsonOriginalPublicTrialPhasePlates
