import YM.Integration.WilsonReportHarvestSlabSingle
import YM.Integration.WilsonPositionSeparatedProfileStableReturn

/-! Extract the horizon-zero coefficient of the new grouped mark through
its actual physical Wilson door. Its density is the push of the entire
unnormalized signed group, at every held coarser field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabGerm
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.View
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} (R:Run G) {b N per:ℕ}
set_option quotPrecheck false
local notation "C" => R.family
local notation "A" => (C).path
local notation "Y" => (C).path.rep N per
local notation "S" => (A).levels.clock.op b per
local notation "bill" => bling (A).levels b

theorem original (tiers:Cater C R.doors) (top:b<N) (eligible:3≤(A).levels.clock.J b)
    {o:Site ((C).side (b+1) per)} (home:(S).ratio.parent o=0)
    (new:Three G ((C).side (b+1) per)) (valid:Useful (Y (b+1)) new)
    {v:ℝ} (raw:MergeProof.Float.Blade (Y (b+1)) o new.2.1
      (profile (Y (b+1)).activities new.2.2) 0 v) (pos:0≤v) :
    ∃K:Coefficient ((C).labels.level 0) ((C).side b per),
      K.Format 0 (C).params (Y b) ∧ K.remBound 0 (Y b) (kappa A b) (bill*v) ∧
      ((C).labels.level 0).coeffSize K.x≤bill*v ∧
      K.density 0 ((C).localSection 0) (Y b)=(S).push (Y (b+1)).beta new.1 ∧
      ∀u (age:u≤b),WilsonPositionSeparatedProfileStableReturn.read (N:=N) R age K=
        pushTo A N per (age.trans b.le_succ) new.1 1/liftVac A N per u 1 := by
  obtain ⟨_,_,course,_⟩:=tiers.tiers b N per top
  have plated:=tiers.throve 0 b N per top eligible
  have positive:0≤bill:=(Real.exp_pos _).le
  obtain ⟨K,fmt,tariff,size,ride⟩:=RG05Readout.Address.peppers («C»:=R.family) R.makes plated home top
    course.publishes.propagate positive valid raw pos
  have field:K.density 0 ((C).localSection 0) (Y b)=(S).push (Y (b+1)).beta new.1:=by
    have step:=ride.exactStep
    rw [pow_zero,one_smul] at step
    exact step
  refine ⟨K,fmt,tariff,size,field,fun u age=>?_⟩
  unfold WilsonPositionSeparatedProfileStableReturn.read
  refine (congrArg (fun f=>pushTo A N per age f 1/liftVac A N per u 1) field).trans ?_
  rw [pushTo_next A N per age]

end YM.Integration.WilsonReportHarvestSlabGerm
