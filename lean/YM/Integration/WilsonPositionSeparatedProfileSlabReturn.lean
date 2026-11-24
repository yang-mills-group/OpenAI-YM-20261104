import YM.Integration.WilsonReportHarvestSlabSigned

/-! The full signed physical difference at capture has a numerical old read on the same vacuum. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileSlabReturn
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.View
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} (R:Run G) {b N per:ℕ}
set_option quotPrecheck false
local notation "C" => R.family
local notation "A" => (C).path
local notation "Y" => (C).path.rep N per
local notation "S" => (A).levels.clock.op b per
local notation "bill" => bling (A).levels b

theorem original (D : OPE.Package R.family R.w (Bandage.mutt R.family.path.levels R.Q) R.doors)
    (tiers:Cater C R.doors) (top:b<N) (eligible:3≤(A).levels.clock.J b)
    {o:Site ((C).side (b+1) per)} (home:(S).ratio.parent o=0)
    (amp base:Three G ((C).side (b+1) per)) (used:Useful (Y (b+1)) amp)
    (kept:Useful (Y (b+1)) base) {v δ:ℝ} (income:0≤v) (weight:0≤δ)
    (high:MergeProof.Float.Blade (Y (b+1)) o amp.2.1 (profile (Y (b+1)).activities amp.2.2) 0 v)
    (low:MergeProof.Float.Blade (Y (b+1)) o base.2.1 (profile (Y (b+1)).activities base.2.2) 0 v) :
    let raw:=fun W=>(δ:ℂ)*(amp.1 W-base.1 W)
    ∀u, (C).ref 0 ≤ u → ∀(age:u≤b),
      ‖pushTo A N per (age.trans b.le_succ) raw 1/liftVac A N per u 1‖ ≤
        (1+WilsonPositionSeparatedProfileStableReturn.price)*(bill*(2*δ*v)) := by
  obtain ⟨X,form,cash,small,_,readout⟩:=WilsonReportHarvestSlabSigned.original R tiers top eligible
    home amp base used kept income weight high low
  intro raw u grade age
  rw [←readout u age]
  have centered:=WilsonPositionSeparatedProfileStableReturn.original R D grade age top.le X form cash
  have unit : ‖X.x 0‖ ≤ ((C).labels.level 0).coeffSize X.x :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
  calc
    _ ≤ ‖WilsonPositionSeparatedProfileStableReturn.read (N:=N) R age X-X.x 0‖+‖X.x 0‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ WilsonPositionSeparatedProfileStableReturn.price*(bill*(2*δ*v))+bill*(2*δ*v) :=
      add_le_add centered (unit.trans small)
    _ = _ := by ring

end YM.Integration.WilsonPositionSeparatedProfileSlabReturn
