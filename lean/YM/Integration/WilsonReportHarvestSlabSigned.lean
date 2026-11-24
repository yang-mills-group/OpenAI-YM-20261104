import YM.Integration.WilsonReportHarvestSlabGerm

/-! Combine the two actual captured marks before crossing the physical
door. The same forced inventory is kept in both their signed densities. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestSlabSigned
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

theorem original (tiers:Cater C R.doors) (top:b<N) (eligible:3≤(A).levels.clock.J b)
    {o:Site ((C).side (b+1) per)} (home:(S).ratio.parent o=0)
    (amp base:Three G ((C).side (b+1) per)) (used:Useful (Y (b+1)) amp)
    (kept:Useful (Y (b+1)) base) {v δ:ℝ} (income:0≤v) (weight:0≤δ)
    (high:MergeProof.Float.Blade (Y (b+1)) o amp.2.1 (profile (Y (b+1)).activities amp.2.2) 0 v)
    (low:MergeProof.Float.Blade (Y (b+1)) o base.2.1 (profile (Y (b+1)).activities base.2.2) 0 v) :
    let raw:=fun W=>(δ:ℂ)*(amp.1 W-base.1 W)
    ∃K:Coefficient ((C).labels.level 0) ((C).side b per),
      K.Format 0 (C).params (Y b) ∧ K.remBound 0 (Y b) (kappa A b) (bill*(2*δ*v)) ∧
      ((C).labels.level 0).coeffSize K.x≤bill*(2*δ*v) ∧
      K.density 0 ((C).localSection 0) (Y b)=(S).push (Y (b+1)).beta raw ∧
      ∀u (age:u≤b),WilsonPositionSeparatedProfileStableReturn.read (N:=N) R age K=
        pushTo A N per (age.trans b.le_succ) raw 1/liftVac A N per u 1 := by
  let z:ℂ:=δ
  let pos:=z • amp
  let neg:=(-z) • base
  have hp:=Useful.smul (Y (b+1)) amp z used
  have hn:=Useful.smul (Y (b+1)) base (-z) kept
  have joined:=Useful.join (Y (b+1)) (R.makes.wilson.represents N per (b+1) top).good hp hn
  have wz:‖z‖=δ:=by simp [z,abs_of_nonneg weight]
  have solid:MergeProof.Float.Blade (Y (b+1)) o (pos+neg).2.1
      (profile (Y (b+1)).activities (pos+neg).2.2) 0 (2*δ*v):=by
    change MergeProof.Float.Blade _ _ (z • amp.2.1+(-z) • base.2.1)
      (profile _ (z • amp.2.2+(-z) • base.2.2)) 0 _
    have dh:Dominated (z • amp.2.2):=hp.normK
    have dl:Dominated ((-z) • base.2.2):=hn.normK
    rw [MergeProof.Float.prof_add _ dh dl,profile_scale,profile_scale]
    have paid:=(high.rate z).comp (low.rate (-z))
    rw [mul_zero,mul_zero,add_zero,norm_neg,wz,←add_mul,←two_mul] at paid
    exact paid
  have issued:=WilsonReportHarvestSlabGerm.original R tiers top eligible home
    (pos+neg) joined solid (mul_nonneg (mul_nonneg (by norm_num) weight) income)
  have eq : (pos+neg).1=fun W=>(δ:ℂ)*(amp.1 W-base.1 W):=by
    funext W
    change (δ:ℂ)*(amp.1 W)+(-(δ:ℂ))*(base.1 W)=_
    ring
  dsimp only
  rw [eq] at issued
  exact issued

end YM.Integration.WilsonReportHarvestSlabSigned
