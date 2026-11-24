import YM.Integration.WilsonReportHarvestSlabGerm
import YM.Integration.WilsonMacroscopicRichBookedReportMeter

/-! A single original rooted upper source files its complete Wilson credit at any eligible output degree. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichGradedCapture
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

open RG16.Literal

theorem original (h:ℕ)(tiers:Cater C R.doors) (top:b<N) (eligible:h+3≤(A).levels.clock.J b)
    {o:Site ((C).side (b+1) per)} (home:(S).ratio.parent o=0)
    (X:Three G ((C).side (b+1) per)) (valid:Useful (Y (b+1)) X)
    {v:ℝ} (raw:MergeProof.Float.Blade (Y (b+1)) o X.2.1
      (profile (Y (b+1)).activities X.2.2) 0 v) (pos:0≤v)
    (f:Cut C N per) (cont:Continuous f) (actual:X.1=credit C N per 0 f (b+1) top):
    let fee:=(C).S.a (b+1)^h*(bill*v)
    (∃ K:Coefficient ((C).labels.level h) ((C).side b per),
      K.Format 0 (C).params (Y b) ∧ K.remBound 0 (Y b) (kappa A b) fee ∧
      ((C).labels.level h).coeffSize K.x≤fee ∧
      credit C N per h f b top.le=K.density 0 ((C).localSection h) (Y b)) ∧
      Booked C N per h f b top.le:=by
  dsimp only
  obtain ⟨_,_,course,_⟩:=tiers.tiers b N per top
  have plated:=tiers.throve h b N per top eligible
  have positive:0≤bill:=(Real.exp_pos _).le
  obtain ⟨K,fmt,tariff,size,ride⟩:=RG05Readout.Address.peppers («C»:=R.family) R.makes plated home top
    course.publishes.propagate positive valid raw pos
  let α:ℂ:=((C).S.a (b+1):ℂ)^h
  have scale:‖α‖=(C).S.a (b+1)^h:=by
    rw [show α=((C).S.a (b+1):ℂ)^h by rfl,norm_pow,Complex.norm_real,Real.norm_of_nonneg ((C).S.a_pos _).le]
  have step:K.density 0 ((C).localSection h) (Y b)=
      (((C).S.block b).val:ℂ)^h • (S).push (Y (b+1)).beta X.1:=ride.exactStep
  have carried:(S).push (Y (b+1)).beta X.1=credit C N per 0 f b top.le:=by
    rw [actual]
    have next:=credit_step C N per 0 f cont top
    change _ = (((C).S.block b).val:ℂ)^0 • (S).push (Y (b+1)).beta
      (credit C N per 0 f (b+1) top) at next
    simpa only [pow_zero,one_smul] using next.symm
  have mesh:((C).S.a (b+1):ℂ)*(((C).S.block b).val:ℂ)=((C).S.a b:ℂ):=by
    rw [(C).S.a_step];push_cast;field_simp
  have full:credit C N per h f b top.le=(stretch α K).density 0 ((C).localSection h) (Y b):=by
    funext U
    rw [stretch_density]
    change _=(α • K.density 0 ((C).localSection h) (Y b)) U
    rw [step,carried,smul_smul,show α=((C).S.a (b+1):ℂ)^h by rfl,←mul_pow,mesh]
    simp only [credit,pow_zero,one_smul]
  have amount:(stretch α K).remBound 0 (Y b) (kappa A b) ((C).S.a (b+1)^h*(bill*v)):=by
    simpa only [←scale] using stretch_rem α tariff
  have face:((C).labels.level h).coeffSize (stretch α K).x≤(C).S.a (b+1)^h*(bill*v):=by
    change ((C).labels.level h).coeffSize (α • K.x)≤_
    rw [Size.smul,scale]
    exact mul_le_mul_of_nonneg_left size (pow_nonneg ((C).S.a_pos _).le _)
  exact ⟨⟨_,stretch_format α fmt,amount,face,full⟩,⟨_,_,⟨stretch_format α fmt,amount⟩,full⟩⟩

end YM.Integration.WilsonMacroscopicRichGradedCapture
