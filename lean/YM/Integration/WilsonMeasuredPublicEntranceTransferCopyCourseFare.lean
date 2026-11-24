import YM.Integration.WilsonMeasuredPublicEntranceTransferCopyGroupClock
import YM.Integration.WilsonMeasuredPublicEntranceTransferCopyRowSalary
import YM.Integration.WilsonMeasuredPublicEntranceTransferCopySeedRoster

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCopyCourseFare
open Filter Real Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Legato.Bandage
open WilsonOriginalPublicTrialPhaseRowRun (width)
open WilsonOriginalPublicTrialPhaseSpine (capital)
open WilsonMeasuredPublicEntranceTransferCopySpineCash (stock)
open scoped Classical Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "S" => R.family.S
local notation "H" j:arg => R.family.path.levels.clock.hatBeta j
local notation "levels" => R.family.path.levels
local notation "δ" => renal levels
local notation "group" => WilsonOriginalPublicTrialPhaseGroup.wage
local notation "beam" => WilsonOriginalPublicTrialPhaseRay.weight
local notation "race" => WilsonOriginalPublicTrialPhaseRace.wage

include simple in
theorem original {I:Type}[Fintype I][DecidableEq I](i:I)(u q A D e L:ℕ)(T Z Z₀:ℝ)
    (tp:0≤T)(z0:0≤Z+1/2):
    ∀ᶠ c:ℕ in atTop,∀ f K:ℕ,c≤f→f≤K→∀ck:c+1≤K,H K≤2*H c→(S).a c/(S).a K≤(H c)^A →
    ∃ B:ℝ,1≤B ∧
      (let r:=(1+8*(bling levels c+2)*B)/min 1 (δ c)
       let w:=beam (S) r c u
       let a:=w*race (S) r c u
       exp (Z₀+a+a+2)/w≤1/(H f)^q) ∧
      ∀{V:Type}[Fintype V][DecidableEq V],∀v:V,∀d:V×I→ℕ,∀b w:V×I→ℝ,∀z:ℝ,∀l:ℕ,
      (∀s,d s≤D)→(∀s,0≤b s)→(∀s,b s≤T*(H K)^e)→(∀s,0<w s)→(∀s,(w s)⁻¹≤b s)→
      z≤Z → l≤L →
      let moves:=fun j s=>capital (S) (d s) K j (b s)
      let fW:=width δ w moves K (c+1) ck
      (group i fW z (δ (c+1)) l ((),v))⁻¹≤B:=by
  let ticket:=stock T e
  have t1:1≤ticket:=by change 1≤1+2*T*(2:ℝ)^e;exact le_add_of_nonneg_right (by positivity)
  have earlier:=WilsonMeasuredPublicEntranceTransferCopyGroupClock.original R simple i A (A*(D+4)+e) L ticket Z t1 z0
  have after:=WilsonMeasuredPublicEntranceTransferCopyAwardPrice.original R simple Z₀ u q
  filter_upwards [earlier,after] with c pay release
  intro f K cf fk ck heat dist
  have mono:=WilsonStartup.Timing.hat_mono levels (Gauge.slopeConstant_pos simple).le
  have h0:0≤H c:=zero_le_one.trans (R.family.path.levels.fits.delayed c).le
  have dist':(S).a c/(S).a K≤(H K)^A:=
    dist.trans (pow_le_pow_left₀ h0 (mono (by omega:c≤K)) _)
  obtain ⟨B,b1,small,all⟩:=pay K ck heat dist'
  refine ⟨B,b1,release f cf ((mono fk).trans heat) B b1 small,?_⟩
  intro V _ _ v d b w z l ds bp fee pos spent cap geometry moves fW
  have rate:=WilsonMeasuredPublicEntranceTransferCopyRowSalary.original R simple ck d D A e T tp ds b w bp pos spent fee heat dist
  exact all v fW z l cap geometry (fun t=>(rate (v,t)).1) (fun t=>(rate (v,t)).2)
end YM.Integration.WilsonMeasuredPublicEntranceTransferCopyCourseFare
end
