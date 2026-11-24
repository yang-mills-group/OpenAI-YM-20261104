import YM.MSbar.Fiber.Erode
import YM.MergeProof.North.Freckles

/-! Part A probe: Explicit same stage and shape; can require threshold dominance
at delay **after** Fixing L. Payload replacement before warm. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple)
namespace Bandage
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) (Y:Bolt A)
open YM.MergeProof
local notation "H"=> Issue.trail Y
open MergeProof Accent Menu
variable {K':ℕ→ℕ→ℕ}{μ:ℕ→ℕ→ℕ}
local notation "T0"=>Issue.trail Y
local notation "P0"=> A.B.a
local notation "P!"=> A.B.a.clock
set_option quotPrecheck false
variable {j n m:ℕ}(hm:m<n)
local notation "iY"=> (P!).J m
local notation "iX"=> (P!).J (m+1)
local notation "L"=> P.L iX
local notation "x0"=> (P!).hatBeta m
local notation "x1"=> (P!).hatBeta (m+1)
local notation "K0"=> (P0).budget m
local notation "K1"=> (P0).budget (m+1)

local notation "F'"=> hol G

open YM.MSbar.Bulk
section gates
variable {pT : Pressure.Teller G}
open ConnectedActivityE6 Push.AbsoluteSums Pressure
lemma winter (Ξ:ConnectedActivityE6.Target G pT)(Lb:Side)(μ:ℝ)(hp:0<μ) : ∀ᶠ x in atTop,(Ξ.goal Lb x)⁻¹ * Real.exp (-(Ξ.mark Lb μ x)) ≤ Real.exp (-(Push.AbsoluteSums.Delay.fineMonitor G Lb x)):=by
   let d:=μ/8; have hD:0<d:=by unfold d; positivity
   let M:=Push.AbsoluteSums.Delay.fineMonitor G Lb; let a x:=(betaF G x Lb)^Ξ.rate
   let u (x:ℝ):=Real.exp (-d*M x^2)
   have hx: Rate G Lb (Ξ.rate-1) u:=by simpa only [Real.rpow_two] using Rate.monitor_cutoff (a:=Ξ.rate-1) (G:=G) («L»:=Lb) hD (show 0<(2:ℝ) by norm_num)
   have hm : Tendsto M atTop atTop:= Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (by omega:2≠0)).comp (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (Work.E09.betaF_growth G Lb))))
   filter_upwards [hx Ξ.rate (by linarith),hm.eventually_gt_atTop d⁻¹,Delay.shift_pos G Lb] with x hh hs he
   have hv : u x≤a x:= (le_abs_self _).trans hh; have ht:0<a x:= Real.rpow_pos_of_pos he _; have hf:M x≤ d*M x^2:=by
     have hh:1 ≤ d*M x:=by apply le_trans (b:=d*d⁻¹) ?_ (mul_le_mul_of_nonneg_left hs.le hD.le); rw [mul_inv_cancel₀ hD.ne']
     have he := mul_le_mul_of_nonneg_right hh (show 0≤M x from (Real.exp_pos _).le); linarith
   have hl : Ξ.mark Lb μ x=2*(d*M x^2) := by
     change μ/2*(1/2)*(M x)^2= _; unfold d; ring
   rw [hl,show -(2*(d*M x^2))=-d*M x^2 + -d*M x^2 by ring,Real.exp_add,← mul_assoc]; refine le_trans ?_ (Real.exp_monotone (show -d*M x^2 ≤ -(M x) by linarith only [hf]))
   let y:= u x; have hz:(a x)⁻¹*y ≤1:= (mul_le_mul_of_nonneg_left hv (inv_pos.mpr ht).le).trans (le_of_eq (inv_mul_cancel₀ ht.ne')); exact mul_le_of_le_one_left (Real.exp_pos _).le hz
end gates
include hm b
lemma inSpring (h : Nest X Y) {D:GaugeDoor ((Issue.trail Y).rep n j (m+1)) ((Issue.trail Y).rep n j m)}
    (hi:Climbs X Y n m j D) :
    let Q:=X.target iX iY; let f:= (Q.goal L x0)⁻¹*Real.exp (-(Q.mark L (X.shape.μ iX iY) x0))
    Psalm ((P!).op m j) ((Issue.trail Y).rep n j (m+1)) ((P!).threshold m) f:=by
   obtain ⟨l,v,Q,U,x,he,hx,rfl⟩:=hi; intro d F; rw [hx]; exact Many.atSpring hm U x b.r
end Bandage
end YM.PhysicalNext.Repeat.Legato
