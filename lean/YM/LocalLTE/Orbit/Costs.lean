import YM.LocalLTE.Drift.Hutch
import YM.LocalLTE.Ticket.Millen
import YM.LocalLTE.Drift.Outlay
/-! Thresholds for arbitrary-history stage. Gain in L spent also on stance, EXACT numbers. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Spool
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open ConnectedActivityE6
open Mallow Daisy Charity Lotus
variable {G:Gauge}
open YM.LocalLTE.Dilation Push.AbsoluteSums
open LocalLTE LocalLTE.Ticket LocalLTE.River LocalLTE.Drift Extra.Histories
variable (X Y:RG.Stage) (l p r j K:ℕ) (L:Side) (e t:ℝ)
set_option quotPrecheck false
variable {S:Teller G} (Q:ConnectedActivityE6.Target G S) {μ a a':ℝ}
open Push Price
local notation "f'" x=> betaF G x L
local notation "R"=> rotationP ((Labels.frames G).level p) X.order X.power
local notation "P"=> ((Labels.frames G).level p)
local notation "F"=> Motion.orbitCost ((Labels.frames G).level p)
local notation "σ"=> (1/16:ℝ)
noncomputable def echoBit (j:ℕ):ℝ :=-(j:ℝ)/128
noncomputable def weightC (t:ℝ)(j:ℕ):ℝ:= t^(echoBit j)
lemma weight_rate : Rate G L (echoBit j) (fun x=> weightC (betaF G x L) j):= Rate.power
-- incoming budgets Reg.Path.KT approvals parameter. Lift purchases ratio jerk R*C.Post.
local notation "u"=> Y.columns
noncomputable def hoist (G:Gauge) :ℝ :=rotationP ((Labels.frames G).level p) X.order X.power* Motion.orbitCost ((Labels.frames G).level p)*Y.columns
variable (G)
lemma hoist0 :0 ≤ hoist X Y p G := mul_nonneg (mul_nonneg (zero_le_one.trans (rotation_one ..)) (zero_le_one.trans (Motion.orbitCost_one_le _))) (zero_le_one.trans Y.columns_ge)
structure OnRamp (G:Gauge)(L:Side) : Prop where
    basic: hoist X Y p G*debtR G X l p L *Y.columns ≤ (1/10:ℝ) -- opener after-L
    move: hoist X Y p G*debtR G X l p L ≤ 1/10
    forced: hoist X Y p G*debtK G X l p L ≤ 1/10
-- preblock. Note `p` arbitrary but fixed application.
local notation "hx"=>hoist X Y p G
local notation "dy"=> Push.Local.factor (hol G) (localSection G p) X.supportExponent (Cub.title G X)
local notation "si"=> (sill X.supportExponent l)
lemma acquired : ∃ v0:ℕ,∀ L:Side,v0≤L.val→OnRamp X Y l p G L:=by
   obtain ⟨v,hV⟩:=Doors.pre_tilt ((10:ℝ)*(hx*dy*si)*Y.columns) 1; obtain ⟨v',hv⟩:= Doors.pre_tilt ((10:ℝ)*hx*(1+si+dy*si)) 1
   refine ⟨v+v',fun L hL=>?_⟩
   have he:hx*debtR G X l p L *Y.columns ≤ (1/10:ℝ):=by
       have h:= (hV L (by omega)).1; unfold debtR; linarith only [show (Doors.rate L)*(10*(hx*dy*si)*Y.columns)≤1 from h] -- comm.
   refine ⟨he,(le_mul_of_one_le_right (mul_nonneg (hoist0 G X Y p) (debtR0 G X l p L)) Y.columns_ge).trans he,?_⟩
   have h:= (hv L (by omega)).1; unfold debtK; linarith only [show (Doors.rate L)*(10*hx*(1+si+dy*si))≤1 from h]
variable {G}
-- rates
lemma echo_antitone : Antitone echoBit:=by intro i j hj; unfold echoBit; linarith only [Nat.cast_le (α:=ℝ)|>.mpr hj]
lemma stepBit (j:ℕ): echoBit j - (1/16:ℝ) < echoBit (j+1):=by unfold echoBit; push_cast; linarith
lemma bitN (j:ℕ): echoBit j ≤ 0:=by unfold echoBit; linarith only [Nat.cast_nonneg (α:=ℝ) j]
lemma trancheR : Rate G L (- (1/16:ℝ)) (smallMeter X l p L G):=by unfold smallMeter; exact ((((Rate.power (a:=-(1/16:ℝ))).mul_left _).mul_left _).mul_left _)
section prices
variable (μ:ℝ)(hW: -(((r:ℝ)+1))/2 < echoBit K)(he:2-e < echoBit K)(hμ:0<μ)(hp:OnRamp X Y l p G L)
local notation "Tz" x β hβ => (outlay X Y l p r L e Q μ x β hβ)
local notation "suKe" x=> (weightC (betaF G x L))
lemma nextPay (F0 :ℝ→ℝ)(a d:ℝ)(hF:Rate G L a F0)(ht:a<d) (r:ℝ)(hv:0<r) : ∀ᶠ x in atTop, F0 x≤r*(betaF G x L)^d:=by
    filter_upwards [(hF.mul_left r⁻¹) d ht] with x hx'
    have hz:= (mul_le_mul_of_nonneg_left ((le_abs_self (r⁻¹*F0 x)).trans hx') hv.le); rwa [mul_inv_cancel_left₀ hv.ne'] at hz
variable {x:ℝ}
include he hp
lemma slipsPost (j:ℕ)(hj:j≤ K): ∀ᶠ x in atTop, ∀ β:ℝ, ∀ hβ:0< betaF G x L, hoist X Y p G*((outlay X Y l p r L e Q μ x β hβ).slip (Y.columns) (fun _=> betaF G x L) (weightC (betaF G x L)) (weightC (betaF G x L)) j) ≤ (3/10:ℝ)*weightC (betaF G x L) j:=by
    obtain _|j:=j
    · filter_upwards with x β hβ; unfold TariffX.slip; rw [weightC, echoBit]; simp only [Nat.cast_zero,neg_zero,zero_div,Real.rpow_zero,mul_one]
      change hx*(debtR G X l p L *u)≤_; rw [← mul_assoc]; exact hp.basic.trans (by norm_num)
    let m x:= dy * regularNet G X l p L e x; let g x:= smallMeter X l p L G x; let a:= echoBit (j+1)
    have h := nextPay L (G:=G) (fun x=> hx*(m x* betaF G x L)) _ a ((((regain G X l p L e).mul_left dy).mul Rate.hat).mul_left _) (by have h:= he.trans_le (echo_antitone hj); linarith only [h]) ((1:ℝ)/10) (by norm_num) -- order
    have hg:= nextPay L (G:=G) (fun x=> hx*(g x* weightC (betaF G x L) j)) _ a (((trancheR (G:=G) X l p L).mul (weight_rate j L)).mul_left _) (by have h:=stepBit j; unfold a; linarith only [h]) ((1:ℝ)/10) (by norm_num)
    filter_upwards [h,hg] with x ht hv β hβ
    let w:=weightC (betaF G x L) (j+1); have hs:0 ≤ w:= Real.rpow_nonneg hβ.le _; have h: hx*(debtR G X l p L*w)≤(1/10:ℝ)*w:=(mul_assoc ..|>.symm).trans_le (mul_le_mul_of_nonneg_right hp.move hs)
    change hx*(debtR G X l p L*w+ m x* betaF G x L+ g x* weightC (betaF G x L) j)≤ (3/10:ℝ)*w
    linarith only [h,show hx*(m x* betaF G x L)≤ (1/10:ℝ)*w from ht,show hx*(g x*weightC (betaF G x L) j)≤ (1/10:ℝ)*w from hv]
end prices
end YM.PhysicalNext.Repeat.Legato.Spool
