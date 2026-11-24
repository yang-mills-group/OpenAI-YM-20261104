import YM.LocalLTE.XPre.Opal
import YM.LocalLTE.XPre.Runway
import YM.LocalLTE.XPane.Tops
/-! Calibration Reserve buys.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow ConnectedActivityE6 Push.AbsoluteSums LocalLTE.Vinca VoucherB
open Clock Next.Scheduling.Clock Progress.DirectedRecipe Pressure
open YM.LocalLTE LocalLTE.Fan
open Bandage.Harmonics Spiral
-- Campaign proof C.I terms per x.Price constants from post L_X.Refresh.
variable {G:Gauge}(d:ℕ)(p:Stage)
    (P Q l p0:ℕ) (L:Side) (e:ℝ)
set_option quotPrecheck false
local notation "lK"=> ((Labels.frames G).level d)
variable (q:Stage) (G)
noncomputable def burnT (x v:ℝ):ℝ:= Extra.Histories.Motion.orbitCost lK * (LocalLTE.River.rotationP lK p.order p.power * ((Bandage.Harmonics.payG G q p l d L).beam+2*(x+v+(v+v)))) -- y/v error relative.Credit(0,1)
noncomputable def shapeT (v:ℝ):ℝ:= Extra.Histories.Motion.orbitCost lK * ((Bandage.Harmonics.payG G q p l d L).grant +(Bandage.Harmonics.payG G q p l d L).canopy*(p.columns +(v+v)))
noncomputable def rateT (v:ℝ):ℝ:= Extra.Histories.Motion.orbitCost lK * (LocalLTE.River.rotationP lK p.order p.power*(2*(v+(v+v))))
-- weights bought upon Opportunity.Read.Earlier powers tem.
variable (K T:ℕ)
set_option quotPrecheck false
-- j.Tx runner cap w=1. y exponent from INPUT m+1. Y relative.
noncomputable def wound (X:ℝ):= X^ (-(2:ℝ))
-- $Cb payable, growth K stage.CSC. Additional Λ powers.
-- note local macros precedence.
noncomputable def NoDraw (x:ℝ): Prop := let X:= betaF G x L; let v:= X^(grantZ p0 T 0); let w:= X^(-(5:ℝ)); let a:=shapeT G d p l L q v; let t:=burnT G d p l L q X v; let z:= rateT G d p v;
    0 ≤ a ∧ 0 ≤ t ∧ 0 ≤ z ∧ 1≤ X ∧ w*a≤ X^Mallow.aust ∧ (((K:ℝ)*w*t) + X^e *((K:ℝ)*(2*w*(z+v))) ≤ wound X) ∧ (wound X+(Real.exp (wound X)-1) ≤ X^(-(1:ℝ))) ∧ ∀ β , betaF G x L/2≤β→ β ≤ 2*betaF G x L→ X^((5:ℝ)*K) *X^(-e) ≤ (Coat.gStep β)^((P:ℝ)+1)
-- limits: power conversion torque independent amplitude.Layout ζ. 
variable (hp:grantZ p0 T 0+e ≤ 0)(hQ:(5:ℝ)*K+ -e < -((P:ℝ)+1)/2)
include hp hQ
lemma cloudY : ∀ᶠ x:ℝ in atTop, NoDraw G d p P l p0 L e q K T x:=by
    let j:=Motion.orbitCost lK; have hj : 0 ≤ j:= zero_le_one.trans (Motion.orbitCost_one_le _)
    let k:=LocalLTE.River.rotationP lK p.order p.power; have hk:0 ≤k:= zero_le_one.trans (River.rotation_one ..)
    let S:=payG G q p l d L; have hs:0≤p.columns:=zero_le_one.trans p.columns_ge
    have hv : grantZ p0 T 0 ≤ 0:=by unfold grantZ; push_cast; linarith only [Nat.cast_nonneg (α:=ℝ) T, Nat.cast_nonneg (α:=ℝ) p0]
    let n:= grantZ p0 T 0; let R x:= (betaF G x L)^n
    let Kz x:= burnT G d p l L q (betaF G x L) (R x); let X x:= shapeT G d p l L q (R x); let Tz x:=j*(k*(2*(R x+(R x+R x))))
    let omegaV x:= (betaF G x L)^ (-(5:ℝ))
    have ha:Rate G L (grantZ p0 T 0) R:= Rate.power; have hh : Rate G L n fun x=> (R x+R x):= ha.add ha
    have hc:Rate G L 0 X:= (((Rate.const S.grant).add (((Rate.const p.columns).add ((ha.add ha).weaken hv)).mul_left _)).mul_left _) -- order. X binder macro confusion
    have hℓ:Rate G L n Tz:= (((ha.add hh).mul_left _).mul_left _).mul_left _
    have ht:Rate G L 1 Kz:= by
        have h : Rate G L 1 (fun x=> betaF G x L):=by simpa only [Real.rpow_one] using! (Rate.power (G:=G) (L:=L) (a:=1))
        exact (((((Rate.const S.beam).weaken (by norm_num)).add ((((h.add (ha.weaken (hv.trans zero_le_one))).add (hh.weaken (hv.trans zero_le_one))).mul_left 2))).mul_left _).mul_left _) -- count
    have homegaV:Rate G L (-5) omegaV:= Rate.power -- test numeral ℝ
    let v x:= omegaV x*X x
    let z' x:= ((K:ℝ)*omegaV x*Kz x)+(betaF G x L)^e*((K:ℝ)*(2*omegaV x*(Tz x+R x)))
    have ht' : Rate G L (-4) z':=by
        have h1:= (homegaV.mul_left (K:ℝ)).mul ht; rw [show (-(5:ℝ))+1=-4 by norm_num] at h1; have h2:Rate G L (e+ (-5+n)) (fun x=> (betaF G x L)^e*((K:ℝ)*(2*omegaV x*(Tz x+R x)))):= Rate.power.mul ((((homegaV.mul_left 2).mul (hℓ.add ha))).mul_left _)
        exact h1.add (h2.weaken (by unfold n; linarith only [hp]))
    have ht : ∀ᶠ x:ℝ in atTop, ∀ β, betaF G x L/2 ≤ β→ β≤2*betaF G x L →(betaF G x L)^((5:ℝ)*K+ -e) ≤ (Coat.gStep β)^((P:ℝ)+1):=by
       have hx:= Urns.actualG (G:=G) L ((P:ℝ)+1) (fun t=> (betaF G t L)^((5:ℝ)*K+ -e)) ( (5:ℝ)*K+ -e) Rate.power hQ
       exact hx -- order
    have hz:= (Work.E09.betaF_growth G L).eventually_ge_atTop (α:=ℝ) 4 -- arg ?
    filter_upwards [ht' _ (show (-(4:ℝ))< -2 by norm_num),(homegaV.mul hc) aust (by norm_num [aust]),ht,hz] with x hu hζ hv' he
    let X0:= betaF G x L; have hz:0<X0:= (show (0:ℝ)<4 by norm_num).trans_le he; let x0:=X0^(grantZ p0 T 0); have hx:0 ≤ x0:= Real.rpow_nonneg hz.le _; have hx':= add_nonneg hx hx
    have hβ:1 ≤ X0:= le_trans (show (1:ℝ)≤4 by norm_num) he
    refine ⟨mul_nonneg hj (add_nonneg S.pole (mul_nonneg S.crown (add_nonneg hs hx'))),mul_nonneg hj (mul_nonneg hk (add_nonneg S.future (mul_nonneg zero_le_two (add_nonneg (add_nonneg hz.le hx) hx')))),mul_nonneg hj (mul_nonneg hk (mul_nonneg zero_le_two (add_nonneg hx hx'))), hβ,(le_abs_self _).trans hζ,(le_abs_self _).trans hu,?_ ,fun β hh hc=>?_⟩
    · have hh0: wound X0+(Real.exp (wound X0)-1) ≤ 3*wound X0:= by
            have hh :0 ≤ wound X0:= Real.rpow_nonneg hz.le _; have ht: |wound X0| ≤ 1:= (abs_of_nonneg hh).trans_le (Real.rpow_le_one_of_one_le_of_nonpos hβ (by norm_num : (- (2:ℝ))≤0)); have hx :=(le_abs_self _).trans (Real.abs_exp_sub_one_le ht);rw [abs_of_nonneg hh] at hx; linarith only [hx]
      refine hh0.trans (?_); unfold wound; change 3*_≤ X0^(-(1:ℝ)); rw [Real.rpow_neg hz.le,Real.rpow_neg hz.le, Real.rpow_one, Real.rpow_two]; field_simp; nlinarith only [he,hz]
    change X0^((5:ℝ)*K)*X0^(-e) ≤ _; rw [← Real.rpow_add hz]; exact hv' β hh hc -- but nominal X0.
end YM.PhysicalNext.Repeat.Legato
