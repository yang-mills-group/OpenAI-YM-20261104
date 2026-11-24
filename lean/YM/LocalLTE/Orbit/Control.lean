import YM.LocalLTE.Drift.Hutch
import YM.LocalLTE.Ticket.Millen
import YM.LocalLTE.Orbit.Costs
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
local notation "u"=> Y.columns
section prices
variable (μ:ℝ)(hW: -(((r:ℝ)+1))/2 < echoBit K)(he:2-e < echoBit K)(hμ:0<μ)(hp:OnRamp X Y l p G L)
local notation "Tz" x β hβ => (outlay X Y l p r L e Q μ x β hβ)
local notation "suKe" x=> (weightC (betaF G x L))

local notation "T#" => (outlay X Y l p r L e Q μ)
-- compare exact certified budgets.C renewals. 
structure Ride (t:ℝ) : Prop where
   receipt : 0< betaF G t L
   expenses(β x:ℝ)(_hβ:betaF G t L/2 ≤ β)(_hxB:β≤2* betaF G t L)(_hX:x≤1): let W:=weightC (betaF G t L); let s:= fun _:ℕ=> betaF G t L; let U:= (outlay X Y l p r L e Q μ t β receipt); (∀ j≤K,U.peak Y.columns s W W j* hoist X Y p G≤ t ∧ hoist X Y p G*U.delta Y.columns s W W (fun i=>x*(W i+W i)) j ≤ weightC t j) ∧ ∀ j,j<K→ hoist X Y p G*(U.slip Y.columns s W W (j+1)+U.slip Y.columns s W W j)≤weightC t j
-- local binder tk.H issues use hx.Price Always purchase r*µ post.
variable (hϵ :1 ≤ e)
include he hp hW hμ hϵ
lemma purchase : ∀ᶠ t in atTop,Ride X Y l p r K L e Q μ t:=by
    let Y' t:= betaF G t L; let w t:= weightC (Y' t); let C':= hoist X Y p G
    let I t:= projectionG X Y l p L e G t+ stalk Y p L G; let A t:= C'*I t; let O:= C'*debtR G X l p L* Y.columns; let a t:= C'*(rareX X l p L Q μ t* Y.columns)
    have hK:(echoBit K) ≤ 0:=bitN K
    have h : Rate G L (-1) (fun x=>A x*x⁻¹):=by
       have ht:= (expoCost X Y l p L e G hϵ).mul_left C'; simpa only [zero_add, Real.rpow_neg_one, Real.rpow_one] using! (ht.mul (Mallow.flagE L (-1:ℝ) (by norm_num)))
    have ha j(hj:j≤K):∀ᶠ x in atTop,a x≤weightC (betaF G x L) j*(1/10:ℝ):=by
       let b:= echoBit K-1
       have hp:Rate G L b a:= (((burst X l p L Q μ hμ b).mul_right _).mul_left C')
       filter_upwards [nextPay L a b (echoBit j) hp (lt_of_lt_of_le (by unfold b;linarith only) (echo_antitone hj)) _ (by norm_num: (0:ℝ)<1/10)] with x h
       exact h.trans_eq (mul_comm ..)
    have hs j(hj:j≤K):∀ᶠ x in atTop,C'*(powerR r (Y' x/2)) ≤ (1/10:ℝ)*w x j:= nextPay L (fun x=> C'*powerR r (Y' x/2)) _ (echoBit j) ((rateHalf r L G).mul_left _) (lt_of_lt_of_le hW (echo_antitone hj)) _ (by norm_num)
    have hc:0 ≤ C':=hoist0 ..
    filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop (2*(O+1)),h.below (by norm_num) ((1:ℝ)/2) (by norm_num),eventually_all.mpr fun i:Fin (K+1)=> (ha i.val (Nat.le_of_lt_succ i.isLt)).and ((hs i.val (Nat.le_of_lt_succ i.isLt)).and (slipsPost X Y l p r K L e Q μ he hp i.val (Nat.le_of_lt_succ i.isLt)))] with t ht' hz hT hP
    let W:= w t; let Yp:= Y' t; have hx': 0<t:= zero_lt_one.trans ht'; have ht: t ≤ Yp:= le_add_of_nonneg_right (Work.E04.shift_nonneg ..); have hv':0< Yp:=hx'.trans_le ht
    refine ⟨hv',?_⟩; intro β x hβ hp' hX U pJ Xt
    have hΨ j: W j ≤ weightC t j:= Real.rpow_le_rpow_of_nonpos hx' ht (bitN j)
    have hR : powerR r β ≤ powerR r (betaF G t L/2):= Real.rpow_le_rpow (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_anti₀ (Real.sqrt_pos.mpr (half_pos hv')) (Real.sqrt_le_sqrt hβ)) (by positivity : 0 ≤ (r:ℝ)+1)
    have he(j)(hj:j ≤ K): C'*(Xt.slip Y.columns pJ W W j) ≤(3/10:ℝ)*W j:= (hP ⟨j,Nat.lt_add_one_of_le hj⟩).2.2 _ hv'
    constructor
    · intro j hj; let Z:=Xt.slip Y.columns pJ W W j; have hu:W j ≤ 1:= Real.rpow_le_one_of_one_le_of_nonpos (ht'.le.trans ht) (bitN j)
      have He:C'*Z≤(3/10:ℝ)*W j:= he _ hj
      constructor
      · change (I t+(debtR G X l p L*Y.columns+Z))* C' ≤ t; have hf: C'*I t≤ t/2:=by
            let g:=A t*t⁻¹; have hp:g≤(1:ℝ)/2:=(le_abs_self _).trans hT; unfold g at hp; rw [←div_eq_mul_inv,div_le_iff₀ hx'] at hp; exact hp.trans_eq (by ring)
        unfold O at hz; linarith only [hz,hf,hu,He]
      apply le_trans _ (hΨ j)
      change C'*(powerR r β+(rareX X l p L Q μ t*Y.columns+Z)+debtK G X l p L*(x*(W j+W j)))≤ W j
      have Ht := hP ⟨j,Nat.lt_add_one_of_le hj⟩; have hΨ:0 ≤ W j:=Real.rpow_nonneg hv'.le _; have hz:C'*(debtK G X l p L)*(x*(W j+W j))≤(1/10:ℝ)*(W j+W j):=by
         exact (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (add_nonneg hΨ hΨ) hX) (mul_nonneg hc Xt.token.fFlag)).trans (mul_le_mul_of_nonneg_right hp.forced (add_nonneg hΨ hΨ))
      linarith only [show C'*powerR r β ≤ _ from (mul_le_mul_of_nonneg_left hR hc).trans (show _ ≤ (1/10:ℝ)*W j from Ht.2.1),show C'*(rareX X l p L Q μ t*Y.columns)≤ W j*(1/10) from Ht.1,hz,hΨ,He]
    intro j hj; apply le_trans _ (hΨ j); have hκ : W (j+1) ≤ W j:= Real.rpow_le_rpow_of_exponent_le (ht'.le.trans ht) (echo_antitone (Nat.le_succ _)); change C'*(Xt.slip Y.columns pJ W W _+Xt.slip Y.columns pJ W W _) ≤ W j; rw [mul_add]; exact (add_le_add (he (j+1) hj) (he j hj.le)).trans (by linarith only [hκ, show 0 ≤ W j from Real.rpow_nonneg hv'.le _])
end prices
end YM.PhysicalNext.Repeat.Legato.Spool
