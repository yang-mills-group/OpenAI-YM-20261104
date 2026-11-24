import YM.LocalLTE.Ticket.Beast
/-! ## Relative earned revenues. Full transport to finite windows from ANY top. Orders bought with construction PER Ω lengths (unlimited periods). Simply cannot claim decay of shorter charts for arbitrarily many epochs here! ARTS depth may change each.Period-indicators. -/
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
open LocalLTE LocalLTE.Ticket LocalLTE.River Extra.Histories
variable (X Y:RG.Stage) (l p r m j:ℕ) (L:Side) (e:ℝ) {β v a w t:ℝ}
local notation "K"=> Push.Local.factor (hol G) (localSection G p) X.supportExponent (Cub.title G X)
set_option quotPrecheck false
-- η parameter as Real exponents.V → pre radius.Rem.Raw begins.Aroma.
variable {S:Teller G} (Q:ConnectedActivityE6.Target G S) (μ a a':ℝ)
open Push Price
local notation "f" x=> betaF G x L
local notation "R"=> rotationP ((Labels.frames G).level p) X.order X.power
local notation "P"=> ((Labels.frames G).level p)
local notation "Fl"=> Motion.orbitCost ((Labels.frames G).level p)
-- compare.Fl.Stencil transfer.Shift buys
local notation "ISS" x β hβ => Legato.Spool.budgetV X Y l p r L e Q μ x β hβ
structure Resale (t:ℝ) : Prop where
    paid:0 < betaF G t L
    unit: 1 ≤ t
    fits (β v:ℝ)(hβ: betaF G t L/2≤β)(hp:β≤2* betaF G t L)(hv:v≤1):let X' := Legato.Spool.budgetV X Y l p r L e Q μ t β paid; let a₁ := X'.first Y.columns (betaF G t L) ((betaF G t L)^a); let c:=X'.second Y.columns (betaF G t L) ((betaF G t L)^a) v
       ( (rotationP ((Labels.frames G).level p) X.order X.power*a₁)*Fl)*Y.columns ≤ t∧ ( (rotationP ((Labels.frames G).level p) X.order X.power*c)*Fl)*Y.columns ≤ t^a'
lemma rateHalf (G:Gauge) : Rate G L (-( (r:ℝ)+1)/2) (fun x=> powerR r (betaF G x L/2)):=by
   let s:= (r:ℝ)+1
   refine Rate.congr ((Rate.power (G:=G) (L:=L) (a:=-s/2)).mul_left ((2:ℝ)^(s/2))) ?_
   filter_upwards [Delay.shift_pos G L] with x hx
   set t:= betaF G x L
   change ((Real.sqrt (t/2))⁻¹)^s= _; rw [Real.sqrt_eq_rpow,← Real.rpow_neg (half_pos hx).le,← Real.rpow_mul (half_pos hx).le,Real.div_rpow hx.le zero_le_two]
   rw [show (- (1/2:ℝ) * s)= -s/2 by ring, show -s/2=-(s/2) by ring, Real.rpow_neg hx.le, Real.rpow_neg zero_le_two, div_inv_eq_mul]
   -- RHS need changes b= .
   rw [mul_comm]
lemma expoCost (G:Gauge) (h:1 ≤ e) : Rate G L 0 (fun x=> projectionG X Y l p L e G x+ stalk Y p L G):=by
    let H:= sill X.supportExponent l; let q:= Legato.ticR G Y; let C:= cl0 Y p L
    let Z:= regularNet G X l p L e; have he (x): denP G Y X l p L e x=Z x * q:=by unfold denP Z regularNet q; ring
    unfold projectionG; simp_rw [he]; exact (((Rate.const (H*C)).add ((((regain G X l p L e).mul_right q).weaken (by linarith)))).mul_left _).add (Rate.const _)
variable (ha:a ≤ 0)(hv: a < a')(he: a' ≤ 0)(hs:-(((r:ℝ)+1))/2 ≤ a)(hμ:0<μ)(hx:2-e ≤ a)
include ha hv he hμ hx hs
lemma green : ∀ᶠ x in atTop, Resale X Y l p r L e Q μ a a' x:=by
   let inn x:= (betaF G x L)^a; let r1:=K; let ra:= R; let b:=Fl; let y:=Y.columns
   let O:= debtR G X l p L; let M x:= r1*regularNet G X l p L e x
   let f' x:= O*Y.columns+ M x*(betaF G x L)+ O*inn x; let v x:=ra*((projectionG X Y l p L e G x+ stalk Y p L G)+f' x)*b*y
   have hi: Rate G L a inn := Rate.power
   have hm: Rate G L a (fun x=> M x*(betaF G x L)):= (((regain G X l p L e).mul_left r1).mul Rate.hat).weaken (by linarith only [hx])
   have hR: Rate G L 0 v:= (((expoCost X Y l p L e G (by linarith only [hx,ha])).add (((Rate.const _).add (hm.weaken ha)).add ((hi.mul_left _).weaken ha))).mul_left ra|>.mul_right b).mul_right _ -- edit `projection` vars implicit
   let q x:=powerR r (betaF G x L/2)+(rareX X l p L Q μ x *y+ M x* betaF G x L+ O*inn x)+ (debtK G X l p L)*(inn x+inn x); let t x:=ra*q x*b*y
   have ht: Rate G L a t:=by
       have hk:= ((rateHalf r L G).weaken hs).add ((((burst X l p L Q μ hμ a).mul_right y).add hm).add (hi.mul_left O))
       exact (((hk.add ((hi.add hi).mul_left (debtK G X l p L))).mul_left ra).mul_right b).mul_right y
   -- v ≤ Cost; v/x Rate -1.
   have hv' : Rate G L (-1) (fun x:ℝ=>v x*x⁻¹):=by simpa only [zero_add, Real.rpow_neg_one, Real.rpow_one] using! (hR.mul (Mallow.flagE L (-1:ℝ) (by norm_num)))
   filter_upwards [eventually_gt_atTop (1:ℝ), (hv'.below (by norm_num)) 1 zero_lt_one,ht a' hv] with x hx' hw hx
   have hu: 0 < x:=zero_lt_one.trans hx'
   have hβ' :x≤betaF G x L:=le_add_of_nonneg_right (Work.E04.shift_nonneg ..)
   have hp:= hu.trans_le hβ'; refine ⟨hp,hx'.le,?_⟩
   intro β υ hβ hh hz C A B'
   have hπ : powerR r β≤powerR r (betaF G x L/2):= Real.rpow_le_rpow (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_anti₀ (Real.sqrt_pos.mpr (half_pos hp)) (Real.sqrt_le_sqrt hβ)) (by positivity : 0 ≤ (r:ℝ)+1)
   constructor
   · change v x≤x; rw [← div_eq_mul_inv] at hw; exact (div_le_one hu).1 ((le_abs_self _).trans hw)
   refine le_trans (b:=t x) ?_ (((le_abs_self _).trans hx).trans (Real.rpow_le_rpow_of_nonpos hu hβ' he))
   have h:0 ≤ inn x:= Real.rpow_nonneg hp.le _
   apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans Y.columns_ge); apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans (Motion.orbitCost_one_le _)); apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (River.rotation_one X.order X.power))
   apply add_le_add (add_le_add hπ le_rfl)
   exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (add_nonneg h h) hz) (C.fFlag)
end YM.PhysicalNext.Repeat.Legato.Spool
