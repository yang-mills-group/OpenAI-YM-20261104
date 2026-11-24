import YM.AllOrder.Carillon.Vault
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Carillon
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L₀ : Side} {k j m π : ℕ} {K : Teller G} {p a W U V : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T: Tube G S} {R : RG.Rep G f} {H : Cash W p a L₀ X o U T R}
local notation "Θ" => (Match.staple (H:=H) (J:=H) rfl rfl rfl)
/- Price arithmetic: preserve grade through k=order/3 floors. Bills α<9/8.L scaling.B sizes.K weights with Phi & Tire.Turn.Pieces. -/
namespace Cap
open Fare Trio Slide Boulevard Shop Burn High Height Tilt Floe
open Rosary.Repair Sienna
variable (G)(b L:Side)(t:ℝ)(S:Stage)(ε:ℝ)(k g:ℕ)
local notation "Y"=>betaF G t L -- fine hat
local notation "V"=> radiusB t
local notation "P"=> PostP.θ1 G S t k
local notation "D"=> (Meadow.studio g V)
local notation "Q"=> Trio.base g V
abbrev pen (G:Gauge)(L:Side)(k:ℕ)(t:ℝ)(e:ℝ):ℝ:= (betaF G t L) ^ (Burn.credit k-1/80+e)
local notation "m0"=> Burn.credit k-1/80
local notation "M"=>pen G L k t
local notation "Ζ"=> M 0
def fee1 := Y ^ (-(7/16:ℝ))
def lump := away S * (6*fee1 G L t) -- enough for old & β×4.Any.All sizes update.
def tail := away S*(Ζ+Ζ)+Ζ
-- tune to 1/4 constants. Need eta positive.S disp δ supports and projections etc.
def field := M (1/400)
def tab (i:Stars):ℝ:=Boulevard.ticket S.order (field G L t k)+2*((Fintype.card (Site (Trio.fence g (V) i)):ℝ)*tail G L t S k)
def guard_fee (B:BudgetPoint) :ℝ:= oroW B Q (tab G L t S k g)
-- add symbol
lemma shop_tier (x:Stars): Rate G L (m0+(1/400:ℝ)) (fun t:ℝ=> tab G L t S k g x) :=by
 have he: Rate G L (Burn.credit k-1/80+1/400) (fun t=>field G L t k):= Rate.power; let v:=(m0+(1/400:ℝ)); let S' : Rate G L v (fun t=> pen G L k t 0) := Rate.weaken Rate.power (by unfold v; linarith); -- prices ν
 have hh:= ((S'.add S').mul_left (away S)).add S'
 refine (Rate.add ((he.mul_left _).mul_right ((1+ (1+1):ℝ)^S.order)) (((Trio.feeStars G L g x|>.mul hh).weaken (by rw [zero_add])).mul_left _)); -- holes
lemma funds : Rate G L (m0+1/400:ℝ) (fun t=> guard_fee G L t S k g (Time.probe S)):= by
 let hb := (Trio.rows G L g).2.2.1; unfold guard_fee Trio.oroW; apply Trio.sparks G L (f:=fun i t=>|Slide.ray i| * _); intro x; simpa only [zero_add] using! ((((Lantern.Bolt.still ((2:ℝ)^S.order)).times (((Lantern.Bolt.still 1).joins hb).nod (S.power*S.order))).uses.mul (shop_tier G L S k g x)).mul_left |Slide.ray x|)
-- Util Marketing.Cost. Soft & hard.
def micro := (Animals.ballCost D:ℝ)*lump G L t S+fee1 G L t -- model needs ≤ fee1. all Healthy in hull.
def stem := micro G L t S g+(micro G L t S g)+ ∑ i:Stars, |Slide.ray i| *((Fintype.card (Site (Trio.fence g (V) i)):ℝ)*(micro G L t S g+micro G L t S g))
lemma priceH :Rate G L (-(7/16:ℝ)) (fun t:ℝ=>stem G L t S g):= by
 have he: Rate G L (-(7/16)) (fun t=>fee1 G L t):= Rate.power; let hp:= ((Trio.balls G L (Trio.rows G L g|>.1)).mul (he.mul_left 6|>.mul_left (away S))).weaken (by simp : (0:ℝ)+ -(7/16:ℝ) ≤ -(7/16:ℝ)); have hz:Rate G L (-(7/16)) (fun t=>micro G L t S g):= hp.add he; unfold stem; let ht:= hz.add hz; exact Rate.add ht (Trio.sparks G L (f:=fun x t=>|Slide.ray x| * _) fun x=> (by simpa only [zero_add] using! (((Trio.feeStars G L g x).mul ht).mul_left |Slide.ray x|)))
local notation "Y1"=>Time.probe S
-- true requirements. preExponent for hats. support losses interplay. θ1/δ j-side. $μ$ positive post.HF.
def footprint (B:BudgetPoint) := (guard_fee G L t S k g B)*Real.exp (preExponent B*Trio.coverTicket g)
def authentic := away S*((Ζ+2*(heap G S (1/16)*young Y k))+Ζ)+Ζ
structure HorizonW (B:BudgetPoint):Prop where
 middle : authentic G L t S k+turnFee B*(footprint G L t S k g B)≤ PostP.θ1 G S t k
 curtain : Marlin.tithe (2*(Trio.base g (radiusB t))) (stem G L t S g) B (coverTicket g) ≤ betaF G t L ^ (-(1/8:ℝ))
-- guard fee at horizon κ.L.Bounds.
lemma foyer (a:BudgetPoint)(h:Time.Same S a): turnFee a * footprint G L t S k g a= turnFee (Time.probe S)* footprint G L t S k g (Time.probe S) := by
 unfold footprint preExponent turnFee guard_fee Trio.oroW Trio.tilt Time.probe; -- dsimp only; rw [...]
 dsimp; rw [h.1,h.2.1,h.2.2]
lemma constr : ∀ᶠ t:ℝ in atTop,∀ a:BudgetPoint,Time.Same S a → HorizonW G L t S k g a:= by
 let W:= (Trio.balls G L (Trio.rows G L g|>.2.2.2)).mul (priceH G L S g)|>.mul_right (Real.exp ((S.supportExponent+1+1)*coverTicket g));
 let T:=Burn.credit k; let J:=(m0+(1/400:ℝ)); let p:=Time.credit G S; have hp: 0<p:=Time.credit_pos ..; let u x:=turnFee Y1* footprint G L x S k g Y1; let f'(x:ℝ):=pen G L k x 0; have he: Rate G L J f':= Rate.weaken Rate.power (by unfold J; linarith); let hv:=funds G L S k g; have ht: Rate G L J u:=((hv.mul_right _).mul_left _); let hE:= (((he.add he).mul_left (away S)).add he).add ht; let e:=T; filter_upwards [(hE.mul_left (2/p)) e (by unfold J e T; linarith),eventually_gt_atTop (0:ℝ), W _ (by norm_num : (0:ℝ) + -(7/16:ℝ) < -(1/8:ℝ))] with t hk ht hv a ha
 have hx:t ≤(betaF G t L):=le_add_of_nonneg_right (Work.E04.shift_nonneg ..); have hz : 0<(betaF G t L):=ht.trans_le hx; have hw:=Real.rpow_le_rpow_of_nonpos ht hx (by linarith only [PostP.earns k] : Burn.credit k≤0); have hZ : 0< (betaF G t L) ^ T:= Real.rpow_pos_of_pos hz _; have hc:turnFee a=away S:= congr_arg₂ Push.Local.turnCost ha.2.1 ha.1; have hQ:0< away S:=hc ▸ turnFee_pos a; refine ⟨?_,?_⟩
 · rw [foyer G L t S k g a ha]; unfold authentic; have hT : away S*heap G S (1/16)=p/16:=by unfold Height.heap; field_simp; rfl
   let x':= away S; let u':=heap G S (1/16); let v':=p* (betaF G t L)^T
   have hx: (2/p)*(x'*((pen G L k t 0)+(pen G L k t 0))+(pen G L k t 0)+u t)≤ (betaF G t L)^T:= (le_abs_self _).trans hk
   change x'*(((pen G L k t 0)+2*(u'*(betaF G t L)^T))+(pen G L k t 0))+(pen G L k t 0)+u t≤ p*t^T; have he':2*(x'*((pen G L k t 0)+(pen G L k t 0))+(pen G L k t 0)+u t) ≤ v' := by
       apply le_of_mul_le_mul_left (a:=p⁻¹) ?_ (inv_pos.mpr hp); unfold v'; rw [inv_mul_cancel_left₀ hp.ne']; rw [← mul_assoc, mul_comm (p⁻¹), ← div_eq_mul_inv]; exact hx
   have hv:x'*u'=p/16:=hT; nlinarith only [mul_pos hp hZ, he', show p* (betaF G t L)^T ≤ p*t^T from (mul_le_mul_of_nonneg_left hw hp.le),show v'=p*(betaF G t L)^T from rfl, (show x'*u'*((betaF G t L)^T:ℝ)=p/16*(betaF G t L)^T from congr_arg (·*_ ) hv)]
 unfold Marlin.tithe; rw [ha.2.2]; exact (le_abs_self _).trans hv
end Cap
end YM.AllOrder.Carillon
