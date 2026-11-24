import YM.Gaps1020.Local.Brace
set_option autoImplicit false
noncomputable section
namespace YM.GapsLocal.Renew
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Time Rain Mallow Roost UVNext.CouplingReset Daisy.Charity.RG12
open YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open YM.ConnectedActivityE6.Blaze.Thermal1020
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
-- stage funding. demand (actual projection). Use one extra phase request
-- so receipt post stage fit includes all fees named on this path. No money
-- from Offer widths. Post κ currency still separate (one divisor at epoch).
-- Can present costlier post-hyp gates without rewriting the Thermal estimate
-- onto a weaker exponent, any B.Support in actual scene.
local notation "ST" S => Time.probe S
variable (L:Side)
open Blaze.Thermal1020
-- stage operand function for auxiliary budgets (no mask interpolation costs not shown)
def soul (k:ℕ)(S:RG.Stage)(w:ℝ):ℝ:= Trio.oroW (ST S) (Trio.base k (radiusB w)) (fun i=> 2*(Fintype.card (Site (fence k (radiusB w) i)):ℝ)*(Height.away S))
def mapC (k:ℕ)(S:RG.Stage)(w:ℝ) := Height.away S+Height.away S * (soul k S w * Real.exp (Trio.stout S * Trio.coverTicket k))
def billP (k:ℕ)(_S:RG.Stage)(w:ℝ) := ballCost (Meadow.studio k (radiusB w))
-- avoid let p parser unused parameter S for billP
lemma map0 (k:ℕ)(S:RG.Stage)(w:ℝ):0 ≤ mapC k S w:=by
   let t:= (Trio.base k (radiusB w)); let W:= ST S; have hp : 0 < Height.away S:= turnFee_pos W
   have h : 0 ≤ Trio.tilt W t:= by unfold Trio.tilt; positivity; -- parser
   have hv:0 ≤ soul k S w:= by unfold soul Trio.oroW; apply sum_nonneg; intro i _; exact mul_nonneg (abs_nonneg _) (mul_nonneg h (mul_nonneg (by positivity) hp.le))
   unfold mapC; positivity
lemma mapRate (k:ℕ) (S:RG.Stage): Rate G L 0 (mapC k S):=by
   have hx:= (Trio.rows G L k).2.2.1; let v:= ST S; have hp : Rate G L 0 (soul k S):= by
     refine Trio.sparks G L (f:=fun i t=> |Slide.ray i| * (Trio.tilt (ST S) (Trio.base k (radiusB t))* (2*(Fintype.card (Site (fence k (radiusB t) i)):ℝ)*(Height.away S)))) (fun i=>?_)
     have hu := ((Trio.feeStars G L k i).mul_left 2).mul_right (Height.away S)
     have hy : Rate G L 0 (fun t=> Trio.tilt (ST S) (Trio.base k (radiusB t))) := by
        exact (((Bolt.still (2^S.order:ℝ)).times (((Bolt.still 1).joins hx).nod (S.power*S.order))).uses)
     simpa only [zero_add] using! (hy.mul hu).mul_left |Slide.ray i|
   exact (Rate.const _).add ((hp.mul_right _).mul_left _)
structure SupplyP (G:Gauge)(L:Side)(k:ℕ)(S:RG.Stage)(s:ℝ):Prop where
    tally : mapC k S s+(billP k S s:ℝ)*Height.away S≤ horizonRadius G L s
    bought : Time.base G S*mapC k S s≤ horizonRadius G L s

def checkout (G:Gauge): Decal G := ⟨fun _ Q _ L _ _ _ S _ s=> SupplyP G L Q.halo S s, by
   intro P Q F; refine ⟨0,fun L h W μ O D i _ _ _ => ?_⟩; have he:= mapRate (G:=G) L Q.halo D; have ht:= (Trio.balls G L (Trio.rows G L Q.halo).1).mul_right (Height.away D)
   have hr : 0 < Thermal1020.ray:=by norm_num [Thermal1020.ray]
   filter_upwards [ (he.add ht) Thermal1020.ray hr, (he.mul_left (Time.base G D)) Thermal1020.ray hr] with x hx hz; exact ⟨(le_abs_self _).trans hx,(le_abs_self _).trans hz⟩ ⟩

variable {X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Factor A} {c f:Side} {m n N ℓ i k d M:ℕ}{l s:ℝ}
variable {Y: UVNext.CouplingReset.In A.B.a m n} (H: Spring R N m n l s Y)(x:Set.Icc l s)
local notation "i0" => A.B.a.clock.J (m+1)
local notation "j0" => A.B.a.clock.J m
local notation "O" => Chi.canonical
local notation "P₀"=> A.B.a.budget m
local notation "x₀"=> A.B.a.clock.hatBeta m
local notation "W"=> A.B.a.params m
local notation "HORIZON"=> A.B.a.clock.hatBeta (m+1)
local notation "L0"=> D.L i0
local notation "Z"=> Thermal1020.horizonRadius G L0 x₀
variable (h:m<N) (he: Mallow.RG12.Earned (Thermal1020.Shared.markerBudget G) R.shape A.delay) (hM:M ≤ A.B.a.clock.J (m+1))
local notation "Δ" => quota A m M
local notation "u" => (Z^(M+1))⁻¹
local notation "K"=> Rain.lint R.target A m
local notation "δ0"=> demand A K m Δ
local notation "pX"=>opening H.H
local notation "ψ"=> (billP K (A.B.a.params m) x₀:ℝ)

lemma bills {k : ℕ} :
     demand A k m Δ= mapC k W x₀ * u := by
   let T:= (P₀); let t:= Trio.base k (radiusB x₀); let v:= (turnFee T)
   have h : seatNeed A k m Δ= soul k W x₀ * u := by
     unfold seatNeed soul Trio.oroW; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _=>?_ ; have hh : Trio.tilt T t = Trio.tilt (ST W) t:= rfl; change _*(Trio.tilt T t*_)= _*(Trio.tilt _ t*_)*_; rw [← hh]; unfold quota; change _*(_*(_*(v*_)))=(_*(_*(_*v)))*_; ring
   unfold demand mapC; rw [h]; rw [show Trio.stout W=preExponent P₀ from rfl,show Height.away W= v from rfl]; change v*u+v*((_*u)*_)=_; ring
lemma βinv : (((A.B.a.budget m).threshold)^2)⁻¹ ≤ Z^3:=by
   let x:= x₀; let b:= HORIZON; have hx:0<x:= zero_lt_one.trans (A.B.a.fits.delayed _); have hb:1 ≤ b:=(A.B.a.fits.delayed _).le
   have h0 : (Real.sqrt x)⁻¹ ≤ (P₀).threshold := le_mul_of_one_le_right (by positivity) (Real.one_le_exp (sq_nonneg _))
   have hp:0 < (Real.sqrt x)⁻¹ := by positivity
   have ht:HORIZON=betaF G x L0:= Push.PriceCompiler.beta_eq A.B.valid m
   refine le_trans (inv_anti₀ (pow_pos hp 2) (pow_le_pow_left₀ hp.le h0 2)) ?_; rw [inv_pow, inv_inv,Real.sq_sqrt hx.le,horizonRadius]; have hh:x≤ b:= by unfold b; rw [ht]; exact le_add_of_nonneg_right (Work.E04.shift_nonneg ..)
   change x ≤ (betaF G x L0 ^ Thermal1020.ray)^ (3:ℕ); rw [← ht,← Real.rpow_mul_natCast (by change 0 ≤ b; linarith)]; exact hh.trans ((Real.rpow_one b).symm.trans_le (Real.rpow_le_rpow_of_exponent_le hb (by norm_num [Thermal1020.ray])))
local notation "p0"=> Time.base G (A.B.a.params m)
-- use extra 4 internal exponents for the stronger *bare* kinetic estimate
-- explicit constant fixed with d (no claim order-independent). Hands off χ
abbrev premium (d:ℕ):= Vacuum.targetM d+4
include h he hM H
set_option quotPrecheck false
local notation "b0"=> (Y x.val).beta
local notation "cost"=> (Real.sqrt 2 * Vacuum.nativeG b0)^(d+1)
local notation "Φ" y:max => Averaging.delta ((opening H.H).read y)
lemma bank (hC: Mallow.RG12.Earned (checkout G) R.shape A.delay)(hx:M=premium d):
    p0*δ0≤cost ∧ δ0+ψ*Δ≤cost ∧
    δ0 / (A.B.a.budget m).threshold^2 ≤ cost:=by
   obtain ⟨-,C,d',v,Y',a,b,r,B,q,k,N',hh⟩:= Vacuum.Markets.certified (R:=R) (houseS H x) h he M hM
   have hp: SupplyP G L0 K (X.p.profile j0) x₀:= hC i0 x₀ (A.B.valid.pays m) j0 (step_paid _ m); rw [← params_eq A.B.valid m] at hp
   have hZ:2 ≤ Z:= hh.large; have hc:1 ≤ Z:=by linarith
   have hT:M+1=2*(d+1)+4:=by unfold premium Vacuum.targetM at hx; omega
   let d':= 2*(d+1); let y := Z^(d':ℕ); have hy: Z^4 * u = y⁻¹ :=by rw [hT,pow_add,_root_.mul_inv_rev]; change Z^4*((Z^4)⁻¹*y⁻¹)=_; rw [←mul_assoc,mul_inv_cancel₀ (by positivity),one_mul]; -- name
   have hb:= (H.knows _ x.property).2
   have hz : y⁻¹≤ cost:= Vacuum.radiusBill b0 (by have he:= A.B.a.fits.delayed (m+1); linarith only [he,hb.1]) hb.2 (d+1)
   rw [bills]
   have hf: Z * u ≤ cost:=((mul_le_mul_of_nonneg_right (le_trans (le_of_eq (pow_one Z).symm) (pow_le_pow_right₀ hc (by norm_num))) (show 0 ≤ u from by positivity))).trans (hy.trans_le hz)
   constructor; swap; · constructor; swap
                        · rw [div_eq_mul_inv]; apply le_trans _ (hy.trans_le hz); have ht : 0≤ mapC K W x₀:= map0 ..
                          have h : mapC K W x₀ ≤ Z:= le_trans (le_add_of_nonneg_right (mul_nonneg (by positivity) (show 0≤Height.away W from (turnFee_pos P₀).le))) hp.tally
                          refine (mul_le_mul (mul_le_mul_of_nonneg_right h (by positivity)) βinv (by positivity [(A.B.a.budget m).threshold_pos]) (by positivity)).trans_eq ?_; ring
                        unfold quota; change mapC K W x₀ * u + ψ*(Height.away W*u)≤cost; rw [← mul_assoc, ← add_mul]; exact (mul_le_mul_of_nonneg_right hp.tally (by positivity)).trans hf
   rw [← mul_assoc]; exact (mul_le_mul_of_nonneg_right hp.bought (by positivity)).trans hf
end YM.GapsLocal.Renew
