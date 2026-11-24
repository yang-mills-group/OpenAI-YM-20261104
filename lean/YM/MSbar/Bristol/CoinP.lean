import YM.MSbar.Bristol.Ward
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bristol
open Function Filter Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film -- remove
variable {G:Gauge}{c f:Side} {S:StepData c f} (R:Rep G c)(U:Nesting G c)
open Measuring
local notation "W"=>Positions (Primary c G)
local notation "K"=>Primary c G
variable (v:G.ColorIndex){i j k p o s:ℕ}{r w c1 c2 c3 t A b a Y C D h':ℝ}
variable {g:ℝ → Config G c→ℝ}(hT:Trend g U R.path R.clip p)(h:Keeps U p (sun G v))
local notation "R₀"=> Aqua.vine R r
local notation "P'"=> tariff c p R.clip R.path U
local notation "P"=>film R U r p
local notation "T"=>Measuring.chart c G
local notation "Y'"=> buoy P 0
local notation "η"=>rim (collectT c R.path R.clip)
local notation "Y₀"=>Aqua.ore R U r p
variable {η' k₀ d:ℝ}(hP: ContDiffAt ℝ (↑k) (Aqua.vine R r) 0) (hh:Touch R.eval)
variable (he:0 < r)(hG:G.Simple)(ht:|stackH c (sun G v) (rim (film R U r p))|≤ t)(hx:6 ≤ s)(hp:4 ≤ k)(hb:0≤b)
variable (hV:∀ j≤3,JetTab (Measuring.chart c G) b s w ({0}:Set _) (film R U r p) j A)(hw:1≤ w)
include hT hP hh he hG ht hV hp hw hx hb
noncomputable def coal (p:ℕ) (b t:ℝ)(c:Side):=64*(t+100*tumbler c b)
lemma solid (x:Primary c G) : Conde (target x) (coal p (A/w^2) t c) 1 3 (fun l=>Y' (x::l)):=by
    have hv:0<w:=zero_lt_one.trans_le hw; have hR : Ribbon (rim P):=Aqua.booking hT hh hP hp hG he
    let f:=P; have he(v0 s')(hh:v0.length <3):= Lis.candles f (show ContDiffAt ℝ 2 P 0 from (hP.sub ((Aqua.pure R U r p).contDiffAt.of_le le_top)).of_le (by exact_mod_cast (show 2≤k from by omega))) hG v hR hb hx (fun i=> JetTab.count (hV 1 (by omega)) hv 0 (Set.mem_singleton _) i) x s' v0 hh -- adjust proof
    intro L S hh; have hx':= he L S hh; apply le_trans hx'; rw [Midpoint.cost,← Midpoint.close hR (sun G v)]; exact mul_le_mul_of_nonneg_left (add_le_add_left ht _) (by norm_num)
omit hG ht
noncomputable def toll (r w B Z Y:ℝ)(p m:ℕ)(G:Gauge) := 2*fCost B r w 0*solo m G*Z +∑ i∈ range (p+1),r^i*(2*fCost B r w (p-i)*solo m G*Y)
local notation "K!" m=> toll r 1 D A Y p m G
local notation "x!"=> (0:Positions K)
variable (hσ:∀ i≤p, Stone G i k h' D)(hg: r ≤1)(hY:∀ i≤ p, Tokew (Measuring.chart c G) b s 3 0 (PowerSeries.coeff i (tariff c p R.clip R.path U)) Y)
include hσ hg hY
lemma candle (x:Primary c G) (y:Strand G) (hz:j ≤2) : Yarn j (fun L:List K=> Lis.tide (x::L)*|buoy (Lis.deck P x y) 0 (x::L)|) ≤ toll r 1 D A Y p j G:=by
    have hx': 0<w:=zero_lt_one.trans_le hw
    have hK (i:ℕ)(hi:i≤p)(x:Primary c G)(l:ℕ)(hp:l≤j+1): Yarn l (fun L:List K=>|buoy (atlas U p i R.path R.clip) 0 (x::L)| * swipe T b s (x::L)) ≤ Y:= by
         let f:=PowerSeries.coeff i (tariff c p R.clip R.path U); change Yarn _ (fun L=>|buoy (clue f) _ _| * _ )≤ _; rw [CrossH.scored f x]; exact CrossH.token f|>.mp (hY _ hi)|>.2 _ (by omega) _
    have hR (x:Primary c G)(l:ℕ)(hp:l≤j+1): Yarn l (fun L:List K=> |buoy P 0 (x::L)| * swipe T b s (x::L))≤ A := (JetTab.count (hV l (by omega)) hx' 0 (Set.mem_singleton _) x).trans (div_le_self (hV l (by omega)|>.1) (one_le_pow₀ hw))
    have hP':0<h':= (hσ 0 (by omega)).1 -- check
    exact sense hT hh 0 hσ (fun i=>by rw [smul_zero,map_zero,Pi.zero_apply,norm_zero]; exact hP') hP he (fun i=>by rw [map_zero,Pi.zero_apply,norm_zero]; exact zero_le_one) le_rfl hg (by omega) rfl Y A hb hx x y hK hR
local notation "R!"=>(4*100^3/(c.val:ℝ)^3)
lemma slopeQ(x:Primary c G): Conde (target x) (R!* (A/w^3)+K! 1) 2 2 (fun l=>Y' (x::l)):=by
    apply Lis.slope (P) x k (hP.sub ((Aqua.pure R U r p).contDiffAt.of_le le_top)) hb hx (JetTab.count (hV 2 (by omega)) (zero_lt_one.trans_le hw) 0 (Set.mem_singleton _) x) (fun y=> candle R U hT hP hh he hx hp hb hV hw hσ hg hY x y (by omega)) (by omega) -- actual args
lemma angelQ(x:Primary c G): Conde (target x) (R!* (A/w^4)+K! 2) 3 1 (fun l=>Y' (x::l)):=by
    apply Lis.angel (P) x k (hP.sub ((Aqua.pure R U r p).contDiffAt.of_le le_top)) hb hx (JetTab.count (hV 3 (by omega)) (zero_lt_one.trans_le hw) 0 (Set.mem_singleton _) x) (fun y=> candle R U hT hP hh he hx hp hb hV hw hσ hg hY x y (by omega)) hp -- actual args
end YM.MSbar.Bristol
