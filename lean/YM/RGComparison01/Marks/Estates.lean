import YM.RGComparison01.Marks.Stereo
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Pledge
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter Mixed Reserves
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider Gas Ursell Trees Height Sail
open PhysicalNext.Repeat.Lotus Team Merge
open AnalyticBridge VerifiedReset Collection Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {ι : Type} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : RG.Rep G f}
    {n : ℕ} {W a r σ Λ μ s κ w c' C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
    {d C' A B e δ t D D' v K :ℝ} {j k ℓ:ℕ} {χ:Chi}
    {Ψ : ℕ → Prop} {x:ℕ→ℝ}
namespace Estates
open Foreman Checks Baked Palette Pillow Resin Season Ink Heron Switch Mallow Ovens OmitClusters Song Refrain Motion Luggage Oceanic Extra.Iteration
open Push.PriceCompiler Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03 ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter PhysicalNext PhysicalNext.Repeat Deck Stellar Mint Greenbelt Boulevard Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Divides Input Org Supply PriceCompiler Next.Scheduling Progress.DirectedRecipe Time Opera Slide
open Hoboken Stowe SliceRows Push.Uniform Sienna Fare Lapis
variable (G:Gauge)(K : Teller G) (Q:ConnectedActivityE6.Target G K)
-- Upper soft tariff per-root shift.O.Support.
def softFee (Z:ℕ)(x v d:ℝ):=(ballCost Z:ℝ)*x*Real.exp (v*d)
lemma uplift (v d:ℝ) (z:ℝ→ℕ) (p :ℝ→ℝ)(hp:Geo G L p) (hz:Geo G L (fun i=>(z i:ℝ))): Geo G L (fun i=> softFee (z i) (p i) v d):= ((Geo.balling hz).times hp).times (Geo.fixed _)
-- Prices_Pack
variable (L : Side) (P : ℝ→ℝ) (a δ : ℝ)
local notation "b0"=> betaF G
local notation "Z0"=> (fun s=>Q.mark L μ s)
-- qE motion.Name ω
abbrev shield (Q:ConnectedActivityE6.Target G K) (L:Side) (μ s:ℝ):=3/4*Q.mark L μ s -- G K param cleanup
abbrev cashK (Q:ConnectedActivityE6.Target G K) (L:Side) (μ s:ℝ) := Real.exp (- shield G K Q L μ s)
local notation "Hk"=> shield G K Q L μ
-- C.Cost.Cap.
variable (Z : ℝ→ℕ)
lemma office (h:Geo G L (fun s=>(Z s:ℝ))) (hp:Geo G L P) (hμ:0<μ) : ∃ Y:ℝ→ℝ, Geo G L Y ∧ (∀ x,1 ≤ Y x) ∧ ∀ᶠ x in atTop,
    let u:=Real.exp (-Q.mark L μ x); let w:= betaF G x L^(-(1/8 : ℝ)); let W:= softFee (Z x) ((Y x)⁻¹* |P x|) a δ
    Payments.Rates (radiusB x) (Real.exp (- (Hk x))) u (w + W) (Hk x) := by
   let k s:= Hk s
   let c x:=(↑(radiusB x + radiusB x+1:ℕ):ℝ)^4
   have hv x:1≤ c x:= one_le_pow₀ (Nat.one_le_cast.mpr (by omega))
   have hV:Geo G L c:= Geo.power (((Geo.radii.joins Geo.radii).joins (Geo.fixed 1)).compact ?_) _ -- fails
   swap; · filter_upwards with t; push_cast; rfl
   let Ψ x:=betaF G x L^(-(1/8:ℝ))
   let h x:= softFee (Z x) |P x| a δ
   have hh:= uplift G a δ Z (fun s=> |P s|) hp.mean ‹_›; have hH x:0 ≤ h x:= by unfold h softFee; positivity
   obtain ⟨Ω,Y,hΩ,hY,he⟩:= Foreman.reduces (hV.times hh) (1/16) (by norm_num)
   let Y' x:= 1+|Y x|; have hk' s:1 ≤ Y' s:=le_add_of_nonneg_right (abs_nonneg _)
   have hP := (hV.rate.mul (Rate.power (a:=-(1/8:ℝ)))).below (by norm_num) (1/16) (by norm_num)
   let X s:=k s +(-(Q.mark L μ s)); let F s:=Real.exp (X s)
   have hF:Rate G L (-1) F:= by
      have hz s: F s= Real.exp ((-(μ/16))*Delay.fineMonitor G L s^(2:ℝ)) := by
        unfold F X k shield; apply congr_arg Real.exp; rw [Real.rpow_two];
        change 3/4*(μ/2*(1/2)*Delay.fineMonitor G L s^2)+(-(μ/2*(1/2)*Delay.fineMonitor G L s^2))=_; ring
      rw [funext hz]; exact Rate.monitor_cutoff (by positivity) zero_lt_two
   refine ⟨Y',(Geo.fixed _).joins hY.mean,hk',?_⟩
   filter_upwards [hP,(hV.rate.mul hF).below (by norm_num) (1/4) (by norm_num),(Work.E09.betaF_growth G L).eventually_gt_atTop 0] with x hx hy h0 u w W
   have hp₀ : 0 < k x:= by
      change 0<3/4*(μ/2*(1/2)*Delay.fineMonitor G L x^2); exact mul_pos (by norm_num) (mul_pos (by positivity : 0 < μ/2*(1/2)) (pow_pos (Delay.monitor_pos ..) _))
   have hT := (le_abs_self _).trans hx; change c x*w ≤ 1/16 at hT; have hE:= he x
   have hu' : W ≤ Ω x*h x:= by
       have hQ : W = (Y' x)⁻¹*h x:= by unfold W softFee h; unfold softFee; ring -- fix
       rw [hQ]; apply mul_le_mul_of_nonneg_right _ (hH x); apply (inv_le_comm₀ (zero_lt_one.trans_le (hk' x)) (he x|>.1)).mpr
         (show (Ω x)⁻¹ ≤ Y' x from (hE.2.1 ▸ (le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)))
   have hB:c x*W ≤ 1/16:= (mul_le_mul_of_nonneg_left hu' (zero_le_one.trans (hv x))).trans (le_trans (le_of_eq (show c x*(Ω x*h x)=c x*h x*Ω x by ring)) ((mul_le_mul_of_nonneg_right (le_abs_self _) (hE.1.le)).trans (he x|>.2.2)))
   have hj:0≤ W:=by unfold W softFee; have H:= hk' x; positivity
   have hn:0 ≤ w:= (Real.rpow_pos_of_pos h0 _).le
   let D:=Payments.inflation u (w+W) (k x); have he : D= F x+ 2*(w+W):= by unfold D Payments.inflation F; rw [show u= _ from rfl,← Real.exp_add]
   have hD:0 ≤ D:=by rw [he]; unfold F; positivity
   have hz:c x*D ≤ (1:ℝ)/2 := by rw [he]; have hk: c x*F x ≤ 1/4 := (le_abs_self _).trans hy; linarith
   have hv':D ≤ 1/2:= le_trans (le_mul_of_one_le_left hD (hv x)) hz
   have h': (Real.exp D-1) ≤ 1:= by
      have hF:=Real.abs_exp_sub_one_le (x:=D) (show |D| ≤ 1 from (abs_of_nonneg hD)|>.trans_le (hv'.trans (by norm_num : (1:ℝ)/2 ≤ 1))) -- arg name
      rw [abs_of_nonneg hD] at hF
      linarith only [hv', hF, le_abs_self (Real.exp D-1)]
   refine ⟨hp₀.le,(Real.exp_pos _).le,add_nonneg hn hj,?_ ,hz.trans (by norm_num),mul_le_of_le_one_right (Real.exp_pos _).le h'⟩
   linarith only [le_trans (le_mul_of_one_le_left hn (hv x)) hT, le_trans (le_mul_of_one_le_left hj (hv x)) hB]
end Estates
end YM.RGComparison01.Pledge
