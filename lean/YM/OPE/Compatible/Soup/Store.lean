import YM.OPE.Compatible.Soup.Adept
/-!
# Epoch growth. Limited trajectory tape. variance observables without spectral cost loss
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.OPE.Owl.HillZ
open Function Filter MeasureTheory Lattice Laurent Wilson Matrix RG Gauge Precision
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ENNReal ContDiff
open Eyrie Push Push.AbsoluteSums Push.Mark Cascade Flume Flume.Page Flume.Script Pilot Finset
open Silt Libra Coin Rill Silt.Float Votive PertExtension Series GaussianScore Radial Next.Foundations
open Merchant Merchant.Aloof Merchant.Sleeve Merchant.SiteL
open Next.Free Next.Scheduling Stroke Spells Lass Lass.Zest Pill CardinalQ
variable {I:Type}{φ:Filter I}{G:Gauge} {K:Sponsor G}{T:Seasons K}
variable {β:I→ℝ}{n:I→Side}{S:Stage}{i j d r k:ℕ}{τ s a B:ℝ}
variable {A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x)}{U: Scaffold φ (Counters β) n (Mnd i S A) r}
variable (D:I→ Law (Merchant.Chamber G r))(hs:G.Simple)
open Merchant.SiteL
variable (h:Tendsto β φ atTop)(hD: GaugeD A U D)
open Cinders Metric Set Zeph Jargon Crown PertExtension Flock
variable {N:ChartRatio G} {s c R:ℝ} (H:StackP N s c R)(hN:LocalRatio N)
variable (x:∀ i,Bid.Dir G (n i)) (g:ℂ→L[ℝ]ℝ) (P:Pad G)
variable {D} (hp:Lyd A φ x)
include hp h hs hD
local notation "E*"=>Merchant.Chamber G r
set_option quotPrecheck false
local notation "Uμ"=> ShoreP D
local notation "Q★"=> Grain (ShoreP D) φ (Counters β)
local notation "M(L)"=> liftedM A U D x
lemma curtain_R : Q★ (fun i y=>‖liftedM A U D x i y‖) 0∧ (∀ᶠ i in φ, Measurable (liftedM A U D x i))∧ ∀ᶠ i in φ, ∀ y, SerT (liftedM A U D x i y) (WorkB A i):=by
        have he:=Lyn hs h hD x hp; let q:= D_Grain (D:=D) hD h; have hx:∀ i, Measurable (liftedM A U D x i):=fun i=>measurable_const.add (Stair A U i).measurable; refine ⟨Grain.of_le ((Grain.const (μ:=Uμ) (waitG h he.brim)).add q (carth h)) ?_ ?_,Eventually.of_forall hx,?_⟩
        · exact Eventually.of_forall fun i=> (hx i).norm.aestronglyMeasurable
        · apply Eventually.of_forall fun i=> Eventually.of_forall fun y=> (norm_norm _).trans_le ((norm_add_le ..).trans ((add_le_add le_rfl (money_s G (Punched A U i) y)).trans (Real.le_norm_self _)))
        exact he.habit.mono fun i hi y=> SerT.plus hi ((sparse_s G _ y).raise (broader A U i))
lemma noteG : Butte (ShoreP D) φ (Counters β) (fun i y=> ArtY A P g i (M(L) i y)):=by
       obtain ⟨he,hp,hx⟩:=curtain_R hs h hD x hp; exact moneyArt h g P _ A he hp
lemma jarV : Q★ (TJar A U D x) 0:=by
       let f:= M(L); let Y:= cEye A U D x; obtain ⟨he,hp',ht⟩:=curtain_R hs h hD x hp; have hu:= rope_φ hs h _ (Lyn hs h hD x hp); have hy(k:ℕ)(hx:1≤ k)(hT:k ≤ 3): Q★ (fun i y=> -(1:ℝ)*jet (KPole A i) (k+2) (f i y)) 0:=((Grain.const (RateLE.const (-1) (carth h))).mul (πp (A:=A) (k:=k+2) hs h f he hp' ht (by omega) (Nat.add_le_add_right hT 2)).1).mint (by simp)
       have hQ: Q★ (fun i y=> -jet (KPole A i) 3 (f i y)-jet (LPole A i) 1 (f i y)) 0:=by
            refine ((hy 1 (by omega) (by omega)).sub (πp (A:=A) (k:=1) hs h f he hp' ht (le_refl 1) (by omega)).2 (carth h)).shift (Eventually.of_forall fun i=>funext fun y=>by simp)
       exact hQ.sub (Grain.const hu.1) (carth h)
include H hN
lemma jarJ: Q★ (TJjr A U D x N) 0:=by
       let f:=M(L); let Y:= cEye A U D x; let v(j:I)(p:E*):=p+PinT (r:=r) G (Y j); have he:=Lyn hs h hD x hp; have hc:=OddsFee A _ he; have hv: Receipt β φ (fun i=> ‖PinT (r:=r) G (Y i)‖):=hc.liftp (Eventually.of_forall fun i=> le_of_eq (norm_norm _)); have hz:= D_Grain (D:=D) hD h; have hV: Q★ (fun i y=>‖v i y‖) 0:=Grain.of_le (hz.add (Grain.const (μ:=Uμ) (waitG h hv)) (carth h)) (Eventually.of_forall fun i=> (show Continuous (fun y=> ‖v i y‖) from (continuous_id.add continuous_const).norm).aestronglyMeasurable) (Eventually.of_forall fun i=> Eventually.of_forall fun y=> (norm_norm _).trans_le ((norm_add_le ..).trans (Real.le_norm_self _)))
       let g(c:ℝ):= Grain.const (μ:=Uμ) (RateLE.const c (carth h)); let a:=carth h; have ht: Q★ (fun i y=> jet (feeX N) 2 (v i y)) 0:= Grain.of_le (((g (Fintype.card (fieldP r))).mul ((g R).mul (hV.pow a 2))).mint (by norm_num)) (Eventually.of_forall fun i=> ((Raucous.Host.jetSun _ _).comp (continuous_id.add continuous_const)).aestronglyMeasurable) (Eventually.of_forall fun i=> Eventually.of_forall fun y=> (feeCapital hN H (v i y) (show 2 ≤ 3 by decide)).trans (Real.le_norm_self _)); obtain ⟨hU,hp,hx⟩:=curtain_R hs h hD x hp; have hQ := rope_φ hs h _ he; let K(k:ℕ):= πp (A:=A) (k:=k) hs h f hU hp hx
       have hZ: Q★ (fun i x=> -(jet (KPole A i) 4 (f i x))) 0 := by
             have H : Q★ (fun i x=> (-1:ℝ)*jet (KPole A i) 4 (f i x)) 0:= ((g (-1)).mul (K 4 (show 0<4 by omega) (by omega)).1).mint (by simp); exact H.shift (Eventually.of_forall fun i=>funext fun y=>by simp)
       exact ((hZ.sub (K 2 (show 0<2 by decide) (by decide)).2 a).sub (Grain.const hQ.2) a).add ht a
lemma Kpeak:Butte (ShoreP D) φ (Counters β) (Tact A U D x N):=by
       have hP:= jarV hs h hD x hp; intro i; fin_cases i
       · exact Grain.const (RateLE.const (1:ℝ) (carth h))
       · exact hP
       have he : Q★ (fun i x₀=> ((TJar A U D x i x₀)^2)*(2:ℝ)⁻¹) 0:= ((hP.pow (carth h) 2).mul (Grain.const (μ:=Uμ) (RateLE.const _ (carth h)))).mint (by norm_num); apply ((jarJ hs h hD H hN x hp).add he (carth h)).shift; filter_upwards with i; ext1 y; exact congr_arg (TJjr A U D x N i y+ ·) (div_eq_mul_inv ..).symm
lemma greetK : Butte (ShoreP D) φ (Counters β) (Glaco A U D N P x g):= gluing (noteG hs h hD x g P hp) (Kpeak hs h hD H hN x hp) (carth h)
end YM.OPE.Owl.HillZ
