import YM.OPE.Compatible.Fiord.Sheaf
/-!
# Marginal plans. True relative density jets, *before* normalization
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
variable (A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x))(U: Scaffold φ (Counters β) n (Mnd i S A) r)
variable (D:I→ Law (Merchant.Chamber G r))(hs:G.Simple)
open Merchant.SiteL
variable (h:Tendsto β φ atTop)(hD: GaugeD A U D)
open Cinders Metric Set Zeph Jargon Crown PertExtension Flock Stranded
variable {N:ChartRatio G} {s c R:ℝ} (H:StackP N s c R)(hN:LocalRatio N)
variable (x:∀ i,Bid.Dir G (n i)) (g:ℂ→L[ℝ]ℝ) (P:Pad G)
open ScriptJ
local notation "TC"=> Merchant.Chamber G r
section
variable {J:I→Type}[∀ i, MeasurableSpace (J i)]{μ:∀ i,Measure (J i)}[∀ i, IsProbabilityMeasure (μ i)]
variable (X:(i:I)→J i→Bid.Dir G (n i))(Y:(i:I)→J i→ Merchant.Chamber G r)
open Merchant.Sleeve.Scaffold
local notation "qK"=> KPole A
local notation "qL"=> LPole A
local notation "ΓZ"=> Counters β
local notation "V!"=> Punched A U
local notation "Q!"=> SkinQ n ΓZ μ φ
local notation "A!"=> SkyQ r ΓZ μ φ
variable (hp:SkinQ n (Counters β) μ φ X)(he: SkyQ r (Counters β) μ φ 0 Y)
noncomputable def ZKick (j:I)(z:J j):= FelT A U D j (X j z) (Y j z)
omit [∀ i, IsProbabilityMeasure (μ i)][∀ i, MeasurableSpace (J i)] in
lemma ζLift (j:I)(z:J j): ZKick A U D (XTarg A X) Y j z= ZKick A U D X Y j z+ (VPhi A U D X j z):=by
       unfold ZKick FelT; let a:= WPush A U D X j z; let t:= WPush A U D (XTarg A X) j z; let f:=PinT (n:=n j) (r:=r) G; let v:=VPhi A U D X j z; let P:=Cpit G n (Mnd i S A) j; have He:=ΦRho A U D X j z; have he:t= P a+ Stair A U j v:=(by with_reducible_and_instances exact He); have ht:f (P a)=f a:= Sill_pin (Punched A U j) a (broader A U j)
       have hu:f (Stair A U j v)=v:=by with_reducible_and_instances exact ave G (Punched A U j) v
       have hh:Y j z+f t=Y j z + f a + v:=by rw[he,map_add,hu,ht, add_assoc]
       unfold t a WPush Sleeve.Coach at hh; with_reducible_and_instances exact hh
omit [∀ i, IsProbabilityMeasure (μ i)] [∀ i, MeasurableSpace (J i)] in
private lemma kick_sum : ZKick A U D X Y = Y + (fun i z => PinT G (WPush A U D X i z)) := by
  funext i z
  simp only [ZKick, FelT, WPush, Sleeve.Coach, mixT, Stair, Pi.add_apply]
include hp he hs hD
local notation "Z!"=> Grain μ φ ΓZ
private lemma Kings : A! 0 (ZKick A U D X Y):=by
       rw [kick_sum]
       exact he.spend (αPin U (GainW A U D hs hD X hp)) U.top.fair
noncomputable def Iris (N:ChartRatio G)(i:I)(z:J i):= jet (feeX N) 2 (ZKick A U D X Y i z)
open Variance
lemma rillV (N:ChartRatio G) : Z! (Iris A U D X Y N) 0:=by
       have hp:= Kings A U D hs hD X Y hp he; exact InkD _ _ U.top.fair hp.aug (tallJ 2 (feeX N (F:=↥(fieldP r))) 0) hp.leg
lemma glibly (N:ChartRatio G) : Z! (fun i z=> Iris A U D X Y N i z-Iris A U D (XTarg A X) Y N i z) c:=by
       let x':=XTarg A X; have ht:= Kings A U D hs hD X Y hp he; have hv:= Kings A U D hs hD x' Y (hp.Rise X) he; have hz:= HaltV (c:=c) A U D hs hD X hp; apply DiffIK (jet (feeX N) 2) _ _ U.top.fair ht.aug (tallJ 2 (feeX N) 0) ht.leg hv.aug hv.leg -- explicit order
       apply hz.leg.shift; filter_upwards with i; funext v; unfold x'; rw[ζLift A U D X Y i v,norm_sub_rev,add_sub_cancel_left]
include h
noncomputable def FogO (P:ChartRatio G)(i:I)(z:J i):= Fob A U D P i (X i z) (Y i z)
lemma recept (P:ChartRatio G): Butte μ φ (Counters β) (FogO A U D X Y P):=by
       obtain ⟨ht,hv⟩:=saleQ A U D hs h hD X Y hp he; intro i; let v:=U.top.fair; fin_cases i;· exact Grain.const (RateLE.const 1 v)
       · exact ht
       apply ((hv.add (rillV A U D hs hD X Y hp he P) v).add ((((ht.pow v 2).mul (Grain.const (μ:=μ) (RateLE.const (1/2:ℝ) v)))).mint (by norm_num)) v).shift; filter_upwards with i; funext x; change _+_=( ((Flex A U D X Y i x).h+Iris A U D X Y P i x)+(Flex A U D X Y i x).l^2/2); ring
lemma Resp (P:ChartRatio G)(hc:c≤0): ∀ j:Fin 3,Z! (run_H (FogO A U D X Y P-FogO A U D (XTarg A X) Y P) j.val) c:=by
       obtain ⟨ht,hv⟩:=κFlip A U D hs h hD X Y hp he hc; intro j; let v:=U.top.fair; let f(i:I)(z:J i):=(Flex A U D X Y i z).l; let g(i:I)(z:J i):=(Flex A U D (XTarg A X) Y i z).l; have hb: Z! (fun i z=> f i z+g i z) 0:=(saleQ A U D hs h hD X Y hp he).1.add (saleQ A U D hs h hD (XTarg A X) Y (hp.Rise X) he).1 v; have hg:= ((ht.mul hb).mul (Grain.const (μ:=μ) (RateLE.const (1/2:ℝ) v))).mint (show _ ≤ c by simp); fin_cases j; · apply (Grain.const (μ:=μ) (p:=0) (RateLE.zero φ ΓZ c)).shift; filter_upwards with i; funext x; exact (sub_self (1:ℝ)).symm
       · exact ht
       apply (((hv.add (glibly (c:=c) A U D hs hD X Y hp he P) v)).add hg v).shift; filter_upwards with i; funext x; change _+_= ( ((Flex A U D X Y i x).h+Iris A U D X Y P i x)+f i x^2/2) - (((Flex A U D (XTarg A X) Y i x).h+Iris A U D (XTarg A X) Y P i x)+g i x^2/2); unfold f g;ring
end
end YM.OPE.Owl.HillZ
