import YM.OPE.Compatible.Fiord.Reap
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
variable (X:(i:I)→J i→Bid.Dir G (n i))(Y Y':(i:I)→J i→ Merchant.Chamber G r)
open Merchant.Sleeve.Scaffold
local notation "qK"=> KPole A
local notation "qL"=> LPole A
local notation "ΓZ"=> Counters β
local notation "V!"=> Punched A U
noncomputable def WPush:= Coach (KPole A) (Punched A U) X D
noncomputable abbrev XTarg:= HopPI n (Mnd i S A) X
noncomputable abbrev WField (i:I)(w:J i):= Kho A U D i (X i w) (Y i w)
noncomputable abbrev VPhi:=(Chair (KPole A) (Punched A U) X D)-Chair (KPole A) (Punched A U) (XTarg A X) D
local notation "x_0"=> XTarg A X
local notation "W0"=> WPush A U D X
local notation "WK"=> WPush A U D (x_0)
lemma WFul (j:I)(x:Bid.Dir G (n j))(y:TC) : Kho A U D j x y=mixT A U D j x+Stair A U j y:=rfl -- warns instances
omit [∀ i, IsProbabilityMeasure (μ i)][∀ i,MeasurableSpace (J i)]
lemma ΦRho (j:I)(z:J j): WPush A U D (XTarg A X) j z= XTarg A (W0) j z + Stair A U j (VPhi A U D X j z):=by
       unfold VPhi WPush XTarg; have he:= marchD U (V!) X D (KPole A) j z; unfold TCoach fallS CDelta at he; with_reducible_and_instances exact he
lemma villageT (j:I)(z:J j): WField A U D (XTarg A X) Y j z= XTarg A (WField A U D X Y) j z+Stair A U j (VPhi A U D X j z):=by
       let f:= Stair A U j; let p:= Cpit G n (Mnd i S A) j; let a:=VPhi A U D X j z; let x:=W0 j z; let t:=WK j z; let y:=Y j z
       have hh:r+1≤Mnd i S A j+1:=(U.top.room j).wide
       have Hp:p (f y)=f y:=by with_reducible_and_instances exact Sill_sail (Punched A U j) y hh
       have hh:=ΦRho A U D X j z; have ht:t=p x + f a:=by with_reducible_and_instances exact hh
       unfold WField; rw [WFul]; let H : t+f y=p (x+f y)+f a:=by rw[ht,map_add,Hp,add_right_comm]
       unfold t x WPush Sleeve.Coach at H; unfold XTarg HopPI; dsimp only[]; rw [WFul]; unfold XTarg HopPI at H; with_reducible_and_instances exact H
end
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
include hs
lemma holdZ: Shor U (KPole A) (ShadowP i S A U):= hEra (VesselP i S A) hs U (capB A) _
include h in lemma holdL: Shor U (LPole A) (ShadowL i S A U):= lEra (VesselP i S A) hs U (mUses A h) _
variable (hp:SkinQ n (Counters β) μ φ X)(he: SkyQ r (Counters β) μ φ 0 Y)
include hp hD
lemma GainW : SkinQ n (Counters β) μ φ (WPush A U D X):= TourP U (KPole A) _ (holdZ A U hs) (V!) X hp D hD.obey (Fractage S r) hD.rate
lemma HaltV : SkyQ r (Counters β) μ φ c (VPhi A U D X):=TourDiff U (KPole A) _ (holdZ A U hs) (V!) X hp D hD.obey (Fractage S r) hD.rate
include he
lemma ΩBound: SkinQ n (Counters β) μ φ (WField A U D X Y):=by
       have ht:= he.turns (V!) _; have hU:=SkinQ.roos _ (GainW A U D hs hD X hp) ht U.top.fair; have he: WField A U D X Y=WPush A U D X+fallS (Punched A U) Y:=by funext i z; unfold WField WPush Sleeve.Coach; rw [WFul]; simp only [Pi.add_apply,fallS]
       rw [he]; exact hU
include U
lemma GrowthV : Grain μ φ (Counters β) (fun i x=> ‖XTarg A (WField A U D X Y) i x‖) 0:= bodyS U _ (ΩBound A U D hs hD X Y hp he)
omit hp he hD hs [∀ i, IsProbabilityMeasure (μ i)][∀ i,MeasurableSpace (J i)] in
private lemma ΓSkirt (j:I)(x:J j): ‖XTarg A (WField A U D X Y) j x-WField A U D (XTarg A X) Y j x‖ ≤ ‖VPhi A U D X j x‖:=by
       let P:=VPhi A U D X j x; rw [villageT A U D X Y j x,norm_sub_rev,add_sub_cancel_left]; with_reducible_and_instances exact money_s G (Punched A U j) P
lemma skirt: Grain μ φ (Counters β) (fun i x=>‖XTarg A (WField A U D X Y) i x-WField A U D (XTarg A X) Y i x‖) c:=by
       let S:=WField A U D (XTarg A X) Y; let T:=XTarg A (WField A U D X Y); have ht: Q! T:= (ΩBound A U D hs hD X Y hp he).Rise _; have hs: Q! S:= ΩBound A U D hs hD _ Y (hp.Rise X) he
       have he:= HaltV A U D (by assumption) hD X hp (c:=c); refine he.leg.of_le ?_ (Eventually.of_forall fun i=> Eventually.of_forall fun x=>?_)
       · refine (ht.meat.and hs.meat).mono fun i hi=>?_ ; exact (hi.1.sub hi.2).norm.aestronglyMeasurable
       rw[norm_norm,norm_norm]; exact ΓSkirt A U D X Y i x
end
end YM.OPE.Owl.HillZ
