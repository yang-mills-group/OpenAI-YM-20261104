import YM.OPE.Compatible.Fiord.Duct
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
noncomputable abbrev ΓObv (i:I)(z:J i):= ArtY A P g i (WField A U D X Y i z)
local notation "X!"=> XTarg A X
local notation "C!"=> XTarg A (WField A U D X Y)
local notation "Gρ"=> ΓObv A U D g P X Y
include hp he hs hD
lemma ρSeek : Q! (XTarg A (WField A U D X Y)):= (ΩBound A U D hs hD X Y hp he).Rise _
include h in lemma lGeo : Butte μ φ (Counters β) (ΓObv A U D g P X Y):=by
       let G0:= Gρ; let T:= C!; rw[show Gρ=(fun i x=>ArtY A P g i (T i x)) from funext fun i=>funext fun x=> (EmBound A U g P i _).symm]; exact moneyArt h g P T A (GrowthV A U D hs hD X Y hp he) (ρSeek A U D hs hD X Y hp he).meat
-- Lips roots.Ph
lemma κGrowth : Grain μ φ ΓZ (fun i x=> ‖WField A U D (XTarg A X) Y i x‖) 0:=by
       let f:=WField A U D (X!) Y; let g:= XTarg A (WField A U D X Y); have ht: SkinQ n ΓZ μ φ f:= ΩBound A U D hs hD _ Y (hp.Rise X) he; let hU:Grain μ φ ΓZ (fun i x=>‖g i x-f i x‖) 0:= skirt A U D hs hD X Y hp he; apply (hU.add (GrowthV A U D hs hD X Y hp he) U.top.fair).of_le (ht.meat.mono fun i hi=> hi.norm.aestronglyMeasurable); filter_upwards with i; filter_upwards with x; let a:= f i x; let b:=g i x; change ‖‖a‖‖ ≤ ‖‖b-a‖+‖b‖‖; rw [norm_norm, Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),norm_sub_rev]; exact (congr_arg (fun (x:Bid.Dir G (n i))=>‖x‖) (sub_add_cancel a b).symm).trans_le (norm_add_le (a-b) b)
omit hp he hs hD [∀ i, IsProbabilityMeasure (μ i)][∀ i, MeasurableSpace (J i)] in
private lemma Houch (j:I)(v:J j)(s:Fin 3): let Q:=ArtY A P g j; let x:= XTarg A (WField A U D X Y) j v; let y:= WField A U D (XTarg A X) Y j v; let u:=1+(‖x‖+‖y‖)
       ‖(Q (WField A U D X Y j v)).seq s.val-(Q y).seq s.val‖≤ ‖Jfair (RedG G (νsize A j) u) (TorC A P g j)*DxT G (νsize A j) u*‖x-y‖‖:=by
       intro Q x y u; let z:=WField A U D X Y j v; have hz:Q z=Q x:=by with_reducible_and_instances exact (EmBound A U g P j z).symm
       have hp :1 ≤ u:=le_add_of_nonneg_right (add_nonneg (norm_nonneg x) (norm_nonneg y));have ht:‖x‖ ≤ u:= (le_add_of_nonneg_right (norm_nonneg y)).trans (le_add_of_nonneg_left zero_le_one); have hh:‖y‖≤u:= (le_add_of_nonneg_left (norm_nonneg x)).trans (le_add_of_nonneg_left zero_le_one); rw[show Q (WField A U D X Y j v)= Q x from hz,mul_assoc (Jfair ..) (DxT ..)]; exact (AmpG A P g j x y ht hh hp s).trans (Real.le_norm_self _)
include h
noncomputable def γHeight (i:I)(z:J i):= 1+(‖C! i z‖+‖WField A U D (XTarg A X) Y i z‖)
noncomputable def γSell (i:I)(z:J i):= Jfair (RedG G (νsize A i) (γHeight A U D X Y i z)) (TorC A P g i)*DxT G (νsize A i) (γHeight A U D X Y i z)*‖XTarg A (WField A U D X Y) i z - WField A U D (XTarg A X) Y i z‖
omit h in lemma heavyΩ : Grain μ φ ΓZ (γHeight A U D X Y) 0:=by
       have ht:=GrowthV A U D hs hD X Y hp he; let L:=U.top.fair; have hU:=ht.add (κGrowth A U D hs hD X Y hp he) L; unfold γHeight; with_reducible_and_instances exact (Grain.const (RateLE.const 1 L)).add hU L
lemma rent_Ω : Grain μ φ ΓZ (γSell A U D g P X Y) c:=by
       have hp:=((ΛPrice A h g P (γHeight A U D X Y) (heavyΩ A U D hs hD X Y hp he)).mul (skirt (c:=c) A U D hs hD X Y hp he)).mint (le_of_eq (zero_add _))
       unfold γSell; with_reducible_and_instances exact hp
lemma ΩPα : Pine μ φ ΓZ (Gρ-ΓObv A U D g P (XTarg A X) Y) c:=by
       have H:= rent_Ω A U D hs h hD g P X Y hp he (c:=c); have hX:= lGeo A U D hs h hD g P X Y hp he; have hY:= lGeo A U D hs h hD g P (XTarg A X) Y (hp.Rise X) he
       intro s; rw [pegComp]; refine H.of_le (((hX s).integral.1.and (hY s).integral.1).mono fun i hi=> (hi.1.sub hi.2).aestronglyMeasurable) ?_; filter_upwards with i; filter_upwards with v;
       let a:= Houch A U D g P X Y i v s; simp only [Pi.sub_apply,run_H,γSell,γHeight]; with_reducible_and_instances exact a
end
end YM.OPE.Owl.HillZ
