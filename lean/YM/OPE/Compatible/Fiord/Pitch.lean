import YM.OPE.Compatible.Fiord.Pwal
import YM.OPE.Compatible.Fiord.Rein
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
local notation "X!"=> Bx (r:=r) X
local notation "Y!"=> By G J r
local notation "μ_p"=> RentRa D μ
local notation "xK"=> XTarg A X
variable (hp:SkinQ n (Counters β) μ φ X)
local notation "G!"=>Butte (μ_p) φ (Counters β)
-- Annual eligibility.L along Ω_censor
noncomputable abbrev SnapL (N:ChartRatio G)(i:I)(z:J i × Merchant.Chamber G r):= StoryF A U D N P g i (Bx X i z) (By G J r i z)
noncomputable def ΦMean (N:ChartRatio G)(j:I)(x:J j) := ∫ y, aftD (SnapL A U D g P X N) (et A) j (x,y) ∂ShoreP D j
include h hs hD hp
-- μ brace growth cost.Op.Mark. -- hN Req for same mark projections even if unused
lemma SnapG: Butte (RentRa D μ) φ (Counters β) (SnapL A U D g P X N):=by
       let q:=ΓObv A U D g P (X!) (Y!); have he:=lGeo A U D hs h hD g P (X!) (Y!) (Sender D X hp) (TailZ A U D h hD μ); exact gluing (HeatΩ A U D hs h hD (N:=N) X hp) he (carth h)
lemma SnapQ (hc:c≤0): Pine (RentRa D μ) φ (Counters β) (SnapL A U D g P X N-SnapL A U D g P (XTarg A X) N) c:=by
        let q:=ΓObv A U D g P (X!) (Y!); let p:=ΓObv A U D g P (XTarg A X!) (Y!) -- X!
        let x':= XTarg A X; let K:= ΩReal A U D x' N; have hg:= ΩPα (c:=c) A U D hs h hD g P (X!) (Y!) (Sender D X hp) (TailZ A U D h hD μ); have he: Pine μ_p φ ΓZ p 0:= lGeo A U D hs h hD g P (XTarg A X!) (Y!) ((Sender D X hp).Rise _) (TailZ A U D h hD μ); have hz:= PineC U.top.fair (PhaseΛ A U D hs h hD (N:=N) X hp hc) (HeatΩ A U D hs h hD (N:=N) X hp) hg he
        let V:= ΩReal A U D X N; have hV: SnapL A U D g P X N=V*q:=rfl; have hK: SnapL A U D g P x' N=K*p:=by
             funext i x; unfold K p SnapL ΩReal StoryF Bx x' XTarg By HopPI; with_reducible_and_instances simp only [Pi.mul_apply, ΓObv,WField]
        rw[hV, show SnapL A U D g P (XTarg A X) N= _ from hK]; with_reducible_and_instances exact hz
local notation "A✅"=> SnapG A U D hs h hD g P hp
lemma atSnap : Grain (RentRa D μ) φ (Counters β) (aftD (SnapL A U D g P X N) (et A)) 0 := (beaconP (carth h) _ _ (SnapG A U D hs h hD (N:=N) g P X hp) ((poleV A h).mono (by norm_num)))
local notation "GΦ"=> Grain μ φ (Counters β)
lemma Demand : GΦ (ΦMean A U D g P X N) 0:=(atSnap A U D hs h hD (N:=N) g P X hp).ault _
lemma perT (hc:c ≤ 0): Grain μ φ (Counters β) (ΦMean A U D g P X N-ΦMean A U D g P (XTarg A X) N) c:=by
       let a:= Demand A U D hs h hD (N:=N) g P X hp; let p:=xK; have hr:SkinQ n ΓZ μ φ p:= hp.Rise X; let b:= Demand A U D hs h hD (N:=N) g P p hr; let v:= aftD (SnapL A U D g P X N) (et A); let f:=aftD (SnapL A U D g P p N) (et A); have hK:= (BeaconΔ U.top.fair _ _ (et A) (SnapQ A U D hs h hD (N:=N) g P X hp hc) ((poleV A h).mono (by norm_num))); apply (hK.ault (v-f)).of_le ((a.integral.1.and b.integral.1).mono fun i hi=> (hi.1.sub hi.2).aestronglyMeasurable); filter_upwards[(atSnap A U D hs h hD (N:=N) g P X hp).integral.1, (atSnap A U D hs h hD (N:=N) g P p hr).integral.1] with i hi hx; filter_upwards[hi.prod_right_ae,hx.prod_right_ae] with x hv hh; change ‖(∫ y,v i (x,y) ∂ShoreP D i)-(∫ y, f i (x,y) ∂ShoreP D i)‖ ≤ ‖(∫ y, v i (x,y)-f i (x,y) ∂ ShoreP D i)‖; rw [integral_sub hv hh] -- no goals
end
end YM.OPE.Owl.HillZ
