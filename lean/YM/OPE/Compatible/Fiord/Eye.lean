import YM.OPE.Compatible.Fiord.Pitch
import YM.OPE.Compatible.Camo.Hilt
import YM.OPE.Compatible.Fiord.Rein
/-!
# Estimates for chamber means before normalization

`SchedR` restricts to samples with `Roster (X i x) ≤ p i`. `VisionCost` controls
the transformed field on this set. Under the field estimates and the bound on the
measure of its complement, `χResp` bounds the transformed chamber mean for `Deb < a`.
`SelectorK` gives the corresponding estimate for the original field when also `a ≤ 0`.
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
-- Restrict the sample set to the indicated bound on the exterior field.
noncomputable def SchedR (p:I→ℝ)(i:I):Set (J i):= {x| Roster (X i x)≤p i}
section
variable {q:I→ℝ}(hq: Receipt β φ q)
include h
include hq in
omit [∀ i, IsProbabilityMeasure (μ i)][∀ i,MeasurableSpace (J i)] in
lemma VisionCost (V:(i:I)→ J i)(he:∀ᶠ i in φ,V i∈ SchedR X q i): Lyd A φ (fun i=>XTarg A X i (V i)):=by
        have hp:= (YM.OPE.Score.steady (1:ℝ) (carth h)).plus (MintW A h) (carth h); refine ⟨Eventually.of_forall fun i=>sillB _ (WorkB A i),(hp.product hq).under ?_⟩; filter_upwards [he] with i hi; rw[norm_norm]; apply le_trans (Sill_price (X i (V i)) _); exact mul_le_mul_of_nonneg_left hi (by positivity : (0:ℝ) ≤ 1+↑(WorkB A i))
variable (V:(i:I)→ J i)
include H hN hD hs
omit [∀ i,IsProbabilityMeasure (μ i)][∀ i,MeasurableSpace (J i)] in
lemma tub (hp:Lyd A φ (fun i=> X i (V i))): Wax β φ (fun i=> ΦMean A U D g P X N i (V i)) Deb:=by
        let x(i):= X i (V i); let he:= PeakPin hs h hD H hN x g P hp; apply he.congr; filter_upwards with i; unfold ΦMean; rw[←HuskK]; rfl 
variable [∀ i,Nonempty (J i)]
variable (hv:∀ᶠ i in φ,(SchedR X q i).Nonempty)(hV:Wick β φ (fun i=>(μ i).real (SchedR X q i)ᶜ))
include hv hV hp hq
lemma χResp (ha:Deb < a): Grain μ φ (Counters β) (ΦMean A U D g P (XTarg A X) N) a:=by
       have hT:=Demand A U D hs h hD (N:=N) g P (XTarg A X) (hp.Rise X); apply Borealis.Galea.recoverP (carth h) ?_ hV ?_ hT; swap
       · refine Mappable (carth h) ha hv (fun P' hZ=>?_); exact (tub A U D hs h hD H hN g P _ _ (VisionCost A h X hq P' hZ)).norm 
       refine hp.meat.mono fun i hi=>?_ ; unfold SchedR; exact measurableSet_le ((skinV _).comp hi) measurable_const
lemma SelectorK (ha:Deb<a)(hc:a≤0): Grain μ φ (Counters β) (ΦMean A U D g P X N) a:=by
       have hP:= perT A U D hs h hD (N:=N) g P X hp hc; have hz:= χResp A U D hs h hD H hN g P X hp hq hv hV ha; apply (hP.add hz U.top.fair).shift; filter_upwards with i; funext x; exact sub_add_cancel ..
end
end
end YM.OPE.Owl.HillZ
