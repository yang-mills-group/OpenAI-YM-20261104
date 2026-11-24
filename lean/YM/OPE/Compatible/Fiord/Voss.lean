import YM.OPE.Compatible.Fiord.Sip
import YM.OPE.Compatible.Camo.Hilt
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
open Ibis Jargon Crown Exterior Silt.Phere Paver
noncomputable abbrev Plato (n:I→Side)(j:I)(x:Bid.Dir G (n j)):= x
noncomputable abbrev FeetV (i:I):= (Mater A i).gear
variable (hz:4 ≤ i)
noncomputable abbrev XLaw (i:I):= Vessel K.K (FeetV A i) G (n i) hz
noncomputable abbrev Vela(i:I):= quart (XLaw A hz i) (Chart.tangent G (Body 1 (n i)))
noncomputable abbrev cloudB (G:Gauge)(β:I→ℝ)(i:I):= 2*LockA G*(Counters β i)^2
include h
lemma ΘIncome : SkinQ n (Counters β) (Vela A hz) φ (Plato n (G:=G)):=by
       refine ⟨Eventually.of_forall fun _=>measurable_id,fun k hk=>?_⟩; exact ⟨_,RateLE.const _ (carth h),Eventually.of_forall fun i=> JPaid (FeetV A i) hz (G:=G) (K:=K.K) _ hk⟩
lemma Confident : Wick β φ (fun i=> (Vela A hz i).real (SchedR (Plato n (G:=G)) (cloudB G β) i)ᶜ):=by
       let p(i):= Real.exp (-((Counters β i)^2)); let c:= Yrent K.K G hz; have hv: Wick β φ p:= fun a=> (Wick_bill h zero_lt_one a).congr (Eventually.of_forall fun i=>by unfold Burl p; rw[neg_one_mul]) -- memory order
       intro a; apply RateLE.of_norm_le (((RateLE.const c (carth h)).mul (hv a)).mono (by simp)); filter_upwards with i; rw[Real.norm_of_nonneg measureReal_nonneg]; rw [show (SchedR (Plato n (G:=G)) (cloudB G β) i)ᶜ={x:Bid.Dir G (n i)|cloudB G β i< Roster x} from Set.ext fun x=>(show (¬Roster x ≤ cloudB G β i) ↔ cloudB G β i < Roster x from not_le)]; exact Ibis.overΩ (FeetV A i) hz (K:=K.K) _ ((Counters β i)^2)
lemma CountsZ : Receipt β φ (cloudB G β):= (YM.OPE.Score.steady (2*LockA G) (carth h)).product ((sans h).power 2 (carth h))
include hN hD hs
lemma ArtNorm : Grain (Vela A hz) φ (Counters β) (ΦMean A U D g P (Plato n) N) q1:=by
       obtain ⟨r',c,t,H⟩:= LiftFee hN; let S:=SchedR (Plato n (G:=G)) (cloudB G β); apply SelectorK A U D hs h hD H hN g P _ (ΘIncome A h hz) (CountsZ (G:=G) h) (show ∀ᶠ i in φ,(S i).Nonempty from ?_) (Confident A h hz) (by norm_num[Deb,q1]) (by norm_num [q1]); filter_upwards with i; refine ⟨0,?_⟩; change ‖_‖ ≤ 2*LockA G*_; change ‖(tellerT G (n i)).symm (0:Bid.Dir G (n i))‖≤ _; rw[map_zero,norm_zero]; exact mul_nonneg (mul_nonneg zero_le_two (zero_le_one.trans LockOne)) (sq_nonneg _)
end YM.OPE.Owl.HillZ
