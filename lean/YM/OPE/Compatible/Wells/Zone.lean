import YM.OPE.Compatible.Wells.Can
import YM.OPE.Compatible.Wells.Honor
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
local notation "X!"=>cEye A U D x
open Variance
local notation "m!"=> (ΓWeight (G:=G) (Punched A U _) (cEye A U D x _) (KPole A _) (LPole A _))
include hN
section
omit hN
private lemma drawK (p:(i:I)→Merchant.Chamber G r→Token)(i:I): propH (ShoreP D) p i=draw (p i) (D i) (Chart.tangent G (fieldP r)):=by apply JetS.eta <;> exact has_p ..
lemma εpion (i:I):epmt A U D x N i=draw (Tact A U D x N i) (D i) (Chart.tangent G (fieldP r)):=drawK ..
include hN
lemma vBond (j:I):ScriptJ.B (vclay A U D x N j):=height (p:=fun _=>_) (Bfray _) (Kgrade A U D hN x j) -- ambiguity
lemma oneMt (j:I):draw (vclay A U D x N j) (D j) (Chart.tangent G (fieldP r))=1:=by
       unfold vclay; rw[drips _ _ _ _ (Kgrade A U D hN x j), ← εpion A U D x j]; apply JetS.uniting; rw[ep_s]; exact one_ne_zero
lemma Loaded.checkT {f:Forge G n}(h:Loaded A U D f (N:=N)): ∀ᶠ j in φ,∀ x:∀ i,Bid.Dir G (n i), draw (vclay A U D x N j*(f j ∘ liftedM A U D x j)) (D j) (Chart.tangent G (fieldP r))=0:=by
        filter_upwards[h.fees] with j hi x; obtain ⟨hh,hq⟩:=hi x; let Z:=Tact A U D x N j; let p:= (epmt A U D x N j)⁻¹; let t:=f j∘ liftedM A U D x j; let W:=Z*t; let V:=D j; let μ:= Chart.tangent G (fieldP r); have ht: ScriptJ.B t:=by with_reducible_and_instances exact turnB (Stair A U j) (cEye A U D x j) _ hh
        change draw (_*t) V μ=0; rw [show vclay A U D x N j*t=(fun x=>p*W x) from funext fun i=>mul_assoc .., drips μ V W p (height (Kgrade A U D hN x j) ht), show draw W V μ=0 from hq,mul_zero]
end
end YM.OPE.Owl.HillZ
