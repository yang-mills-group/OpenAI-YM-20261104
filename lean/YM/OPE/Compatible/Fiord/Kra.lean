import YM.OPE.Compatible.Fiord.Jewel
import YM.OPE.Compatible.Mason.Zeal
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
variable (hz:4 ≤ i)
open Silt.Phere Jargon Crown Paver Cloud Stranded Merchant.SiteL Libra.Shift ScriptJ Drift
local notation "TC"=> Merchant.Chamber G r
noncomputable abbrev αWorld (j:I) : Bid.Dir G (n j)×Merchant.Chamber G r →L[ℝ] FreeResolvent.Vec G (n j) 1:=(flats G (n j)).toContinuousLinearMap ∘L visor A U D j -- namespace
noncomputable abbrev XTape (j:I):= Chart.tangent G (Body 1 (n j))
noncomputable abbrev YTape:=Chart.tangent G (fieldP r)
noncomputable abbrev TX (j:I):= (XTape (G:=G) (n:=n) j).prod (YTape (G:=G) (r:=r))
noncomputable abbrev Dayμ (j:I):= united (XLaw A hz j) (D j)
open Borealis
include hD in lemma ΓVoice (j:I): Silt.Phere.Licence (αWorld A U D j) (Dayμ A D hz j) (FeetV A j) K.K:= LeaseX (Mater A j) hz (Punched A U j) (D j) (hD.obey j)
noncomputable abbrev αSoft(j:I):= RestD 0 P (hNu A j) (Meta A j) (ScoreX A j) g K.K (FeetV A j) hz (et A j) (AuthCap A j)
variable {τ':Libra.Char.Phase→ℕ}
noncomputable abbrev Ctag (H: Aware (d+6+6) τ')(j:I) := ChiselV H (Recon 0 P (hNu A j) (Meta A j) (ScoreX A j) g K.K (FeetV A j) hz (et A j) (AuthCap A j))
noncomputable abbrev Gsky (j:I)(u:Bid.Dir G (n j) × Merchant.Chamber G r):= αSoft A g P hz j (Charu 0 (αWorld A U D j) u)
lemma Cohort (j:I):(TX (G:=G) (n:=n) (r:=r) j).IsAddHaarMeasure := arduous (X:=Bid.Dir G (n j)) (Y:=TC) (Chart.tangent G (Body 1 (n j))) (Chart.tangent G (fieldP r))
where arduous {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X][MeasurableSpace X][BorelSpace X][NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y][MeasurableSpace Y][BorelSpace Y] (μ:Measure X)[μ.IsAddHaarMeasure](ν:Measure Y)[ν.IsAddHaarMeasure] : (μ.prod ν).IsAddHaarMeasure:=inferInstance
include hD in lemma moll_s (j:I): Borealis.Weight (Dayμ A D hz j) (TX (G:=G) (r:=r) (n:=n) j) (d+6) (Gsky A U D g P hz j):=by
       haveI := Cohort (G:=G) (n:=n) (r:=r) j; let X:= αWorld A U D j; let B:= Dayμ A D hz j; refine ⟨fun i=>?_⟩; have hh:=shineD 0 _ hz X (TX (G:=G) (r:=r) (n:=n) j) B K.K _ (ΓVoice A U D hD hz j) P (Meta A j) (et A j) (ScoreX A j) g (hNu A j) (AuthCap A j) i; exact hh.skids (Nat.zero_le _) le_rfl -- cast
local notation "P!"=>fun t=>1
noncomputable def wMirror (f:Forge G n) (j:I)(x: Bid.Dir G (n j) × Merchant.Chamber G r) := f j (visor A U D j x)
lemma UnW (j:I)(p:Bid.Dir G (n j)× Merchant.Chamber G r): Gsky A U D g P hz j p= αSoft A g P hz j (charW 0 (visor A U D j p)):=by
       unfold Gsky; rw[← climbsF,show αWorld A U D j p=flats G _ _ from rfl, (flats G (n j)).symm_apply_apply]; rfl
lemma φMatch (H: Aware (d+6+6) τ')(j:I)(x:Bid.Dir G (n j) × TC): ArtY A P g j (visor A U D j x)= (wMirror A U D (ego G n (Ctag A g P hz H)) j x)+Gsky A U D g P hz j x:=by rw [UnW]; exact weds 0 P _ _ _ g _ _ hz _ _ H _ -- API
include hD
local notation "G!"=> Gsky A U D g P hz
local notation "ΩX!"=> ΩReal A U D (Plato n) N
local notation "XG!"=>Dayμ A D hz
lemma KinΔ (j:I): Weight (Dayμ A D hz j) (TX (G:=G) (r:=r) (n:=n) j) (d+6) ((ΩReal A U D (Plato n) N j)*(Gsky A U D g P hz j)):=by
        letI := Cohort (G:=G) (r:=r) (n:=n) j; rw [mul_comm]; exact Weight.sure _ _ (moll_s A U D hD g P hz j) (Mammon (A:=A) (U:=U) (N:=N) (D:=D) j)
noncomputable def ΞMark (N:ChartRatio G)(j:I) := crossT (Chart.tangent G (fieldP r)) (D j) (ΩReal A U D (Plato n) N j*(Gsky A U D g P hz j))
lemma WoutK (j:I):Weight (XLaw A hz j) (Chart.tangent G (Body 1 (n j))) (d+6) (ΞMark A U D g P hz N j):=by unfold ΞMark; with_reducible_and_instances exact Weight.house (XLaw A hz j) (Chart.tangent G (Body 1 (n j))) (D j) (Chart.tangent G (fieldP r)) (KinΔ (N:=N) A U D hD g P hz j)
end YM.OPE.Owl.HillZ
