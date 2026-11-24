import YM.OPE.Compatible.Fiord.Power
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
open Borealis Borealis.Lav Cameo Claw Libra.Char Variance
local notation "Tc"=> Merchant.Chamber G r
variable {τ':Phase→ℕ}{C V W:Forge G n}{H:Aware (d+6+6) τ'}
variable (hX:AcctΩ A U g P hz H C V W)
local notation "PP!"=> RentRa D (Vela A hz)
local notation "Ψ"=> Vela A hz
local notation "ΩK"=> ΩReal A U D (Plato n) N
local notation "Z!"=> Counters β
local notation "F*"=> Mouth A U D
-- κ D residual
include h hX
lemma MFine: Pine (Vela A hz) φ (Counters β) (C-V) c:=by
       exact Flown (Plato n) (ΘIncome A h hz) (carth h) (C-V) (hX.rise _) (δRoll A U g P hz hX)
include hs hD
omit h hX hD hs in
lemma EliteΩ:∀ i:I,IsProbabilityMeasure (RentRa D (Vela A hz) i):= by
       intro i; exact Phh (μ:=Ψ i) (ν:=ShoreP D i)
where Phh {E F:Type}[MeasurableSpace E][MeasurableSpace F]{μ:Measure E}{ν:Measure F}[IsProbabilityMeasure μ][IsProbabilityMeasure ν]:IsProbabilityMeasure (μ.prod ν):=inferInstance
lemma MGrade: Pine (RentRa D (Vela A hz)) φ (Counters β) (fun i=> wMirror A U D (C-V) i) c:=by
       letI:=EliteΩ A D hz; let X:= ΩBound A U D hs hD (Bx (Plato n)) (By G _ r) (Sender D _ (ΘIncome A h hz)) (TailZ A U D h hD (Vela A hz))
       let F(i:I):= wMirror A U D (C-V) i; let q:= WField A U D (Bx (Plato n)) (By G (fun i=>Bid.Dir G (n i)) r); let hP:= Flown q X (carth h) (C-V) (hX.rise c) (δRoll A U g P hz hX); have he:F=fun i (v:Bid.Dir G (n i) × Tc)=> (C-V) i (q i v):=by
            funext i v; obtain ⟨x,y⟩:= v; unfold F wMirror; rw[torn A U D]; unfold q WField Plato Bx By; with_reducible_and_instances rfl
       change Pine _ _ _ F _; rw [he]; exact hP
lemma ΚTag: Pine (RentRa D (Vela A hz)) φ (Counters β) (Mouth A U D (C-V) N) c:=by -- greek K lexer?
       let v:= HeatΩ A U D hs h hD (N:=N) _ (ΘIncome A h hz); let q:= MGrade A U D hs h hD g P hz hX (c:=c); exact fun i=> (PineM (carth h) v q i).mint (le_of_eq (zero_add _))
omit hs hD in lemma EntZ: Grain (Vela A hz) φ (Counters β) (fun i=> tariff (et A i) ((C-V) i)) c:= beaconP (carth h) (C-V) _ (MFine A U h g P hz hX) ((poleV A h).mono (by norm_num)) -- U param from hX
lemma αEra : Grain Ψ φ Z! (fun i=> tariff (et A i) (marX A U D (C-V) N i)) c:=by
       letI:=EliteΩ A D hz; let v:= Mouth A U D (C-V) N; let K:= ΚTag A U D hs h hD (N:=N) g P hz hX (c:=c); let b:= beaconP U.top.fair v (et A) K ((poleV A h).mono (by norm_num)); apply (b.ault (aftD v (et A))).shift; filter_upwards [δHeads A U g P hz hX] with i hi; funext x; let Q:=D i; let T:=et A i; let μ:=Chart.tangent G (fieldP r); exact (Boν Q μ (v i) (handy A U D i _ hi) x T).symm
end YM.OPE.Owl.HillZ
