import YM.OPE.Compatible.Fiord.Otis
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
open Merchant.Sleeve
variable (hp:SkinQ n (Counters β) μ φ X)
local notation "G!"=>Butte (μ_p) φ (Counters β)
local notation "pΦ"=>peg A U D X N
local notation "pλ"=> peg A U D (XTarg A X) N
noncomputable abbrev ΩReal (P:ChartRatio G)(i:I)(z:J i × Merchant.Chamber G r):= MonoΩ A U D P i (X i z.1) z.2
noncomputable def CoatI (Q:Hang J)(i:I)(z:C_Ra J (G:=G) (r:=r) i):Token:= (Q i z.1)
variable {P:Pad G}
include hp hs h hD
local notation "XP!"=> CoatI (r:=r) (G:=G)
-- salary normalized
lemma HeatΩ : Butte (μ_p) φ (Counters β) (ΩReal A U D X N):=by
       let X:= Ωwt A U D X N; have hP:=Emb A U D hs h hD _ hp N; let q:=pΦ; let T:= XP! (Trek q); have he:G! T:=by intro i; exact (PineInv (carth h) hP (fun j v=> fullHt A U D j _) i).loco -- Cost.Morn
       exact gluing he (lev A U D hs h hD _ hp N) U.top.fair
lemma PhaseΛ (hc:c≤0): Pine (RentRa D μ) φ (Counters β) (ΩReal A U D X N-ΩReal A U D (XTarg A X) N) c:=by
        have hr:=hp.Rise X (W:=Mnd i S A); let x:= Ωwt A U D X N; let q:= pΦ; let H:=Ωwt A U D (xK) N; let P:= peg A U D (xK) N; let f:= XP! (Trek q); let g:=XP! (Trek P); let v:=U.top.fair; have hT:=Camp A U D hs h hD X hp hc N; have ht:= Emb A U D hs h hD X hp N; have hz:G! f:= fun i=> (PineInv v ht (fun _ _=>fullHt ..) i).loco; have hS:Pine (μ_p) φ ΓZ (x-H) c:=levE A U D hs h hD X hp hc N
        have hx: Pine (μ_p) φ ΓZ (f-g) c:= fun i=> (PerV v ht (Emb A U D hs h hD _ hr N) hT (fun j a=>fullHt ..) (fun j a=>fullHt ..) i).loco
        exact PineC v hx hz hS (lev A U D hs h hD _ hr N)
end
end YM.OPE.Owl.HillZ
