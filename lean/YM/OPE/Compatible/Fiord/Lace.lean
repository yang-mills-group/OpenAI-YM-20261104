import YM.OPE.Compatible.Fiord.Minx
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
private lemma PayAdd {E:Type}(x y:E→Token)(t:ℝ): tariff t (x+y)=tariff t x+tariff t y:=by funext i; change _= tariff t x i+tariff t y i; simp only[tariff, JetS.atK,Pi.add_apply,JetS.pl_s,JetS.pl_l,JetS.pl_h,smul_eq_mul];ring
local notation "ΩF"=>RentZ A U D g P N
local notation "Σx"=> ΞMark A U D g P hz N
local notation "α"=>N
local notation "x'"=>C-V
include hD
lemma ΞStar (j:I) : Spectre (XLaw A hz j) (Chart.tangent G (Body 1 (n j))) (tariff (et A j) (ΞMark A U D g P hz N j)) (d+6) 0:=by
        let f:=ΞMark A U D g P hz N j; let V:=XLaw A hz j; let μ:=Chart.tangent G (Body 1 (n j)); have he := WoutK (N:=N) A U D hD g P hz j; refine (Bouquet (p:=f) (A:=V) (μ:=μ) (t:=(0:ℝ)) (et A j) (fun i=>?_)).widen (le_of_eq (mul_zero _)); have hp:=he.color i; exact Spectre.back (hp.block.points (by have ht:=i.isLt;omega)) (Ppu _ _ hp.hW)
omit hD
private lemma LawSum {E:Type} (p q r s:E→Token)(a:E→ℝ)(t:ℝ)(h:a=tariff t (r+p-s)): tariff t (p-q)+tariff t r= a+tariff t s-tariff t q:=by rw [TarSub,h,TarSub,PayAdd]; abel
include h hs hX hN hD
lemma Et : Grain (Vela A hz) φ (Counters β) (fun j=> tariff (et A j) (W j-(C-V) j)+tariff (et A j) (ΞMark A U D g P hz N j)) q1:=by
       let ht:= ArtNorm A U D hs h hD hN g P hz; let H:=EntZ A U h g P hz hX (c:=q1); let hp:= αEra (c:=q1) A U D hs h hD (N:=N) g P hz hX; let t:=U.top.fair; refine ((ht.add hp t).sub H t).shift ?_; filter_upwards [trueΦ A U D hD hN g P hz hX] with i hi; exact (LawSum _ _ _ _ _ _ hi).symm
lemma ζEarn : Audible G K.K n φ (Counters β) i (d+6) (FeetV A) hz (fun j=> tariff (et A j) (W j-(C-V) j)) q1:=by
       obtain ⟨R,hR,H⟩:= Et A U D hs h hD hN g P hz hX 2 two_pos; refine ⟨_,hR,?_⟩; filter_upwards [H,δLau A U g P hz hX,δHeads A U g P hz hX] with j hj ⟨ha,hb⟩ hq; let S:= XLaw A hz j; let μ:= Vela A hz j; let f:= tariff (et A j) (W j-(C-V) j); let g':= tariff (et A j) (ΞMark A U D g P hz N j); have he:= Ppu S (Chart.tangent G (Body 1 (n j))) (freightS (et A j) (puffP_sub _ _ hb hq)); have hz':= ΞStar A U D hD (N:=N) g P hz j; have hq':Pu μ (f+g'):= Borealis.Lav.addedP he hz'.Aet; refine ⟨hj.pos,?_⟩; let Y:= Chart.tangent G (Body 1 (n j)); change Spectre S Y f _ _; have hp :Spectre S Y (f+g'+ -g') (d+6) (R j):= ((Spectre.Ffoot hj hq').scored hz'.minus).widen (le_of_eq (add_zero _)); simpa only [add_assoc,add_neg_cancel,add_zero] using hp
end YM.OPE.Owl.HillZ
