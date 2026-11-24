import YM.OPE.Compatible.Soup.Taste
import YM.OPE.Compatible.Soup.Mya
/-!
# Epoch growth. Limited trajectory tape. variance observables without spectral cost loss
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
variable {A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x)}{U: Scaffold φ (Counters β) n (Mnd i S A) r}
variable (D:I→ Law (Merchant.Chamber G r))(hs:G.Simple)
open Merchant.SiteL
variable (h:Tendsto β φ atTop)(hD: GaugeD A U D)
open Cinders Metric Set Zeph Jargon
variable {N:ChartRatio G} {s c R:ℝ} (H:StackP N s c R)(hN:LocalRatio N)
variable (x:∀ i,Bid.Dir G (n i)) (g:ℂ→L[ℝ]ℝ) (P:Pad G)
open ScriptJ
section
variable {t X Y Q:I→ℝ}(ht:Wax β φ t (-(1/2)))(hx:Wax β φ X 0)(hy:Wax β φ Y 0)
include h ht hx hy
private lemma expCone (hp:Wax β φ (fun i=> Q i-(t i*X i+t i^2*Y i)) Deb) : Wax β φ (fun i=> Real.exp (Q i) - (1+t i*X i+t i^2*(Y i+(X i)^2/2))) Deb:=by
        let a(i):= t i*X i; let v(j):=(t j)^2*Y j; let e:= carth h; have hv:Wax β φ v (-1):=((ht.pow 2 e).mul hy).mono (by norm_num); have hg:Wax β φ a (-(1/2)):= (ht.mul hx).mono (by norm_num); have ha:Wax β φ (fun i=>Q i-a i) (-1):=((hp.mono (by norm_num [Deb])).add hv e).congr (Eventually.of_forall fun i=>by unfold v a; ring)
        have hQ: Wax β φ Q (-(1/2)):= ((ha.mono (by norm_num)).add hg e).congr (Eventually.of_forall fun i=>by ring); have he :Wax β φ (fun i=>(Q i)^2-(a i)^2) (-(3/2)):= ((ha.mul (hQ.add hg e)).mono (by norm_num)).congr (Eventually.of_forall fun i=>by ring)
        have hh : Wax β φ (fun i=> Real.exp (Q i)-(1+Q i+(Q i)^2/2)) Deb:=by
              apply RateLE.of_norm_le ((hQ.norm.pow 3 e).mono (by norm_num [Deb])); filter_upwards [(hQ.norm.tends (by norm_num) e).eventually (ge_mem_nhds zero_lt_one)] with i hi; exact xpZ hi
        apply ((hh.add hp e).add (((he.mul (RateLE.const (1/2:ℝ) e))).mono (by norm_num [Deb])) e).congr; filter_upwards with i; unfold a; ring
end
noncomputable abbrev Glaco (A:∀ x:I,HillZ (T:=T) S i r d τ (β x) (n x))(U:Scaffold φ (Counters β) n (Mnd i S A) r) (D:I→Law (Merchant.Chamber G r))(N:ChartRatio G)(P:Pad G) (x:∀ i,Bid.Dir G (n i)) (g:ℂ→L[ℝ]ℝ) (i:I)(y: Merchant.Chamber G r):= ArtY A P g i (liftedM A U D x i y)* Tact A U D x N i y
variable {D} (y:I→ Merchant.Chamber G r)(hp:Lyd A φ x)(hv:Receipt β φ y)
include H hN hD h hs hp hv
lemma KT_oh : Wax β φ (fun i=>Real.exp (Tresp A U D x N i (y i))-(Tact A U D x N i (y i)).atK (et A i)) Deb:=by
       obtain ⟨hL,hK⟩:=plightJ hs h hD H hN x y hp hv; exact expCone h (poleV A h) hL hK (tribut hs h hD H hN x y hp hv)
lemma BuckA : Cinders.Feast (fun i=> Tact A U D x N i (y i)) φ (Counters β):=by
       obtain ⟨hL,hK⟩:=plightJ hs h hD H hN x y hp hv; let b:=carth h; refine ⟨RateLE.const _ b,hL,hK.add ?_ b⟩; let a:= ((hL.pow 2 b).mul (RateLE.const (1/2:ℝ) b)).mono (show _ ≤ 0 by norm_num); exact a.congr (by filter_upwards with i; ring)
lemma vitalQ : Wax β φ (fun i=> ConV A U D (cEye A U D x) g N i (y i) - (Glaco A U D N P x g i (y i)).atK (et A i)) Deb:=by
        let f(i):= Real.exp (Tresp A U D x N i (y i)); let p(i):= ArtY A P g i (liftedM A U D x i (y i)); let V(i):= Tact A U D x N i (y i); let a(i):=p i|>.atK (et A i); let b(i):= V i|>.atK (et A i); let L:=cEye A U D x; let y'(i):=liftedM A U D x i (y i); let z(i):=g (signalF A i (EC A i (y' i))); have hy':Lyd A φ y':= Lynx hs h hD x y hp hv; have hu:=KT_oh hs h hD H hN x y hp hv; have hK : Cinders.Feast p φ (Counters β):= Perc_A h P g hy'; have hx :=BuckA hs h hD H hN x y hp hv
        have hT_old:= lens_law h H.sweep P g hy'; let Y:= carth h; let T:= poleV A h; have ht : Wax β φ b 0:= lampFee hx Y (T.mono (by norm_num)); have hf: Wax β φ f 0:= ((hu.mono (by unfold Deb;norm_num)).add ht Y).congr (by filter_upwards with i; change f i-_+b i=_; unfold b V; exact sub_add_cancel ..)
        have hr : Wax β φ (fun i=>a i*b i-((p i)*(V i)).atK (et A i)) Deb:= (shiftP hK hx T (by norm_num) Y).mono (by norm_num [Deb]); apply RateLE.congr ((((hT_old.mul hf).mono (by norm_num)).add (((lampFee hK Y (T.mono (by norm_num))).mul hu).mono (by norm_num)) Y).add hr Y); filter_upwards [flagFree A h _ hy' H.sweep] with i hi; rw [ΘLaw A U D x g _ (y i) hi]; change (z i-a i)*f i+a i*(f i-b i)+(a i*b i- (p i*V i).atK (et A i))= z i*f i-(p i*V i).atK (et A i); ring
end YM.OPE.Owl.HillZ
