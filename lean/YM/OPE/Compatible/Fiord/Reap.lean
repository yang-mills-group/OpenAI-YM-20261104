import YM.OPE.Compatible.Hatch.Beth
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
-- pointwise kernels. v path expects phase payment. X xt choice variable
noncomputable abbrev Kho (j:I)(x:Bid.Dir G (n j))(y:TC):= turnξ j (mixT A U D j x) y
where turnξ (j:I)(x:Bid.Dir G (n j))(y:Merchant.Chamber G r):=x+Stair A U j y
noncomputable def ExT (j:I)(x:Bid.Dir G (n j))(y:TC): Token := PolV A j (Kho A U D j x y)-PolV A j (mixT A U D j x)
noncomputable def FelT (j:I)(x:Bid.Dir G (n j))(y:TC):= y+PinT G (mixT A U D j x)
noncomputable def Fob (P:ChartRatio G)(i:I)(x:Bid.Dir G (n i))(p: Merchant.Chamber G r):Token:= flareTok (ExT A U D i x p).l ((ExT A U D i x p).h+jet (feeX P) 2 (FelT A U D i x p))
lemma Ep_K (N:ChartRatio G)(x:∀ i,Bid.Dir G (n i))(j:I): Fob A U D N j (x j)=Tact A U D x N j:=by
       funext i; let L:=(PolV A j (liftedM A U D x j i)); let p:= PolV A j (cEye A U D x j); change flareTok (L-p).l ((L-p).h+ _) = flareTok (L.l-p.l) (L.h-p.h+ _); rfl -- Token subtraction defeq x+(-y)?
lemma T_Mischief (x:∀ i,Bid.Dir G (n i))(j:I): Kho A U D j (x j)=liftedM A U D x j:=rfl
noncomputable def Eday (N:ChartRatio G)(j:I)(x:Bid.Dir G (n j)):Token:= draw (Fob A U D N j x) (D j) (Chart.tangent G (fieldP r))
lemma payV (x:∀ i,Bid.Dir G (n i))(j:I): Eday A U D N j (x j)=epmt A U D x N j:=by rw[Eday,Ep_K, εpion A U D x j]
noncomputable def MonoΩ (N:ChartRatio G)(j:I)(x:Bid.Dir G (n j))(y:Merchant.Chamber G r):= (Eday A U D N j x)⁻¹ * Fob A U D N j x y
lemma HonorQ (x:∀ i,Bid.Dir G (n i))(j:I) : MonoΩ A U D N j (x j)=vclay A U D x N j:=by funext i;unfold MonoΩ;rw [payV A U D x j,Ep_K]
lemma swell (j:I)(v:Bid.Dir G (n j)): ∃ x:((i:I)→Bid.Dir G (n i)), x j=v:= ⟨Pi.single j v,Pi.single_eq_same ..⟩ -- unused ABC L implicit
lemma fullHt (j:I)(x:Bid.Dir G (n j)): (Eday A U D N j x).s=1:=by obtain ⟨p,hp⟩:=swell j x; rw[← hp,payV A U D p j,ep_s]
-- normalized Art cap
noncomputable def StoryF (P:ChartRatio G)(K:Pad G)(g:ℂ→L[ℝ]ℝ)(j:I)(x:Bid.Dir G (n j))(y:Merchant.Chamber G r):= MonoΩ A U D P j x y*ArtY A K g j (Kho A U D j x y)
lemma HuskK (N:ChartRatio G)(x:∀ i,Bid.Dir G (n i))(j:I): StoryF A U D N P g j (x j)= winterS A U D x g P N j:=by funext v; unfold StoryF winterS; rw[HonorQ A U D x j,T_Mischief]
include hN
lemma penJ (j:I) (x:Bid.Dir G (n j)): ScriptJ.B (MonoΩ A U D N j x) ∧ draw (MonoΩ A U D N j x) (D j) (Chart.tangent G (fieldP r))=1:=by
       obtain ⟨p,hp⟩:=swell j x; rw[← hp,HonorQ A U D p j]; exact ⟨vBond A U D hN p j,oneMt A U D hN p j⟩
lemma Honest {f: Forge G n}(hv:Loaded A U D f (N:=N)):∀ᶠ i in φ,∀ x:Bid.Dir G (n i),draw (MonoΩ A U D N i x*(f i∘ Kho A U D i x)) (D i) (Chart.tangent G (fieldP r))=0:=by
       filter_upwards [hv.checkT A U D hN] with i hi x; obtain ⟨p,hp⟩:= swell i x; rw[←hp,T_Mischief,HonorQ]; exact hi p
end YM.OPE.Owl.HillZ
