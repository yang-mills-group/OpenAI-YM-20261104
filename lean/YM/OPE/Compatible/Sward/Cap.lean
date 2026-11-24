import YM.OPE.Compatible.Sward.Corn
import YM.OPE.Compatible.Roost.Mood
import YM.OPE.Compatible.Lob.Top
import YM.OPE.Compatible.Frog.Eye
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
-- budget C estimate.O. Use masks of bad axes
open Cascade Terp Paver Rill Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
open Votive
variable {N:Side}{L:KernelChoices} (x:Site N)
open Drift Shell Char
variable {τ :Char.Phase→ℕ}{d:ℕ}
open PertExtension Series GaussianScore
open Matrix
open Flock Shift
open WithLp Exterior
open Tree Woody Stationary
variable {G:Gauge}{Q:Sponsor G}{T:Seasons Q}{v v' b η:ℝ}{R:ChartRatio G}
variable (h0:LocalRatio R)(P: Flight i j)(Y:Alps Q T i v) (D: Alps Q T j v') (B':Medal P.patch G Q.K i)(W:Aware d τ)(H:Mag i j)(he:Y.gear=P.wing)
variable (p:Tracts G d τ)
section sing
variable (c f:Side) (hx:f.val=c.val*P.L.val)(r:ℝ)
include h0 he
set_option maxHeartbeats 200000 in
lemma loyal :
     let S:= P.visit Q.K hx; let U:=boxF P Q H B' Y.gear; let H':= installed S.ratio (P.duo Q.K.penalty).A0; let o:=P.odd; let T':= S.ratio
     let B:=Vessel Q.K P.land G c H.2.1; let w:=spread G d τ (FoldV W p (pointAt G Y.gear H.1 Q.K f))
     ∀ q:Site c, ∀ t:S.Choices,∀ (g:Bid.Dir G c→AxisChart G (forest T' o)), licensed S P.odd U Y.clip Y.live H' Y.sky g → ∀ X:FibreRep S P.odd U t Y g r, let s:=TracePay S o U Y t g R d w r q X; ratios p k→ MoldH B (Chart.tangent G (Body 1 c)) k s:=by
         intro S U H' o T' B w q t g hG X s ht; let Z:= inkM w d (S.ratio.embed q);
         let μ:=Chart.tangent G (Body 1 c); let ν:= Chart.tangent G (forest T' o).Free; let τμ:=μ.prod ν; let Q':= X.L.Q
         let V:= chorus (climbs (Master S P.odd (P.duo Q.K.penalty).A0) ∘L (flats G c).toContinuousLinearMap) (vertD S P.odd (G:=G)); let A:= united B Q'
         haveI : ((Chart.tangent G (Body 1 c)).prod (Chart.tangent G (forest T' o).Free)).IsAddHaarMeasure:= Pilot.twoHaar (E:=Bid.Dir G c) (F:=AxisChart G (forest T' o)) (Chart.tangent G (Body 1 c)) (Chart.tangent G (forest T' o).Free)
         have hh:= glossB (S.ratio.embed q) W p V ((Chart.tangent G (Body 1 c)).prod (Chart.tangent G (forest T' o).Free)) A Y.gear H.1 Q.K (winter P hx Q T H r v Y he B' g t hG X) ht; apply visionG μ X.L R h0 B (Z ∘ ribz S o); convert! hh using 1
         funext i; let b:=Fiber.drape (Bid.Dir G c) (AxisChart G (forest T' o)) X.L.M; change Z (ribz S o (b i))= Z ((flats G f).symm _); apply congr_arg; apply (flats G f).injective; rw[ContinuousLinearEquiv.apply_symm_apply]; exact uprush S o (P.duo Q.K.penalty).A0 g Y U t hG X i.1 i.2
end sing
end YM.OPE.Silt.Phere
