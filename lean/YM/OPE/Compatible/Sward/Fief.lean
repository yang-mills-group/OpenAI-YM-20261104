import YM.OPE.Compatible.Sward.Flow
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
open Quit.PriceZ Stroke
section T
variable (hu:D.gear=P.land)(hs:G.Simple)(t: Town Y D (boxF P Q H B' Y.gear) R b)
include he hu
lemma matelot (hp:ratios p k): ratios (MotionX h0 hs t W H.1 H.2.1 p) k:=by
       apply secs D.gear H.2.1 W (P:=Q); let M:=Fallix G W Q D.gear H.2.1; let V:=Fallix G W Q Y.gear H.1; rw[show M (MotionX h0 hs t W H.1 H.2.1 p)=yankV D t h0 hs W (V p) from M.apply_symm_apply _]; let S:=actor Y (boxF P Q H B' Y.gear) R 0 ⟨hs,h0,t.eph⟩ W; change TrueRay D.gear _ (L:=Q.K) (rebase G W (-b) (S (V p).val)) _; rw[hu]; exact rugged P.land H.2.1 W _ _ (castor h0 P Y D B' W H he hu hs 0 t.eph p hp)
end T
end YM.OPE.Silt.Phere
