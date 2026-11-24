import YM.Integration.WilsonIndependentSpoutRealMarkRows
import YM.MatchingLedger.Compass.Fix

/-! The exponential-coordinate Haar inputs agree at every rank and every finite board on any two original chart receipts. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutHaarGerms
open Filter Function PowerSeries Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open PertExtension FreeResolvent Metric Precision Exterior
open scoped Topology Classical
variable {G:Gauge}{U V:ChartRatio G}(first:LocalRatio U)(second:LocalRatio V)
include first second

theorem density:dij U =ᶠ[𝓝 0] dij V:=by
  have h:=MatchingLedger.Compass.Interiors.charge first second
  have lim:Tendsto (coatC G) (𝓝 0) (𝓝 0):=by simpa only [map_zero] using (coatC G).continuous.tendsto 0
  exact h.comp_tendsto lim

theorem zeta (c:ℝ):ζ U c=ζ V c:=by
  unfold ζ
  rw [jet_congr (density first second)]

omit first second in
private theorem sprouts {I:Type}[Fintype I]{F H:Lawn I→ℝ}(g:F=ᶠ[𝓝 0] H)(t:ℕ):sprig F t=sprig H t:=by
  have eq (i:ℕ):iteratedFDeriv ℝ i F 0=iteratedFDeriv ℝ i H 0:=
    congrFun ((g.ftaylorSeries (𝕜:=ℝ)).self_of_nhds (x:=0)) i
  funext i
  change shine (rye F (t+i))=shine (rye H (t+i))
  apply congrArg shine
  funext x
  unfold rye
  rw [eq]

theorem finite (n:Side):sprig (unhaar (n:=n) U) 0=sprig (unhaar (n:=n) V) 0:=by
  apply sprouts
  have atLink(e:Edge (Site n)) : (fun x:TreeVars G n=>dij U (dyes x e)) =ᶠ[𝓝 0] (fun x=>dij V (dyes x e)):=by
    apply (density first second).comp_tendsto
    simpa only [dyes_zero] using (dyes_green e).continuousAt.tendsto
  filter_upwards [Filter.eventually_all.mpr atLink] with x hx
  unfold unhaar
  exact Finset.sum_congr rfl fun e _=>congrArg Real.log (hx e)

theorem bearing:bearingJ U=bearingJ V:=by
  have field:blumeA U =ᶠ[𝓝 0] blumeA V:=by
    filter_upwards [density first second] with x hx using congrArg Real.log hx
  funext i
  unfold bearingJ
  rw [sprouts field 0]

end YM.Integration.WilsonIndependentSpoutHaarGerms
