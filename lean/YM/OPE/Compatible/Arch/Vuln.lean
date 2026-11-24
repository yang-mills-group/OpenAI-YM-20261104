import YM.OPE.Compatible.Arch.Door
/-!
# Local graph jets through *relative* Haar normalization
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision
variable {I J:Type}{G:Gauge}[Fintype I]
open Radial Zone ScriptJ Metric
local notation "W" => Chart.tangent G I
local notation "N" => Module.finrank ℝ (Keys G I)
local notation "Lf" => Tested.germ
-- tax theorem
variable {P:ChartRatio G} (R: LocalRatio P)
def mounted (D:Set (Tile G I))(r:ℝ):= put ⁻¹' D ∩ ball 0 r
abbrev peak (f:Tile G I→ℝ) (s) (t:ℝ) := (t^N)⁻¹ * ∫ x in s,f x ∂Chart.physical G I
include R
private lemma gates (f:Tile G I→ℝ)(h:Measurable f){r:ℝ}{s:Set (Tile G I)}(hs: s⊆ Chart.chamber G I r)(hq:MeasurableSet s) (hr:r < Chart.small G P)(ht:0<r):
      (∫ x in s,f x ∂Chart.physical G I) = ∫ x in mounted s r, Chart.jacobian P x * f (put x) ∂W := by
     let y:= Chart.chamber G I r
     let C:=W
     calc
        _ = ∫ x in y,s.indicator f x ∂Chart.physical G I := by
             rw [integral_indicator hq, Measure.restrict_restrict_of_subset hs]
        _ = ∫ x in ball 0 r,Chart.jacobian P x * s.indicator f (put x) ∂C := Chart.Ratio.chamber_integral R _ (h.indicator hq) hr ht
        _ = _:= by
            let S:= put ⁻¹' s
            have he:S.indicator (fun x=> Chart.jacobian P x*f (put x))=fun x=> Chart.jacobian P x*s.indicator f (put x):=by
               funext x; by_cases h:x∈S
               · rw [indicator_of_mem h,indicator_of_mem (show _∈ s from h)]
               rw [indicator_of_notMem h, indicator_of_notMem (show _∉ s from h)]; ring
            have hh: MeasurableSet S:= hq.preimage putC.measurable; rw [← he,integral_indicator hh,Measure.restrict_restrict hh]; rfl
-- main local reading. price given in tangential scaled bill with Haar density.
theorem satisfied {f:ℝ→Tile G I→ℝ}(h:∀ r,Measurable (f r)){u:Keys G I→ℝ}{A:ℝ→Keys G I→ℝ}{c:ℝ}{p:ScriptJ (Keys G I)}(hp:Bears (shade c) A p)(ha:∀ t,Measurable (A t))(hr: KernFit u (c+c))(he:0<c)(hb:Measurable u)
     (ht:∀ᶠ y:Keys G I in 𝓝 0,∀ x t,0<t → t • x = y→ Chart.jacobian P y*f t (put y)= A t x*u x) :
     ∃ s∈𝓝 (1:Tile G I),∀ d:Set (Tile G I),d⊆s→d∈𝓝 1→MeasurableSet d→ Reads (fun t=> peak (f t) d t) (gemLift W u p) := by
     obtain ⟨δ,hδ,hx⟩:= balanceH W hp ha hr he hb; obtain ⟨a,hq,hf⟩:= Metric.mem_nhds_iff.mp ht; let r := min (Chart.small G P/2) (min δ a); let S:=Chart.chamber G I r
     have ht:0<r:= lt_min (half_pos (Chart.Ratio.small_pos R)) (lt_min hδ hq); have hR : r<Chart.small G P:= (min_le_left ..).trans_lt (half_lt_self (Chart.Ratio.small_pos R)); have hv : S∈𝓝 (1:Tile G I):=(Chart.Ratio.chamber_open R hR.le).mem_nhds <| (fun i _=>⟨0,mem_ball_self ht,G.mat_lieExp_zero⟩)
     refine ⟨S,hv,fun d hd hD hg=>?_⟩; let D := mounted d r; let m:=Chart.physical G I; have hM: D ⊆ ball 0 r:=inter_subset_right; have hy: D∈𝓝 0:= inter_mem (putC.continuousAt.preimage_mem_nhds (by rw [put_zero];exact hD)) (ball_mem_nhds _ ht); have hu: MeasurableSet D:=(putC.measurable hg).inter isOpen_ball.measurableSet
     refine (hx D (hM.trans (ball_subset_ball ((min_le_right ..).trans (min_le_left ..)))) hy hu).cong ?_
     filter_upwards [Tested.eventually_pos] with t ht; rw [show peak (f t) d t=(t^N)⁻¹ * ∫ x in D, Chart.jacobian P x*f t (put x) ∂W by rw [peak,gates R (f t) (h t) hd hg hR ‹0<r›]] -- duplicate ht argument
     -- smul
     let F:=fun x:Keys G I=>Chart.jacobian P x*f t (put x)
     let g:=D.indicator F; let U:= Suber D t; have HH: g ∘ (fun x=> t • x) = U.indicator (A t*u):= by
          funext x; change g (t • x)=_; by_cases hi:x∈U
          · have hz:t•x∈D:=hi; unfold g; rw [indicator_of_mem hz, indicator_of_mem hi]; exact hf (ball_subset_ball ((min_le_right ..).trans (min_le_right ..)) (hM hz)) x t ht rfl
          rw [indicator_of_notMem hi]; exact indicator_of_notMem (show t•x ∉ D from hi) _
     have hZ:= Measure.integral_comp_smul_of_nonneg W g t (hR:=ht.le) -- order scalar
     unfold g at *; rw [integral_indicator hu, smul_eq_mul] at hZ; rw [← hZ]; exact (congr_arg (fun p:Keys G I→ℝ=>∫ x,p x ∂W) HH).trans (integral_indicator (show MeasurableSet U from hu.preimage (show Measurable (fun x:Keys G I=> t • x) by fun_prop)))
end YM.OPE.Libra
