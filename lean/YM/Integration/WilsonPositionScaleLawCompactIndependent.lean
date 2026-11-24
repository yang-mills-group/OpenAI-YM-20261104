import YM.Integration.WilsonPositionScaleLawIndependent
import YM.Integration.WilsonPositionScaleLawCompactNative

/-! Compact-time control for the already prescribed independent scale coefficients, on arbitrary bounded positive ratio windows. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawCompactIndependent
open Function Filter Set Finset PowerSeries Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawCompactNative (positive)
open WilsonPositionScaleLawIndependent (trial continuous)
open scoped Topology BigOperators Classical
variable [Win:RangeSpec] {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)

def time (t:Ratio):ℝ:= -Real.log t.val

theorem continuousTime:Continuous time:=(continuous_subtype_val.log (fun t=>(positive t).ne')).neg

theorem geometry (t:Ratio):Real.exp (-(time t))=t.val:=by rw [time,neg_neg,Real.exp_log (positive t)]

include H in
theorem small (d q:ℕ){g:ℝ→ℝ}(hg:Tendsto g Trace.Pilot.trail (𝓝 0)):
    Tendsto (fun z:ℝ×Ratio=>trial Z M ν d q (time z.2) (g z.1)) sweep (𝓝 0):=by
  have joint:Continuous (fun z:Ratio×ℝ=>trial Z M ν d q (time z.1) z.2):=by
    apply continuous_finsetSum;intro k _
    exact (continuous_snd.pow _).smul ((continuous Z M H ν d k).comp
      (continuousTime.comp continuous_fst))
  apply Metric.tendsto_nhds.mpr
  intro ε he
  have unif:=PhysMS.Frame.compact_event ℝ (isCompact_univ : IsCompact (univ:Set Ratio))
    (fun r t=>dist (trial Z M ν d q (time t) (g r)) 0<ε) (l:=Trace.Pilot.trail) (fun t _=>by
      have h:= (joint.tendsto (t,0)).comp (tendsto_snd.prodMk_nhds (hg.comp tendsto_fst))
      have base:trial Z M ν d q (time t) 0=0:=by simp [trial]
      rw [base] at h
      exact Metric.tendsto_nhds.mp h ε he)
  exact (tendsto_fst.eventually unif).mono fun z hz=>hz z.2 (mem_univ _)

end YM.Integration.WilsonPositionScaleLawCompactIndependent
end
