import YM.Integration.WilsonThermometerWeakValueRecovery
import YM.PhysMS.Frame.Phases

/-! The separated all-position continuum family already supplies the measured
regularity in the compact interpolation receipt, simultaneously for all viewers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakMeasuredBounds
open Set Filter Function Spec Trace.Pilot OPE OPE.Orbits Next.UVStress Climb PhysMS PhysMS.Frame
open WilsonThermometerWeakValueRecovery
open scoped Classical Topology ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (U:ℝ→tower S)(H:Leading F U)(simple:G.Simple)(X:Scaling S)(built:Foundation F R)
    {n:ℕ}{d:Caps n}

theorem maxwell (v:MaxwellSlots C d)(K:Set (Points n))(compact:IsCompact K)(clear:K⊆conf n)(j:ℕ):
    ∃B,0≤B ∧ ∀x∈K,‖iteratedFDeriv ℝ j (WickGoal v) x‖≤B:=by
  obtain ⟨B,paid⟩:=compact.exists_bound_of_continuousOn (f:=iteratedFDeriv ℝ j (WickGoal v))
    (fun x hx=>((WickGoal_tied (C:=C) v (clear hx)).continuousAt_iteratedFDeriv (k:=j)
      (WithTop.coe_le_coe.mpr le_top)).continuousWithinAt)
  exact ⟨max 0 B,le_max_left ..,fun x hx=>(paid x hx).trans (le_max_right ..)⟩

include R H simple X built in
theorem original (v:MaxwellSlots C d)(viewer:ℝ→Viewers F)(j:ℕ):
    Bounded trail (conf n) (fun r=>measured F (viewer r) (U r) v r) j:=by
  intro K compact clear
  obtain ⟨B,Bn,paid⟩:=maxwell v K compact clear j
  refine ⟨1+B,by positivity,?_⟩
  filter_upwards [all_leading F R U H simple X built j v K compact clear 1 zero_lt_one] with r small x hx
  exact (norm_le_norm_sub_add (iteratedFDeriv ℝ j (measured F (viewer r) (U r) v r) x)
    (iteratedFDeriv ℝ j (WickGoal v) x)).trans (add_le_add (small x hx (viewer r)).le (paid x hx))

theorem unselected (v:MaxwellSlots C d)(r:ℝ)(pos:0<r):
    ContDiffOn ℝ ∞ (measured F none (U r) v r) (conf n):=
  (S.class_smooth S F.room.kernel.smooth (fun i=>⟨d i,U r (d i) (v i)⟩)).comp
    (show ContDiff ℝ ∞ (fun x:Points n=>r • x) by fun_prop).contDiffOn (fun _ hx=>Work.A05.smul_conf pos hx)

end YM.Integration.WilsonThermometerWeakMeasuredBounds
end
