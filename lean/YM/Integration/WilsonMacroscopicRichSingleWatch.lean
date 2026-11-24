import YM.Integration.WilsonMacroscopicRichWatchLabels

/-! One unchanged physical macroscopic watch against a cutoff-dependent counterterm at the origin. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichSingleWatch
open Function Filter Spec OPE OPE.Orbits Lattice Cells Wilson Next.UVStress
open WilsonMacroscopicRichWatchLabels WilsonMacroscopicRichWatchLaw
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}

def target (W:Watch C)(h:ℕ):C.label h→L[ℂ]ℂ:=
  ((W.tester S h).comp (S.project h)).toContinuousLinearMap

theorem original (F:Final C f S)(W:Watch C)(h:ℕ):
    Tendsto (fun w=>(row W h w).toContinuousLinearMap) f.fuse (𝓝 (target (S:=S) W h)):=by
  apply Dash.fit_plane
  exact limits F W h

theorem moving (F:Final C f S)(W:Watch C)(h:ℕ){l:Filter (ℕ×ℕ)}(le:l≤f.fuse)
    (z:ℕ×ℕ→C.label h)(K:ℝ)(cap:∀ᶠ w in l,‖z w‖≤K)(v:S.Field h)(converges:Tendsto (fun w=>S.project h (z w)) l (𝓝 v)):
    Tendsto (fun w:ℕ×ℕ=>moment (C.beta w.1 w.2) (fun U=>C.O w.1 w.2 (z w) 0 U*W.plot w.1 w.2 U))
      l (𝓝 (W.tester S h v)):=by
  let Q:=target (S:=S) W h
  let E (w:ℕ×ℕ):=(row W h w).toContinuousLinearMap-Q
  have van:Tendsto (fun w=>‖E w‖*|K|) l (𝓝 0):=by
    simpa only [E,Q,sub_self,norm_zero,zero_mul] using (((original F W h).mono_left le).sub_const Q).norm.mul_const |K|
  have error:Tendsto (fun w=>E w (z w)) l (𝓝 0):=by
    apply Metric.tendsto_nhds.mpr
    intro ε ep
    filter_upwards [van.eventually_lt_const ep,cap] with w small bound
    rw [dist_zero_right]
    exact ((E w).le_opNorm _).trans_lt ((mul_le_mul_of_nonneg_left (bound.trans (le_abs_self K))
      (ContinuousLinearMap.opNorm_nonneg _)).trans_lt small)
  have fixed:=((W.tester S h).toContinuousLinearMap.continuous.tendsto v).comp converges
  have total:=error.add fixed
  rw [zero_add] at total
  apply total.congr
  intro w
  change (row W h w (z w)-W.tester S h (S.project h (z w))) + W.tester S h (S.project h (z w))=_
  rw [sub_add_cancel]
  exact same C W (source C h w.1 w.2 (z w))

end YM.Integration.WilsonMacroscopicRichSingleWatch
