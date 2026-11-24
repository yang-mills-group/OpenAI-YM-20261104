import YM.Integration.WilsonOriginalObservedRoseOrders

/-! The continuum reading and the kinetic parameter of each actual UV board use
the same physical one-loop unit. No fixed-length limit of the latter is needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseThermal
open Function Filter Set Spec Extraction RG Lattice OPE OPE.Orbits RG17 Wilson PhysicalNext.Repeat.Legato
open PhysMS PhysMS.Frame FVA2 FVA2.Register Pert.Asymptotics Climb Trace Trace.Pilot Next.UVStress
open WilsonOriginalObservedRoseLedger (Visit)
open scoped Classical Topology
variable {G:Gauge}(R:Run G)(Z:WilsonPrescription G)(simple:G.Simple){B:ℕ}(hB:0<B)(pace:WilsonWindowReportingPace.Slow R.kit)
    {fine index:ℝ→ℕ}(enrolled:WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=simple) (B:=B) Z fine index)
    {f:Extraction.Order}{Y:Ultrafilter (ℕ×ℕ)}(prior:(Y:Filter _)≤f.fuse)
local notation "cut" => trail.curry (Y:Filter (ℕ×ℕ))
local notation "g" => WilsonMaxwellThermometerKineticFineRose.axis (R:=R) fine
local notation "ref" => WilsonMaxwellThermometerKineticLog.unit G

include hB pace enrolled prior in
theorem finite : Tendsto (fun w:Visit=>g w/ref w.1) cut (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε pos
  apply eventually_curry_iff.mpr
  filter_upwards [WilsonMaxwellThermometerKineticUpper.original R simple hB pace Z enrolled pos] with r selected
  filter_upwards [(large_mesh f (fine r)).filter_mono prior] with w eligible
  exact selected w.1 w.2 eligible

include hB pace enrolled prior in
theorem actual (t:ℝ→ℝ)(paid:Coupling G t) :
    Tendsto (fun w:Visit=>t w.1/g w) cut (𝓝 1) := by
  have native:=finite R Z simple hB pace enrolled prior
  have higher:=WilsonMaxwellThermometerKineticLog.running simple paid
  have down:Tendsto (Prod.fst:Visit→ℝ) cut trail:=tendsto_fst.mono_left Filter.curry_le_prod
  have result:=(higher.comp down).div native (show (1:ℝ)≠0 from one_ne_zero)
  rw [div_one] at result
  refine result.congr' ?_
  filter_upwards [native.eventually_ne (show (1:ℝ)≠0 from one_ne_zero)] with w retained
  have unitLive:ref w.1≠0:=by
    intro zero
    exact retained (by simp only [zero,div_zero])
  change (t w.1/ref w.1)/(g w/ref w.1)=_
  field_simp

end YM.Integration.WilsonOriginalObservedRoseThermal
