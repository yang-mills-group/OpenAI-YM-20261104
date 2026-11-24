import YM.Integration.WilsonOriginalObservedRoseThermal
import YM.Integration.WilsonOriginalObservedRoseBornRatio

/-! At the original Wilson cutoffs a quadratically funded public error is small compared with the true kinetic coupling. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornHeat
open Function Filter Finset Set Metric Spec Extraction Table RG Lattice OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Wilson PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Precision FVA2 FVA2.Register Pert.Asymptotics
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonMaxwellThermometerSignedWallet
open MS MS.WilsonBridge.Coupling FVA2.Scale
open scoped Classical Topology
abbrev Visit:=ℝ×(ℕ×ℕ)
variable {G:Gauge}(R:Run G)(simple:G.Simple){B:ℕ}(hB:0<B)(pace:WilsonWindowReportingPace.Slow R.kit)
    (Z:WilsonPrescription G){fine index:ℝ→ℕ}
    (schedule:WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=simple) (B:=B) Z fine index)
    {f:Extraction.Order}{l:Ultrafilter (ℕ×ℕ)}(prior:(l:Filter _)≤f.fuse)
local notation "cut" => trail.curry (l:Filter (ℕ×ℕ))
local notation "gas" => WilsonMaxwellThermometerKineticFineRose.axis (R:=R) fine
local notation "unit" => WilsonMaxwellThermometerKineticLog.unit G

include simple in
theorem vanishes : Tendsto (unit) trail (𝓝 0):=by
  have pos:0<2*b0 G:=b0_normalizes (G:=G) ▸ G.slopeConstant_pos simple
  exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp (PhysMS.to_log_zoom.const_mul_atTop pos))

include hB pace schedule prior in
theorem original {γ:ℝ→ℝ}(measured:Coupling G γ):
    (∀ᶠw:Visit in cut,0<gas w ∧ ‖(gas w:ℂ)‖≤1) ∧
    Tendsto (fun w:Visit=>gas w) cut (𝓝 0) ∧
    Tendsto (fun w:Visit=>(γ w.1)^2/gas w) cut (𝓝 0):=by
  have dates:Tendsto (fun w:Visit=>w.1) cut trail:=by
    apply tendsto_def.mpr
    intro D hD
    have wide:∀ᶠr:ℝ in trail,r∈D:=hD
    exact eventually_curry_iff.mpr (wide.mono fun _ h=>Eventually.of_forall fun _=>h)
  have warm:∀ᶠw:Visit in cut,0<gas w:=by
    apply eventually_curry_iff.mpr
    exact Eventually.of_forall fun r=>((large_mesh f (fine r)).filter_mono prior).mono
      fun _ h=>inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson h))
  have pulse:=WilsonOriginalObservedRoseThermal.finite R Z simple hB pace schedule prior
  have normed:=WilsonOriginalObservedRoseThermal.actual R Z simple hB pace schedule prior γ measured
  have temp:∀ᶠw:Visit in cut,unit w.1≠0:=by
    filter_upwards [pulse.eventually_ne (one_ne_zero: (1:ℝ)≠0)] with w h using (div_ne_zero_iff.mp h).2
  have cool:Tendsto (fun w:Visit=>gas w) cut (𝓝 0):=by
    have small:=(vanishes (G:=G) simple).comp dates
    have product:=pulse.mul small
    rw [one_mul] at product
    exact product.congr' (temp.mono fun _ h=>div_mul_cancel₀ _ h)
  refine ⟨?_,cool,?_⟩
  · filter_upwards [warm,(tendsto_order.1 cool).2 1 zero_lt_one] with w h small
    exact ⟨h,by simpa only [Complex.norm_real,Real.norm_of_nonneg h.le] using small.le⟩
  · have product:=(normed.pow 2).mul cool
    rw [one_pow,one_mul] at product
    apply product.congr'
    filter_upwards [warm] with w h
    field_simp

end YM.Integration.WilsonOriginalObservedRoseBornHeat
