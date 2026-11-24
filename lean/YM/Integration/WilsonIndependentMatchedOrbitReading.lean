import YM.Integration.WilsonIndependentMatchedPairResponse
import YM.FVA2.BareOrb

/-! The dated independent inversion integrand and the conventional elected
tree use the same complete finite orbital Haar quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedOrbitReading
open Function MeasureTheory Lattice Wilson Gauge PertExtension PertExtension.Chart
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Laplace XSpace
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge}{n:Side}

def originalClock : Scale:=⟨fun _=>1,rfl,contDiffAt_const,measurable_const,fun _=>zero_le_one⟩

def insert (O:Config G n→ℝ):Hook G Empty (Orb.OEdge n):=fun _ u _=>O (Orb.liftLinks u)

theorem whole (O:Config G n→ℝ)(N:Scale)(α:ℝ→ℝ)(same:∀t,N.beta t=(α t)⁻¹^2)
    (t:ℝ):rightSum (startO N) (insert O) t=Orb.preNum O (t*α t) := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  rw [head]
  change O (Orb.liftLinks u)*Real.exp (-(N.beta t*(energy (Orb.liftLinks u)/2))/t^2) =
      O (Orb.liftLinks u)*Real.exp (-(energy (Orb.liftLinks u)/2)/(t*α t)^2)
  rw [same]
  congr 2
  simp only [mul_pow, div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

theorem normalized (O:Config G n→ℝ)(N:Scale)(α:ℝ→ℝ)(same:∀t,N.beta t=(α t)⁻¹^2):
    goal N (insert O)=fun t=>Orb.preExpectation O (t*α t) := by
  funext t
  change rightSum (startO N) (insert O) t / rightSum (startO N) (insert (1:Config G n→ℝ)) t = _
  rw [whole O N α same,whole (1:Config G n→ℝ) N α same]
  rfl

/-- On the unreset finite Wilson coupling, every coefficient agrees, on the
specified tree and original fields. This also determines the scalar. -/
theorem diagram {R:XSpace.Period}(T:R.Tree)(O:Config G R.side→ℝ)(h:Orb.PreTest O)
    (allowed:Plan G R.side (insert O)):
    Bare.normalized T G (FVA2.BareOrb.stencil T O)=
      FVA2.TaylorWick.into (PowerSeries.mk (storyPT originalClock (insert O))) := by
  have formula:=Orb.before_tree_formula (even_iff_two_dvd.mpr R.even) (Orb.traySpec G) h
  have emitted:=top_truth originalClock (insert O) (even_iff_two_dvd.mpr R.even) allowed
  rw [normalized O originalClock 1 (fun t=>by simp [originalClock])] at emitted
  simp only [Pi.one_apply,mul_one] at emitted
  rw [FVA2.BareOrb.diagram_eq T h,emitted.unique formula]
  rfl

end YM.Integration.WilsonIndependentMatchedOrbitReading
end
