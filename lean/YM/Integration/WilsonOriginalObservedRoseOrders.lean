import YM.Integration.WilsonOriginalObservedRoseLedger
import YM.Integration.WilsonOriginalObservedRoseKineticGround

/-! Spend the seven original signed badge prices in the native order of cutoffs.
The reference unit is fixed at each physical length before either cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseOrders

open Function Filter Finset Set Metric Spec Extraction Table RG Lattice OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Wilson PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Precision FVA2 FVA2.Register Pert.Asymptotics
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Photo
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonMaxwellThermometerSignedWallet
open WilsonMaxwellThermometerOriginal (lower)
open WilsonOriginalObservedRoseLedger (Visit due)
open scoped Classical Topology BigOperators

variable {G:Gauge}(R:Run G)(D:ChartRatio G)(Z:WilsonPrescription G)
    {f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)(A:ℝ→Group R.family 6)
    (fine:ℝ→ℕ)
local notation "g" => WilsonMaxwellThermometerKineticFineRose.axis (R:=R) fine
local notation "ref" => WilsonMaxwellThermometerKineticLog.unit G

def settled (mesh:ℝ→Mesh)(v:Visit→∀i,Axes R i)(u:Visit→Sec G 6)(P Q:Visit→Module.End ℂ (Sec G 4)) : Prop :=
  ∀ε:ℝ,0<ε → ∀ᶠ r in trail,f.late fun N per=>∀s:Finset (Fin 3), s.Nonempty →
    ‖due R D Z.scheme Z.criterion F J A mesh v u (fun w=>P w (lower G)) (fun w=>Q w (lower G)) g (r,N,per) s‖ ≤ ε*ref r

variable (simple:G.Simple){B:ℕ}(hB:0<B)(pace:WilsonWindowReportingPace.Slow R.kit){index:ℝ→ℕ}
    (schedule:WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=simple) (B:=B) Z fine index)
    {Y:Ultrafilter (ℕ×ℕ)}(prior:(Y:Filter _)≤f.fuse)
local notation "cut" => trail.curry (Y:Filter (ℕ×ℕ))

include hB pace schedule prior in
theorem original (mesh:ℝ→Mesh)(v:Visit→∀i,Axes R i)(u:Visit→Sec G 6)(P Q:Visit→Module.End ℂ (Sec G 4))
    (paid:settled R D Z F J A fine mesh v u P Q) (s:Finset (Fin 3))(non:s.Nonempty) :
    Tendsto (fun w=> due R D Z.scheme Z.criterion F J A mesh v u (fun t=>P t (lower G)) (fun t=>Q t (lower G))
        g w s/(g w:ℂ)) cut (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε pos
  have thermal:=WilsonMaxwellThermometerKineticUpper.original R simple hB pace Z schedule (show (0:ℝ)<1/2 by norm_num)
  apply eventually_curry_iff.mpr
  filter_upwards [paid (ε/4) (by positivity),thermal] with r original wallet
  let quote := fun z:ℕ×ℕ=>∀s:Finset (Fin 3),s.Nonempty →
    ‖due R D Z.scheme Z.criterion F J A mesh v u (fun w=>P w (lower G)) (fun w=>Q w (lower G)) g (r,z) s‖ ≤ ε/4*ref r
  have actual:=((Extraction.Order.fused f quote).mpr original).filter_mono prior
  filter_upwards [actual,(large_mesh f (fine r)).filter_mono prior] with z input live
  let t:=g (r,z)
  have hot:0<t:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson live))
  have spot:=abs_lt.mp (wallet z.1 z.2 live)
  change -(1/2:ℝ)<t/ref r-1 ∧ t/ref r-1<1/2 at spot
  have net:0<t/ref r:=by linarith [spot.1]
  have valid:0<ref r:=(div_pos_iff.mp net).elim And.right (fun bad=>(hot.not_gt bad.1).elim)
  have lower:ref r<2*t:=by
    have insurance:(1/2:ℝ)<t/ref r:=by linarith [spot.1]
    linarith [(lt_div_iff₀ valid).mp insurance]
  rw [dist_zero_right,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hot]
  apply (div_lt_iff₀ hot).mpr
  refine (input s non).trans_lt ?_
  nlinarith [mul_lt_mul_of_pos_left lower (show 0<ε/4 by positivity),
    mul_pos pos hot]

end YM.Integration.WilsonOriginalObservedRoseOrders
