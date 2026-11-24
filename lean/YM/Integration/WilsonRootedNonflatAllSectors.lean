import YM.Integration.WilsonRootedNonflatLog
import YM.Integration.WilsonRootedNonflatCurvedColumn
import YM.Integration.WilsonRootedNonflatAppointment

/-! In the full original kernel only the no-hole sector uses the moving
positive Gaussian. Every rough sector has its original deposited source,
forest, tag and exterior and the full fixed reference change. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedNonflatAllSectors
open Function Filter Finset MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree
open Matrix Pressure Pressure.Testing Pressure.Stores Next.SectorChange Push.SectorMeasure
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open IterationFour IterationFour.Vacuum AnalyticBridge.GaussianFieldAlignment
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open FreeResolvent.Affine
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{I:Type} [DecidableEq I]{Γ:Census I}(R:Run G)(d:LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "Θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "fine" => R.family.side (d.level+1) d.period
local notation "coarse" => R.family.side d.level d.period
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level
local notation "g" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "w" => R.kit.walls (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level)
local notation "E" => Gaussian.Vec (Raw G coarse)

def reading (D:Allocation G Δ Θ w)(q:Chi)(B:E)(u:Config G fine→ℂ):ℂ:=
  ∑ A:Stores Δ,∑ k:(Δ).Choices, if A=noHole Δ then
    ManuscriptQLocalAffineScalar.gaussian R d D q k u B else
    WilsonRootedNonflatReference.full R d D q A k (represent (decode B)) (g⁻¹ • decode B) u

theorem original (D:Allocation G Δ Θ w)(q:Chi):
    ∀ᶠ B:E in 𝓝 0,∀(u:Config G fine→ℂ),Envelope u→GaugeInvariant u→
      reading R d D q B u=(Δ).push (P).beta u (represent (decode B)):=by
  have common:∀ᶠ B:E in 𝓝 0,∀k:(Δ).Choices,
      (PhysicalAffineScalarUncut.gram (Pressure.Testing.ships R.alloy.B d.cutoff d.level d.period)
        Θ k d.forest B).PosDef:=eventually_all.mpr fun k=>ManuscriptQLocalAffineScalar.positive_near R d k
  filter_upwards [common] with B allB
  intro u hu inv
  rw [←WilsonRootedNonflatLog.measured R d D q _ (g⁻¹ • decode B) u hu inv,reading,WilsonRootedNonflatLog.sum]
  apply Finset.sum_congr rfl
  intro A _
  apply Finset.sum_congr rfl
  intro k _
  split
  next h=>
    subst A
    have stored:=ManuscriptQLocalAffineScalar.column_at R d D q k B (allB k) u hu
    exact stored.symm.trans (WilsonRootedNonflatReference.whole R d D q (noHole Δ) k _ _ u hu)
  next _=>rfl

theorem nonflat (D:Allocation G Δ Θ w)(q:Chi)(simple:G.Simple)(size:2≤(coarse).val)
    {θ:ℝ}(hθ:0<θ):
    ∃ B:E,G.curvature (faceValue (represent (decode B)) (WilsonRootedHeldNonflat.selected (coarse)))≠0 ∧
      flags θ (represent (decode B))=∅ ∧
      (∀(u:Config G fine→ℂ),Envelope u→GaugeInvariant u→
        reading R d D q B u=(Δ).push (P).beta u (represent (decode B))) ∧
      ∀{s:ℝ},s≠0→Integral.sample s (s⁻¹ • decode B)=represent (decode B):=by
  obtain ⟨B,h₁,h₂,h₃,h₄⟩:=WilsonRootedNonflatAppointment.original (coarse) simple size hθ _ (original R d D q)
  exact ⟨B,h₃,h₂,h₁,h₄⟩

end YM.Integration.WilsonRootedNonflatAllSectors
