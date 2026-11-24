import YM.Integration.WilsonRootedNonflatDye
import YM.Integration.ManuscriptQLocalAffineScalar

/-! On the curved healthy patch the genuine occupied site and every
uncentered prior mode are retained in the same measured moving Gaussian.
The identity holds as a germ, before choosing a derivative order. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedNonflatCurvedColumn
open Function Filter Finset MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree
open Matrix Pressure Pressure.Testing Pressure.Stores Next.SectorChange Push.SectorMeasure
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open AnalyticBridge.GaussianFieldAlignment
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G:Gauge}{I:Type} [DecidableEq I]{Γ:Census I}(R:Run G)(d:LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "Θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => Pressure.Testing.ships R.alloy.B d.cutoff d.level d.period
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "g" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "w" => R.kit.walls (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level)
local notation "fine" => R.family.side (d.level+1) d.period
local notation "E" => Gaussian.Vec (Raw G (R.family.side d.level d.period))

def Carried (D:Allocation G Δ Θ w)(q:Chi)(k:(Δ).Choices)(u:Config G fine→ℂ)(b:E):Prop:=
  ∀r:ℕ,iteratedFDeriv ℝ r (ManuscriptQLocalAffineScalar.stored R d D q k u) b=
    iteratedFDeriv ℝ r (ManuscriptQLocalAffineScalar.gaussian R d D q k u) b

/-- One common curved neighborhood works simultaneously for all old
rosters, all original modes, both singleton columns and the quiet value.
The earlier signed source may itself be a composite Wilson path. -/
theorem original (D:Allocation G Δ Θ w)(q:Chi)(k:(Δ).Choices):
    ∀ᶠ b:E in 𝓝 0,∀(incoming:Actual.Lit Γ (Config G fine)),Actual.Floor P incoming→
      ∀{Z:SeriesA G}{σ budget:ℝ},0<σ→Draw Z σ budget→∀a∈Z,∀o:Site fine,∀s:Γ.Mode,
      Carried R d D q k (Actual.atMark s incoming) b ∧
      Carried R d D q k (WilsonRootedNonflatDye.marked a g o (Actual.atMark s incoming)) b:=by
  filter_upwards [eventually_eventually_nhds.mpr (ManuscriptQLocalAffineScalar.positive_near R d k)] with b hb
  have read (u:Config G fine→ℂ)(hu:Envelope u):Carried R d D q k u b:=by
    have same:ManuscriptQLocalAffineScalar.stored R d D q k u =ᶠ[𝓝 b] ManuscriptQLocalAffineScalar.gaussian R d D q k u:=
      hb.mono fun y hy=>ManuscriptQLocalAffineScalar.column_at R d D q k y hy u hu
    exact fun r=>(same.iteratedFDeriv (𝕜:=ℝ) r).self_of_nhds
  intro incoming floor Z σ budget hs paid a ha o s
  have wax:=(WilsonRootedNonflatDye.guarded hs paid a ha g o).1
  exact ⟨read _ (floor.safe s),read _ (wax.ofReal_env.mulC (floor.safe s))⟩

end YM.Integration.WilsonRootedNonflatCurvedColumn
