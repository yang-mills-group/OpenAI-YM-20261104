import YM.Integration.WilsonRootedNonflatPerturbation
import YM.Integration.WilsonRootedNonflatResponseDerivative
import YM.Integration.WilsonRootedHeldNonflat

/-! The genuine logarithmic joint response of two original occupied
colours when a prior site is given its own one-time infinitesimal weight. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedNonflatResponse
open Function Filter Finset MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree
open Matrix Pressure Pressure.Testing Pressure.Stores Next.SectorChange Push.SectorMeasure
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonRootedNonflatPerturbation
open scoped Topology BigOperators Classical
variable {G:Gauge}{I:Type} [DecidableEq I]{Γ:Census I}(R:Run G)(d:LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "Θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level
local notation "i₀" => R.alloy.B.a.clock.J d.level
local notation "i₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "w" => R.kit.walls i₁ i₀
local notation "coarse" => R.family.side d.level d.period
local notation "fine" => R.family.side (d.level+1) d.period

/-- Full original input, including its arbitrary deposited mixed entry.
The old-root insertion is measured at its authentic occupied fine site.
Both singleton terms are retained through the same physical normalization. -/
def Reading (D:Allocation G Δ Θ w)(q:Chi)(V:Config G coarse)(x:fieldDir G coarse 1)
    (incoming:Actual.Lit Γ (Config G fine))(a:PrismA G)(o:Site fine)
    (A B:I)(both:({A,B}:Finset I)∈Γ.choices):Prop:=
  let joint:Γ.Mode:=⟨{A,B},both⟩
  let normal:=((P₀).eval V:ℂ)
  let full:=weight R d D q V x incoming
  let old:=prior R d D q V x a o incoming
  let sample:=push R d V a o incoming
  HasDerivAt (fun t:ℂ=>
    sample joint t/sample Γ.quiet t-
      (sample (Γ.fire A) t/sample Γ.quiet t)*(sample (Γ.fire B) t/sample Γ.quiet t))
    (old joint/normal-(old Γ.quiet*full joint+old (Γ.fire A)*full (Γ.fire B)+
      old (Γ.fire B)*full (Γ.fire A))/normal^2+
      2*old Γ.quiet*full (Γ.fire A)*full (Γ.fire B)/normal^3) 0

theorem original (D:Allocation G Δ Θ w)(q:Chi)(V:Config G coarse)(x:fieldDir G coarse 1)
    (incoming:Actual.Lit Γ (Config G fine))(floor:Actual.Floor P incoming)
    {Z:SeriesA G}{σ b:ℝ}(hσ:0<σ)(wallet:Draw Z σ b)(a:PrismA G)(ha:a∈Z)
    (o:Site fine)(A B:I)(both:({A,B}:Finset I)∈Γ.choices):
    Reading R d D q V x incoming a o A B both:=by
  let full:=weight R d D q V x incoming
  let old:=prior R d D q V x a o incoming
  let joint:Γ.Mode:=⟨{A,B},both⟩
  have good:=WilsonRootedNonflatDye.quiet R d D q V x incoming floor
  have zero:full Γ.quiet=((P₀).eval V:ℂ):=good.1
  have nz:full Γ.quiet≠0:=zero.trans_ne (Complex.ofReal_ne_zero.mpr good.2.ne')
  have changed (s:Γ.Mode)(t:ℂ):
      push R d V a o incoming s t=WilsonRootedNonflatResponseDerivative.term (full s) (old s) t:=
    WilsonRootedNonflatPerturbation.original R d D q V x incoming floor hσ wallet a ha o s t
  unfold Reading
  simp_rw [changed]
  rw [←zero]
  exact WilsonRootedNonflatResponseDerivative.signed (full Γ.quiet) (full (Γ.fire A)) (full (Γ.fire B))
    (full joint) (old Γ.quiet) (old (Γ.fire A)) (old (Γ.fire B)) (old joint) nz

/-- A concrete healthy held field with one genuinely nonzero curvature
tests precisely this original signed column and its matching prior site. -/
theorem nonflat (simple:G.Simple)(size:2≤(coarse).val){θ:ℝ}(hθ:0<θ)
    (D:Allocation G Δ Θ w)(q:Chi)(x:fieldDir G coarse 1)
    (incoming:Actual.Lit Γ (Config G fine))(floor:Actual.Floor P incoming)
    {Z:SeriesA G}{σ b:ℝ}(hσ:0<σ)(wallet:Draw Z σ b)(a:PrismA G)(ha:a∈Z)
    (o:Site fine)(A B:I)(both:({A,B}:Finset I)∈Γ.choices):
    ∃u:G.El,G.curvature (faceValue (WilsonRootedHeldNonflat.needle coarse u)
        (WilsonRootedHeldNonflat.selected coarse))≠0 ∧
      flags θ (WilsonRootedHeldNonflat.needle coarse u)=∅ ∧
      Reading R d D q (WilsonRootedHeldNonflat.needle coarse u) x incoming a o A B both:=by
  obtain ⟨u,hp,hc⟩:=WilsonRootedHeldNonflat.original simple coarse size hθ
  exact ⟨u,hp,hc,original R d D q _ x incoming floor hσ wallet a ha o A B both⟩

end YM.Integration.WilsonRootedNonflatResponse
