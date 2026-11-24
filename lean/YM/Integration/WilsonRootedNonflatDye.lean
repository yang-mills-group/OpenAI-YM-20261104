import YM.Integration.WilsonRootedNonflatLog
import YM.Integration.WilsonPhysicalHistoryRetainedSpringSite

/-! One present prior vertex with its actual two-sided colour paths and
the full retained marked density, on the original compact field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedNonflatDye
open Function Filter Finset MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree
open Matrix Pressure Pressure.Testing Pressure.Stores Next.SectorChange Push.SectorMeasure
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open scoped Topology BigOperators Classical
variable {G:Gauge} {n:Side}

/-- The sign and physical order are those of an insertion of a member
of the submitted earlier action in its negative exponential. The root
is retained while the torus orientations are averaged. -/
def vertex (a:PrismA G)(g:ℝ)(o:Site n)(U:Config G n):ℝ:=
  -(g^(a.grade-a.rise))*OriginalMarkedRunAction.sitePacket a.cells o U

theorem guarded {Z:SeriesA G}{σ b:ℝ}(hσ:0<σ)(wallet:Draw Z σ b)
    (a:PrismA G)(ha:a∈Z)(g:ℝ)(o:Site n):
    Envelope (vertex a g o) ∧ GaugeInvariant (vertex a g o):=by
  have fee:=wallet.2 a ha
  obtain ⟨hm,hb⟩:=OriginalMarkedRunAction.site_packet a.cells hσ fee.toll o
  have bounded:Envelope (OriginalMarkedRunAction.sitePacket a.cells o):=⟨hm,_,hb⟩
  refine ⟨(Envelope.const _).mul bounded,?_⟩
  intro h U
  have coil (s:Signed)(i:ℕ):
      (a.cells i).unmasked (pull s 0 (gauge h U)) o=(a.cells i).unmasked (pull s 0 U) o:=by
    rw [Work.F05.pull_gauge_zero]
    unfold Atom.unmasked
    simp only [Work.F05.slot_gauge]
    exact fee.hue i ..
  unfold vertex OriginalMarkedRunAction.sitePacket
  simp only [coil]

variable {I:Type} [DecidableEq I] {Γ:Census I}(R:Run G)(d:LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "Θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level
local notation "g" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "i₀" => R.alloy.B.a.clock.J d.level
local notation "i₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "w" => radiusW R.kit.rider i₁ i₀
local notation "W" => R.kit.walls i₁ i₀
local notation "coarse" => R.family.side d.level d.period
local notation "fine" => R.family.side (d.level+1) d.period

def marked (a:PrismA G)(c:ℝ)(o:Site n)(u:Config G n→ℂ)(U:Config G n):ℂ:=
  (vertex a c o U:ℂ)*u U

/-- The prior dye is applied to all modes of an actual incoming floor.
In particular its joint mode does not factor into its two singleton modes. -/
theorem source (D:Allocation G Δ Θ W)(q:Chi)(V:Config G coarse)(x:fieldDir G coarse 1)
    (incoming:Actual.Lit Γ (Config G fine))(floor:Actual.Floor P incoming)
    {Z:SeriesA G}{σ budget:ℝ}(hσ:0<σ)(wallet:Draw Z σ budget)(a:PrismA G)(ha:a∈Z)
    (root:Site fine)(s:Γ.Mode):
    WilsonRootedNonflatLog.sum R d D q V x (Actual.atMark s incoming)=(Δ).push (P).beta (Actual.atMark s incoming) V ∧
    WilsonRootedNonflatLog.sum R d D q V x (marked a g root (Actual.atMark s incoming))=
      (Δ).push (P).beta (marked a g root (Actual.atMark s incoming)) V:=by
  have hi:GaugeInvariant (Actual.atMark s incoming):=fun k U=>congrArg (fun p:Poly Γ=>p.part s) (floor.gauges k U)
  obtain ⟨pay,hv⟩:=guarded hσ wallet a ha g root
  exact ⟨WilsonRootedNonflatLog.measured R d D q V x _ (floor.safe s) hi,
    WilsonRootedNonflatLog.measured R d D q V x _ (pay.ofReal_env.mulC (floor.safe s))
      (fun k U=>by unfold marked; rw [hv k U,hi k U])⟩

/-- The quiet normalization for the actual signed field is nonzero, on
each coarse compact field, including fields of nonzero curvature. -/
theorem quiet (D:Allocation G Δ Θ W)(q:Chi)(V:Config G coarse)(x:fieldDir G coarse 1)
    (incoming:Actual.Lit Γ (Config G fine))(floor:Actual.Floor P incoming):
    WilsonRootedNonflatLog.sum R d D q V x (Actual.atMark Γ.quiet incoming)=((P₀).eval V:ℂ) ∧
      0<(P₀).eval V:=by
  have hpos:=(Normal.actual R.family.path R.makes.wilson d.cutoff d.period d.level d.below.le).positive V
  refine ⟨?_,hpos⟩
  have hi:GaugeInvariant (Actual.atMark Γ.quiet incoming):=fun k U=>congrArg (fun p:Poly Γ=>p.part Γ.quiet) (floor.gauges k U)
  rw [WilsonRootedNonflatLog.measured R d D q V x _ (floor.safe Γ.quiet) hi]
  have hv:Actual.atMark Γ.quiet incoming=fun U=>((P).eval U:ℂ):=funext floor.vacancy
  change (Δ).push (P).beta (Actual.atMark Γ.quiet incoming) V=_
  rw [hv]
  change (∫U,(Δ).density (P).beta U V • ((P).eval U:ℂ) ∂prior G fine)=_
  simp_rw [Complex.real_smul,←Complex.ofReal_mul]
  rw [integral_complex_ofReal]
  congr 1
  exact (congrFun (R.makes.wilson.steps d.cutoff d.period d.level d.below).1 V).symm

end YM.Integration.WilsonRootedNonflatDye
