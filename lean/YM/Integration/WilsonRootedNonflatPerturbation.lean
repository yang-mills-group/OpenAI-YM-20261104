import YM.Integration.WilsonRootedNonflatDye

/-! The incoming source with a single square-zero distinguished prior
vertex is propagated before its quiet division, on the actual density. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedNonflatPerturbation
open Function Filter Finset MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree
open Matrix Pressure Pressure.Testing Pressure.Stores Next.SectorChange Push.SectorMeasure
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open scoped Topology BigOperators Classical
variable {G:Gauge}
section density
variable {c f:Side}{S:StepData c f}{β:ℝ}(h:S.IsKernel β G)(V:Config G c)

include h in
/-- Affine insertion in an honest Step integral, before any subtraction
or normalization. The original density is independent of this new label. -/
theorem linear (u v:Config G f→ℂ)(hu:Envelope u)(hv:Envelope v)(t:ℂ):
    S.push β (fun U=>u U+t*v U) V=S.push β u V+t*S.push β v V:=by
  have su:=StepData.push_slice h V u (hu.integrableC _)
  have sv:=StepData.push_slice h V v (hv.integrableC _)
  unfold StepData.push
  calc
    _=∫ U,S.density β U V • u U+t*(S.density β U V • v U) ∂prior G f:=by
      apply integral_congr_ae
      filter_upwards with U
      simp only [Complex.real_smul]
      ring
    _=_:=by rw [integral_add su (sv.const_mul _),integral_const_mul]
end density

variable {I:Type} [DecidableEq I]{Γ:Census I}(R:Run G)(d:LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "Θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "g" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "i₀" => R.alloy.B.a.clock.J d.level
local notation "i₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "w" => R.kit.walls i₁ i₀
local notation "coarse" => R.family.side d.level d.period
local notation "fine" => R.family.side (d.level+1) d.period

def push (V:Config G coarse)(a:PrismA G)(o:Site fine)
    (incoming:Actual.Lit Γ (Config G fine))(s:Γ.Mode)(t:ℂ):ℂ:=
  (Δ).push (P).beta (fun U=>Actual.atMark s incoming U+
    t*WilsonRootedNonflatDye.marked a g o (Actual.atMark s incoming) U) V

def weight (D:Allocation G Δ Θ w)(q:Chi)(V:Config G coarse)(x:fieldDir G coarse 1)
    (incoming:Actual.Lit Γ (Config G fine))(s:Γ.Mode):ℂ:=
  WilsonRootedNonflatLog.sum R d D q V x (Actual.atMark s incoming)

def prior (D:Allocation G Δ Θ w)(q:Chi)(V:Config G coarse)(x:fieldDir G coarse 1)
    (a:PrismA G)(o:Site fine)(incoming:Actual.Lit Γ (Config G fine))(s:Γ.Mode):ℂ:=
  WilsonRootedNonflatLog.sum R d D q V x (WilsonRootedNonflatDye.marked a g o (Actual.atMark s incoming))

/-- For every original marked and quiet mode, the entire density with
this single occurrence uses the fixed prescribed Gaussian and its
same-material signed score, at the same free keys and held exterior. -/
theorem original (D:Allocation G Δ Θ w)(q:Chi)(V:Config G coarse)(x:fieldDir G coarse 1)
    (incoming:Actual.Lit Γ (Config G fine))(floor:Actual.Floor P incoming)
    {Z:SeriesA G}{σ budget:ℝ}(hσ:0<σ)(wallet:Draw Z σ budget)(a:PrismA G)(ha:a∈Z)
    (o:Site fine)(s:Γ.Mode)(t:ℂ):
    push R d V a o incoming s t=weight R d D q V x incoming s+t*prior R d D q V x a o incoming s:=by
  have h:=WilsonRootedNonflatDye.source R d D q V x incoming floor hσ wallet a ha o s
  have pay:=((WilsonRootedNonflatDye.guarded hσ wallet a ha g o).1.ofReal_env).mulC (floor.safe s)
  unfold push weight prior
  rw [h.1,h.2]
  exact linear (R.family.path.levels.transition_mass d.level d.period (P).beta) V _ _
    (floor.safe s) pay t

end YM.Integration.WilsonRootedNonflatPerturbation
