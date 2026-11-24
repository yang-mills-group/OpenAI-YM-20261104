import YM.Integration.WilsonRootedNonflatPreviousResponse
import YM.Integration.QLocalPhysicalPathKernel

/-! The complete old posterior and its two-copy centered price. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedPosteriorDifferences
open Filter Function Finset MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree
open Pressure Pressure.Testing Next.SectorChange Push.SectorMeasure
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open IterationFour IterationFour.Vacuum WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open scoped Topology BigOperators Classical
variable {X:Type*}[MeasurableSpace X](μ:Measure X)

def oscillation (w h:X→ℂ):ℂ:=∫u,(∫v,(w u-w v)*(h u-h v) ∂μ) ∂μ

theorem shift (w h:X→ℂ)(c k:ℂ):
    oscillation μ (fun u=>w u+c) (fun u=>h u+k)=oscillation μ w h:=by
  unfold oscillation
  simp only [add_sub_add_right_eq_sub]

theorem centered [IsProbabilityMeasure μ](w h:X→ℂ)(hw:Envelope w)(hh:Envelope h):
    oscillation μ w h=2*((∫u,w u*h u ∂μ)-(∫u,w u ∂μ)*(∫u,h u ∂μ)):=by
  let b:=∫u,h u ∂μ
  let a:=∫u,w u ∂μ
  let u:=∫z,w z*h z ∂μ
  have iw:=hw.integrableC μ
  have ih:=hh.integrableC μ
  have ip:Integrable (fun x=>w x*h x) μ:=(hw.mulC hh).integrableC μ
  have inner (x:X):(∫y,(w x-w y)*(h x-h y) ∂μ)=w x*h x - w x*b-h x*a+u:=by
    have exp (y:X):(w x-w y)*(h x-h y)=w x*h x - w x*h y - h x*w y + w y*h y:=by ring
    simp_rw [exp]
    have s1:Integrable (fun y=>w x*h x-w x*h y) μ:=(integrable_const _).sub (ih.const_mul _)
    have s2:Integrable (fun y=>w x*h x-w x*h y-h x*w y) μ:=s1.sub (iw.const_mul _)
    erw [integral_add s2 ip,
      integral_sub s1 (iw.const_mul _),
      integral_sub (integrable_const _) (ih.const_mul _),integral_const_mul,integral_const_mul,integral_const]
    simp [a,b,u,integral_const_mul]
  unfold oscillation
  simp_rw [inner]
  have s1:Integrable (fun x=>w x*h x-w x*b) μ:=ip.sub (iw.mul_const _)
  have s2:Integrable (fun x=>w x*h x-w x*b-h x*a) μ:=s1.sub (ih.mul_const _)
  erw [integral_add s2 (integrable_const _),
    integral_sub s1 (ih.mul_const _),integral_sub ip (iw.mul_const _),
    integral_mul_const,integral_mul_const,integral_const]
  simp [a,b,u]
  ring

variable {G:Gauge}{I:Type} [DecidableEq I]{Γ:Census I}(R:Run G)(d:LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "coarse" => R.family.side d.level d.period
local notation "fine" => R.family.side (d.level+1) d.period
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level

def law (V:Config G coarse):Measure (Config G fine):=
  ActualWilsonConditionalRoots.fibre R.family (N:=d.cutoff) (p:=d.period) (m:=d.level) V

theorem probability (V:Config G coarse):IsProbabilityMeasure (law R d V):=
  ActualWilsonConditionalRoots.probability R.family R.makes d.below V

theorem kernel (V:Config G coarse):QLocalPhysicalPathKernel.next R.family d.cutoff d.period d.level V=law R d V:=
  QLocalPhysicalPathKernel.held R.family R.makes d.below V

def relative (u:Config G fine→ℂ)(U:Config G fine):ℂ:=u U/((P).eval U:ℂ)

theorem admissible (u:Config G fine→ℂ)(hu:Envelope u):Envelope (relative R d u):=by
  have old:=Normal.actual R.family.path R.makes.wilson d.cutoff d.period (d.level+1) d.below
  change Envelope (fun U=>u U/((P).eval U:ℂ))
  simpa only [div_eq_mul_inv,Complex.ofReal_inv] using hu.mulC old.inv_env.ofReal_env

theorem amount (V:Config G coarse)(u:Config G fine→ℂ):
    (∫U,relative R d u U ∂law R d V)=(Δ).push (P).beta u V/((P₀).eval V:ℂ):=by
  rw [law,ActualWilsonConditionalRoots.average R.family R.makes d.below,actualAverage_push]
  have fields:(fun U:Config G fine=>(P).eval U • relative R d u U)=u:=by
    funext U
    have nz:((P).eval U:ℂ)≠0:=Complex.ofReal_ne_zero.mpr
      ((Normal.actual R.family.path R.makes.wilson d.cutoff d.period (d.level+1) d.below).positive U).ne'
    rw [Complex.real_smul,relative]
    field_simp
  rw [fields,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm]

theorem tilted (V:Config G coarse)(x:Config G fine→ℂ)(u:Config G fine→ℂ):
    (∫U,x U*relative R d u U ∂law R d V)=(Δ).push (P).beta (fun U=>x U*u U) V/((P₀).eval V:ℂ):=by
  rw [←amount R d V]
  apply integral_congr_ae
  filter_upwards with U
  unfold relative
  ring

end YM.Integration.WilsonRootedPosteriorDifferences
