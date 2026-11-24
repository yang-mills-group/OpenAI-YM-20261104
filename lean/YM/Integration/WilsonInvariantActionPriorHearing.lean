import YM.Integration.WilsonInvariantActionConditionalRegistered
import YM.Integration.SelectedCofactorLocalProjection

/-! First variation of the connected measured pair under the full earlier Wilson
prior. The incoming signed insertion may depend jointly on the retained and fresh gauges. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionPriorHearing
open Function Filter Finset MeasureTheory Lattice Wilson RG RG.Shoot OPE.Therm
open PhysicalNext.Repeat.Legato PhysicalWilsonConditionalRestriction
open WilsonInvariantActionConditionalMarginal
open scoped Classical Topology BigOperators

universe u
def readings (X:Type u) [MeasurableSpace X] : Subalgebra ℝ (X→ℝ) where
  carrier:={f|Envelope f}
  mul_mem' :=fun hf hg=>hf.mul hg
  zero_mem' :=Envelope.const 0
  one_mem' :=Envelope.const 1
  add_mem' :=fun hf hg=>hf.add hg
  algebraMap_mem' :=fun r=>Envelope.const r

private def charge {X:Type u} [MeasurableSpace X] (μ:Measure X) [IsFiniteMeasure μ] :
    readings X →ₗ[ℝ] ℝ where
  toFun f:=∫x,f.val x ∂μ
  map_add' f h:=integral_add (f.property.integrable μ) (h.property.integrable μ)
  map_smul' r f:=by exact integral_const_mul r _

variable {G:Gauge} (R:Run G) {N p m:ℕ}
local notation "fine" => Config G (R.family.side (m+1) p)
local notation "coarse" => Config G (R.family.side m p)
local notation "Ω" => (coarse×fine)
local notation "κ" => ActualWilsonConditionalRoots.fibre R.family (N:=N)
local notation "μ" => scene R.family.path N p m

private theorem section_envelope (f:readings Ω) (V:coarse):Envelope (fun U:fine=>f.val (V,U)):=by
  exact ⟨f.property.meas.comp (measurable_const.prodMk measurable_id), f.property.cost.choose,
    fun U=>f.property.cost.choose_spec (V,U)⟩

private theorem deposited (live:m<N) (f:readings Ω):
    Envelope (fun V:coarse=>∫U,f.val (V,U) ∂κ V):=by
  let den:=actualConditionalDensity R.family N p m
  have hden:=ActualWilsonConditionalRoots.density_meas R.family (p:=p) R.makes live
  have named(V:coarse):(∫U,f.val (V,U) ∂κ V)=∫U,den V U*f.val (V,U) ∂prior G _:=by
    rw [ActualWilsonConditionalRoots.average R.family R.makes live V]
    rfl
  refine ⟨?_,f.property.cost.choose,?_⟩
  · simp only [named]
    exact (hden.mul f.property.meas).stronglyMeasurable.integral_prod_right'.measurable
  · intro V
    letI:=ActualWilsonConditionalRoots.probability R.family R.makes live V
    have sec:=(section_envelope R f V).integrable (κ V)
    calc
      ‖∫U,f.val (V,U) ∂κ V‖≤∫U,‖f.val (V,U)‖ ∂κ V:=norm_integral_le_integral_norm _
      _≤∫_:fine,f.property.cost.choose ∂κ V:=integral_mono sec.norm (integrable_const _)
        (fun U=>f.property.cost.choose_spec (V,U))
      _=f.property.cost.choose:=by simp

def conditional (live:m<N):readings Ω →ₗ[ℝ] readings coarse where
  toFun f:=⟨fun V=>∫U,f.val (V,U) ∂κ V,deposited R live f⟩
  map_add' f h:=by
    apply Subtype.ext
    funext V
    letI:=ActualWilsonConditionalRoots.probability R.family R.makes live V
    exact integral_add ((section_envelope R f V).integrable _) ((section_envelope R h V).integrable _)
  map_smul' r f:=by
    apply Subtype.ext
    funext V
    exact integral_const_mul r _

def earlier (live:m<N):readings coarse →ₗ[ℝ] ℝ:=by
  letI:IsProbabilityMeasure μ:=probability R.makes.wilson live.le
  exact charge μ

def joint (live:m<N):readings Ω →ₗ[ℝ] ℝ:=
  (earlier R (p:=p) live).comp (conditional R live)

def covariance {X Y:Type*} [CommRing X] [CommRing Y] (E:X→Y) (f h:X):Y:=E (f*h)-E f*E h

def cubic {X Y:Type*} [CommRing X] [CommRing Y] (E:X→Y) (f h w:X):Y:=
  E (f*h*w)-E (f*h)*E w-E (f*w)*E h-E (h*w)*E f+
    E f*E h*E w+E f*E h*E w

def reweighted {X:Type*} [CommRing X] (E:X→ℝ) (w:X) (t:ℝ) (x:X):ℝ:=(E x+t*E (x*w))/(1+t*E w)

set_option backward.isDefEq.respectTransparency false in
private theorem first {X:Type*} [CommRing X] (E:X→ℝ) (f h w:X):
    HasDerivAt (fun t:ℝ=>covariance (reweighted E w t) f h) (cubic E f h w) 0:=by
  have each(x:X):HasDerivAt (fun t:ℝ=>reweighted E w t x) (covariance E x w) 0:=by
    have num : HasDerivAt (fun t:ℝ=>E x+t*E (x*w)) (E (x*w)) 0 := by
      convert (((hasDerivAt_id (0:ℝ)).mul_const (E (x*w))).const_add (E x)) using 1 <;> first | rfl | simp
    have den : HasDerivAt (fun t:ℝ=>1+t*E w) (E w) 0 := by
      convert (((hasDerivAt_id (0:ℝ)).mul_const (E w)).const_add (1:ℝ)) using 1 <;> first | rfl | simp
    simpa only [Pi.div_def,reweighted,covariance,zero_mul,add_zero,one_pow,mul_one,div_one] using num.div den (by norm_num)
  have product:=(each (f*h)).sub ((each f).mul (each h))
  convert product using 1 <;> first | rfl | (simp [reweighted,covariance,cubic]; ring)

private theorem five {X Y:Type*} [CommRing X] [CommRing Y] [Algebra ℝ X] [Algebra ℝ Y]
    (E:Y→ₗ[ℝ]ℝ) (I:X→ₗ[ℝ]Y) (f h w:X):
    cubic (E.comp I) f h w = covariance E (I w) (covariance I f h) + cubic E (I w) (I f) (I h) +
      E (cubic I f h w) + covariance E (I f) (covariance I h w) + covariance E (I h) (covariance I f w):=by
  simp only [cubic,covariance,LinearMap.comp_apply,mul_sub,map_sub,map_add]
  simp only [mul_left_comm,mul_comm]
  ring

/-- The two changed earlier-vacuum terms and the three terms born on the true conditional. -/
theorem original (live:m<N) (f h w:readings Ω):
    let I:=conditional R live
    let E:=earlier R (p:=p) live
    HasDerivAt (fun t:ℝ=>covariance (reweighted (joint R (p:=p) live) w t) f h)
      (covariance E (I w) (covariance I f h) + cubic E (I w) (I f) (I h) +
       E (cubic I f h w) + covariance E (I f) (covariance I h w) + covariance E (I h) (covariance I f w)) 0:=by
  intro I E
  rw [←five E I f h w]
  exact first (joint R live) f h w

end YM.Integration.WilsonInvariantActionPriorHearing
