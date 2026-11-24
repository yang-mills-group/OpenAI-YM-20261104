import YM.Integration.WilsonInvariantActionRegisteredHearing
import YM.Integration.WilsonRegisteredActionOccurrence

/-! First variation of the normalized, exponentially reweighted earlier Wilson
law. The original conditional and exterior expectations remain in all five terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionExponentialHearing
open Function Set MeasureTheory Filter Lattice Wilson RG OPE.Therm PhysicalNext.Repeat.Legato
open WilsonInvariantActionPriorHearing WilsonInvariantActionRegisteredHearing
open scoped Topology Classical BigOperators

variable {X:Type*} [MeasurableSpace X]

private def cap (f:readings X):ℝ:=|f.property.cost.choose|
private theorem within (f:readings X) (x:X):‖f.val x‖≤cap f:=
  (f.property.cost.choose_spec x).trans (le_abs_self _)

def weighted (w:readings X) (t:ℝ) (f:readings X):readings X:=by
  refine ⟨fun x=>Real.exp (t*w.val x)*f.val x,⟨(Real.measurable_exp.comp (measurable_const.mul w.property.meas)).mul f.property.meas,?_⟩⟩
  refine ⟨Real.exp (|t| *cap w)*cap f,fun x=>?_⟩
  rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul _ (within f x) (norm_nonneg _) (Real.exp_pos _).le
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left (within w x) (abs_nonneg t)))

variable {G:Gauge} (R:Run G) {N p m:ℕ}
local notation "fine" => Config G (R.family.side (m+1) p)
local notation "coarse" => Config G (R.family.side m p)
local notation "Ω" => (coarse×fine)
local notation "κ" => ActualWilsonConditionalRoots.fibre R.family (N:=N)
local notation "μ₀" => scene R.family.path N p m

private theorem bound (live:m<N) (f:readings Ω) (b:ℝ) (hf:∀x,‖f.val x‖≤b):
    ‖joint R live f‖≤b:=by
  letI:IsProbabilityMeasure μ₀:=probability R.makes.wilson live.le
  change ‖∫ V,∫U,f.val (V,U) ∂κ V ∂μ₀‖≤b
  suffices h:∀V:coarse,‖∫U,f.val (V,U) ∂κ V‖≤b by
    simpa using (norm_integral_le_of_norm_le_const (μ:=μ₀) (Filter.Eventually.of_forall h))
  intro V
  letI:=ActualWilsonConditionalRoots.probability R.family R.makes live V
  simpa using (norm_integral_le_of_norm_le_const (μ:=κ V) (Filter.Eventually.of_forall (fun U=>hf (V,U))))


private theorem moment (live:m<N) (w f:readings Ω):
    HasDerivAt (fun t:ℝ=>joint R live (weighted w t f)) (joint R live (f*w)) 0:=by
  let E:=joint (p:=p) R live
  let C:=cap w^2*cap f
  have nc:0≤C:=mul_nonneg (sq_nonneg _) (abs_nonneg _)
  have nw:0≤cap w:=abs_nonneg _
  have at_zero:weighted w 0 f=f:=by apply Subtype.ext;funext x;simp [weighted]
  rw [hasDerivAt_iff_tendsto_slope_zero]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ:=min (1/(cap w+1)) (ε/(C+1))
  have hδ:0<δ:=lt_min (div_pos zero_lt_one (by linarith)) (div_pos hε (by linarith))
  have size:∀ᶠ t:ℝ in 𝓝[≠]0, |t|<δ:=by
    have h:Metric.ball (0:ℝ) δ∈𝓝[≠](0:ℝ):=nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hδ)
    filter_upwards [h] with t ht
    simpa [Metric.mem_ball,Real.dist_eq] using ht
  filter_upwards [size,self_mem_nhdsWithin] with t ht nz
  have hn:t≠0:=nz
  have small:|t| *cap w≤1:=by
    have q:= (lt_div_iff₀ (show 0<cap w+1 by linarith)).mp (ht.trans_le (min_le_left _ _))
    nlinarith [abs_nonneg t]
  have tiny:|t| *C<ε:=by
    have q:=(lt_div_iff₀ (show 0<C+1 by linarith)).mp (ht.trans_le (min_le_right _ _))
    nlinarith [abs_nonneg t]
  let err:readings Ω:=t⁻¹ • (weighted w t f-f-t • (f*w))
  have priced(x:Ω):‖err.val x‖≤|t| *C:=by
    have xsmall:‖t*w.val x‖≤1:=by
      rw [norm_mul,Real.norm_eq_abs]; exact (mul_le_mul_of_nonneg_left (within w x) (abs_nonneg t)).trans small
    have he:=Real.norm_exp_sub_one_sub_id_le (x:=t*w.val x) xsmall
    have fac:err.val x=t⁻¹*(Real.exp (t*w.val x)-1-t*w.val x)*f.val x:=by
      change t⁻¹*(Real.exp (t*w.val x)*f.val x-f.val x-t*(f.val x*w.val x))=_
      ring
    rw [fac,norm_mul,norm_mul,norm_inv]
    calc
      _≤(‖t‖⁻¹*‖t*w.val x‖^2)*cap f:=by gcongr; first | exact he | exact within f x
      _≤(‖t‖⁻¹*(‖t‖*cap w)^2)*cap f:=by rw [norm_mul]; gcongr <;> first | exact within w x | exact abs_nonneg _
      _=|t| *C:=by
        change |t|⁻¹*(|t| *cap w)^2*cap f=|t| *(cap w^2*cap f)
        field_simp [ne_of_gt (abs_pos.mpr hn)]
  have cancel:t⁻¹*(E (weighted w t f)-E f)-E (f*w)=E err:=by
    simp only [err,map_smul,map_sub,smul_eq_mul]
    field_simp [hn]
  change dist (t⁻¹ • (E (weighted w (0+t) f)-E (weighted w 0 f))) (E (f*w))<ε
  rw [zero_add,at_zero,Real.dist_eq,smul_eq_mul,cancel]
  exact (bound R live err _ priced).trans_lt tiny

def normalized (live:m<N) (w:readings Ω) (t:ℝ) (f:readings Ω):ℝ:=
  joint R live (weighted w t f)/joint R live (weighted w t 1)

private theorem zero (w f:readings Ω):weighted w 0 f=f:=by
  apply Subtype.ext
  funext x
  simp [weighted]

private theorem unit (live:m<N):joint R (p:=p) live 1=1:=by
  letI:IsProbabilityMeasure μ₀:=probability R.makes.wilson live.le
  change (∫ V,∫_:fine,(1:ℝ) ∂κ V ∂μ₀)=1
  have h(V:coarse):(∫_:fine,(1:ℝ) ∂κ V)=1:=by
    letI:=ActualWilsonConditionalRoots.probability R.family R.makes live V
    simp
  simp only [h,integral_const,probReal_univ,one_smul]

set_option backward.isDefEq.respectTransparency false in
private theorem row (live:m<N) (w f:readings Ω):
    HasDerivAt (fun t:ℝ=>normalized R live w t f) (covariance (joint R live) f w) 0:=by
  have zero_norm:joint R live (weighted w 0 1)≠0:=by rw [zero,unit];exact one_ne_zero
  have h:=(moment R live w f).div (moment R live w 1) zero_norm
  simpa only [Pi.div_def,normalized,covariance,zero,unit,one_mul,mul_one,one_pow,div_one] using h

open private five from YM.Integration.WilsonInvariantActionPriorHearing

set_option backward.isDefEq.respectTransparency false in
theorem original (live:m<N) (f h w:readings Ω):
    HasDerivAt (fun t:ℝ=>covariance (normalized R live w t) f h) (receipts R live f h w) 0:=by
  unfold receipts
  rw [←five (earlier R (p:=p) live) (conditional R live) f h w]
  let E:=joint R (p:=p) live
  change HasDerivAt _ (cubic E f h w) 0
  have at0(x:readings Ω):normalized R live w 0 x=E x:=by
    simp only [normalized,zero,unit,div_one,E]
  have product:=(row R live w (f*h)).sub ((row R live w f).mul (row R live w h))
  simp only [at0] at product
  have algebra:cubic E f h w=covariance E (f*h) w-
      (covariance E f w*E h+E f*covariance E h w):=by
    unfold cubic covariance
    ring
  rw [algebra]
  exact product

end YM.Integration.WilsonInvariantActionExponentialHearing
