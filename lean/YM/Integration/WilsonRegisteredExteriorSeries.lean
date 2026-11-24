import YM.Integration.WilsonRegisteredExteriorKernel
import YM.Integration.WilsonRootedPosteriorFiledSeries

/-! The exact and finite earlier posterior readings are measurable jointly
in the saved old field and the true held lower field. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredExteriorSeries
open Function Finset MeasureTheory Lattice RG Wilson OriginalMarkedRowCovariance
open PhysicalNext.Repeat.Legato WilsonHeldRetainedAction OriginalMarkedRunAction
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){m N per r:ℕ}(Z:SeriesA G)(σ C:ℝ)
local notation "fine" => Config G (R.family.side (m+1) per)
local notation "coarse" => Config G (R.family.side m per)
local notation "Ω" => (coarse×fine)
variable (S:Support (R.family.side (m+1) per))

def tilted (f:fine→ℂ)(x:Ω):ℂ:=
  let ξ:=OriginalMarkedConditionalAction.patch S x.2
  read (reference R N per m S x.2 x.1) (fun u=>maskedSpringWeight R (N:=N) r Z σ C (ξ u)) (fun u=>f (ξ u))

def moments (n:ℕ)(f:fine→ℂ)(x:Ω):ℂ:=
  let ξ:=OriginalMarkedConditionalAction.patch S x.2
  springMomentSum (springLocalPrior R m N per S x.2 x.1) (springLocalChange R m N per r Z σ C S x.2) n (fun u=>f (ξ u))

def partialSum (n:ℕ)(f:fine→ℂ)(x:Ω):ℂ:=
  moments R (N:=N) (r:=r) Z σ C S n f x / moments R (N:=N) (r:=r) Z σ C S n 1 x

set_option backward.isDefEq.respectTransparency false in
theorem measurable (live:m+1≤N){η:ℝ}(osc:LocalSpringOscillation R m N per r Z σ C η)(n:ℕ)
    (f:fine→ℂ)(mf:Measurable f):Measurable (tilted R (N:=N) (r:=r) Z σ C S f) ∧
      Measurable (partialSum R (N:=N) (r:=r) Z σ C S n f):=by
  let ξ (x:Ω×fine):=OriginalMarkedConditionalAction.patch S x.1.2 x.2
  let h (x:Ω×fine):=springLocalChange R m N per r Z σ C S x.1.2 x.2
  let ν (x:Ω):=springLocalPrior R m N per S x.2 x.1
  have mx:Measurable ξ:=(WilsonRegisteredExteriorKernel.patch S).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have mh:Measurable h:=(osc.1.comp mx).sub (osc.1.comp (measurable_snd.comp measurable_fst))
  have hc:Measurable (fun x=>(h x:ℂ)):=Complex.continuous_ofReal.measurable.comp mh
  have power (k:ℕ)(g:fine→ℂ)(mg:Measurable g):
      Measurable (fun x:Ω=>∫u,(h (x,u):ℂ)^k*g (ξ (x,u)) ∂ν x):=
    WilsonRegisteredExteriorKernel.measurable R live S _ ((hc.pow_const k).mul (mg.comp mx))
  have mp (g:fine→ℂ)(mg:Measurable g):
      Measurable (moments R (N:=N) (r:=r) Z σ C S n g):=by
    unfold moments springMomentSum
    exact Finset.measurable_sum _ (fun k _=>measurable_const.mul (power k g mg))
  have tilt:Measurable (fun x=>(Real.exp (h x):ℂ)):=Complex.continuous_ofReal.measurable.comp mh.exp
  have num:Measurable (fun x:Ω=>∫u,(Real.exp (h (x,u)):ℂ)*f (ξ (x,u)) ∂ν x):=
    WilsonRegisteredExteriorKernel.measurable R live S _ (tilt.mul (mf.comp mx))
  have den:Measurable (fun x:Ω=>∫u,(Real.exp (h (x,u)):ℂ) ∂ν x):=
    WilsonRegisteredExteriorKernel.measurable R live S _ tilt
  have eq (x:Ω):tilted R (N:=N) (r:=r) Z σ C S f x=
      (∫u,(Real.exp (h (x,u)):ℂ)*f (ξ (x,u)) ∂ν x)/(∫u,(Real.exp (h (x,u)):ℂ) ∂ν x):=by
    have pos:=spring_prior_exact R live osc S x.2 x.1
    rw [integral_complex_ofReal]
    apply (eq_div_iff (by exact_mod_cast pos.1.ne')).2
    exact (mul_comm ..).trans (pos.2 f).2
  constructor
  · rw [funext eq]
    exact num.div den
  · exact (mp f mf).div (mp 1 measurable_const)
end YM.Integration.WilsonRegisteredExteriorSeries
