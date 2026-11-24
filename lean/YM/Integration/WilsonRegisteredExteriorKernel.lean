import YM.Integration.WilsonRegisteredExteriorReturn
import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalExact

/-! Joint measurability in the held lower field and the original exterior of
an observation of the complete normalized local physical prior. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredExteriorKernel
open Function Set MeasureTheory Lattice RG Wilson OriginalMarkedRowCovariance
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato WilsonHeldRetainedAction OriginalMarkedRunAction
open private kernel_env kernel_floor from YM.Integration.WilsonHeldExteriorLaw
open scoped Classical
variable {G:Gauge}{n:Side}

set_option backward.isDefEq.respectTransparency false in
theorem patch (S:Support n):Measurable (fun v:Config G n×Config G n=>OriginalMarkedConditionalAction.patch S v.1 v.2):=by
  apply measurable_pi_lambda
  intro e
  have get:Measurable (fun u:Config G n=>u e):=measurable_pi_apply e
  by_cases h:e.1∈S
  · simpa only [OriginalMarkedConditionalAction.patch,if_pos h,Function.comp_def] using (get.comp (measurable_snd : Measurable (fun x:Config G n×Config G n=>x.2)))
  · simpa only [OriginalMarkedConditionalAction.patch,if_neg h,Function.comp_def] using (get.comp (measurable_fst : Measurable (fun x:Config G n×Config G n=>x.1)))

variable (R:Run G){N per m:ℕ}
local notation "fine" => Config G (R.family.side (m+1) per)
local notation "coarse" => Config G (R.family.side m per)
local notation "Ω" => (coarse×fine)
local notation "step" => R.family.path.levels.clock.op m per
local notation "β" => R.family.path.β N per (m+1)
local notation "P" => R.family.path.rep N per (m+1)

def factors (S:Support (R.family.side (m+1) per))(x:Ω×fine):ℝ:=
  let U:=OriginalMarkedConditionalAction.patch S x.1.2 x.2
  (step).density β U x.1.1*(P).eval U

theorem density (live:m+1≤N)(S:Support (R.family.side (m+1) per)):
    Measurable (factors R (N:=N) S):=by
  have u:Measurable (fun x:Ω×fine=>OriginalMarkedConditionalAction.patch S x.1.2 x.2):=
    (patch S).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have source:=(P).envelope (R.makes.wilson.represents N per (m+1) live).good
  exact (((step).density_meas (G:=G) (R.family.path.levels.blocks m per).branches β).comp
    (u.prodMk (measurable_fst.comp measurable_fst))).mul (source.meas.comp u)

set_option backward.isDefEq.respectTransparency false in
theorem mean (live:m+1≤N)(S:Support (R.family.side (m+1) per))(x:Ω)(f:fine→ℂ):
    (∫u,f u ∂springLocalPrior R m N per S x.2 x.1)=
      read (prior G _) (fun u=>factors R (N:=N) S (x,u)) f:=by
  let ξ:=OriginalMarkedConditionalAction.patch S x.2
  let k (u:fine):=(step).density β (ξ u) x.1
  let p (u:fine):=(P).eval (ξ u)
  let μ:=reference R N per m S x.2 x.1
  letI:IsProbabilityMeasure μ:=probability R N per m S x.2 x.1
  have mξ:=OriginalMarkedConditionalAction.measurable_patch (G:=G) S x.2
  have source:=(P).envelope (R.makes.wilson.represents N per (m+1) live).good
  have law:=kernel_env (step) β (R.family.path.levels.blocks m per).branches x.1
  have lift (g:fine→ℝ)(e:Envelope g):Envelope (fun u=>g (ξ u)):=by
    obtain ⟨d,cap⟩:=e.cost
    exact ⟨e.meas.comp mξ,d,fun u=>cap _⟩
  have positive (ν:Measure fine)[IsProbabilityMeasure ν](g:fine→ℝ)(e:Envelope g)
      {a:ℝ}(hp:0<a)(floor:∀u,a≤g u):0<∫u,g u ∂ν:=by
    have paid:=integral_mono (integrable_const (μ:=ν) a) (e.integrable ν) floor
    exact hp.trans_le (by simpa using paid)
  obtain ⟨b,bp,low⟩:=WilsonHeldExteriorLaw.upper_floor R N per m live
  obtain ⟨t,tp,threshold⟩:=kernel_floor R N per m live
  have mass:=positive μ p (lift _ source) bp (fun u=>low (ξ u))
  have nonneg (u):0≤p u:=(bp.trans_le (low (ξ u))).le
  have mg:=positive (prior G _) k (lift _ law) tp (fun u=>threshold (ξ u) x.1)
  have hp:Measurable p:=(lift _ source).meas
  have get:=SignedWeightedMoment.normalized_integral μ hp nonneg mass f
  have eq:(∫u,f u ∂springLocalPrior R m N per S x.2 x.1)=read μ p f:=by
    change (∫u,f u ∂SignedWeightedMoment.normalized μ p)=read μ p f
    simpa only [OriginalMarkedRowCovariance.read,Complex.real_smul,Complex.ofReal_inv] using get
  exact eq.trans (WilsonRegisteredExteriorNormalization.weighted (prior G _) k p f
    (lift _ law).meas (fun u=>(step).density_positive β (ξ u) x.1) mg)

theorem measurable (live:m+1≤N)(S:Support (R.family.side (m+1) per))
    (F:Ω×fine→ℂ)(mf:Measurable F):
    Measurable (fun x:Ω=>∫u,F (x,u) ∂springLocalPrior R m N per S x.2 x.1):=by
  have den:=((density R live S).stronglyMeasurable.integral_prod_right' (ν:=prior G _)).measurable
  have num:=(((Complex.continuous_ofReal.measurable.comp (density R live S)).mul mf).stronglyMeasurable.integral_prod_right' (ν:=prior G _)).measurable
  simp_rw [mean R live S]
  exact (Complex.continuous_ofReal.measurable.comp den).inv.mul num
end YM.Integration.WilsonRegisteredExteriorKernel
