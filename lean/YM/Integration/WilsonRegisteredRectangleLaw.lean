import YM.Integration.WilsonRegisteredRectangleMoment
import YM.Integration.WilsonRegisteredTwoPatchLaw

/-! The signed compact rectangle for the full fitted Wilson conditional. Both
observations retain their physical supports and the two proper means. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredRectangleLaw
open Function Filter MeasureTheory Lattice RG Wilson OriginalMarkedRunAction OriginalMarkedRowCovariance
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open private paid_mass from YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalExact
open scoped Classical
variable {G:Gauge}{l:Side}

def chart (S T:Support l)(ext:Config G l)(x:Config G l×Config G l):Config G l:=
  OriginalMarkedConditionalAction.patch S (OriginalMarkedConditionalAction.patch T ext x.2) x.1

theorem measurable (S T:Support l)(ext:Config G l):Measurable (chart S T ext):=
  (WilsonRegisteredExteriorKernel.patch S).comp (((WilsonRegisteredExteriorKernel.patch T).comp
    (measurable_const.prodMk measurable_snd)).prodMk measurable_fst)

private theorem lift {X Y:Type*}[MeasurableSpace X][MeasurableSpace Y]{f:Y→ℂ}(e:Envelope f)
    {g:X→Y}(mg:Measurable g):Envelope (fun x=>f (g x)):=by
  obtain ⟨c,cap⟩:=e.cost
  exact ⟨e.meas.comp mg,c,fun x=>cap _⟩

theorem integral (S T:Support l)(ext:Config G l)(f:Config G l→ℂ)(e:Envelope f):
    (∫x,f (chart S T ext x) ∂(prior G l).prod (prior G l))=
    ∫u,f (OriginalMarkedConditionalAction.patch (S∪T) ext u) ∂prior G l:=by
  have h:=lift e (measurable S T ext)
  exact (integral_prod_symm _ (h.integrableC _)).trans (WilsonRegisteredTwoPatchHaar.received S T ext f e)

variable (R:Run G){m N per r:ℕ}{Z:SeriesA G}{σ C ε:ℝ}
local notation "fine" => Config G (R.family.side (m+1) per)
local notation "coarse" => Config G (R.family.side m per)
local notation "η" => prior G (R.family.side (m+1) per)

def weight (Z:SeriesA G)(σ C:ℝ)(S T:Support (R.family.side (m+1) per))(ext:fine)(W:coarse)(x:fine×fine):ℂ:=
  (WilsonRegisteredTwoPatchLaw.density R (N:=N) (r:=r) Z σ C W (chart S T ext x):ℂ)

set_option backward.isDefEq.respectTransparency false in
theorem raw (live:m+1≤N)(osc:LocalSpringOscillation R m N per r Z σ C ε)
    (S T:Support (R.family.side (m+1) per))(ext:fine)(W:coarse)(f:fine→ℂ)(ef:Envelope f):
    let p:=weight R (N:=N) (r:=r) Z σ C S T ext W
    let ζ:=(η).prod η
    let M:=∫x,p x ∂ζ
    M≠0 ∧ M*WilsonRegisteredExteriorSeries.tilted R (N:=N) (r:=r) Z σ C (S∪T) f (W,ext)=
      ∫x,p x*f (chart S T ext x) ∂ζ:=by
  intro p ζ M
  let d:=WilsonRegisteredTwoPatchLaw.density R (N:=N) (r:=r) Z σ C W
  let u:=OriginalMarkedConditionalAction.patch (S∪T) ext
  obtain ⟨ed,pd⟩:=WilsonRegisteredTwoPatchLaw.finite R live osc W
  letI:IsProbabilityMeasure η:=inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _:Edge (Site (R.family.side (m+1) per))=>G.probHaar)))
  have liftD:Envelope (fun x=>d (u x)):=by
    obtain ⟨c,cap⟩:=ed.cost
    exact ⟨ed.meas.comp (OriginalMarkedConditionalAction.measurable_patch _ _),c,fun x=>cap _⟩
  have pos:=paid_mass η liftD (fun x=>pd (u x))
  have md:M=((∫x,d (u x) ∂η:ℝ):ℂ):=(integral S T ext (fun x=>(d x:ℂ)) ed.ofReal_env).trans (integral_complex_ofReal)
  have ne:M≠0:=md ▸ Complex.ofReal_ne_zero.mpr pos.ne'
  have num:=integral S T ext (fun x=>(d x:ℂ)*f x) (ed.ofReal_env.mulC ef)
  refine ⟨ne,?_⟩
  rw [WilsonRegisteredTwoPatchLaw.row R live]
  change M*((((∫x,d (u x) ∂η:ℝ):ℂ))⁻¹*(∫x,(d (u x):ℂ)*f (u x) ∂η))=_
  rw [←md,←mul_assoc,mul_inv_cancel₀ ne,one_mul]
  exact num.symm

set_option backward.isDefEq.respectTransparency false in
theorem original (live:m+1≤N)(osc:LocalSpringOscillation R m N per r Z σ C ε)
    (S T:Support (R.family.side (m+1) per))(away:Disjoint S T)(ext:fine)(W:coarse)
    (f g:fine→ℂ)(ef:Envelope f)(eg:Envelope g)(lf:LocalOn S f)(lg:LocalOn T g):
    let p:=weight R (N:=N) (r:=r) Z σ C S T ext W
    let ζ:=(η).prod η
    let M:=∫x,p x ∂ζ
    let L:=fun h=>WilsonRegisteredExteriorSeries.tilted R (N:=N) (r:=r) Z σ C (S∪T) h (W,ext)
    M≠0 ∧ M^2*(L (f*g)-L f*L g)=∫x,(f x.1*g x.2)*(∫y,WilsonRegisteredRectangleMoment.minor p x y ∂ζ) ∂ζ:=by
  intro p ζ M L
  letI:IsProbabilityMeasure η:=inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _:Edge (Site (R.family.side (m+1) per))=>G.probHaar)))
  have first(x:fine×fine):f (chart S T ext x)=f x.1:=by
    apply lf
    intro e hs _
    change e.1∈S at hs
    simp only [chart,OriginalMarkedConditionalAction.patch,if_pos hs]
  have second(x:fine×fine):g (chart S T ext x)=g x.2:=by
    apply lg
    intro e ht _
    change e.1∈T at ht
    have hs:e.1∉S:=fun h=>Finset.disjoint_left.mp away h ht
    simp only [chart,OriginalMarkedConditionalAction.patch,if_neg hs,if_pos ht]
  have ep:Envelope p:=lift (WilsonRegisteredTwoPatchLaw.finite R live osc W).1.ofReal_env (measurable S T ext)
  obtain ⟨ne,a⟩:=raw R live osc S T ext W f ef
  have b:=(raw R live osc S T ext W g eg).2
  have j:=(raw R live osc S T ext W (f*g) (ef.mulC eg)).2
  change M*L f=(∫x,p x*f (chart S T ext x) ∂ζ) at a
  change M*L g=(∫x,p x*g (chart S T ext x) ∂ζ) at b
  change M*L (f*g)=(∫x,p x*(f (chart S T ext x)*g (chart S T ext x)) ∂ζ) at j
  simp_rw [first,mul_comm (p _) (f _)] at a
  simp_rw [second,mul_comm (p _) (g _)] at b
  simp_rw [first,second,mul_comm (p _) (f _*g _)] at j
  refine ⟨ne,?_⟩
  rw [WilsonRegisteredRectangleMoment.measured η η ep f ef g eg,←a,←b,←j]
  change M^2*(L (f*g)-L f*L g)=M*L (f*g)*M-(M*L f)*(M*L g)
  ring
end YM.Integration.WilsonRegisteredRectangleLaw
