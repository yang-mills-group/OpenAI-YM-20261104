import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6PhysicalScalarSeries

/-! Identify the first retained numerical thermal coefficient on its own
true original finite Haar patch, with its physical conditional quiet. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace YM.Integration.FVA1Physical.Exchange.F6Regular
open Function Filter Finset MeasureTheory Lattice RG YM.Wilson OPE.Therm Marked.Inherited
open scoped Classical BigOperators
open private general_measured from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6MeasuredExterior
open private fillPatch_meas tilted_probability from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6OriginalExterior
open private subenv from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6RegularCovariance
variable {G:Gauge}{n:Side}
local notation "Fld" => Config G n

private theorem unit_thermal (s:ℝ):tiltTaylor 1 (-s)=1-s:=by
  simp [tiltTaylor,Finset.sum_range_succ,sub_eq_add_neg]

private theorem centered_linear {X:Type*}[MeasurableSpace X](ν:Measure X)[IsProbabilityMeasure ν]
    (f d:X→ℝ)(fe:Envelope f)(de:Envelope d)(M ω:ℝ)(bound:∀x,|f x|≤M)(band:∀x,|d x|≤ω)(small:ω≤1/4):
    let a:=∫x,f x ∂ν;let T:=firstRead ν f d;let w:=fun x=>1-d x
    let Z:=∫x,w x ∂ν;let y:=(∫x,w x*f x ∂ν)/Z
    3/4≤Z ∧ y=a-T/Z ∧ |y-(a-T)|≤4*M*ω^2:=by
  intro a T w Z y
  let b:=∫x,d x ∂ν
  have mean {g:X→ℝ}{c:ℝ}(cap:∀x,|g x|≤c): |∫x,g x ∂ν|≤c:=by
    simpa only [←Real.norm_eq_abs,probReal_univ,mul_one] using
      (norm_integral_le_of_norm_le_const (μ:=ν) (.of_forall fun x=>by simpa only [Real.norm_eq_abs] using cap x))
  have ab:|a|≤M:=mean bound
  have db:|b|≤ω:=mean band
  have M0:0≤M:=(abs_nonneg _).trans ab
  have w0:0≤ω:=(abs_nonneg _).trans db
  have z:Z=1-b:=by dsimp only [Z,w];rw [integral_sub (integrable_const _) (de.integrable ν)];simp [b]
  have zpos:3/4≤Z:=by rw [z];linarith only [le_abs_self b,db,small]
  have zp:0<Z:=lt_of_lt_of_le (by norm_num) zpos
  have num:(∫x,w x*f x ∂ν)=a-(∫x,f x*d x ∂ν):=by
    simp only [w,sub_mul,one_mul,mul_comm (d _) (f _)]
    exact integral_sub (fe.integrable ν) ((fe.mul de).integrable ν)
  have ct:T=(∫x,f x*d x ∂ν)-a*b:=by
    simpa only [sub_zero] using first_is_covariance ν f d fe de 0
  have yid:y=a-T/Z:=by
    dsimp only [y];rw [num,ct];field_simp;rw [z];ring
  have cap:|T|≤2*M*ω:=by
    apply mean (g:=fun x=>(f x-∫z,f z ∂ν)*d x)
    intro x
    rw [abs_mul];apply mul_le_mul ((abs_sub ..).trans ((add_le_add (bound x) ab).trans_eq (two_mul M).symm)) (band x) (abs_nonneg _) (mul_nonneg zero_le_two M0)
  refine ⟨zpos,yid,?_⟩
  have id:y-(a-T)= -(T*b)/Z:=by rw [yid];field_simp;rw [z];ring
  rw [id,abs_div,abs_neg,abs_mul,abs_of_pos zp];apply (div_le_iff₀ zp).2
  apply (mul_le_mul cap db (abs_nonneg _) (mul_nonneg (mul_nonneg zero_le_two M0) w0)).trans
  calc 2*M*ω*ω=(4*M*ω^2)*(1/2):=by ring
       _≤_:=mul_le_mul_of_nonneg_left ((by norm_num : (1/2:ℝ)≤3/4).trans zpos) (by positivity)

/-- Conditional physical energy without the retained regular tilt, and
the vacuum moment of its first finite Taylor weight. -/
def baseOne (R:Rep G n)(I:Finset (Edge (Site n)))(f:Fld→ℝ)
    (o:({b:Edge (Site n)//b∉I}→G.El)):=∫x,f (fillPatch I o x) ∂tiltedPatch R I o

def firstQuiet (R:Rep G n)(I:Finset (Edge (Site n)))(o:({b:Edge (Site n)//b∉I}→G.El)):ℝ:=
  let J:=fillPatch I o;∫x,1-referenceTilt R (J 1) (J x) ∂tiltedPatch R I o

private theorem read_linear (R:Rep G n){σ C Λ ε ξ:ℝ}(law:R.Lawful σ C Λ ε ξ)(pos:∀U,0<R.eval U)
    (I:Finset (Edge (Site n)))(f:Fld→ℝ)(o:({b:Edge (Site n)//b∉I}→G.El)):
    let J:=fillPatch I o;let ν:=tiltedPatch R I o;let d:=fun x=>referenceTilt R (J 1) (J x)
    finiteOne R I f 1 o=(∫x,(1-d x)*f (J x) ∂ν)/(∫x,1-d x ∂ν):=by
  intro J ν d
  let η:=Measure.pi (fun _:↥I=>G.probHaar)
  let h:=fun u=>R.eval u*Real.exp (R.activities.additive R.p u)
  let u:=h ∘ J
  let c:=Real.exp (-R.activities.additive R.p (J 1))
  have he:Envelope h:=(R.envelope law).mul (show Envelope (R.activities.additive R.p) from
    ⟨R.activities.E_measurable law.labels.regular,(Activities.ESeries law.labels).bound⟩).exp
  have up(x):0<u x:=mul_pos (pos _) (Real.exp_pos _)
  have ue:Envelope u:=⟨he.meas.comp (fillPatch_meas I o),he.cost.choose,fun x=>he.cost.choose_spec _⟩
  have z:0<∫x,u x ∂η:=by
    apply (integral_pos_iff_support_of_nonneg (fun x=>(up x).le) (ue.integrable η)).2
    rw [show Function.support u=Set.univ from Set.eq_univ_of_forall fun x=>(up x).ne'];simp [η]
  have p(x):patchTaylorDensity R (J 1) 1 (J x)=c*(u x*(1-d x)):=by
    rw [patchTaylorDensity,unit_thermal];dsimp only [c,u,h,d,J,Function.comp_apply,referenceTilt]
    rw [Real.exp_sub,Real.exp_neg];ring
  have read (g:(↥I→G.El)→ℝ):(∫x,g x ∂ν)=(∫x,u x*g x ∂η)/(∫x,u x ∂η):=
    general_measured η ue.meas (fun x=>(up x).le) g
  rw [read,read,div_div_div_cancel_right₀ z.ne']
  change (∫x,patchTaylorDensity R (J 1) 1 (J x)*f (J x) ∂η)/(∫x,patchTaylorDensity R (J 1) 1 (J x) ∂η)=_
  simp_rw [p,mul_assoc c,mul_assoc (u _),integral_const_mul];exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

theorem original_first_thermal (R:Rep G n){σ C Λ ε ξ:ℝ}(law:R.Lawful σ C Λ ε ξ)(pos:∀U,0<R.eval U)
    (I:Finset (Edge (Site n)))(width:1≤R.p.supportExponent)(f:Fld→ℝ)(ef:Envelope f)(M:ℝ)(bound:∀U,|f U|≤M)
    (o:({b:Edge (Site n)//b∉I}→G.El)):
    let L:=I.image Prod.fst;let ω:=((halo 8 L).card:ℝ)*(2*Push.GridApprox.Attach.hitConstant R.p.B*ε)
    let T:=patchInsertion R I (R.activities.additive R.p) f o;let a:=baseOne R I f o
    ω≤1/4 → 3/4≤firstQuiet R I o ∧ finiteOne R I f 1 o=a-T/firstQuiet R I o ∧
      |originalOne R I f o-(a-T)|≤12*M*ω^2:=by
  intro L ω T a small
  let J:=fillPatch I o;let ν:=tiltedPatch R I o;let d:=fun x=>referenceTilt R (J 1) (J x)
  letI:IsProbabilityMeasure ν:=tilted_probability R law pos I o
  have pull {g:Fld→ℝ}(e:Envelope g):Envelope (g ∘ J):=⟨e.meas.comp (fillPatch_meas I o),e.cost.choose,fun x=>e.cost.choose_spec _⟩
  have D:Envelope d:=subenv (pull (g:=R.activities.additive R.p) ⟨R.activities.E_measurable law.labels.regular,(Activities.ESeries law.labels).bound⟩) (Envelope.const _)
  have band(x):|d x|≤ω:=by
    apply RoseCut.FiledAction.funded_edit R.p width law.labels (J x) (J 1)
    intro e outside;have miss:e∉I:=fun hit=>outside (Finset.mem_image.mpr ⟨e,hit,rfl⟩)
    simp only [J,fillPatch,dif_neg miss]
  have ans:=centered_linear ν (f ∘ J) d (pull ef) D M ω (fun x=>bound _) band small
  have eq:=read_linear R law pos I f o
  change 3/4≤firstQuiet R I o ∧ (∫x,(1-d x)*f (J x) ∂ν)/(∫x,1-d x ∂ν)=a-T/firstQuiet R I o ∧
    |(∫x,(1-d x)*f (J x) ∂ν)/(∫x,1-d x ∂ν)-(a-T)|≤4*M*ω^2 at ans
  rw [←eq] at ans;refine ⟨ans.1,ans.2.1,?_⟩
  have e:=original_one_finite R law pos I width f ef M bound 1 o small
  rw [abs_sub_comm] at e
  exact (abs_sub_le _ (finiteOne R I f 1 o) _).trans ((add_le_add e ans.2.2).trans_eq (by dsimp only [ω,L];ring))

end YM.Integration.FVA1Physical.Exchange.F6Regular
