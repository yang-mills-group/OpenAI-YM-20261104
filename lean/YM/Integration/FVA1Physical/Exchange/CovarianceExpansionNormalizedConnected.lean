import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionConnectedFreshBasis

/-! The four actual normalized signed tables are integrable after multiplying the
full previously deposited row by its own quiet mass. The bound makes no assumption
on the reciprocal vacuum at any cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset MeasureTheory RG Marker Multi Comparison.RG02.Order
open scoped ENNReal BigOperators Classical
variable {X:Type*}[MeasurableSpace X]{V:Type}[DecidableEq V][Fintype V]{C:Census V}

def fibreLaw (μ:Measure X)(u:X→ℝ):Measure X :=
  μ.withDensity (fun x=>ENNReal.ofReal (u x/(∫z,u z ∂μ)))

private theorem fibre_prob (μ:Measure X) {u:X→ℝ}(ui:Integrable u μ)(hn:∀x,0≤u x)
    (positive:0<∫x,u x ∂μ):IsProbabilityMeasure (fibreLaw μ u) where
  measure_univ:=by
    rw [fibreLaw,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
      ←ofReal_integral_eq_lintegral_ofReal (ui.div_const _) (.of_forall fun x=>div_nonneg (hn x) positive.le),
      integral_div,div_self (ne_of_gt positive),ENNReal.ofReal_one]

private theorem fibre_reading (μ:Measure X) {u:X→ℝ}(um:Measurable u)(hn:∀x,0≤u x)
    (positive:0<∫z,u z ∂μ)(f:X→ℂ):
    (∫x,f x ∂fibreLaw μ u)=FrozenRead.meanOn μ u f:=by
  rw [fibreLaw,integral_withDensity_eq_integral_toReal_smul
    ((um.div_const _).ennreal_ofReal) (.of_forall fun _=>ENNReal.ofReal_lt_top),
    FrozenRead.meanOn,←integral_smul]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (div_nonneg (hn x) positive.le),smul_smul,div_eq_inv_mul]

private theorem postings_all {a b:V}{A B:Bool}{f h:X→ℂ}(fe:Envelope f)(he:Envelope h):
    Leaf.All fun x=>Poly.pass (Multi.lambda C (twoBirthSettings a b A B f h x)):=by
  have row (i:V):Envelope (fun x=>twoBirthSettings a b A B f h x i):=by
    have pure (l:V)(F:X→ℂ)(bounded:Envelope F)(flag:Bool):
        Envelope (fun x=> (if flag then (Pi.single l (F x):V→ℂ) else 0) i):=by
      cases flag <;> by_cases hli:l=i
      all_goals first
        | subst i; simpa using bounded
        | simpa [hli,Ne.symm hli] using Leaf.atom (X:=X) 0
        | simpa using Leaf.atom (X:=X) 0
    exact Leaf.combine (pure a f fe A) (pure b h he B)
  intro s
  simp_rw [Comparison.RG02.Cumulants.pass_lambda]
  have prod (t:Finset V):Envelope (fun x=>∏i∈t,twoBirthSettings a b A B f h x i):=by
    induction t using Finset.induction with
    | empty => simpa using Leaf.atom (X:=X) 1
    | insert i t hit ih => simpa [hit] using Leaf.multiply (row i) ih
  exact prod s.val

private theorem unnormalized_post {k a:X→ℝ}{D:X→Poly C}(km:Envelope k)(am:Measurable a)
    (kn:∀x,0≤k x)(ap:∀x,0<a x)(old:Leaf.All D)(cash:∀x,(D x).part C.quiet=(a x:ℂ))
    {μ:Measure X}[IsFiniteMeasure μ](A:ℝ)(total:A=∫x,k x*a x ∂μ)(pos:0<A)
    {B T:Bool}{i j:V}{f h:X→ℂ}(fe:Envelope f)(he:Envelope h)(s:C.Mode):
    Integrable (fun x=>(postedUnit (unitScale (D x)) (twoBirthSettings i j B T f h x)).part s)
      (fibreLaw μ (fun x=>k x*a x)):=by
  subst A
  let Z:=∫x,k x*a x ∂μ
  let posted:=fun x=>Poly.pass (Multi.lambda C (twoBirthSettings i j B T f h x))*D x
  have lit:Envelope (fun x=>(posted x).part s):=Leaf.mul (postings_all fe he) old s
  have factor: Envelope (fun x=>(k x/Z:ℝ)):=by
    obtain ⟨M,hM⟩:=km.cost
    exact ⟨km.meas.div_const Z,M/|Z|,fun x=>by
      rw [norm_div];exact div_le_div_of_nonneg_right (hM x) (norm_nonneg Z)⟩
  have complexFactor:Envelope (fun x=>(k x/Z:ℂ)):=by
    obtain ⟨M,hM⟩:=factor.cost
    refine ⟨?_,M,?_⟩
    · simpa only [Function.comp_def,Complex.ofReal_div] using Complex.continuous_ofReal.measurable.comp factor.meas
    · intro x;rw [←Complex.ofReal_div,Complex.norm_real];exact hM x
  have both:=Leaf.multiply complexFactor lit
  obtain ⟨cap,caple⟩:=both.cost
  have fund:Integrable (fun x=>(k x/Z:ℂ)*(posted x).part s) μ :=
    Integrable.of_bound both.meas.aestronglyMeasurable cap (.of_forall caple)
  have nn (x:X): 0≤ k x*a x/Z:=div_nonneg (mul_nonneg (kn x) (ap x).le) pos.le
  apply (integrable_withDensity_iff_integrable_smul' (((km.meas.mul am).div_const Z).ennreal_ofReal)
    (.of_forall fun _=>ENNReal.ofReal_lt_top)).2
  apply fund.congr
  filter_upwards with x
  change (k x/Z:ℂ)*(posted x).part s =
    (ENNReal.ofReal (k x*a x/Z)).toReal • (postedUnit (unitScale (D x)) _).part s
  rw [ENNReal.toReal_ofReal (nn x),Complex.real_smul]
  simp only [postedUnit,unitScale,cash,mul_smul_comm,Poly.part_smul,Complex.ofReal_div,Complex.ofReal_mul]
  change (k x/Z:ℂ)*(posted x).part s=
    ((k x:ℂ)*(a x:ℂ)/(Z:ℂ))*((a x:ℂ)⁻¹*(posted x).part s)
  field_simp [Complex.ofReal_ne_zero.mpr (ap x).ne',Complex.ofReal_ne_zero.mpr (show Z≠0 from pos.ne')]

/-- Four independently posted readings, each averaged and made connected on
the original positive fibre after including all the previously marked modes. -/
def connectedFour (μ:Measure X)(k a:X→ℝ)(D:X→Poly C)(i j:V)(s:C.Mode)(f h:X→ℂ):ℂ:=
  let Q:=fun (A B:Bool)=>(Extra.Trajectories.connected (jointPostMean
    (fibreLaw μ (fun x=>k x*a x)) (fun x=>unitScale (D x)) (twoBirthSettings i j A B f h))).part s
  (Q true true-Q false true)-(Q true false-Q false false)

theorem funded_connected_post (μ:Measure X)[IsFiniteMeasure μ] {k a:X→ℝ}{D:X→Poly C}
    (km:Envelope k)(am:Measurable a)(kn:∀x,0≤k x)(ap:∀x,0<a x)
    (ui:Integrable (fun x=>k x*a x) μ)(positive:0<(∫x,k x*a x ∂μ))
    (fund:Leaf.All D)(cash:∀x,(D x).part C.quiet=(a x:ℂ))
    (i j:V)(apart:i≠j)(s:C.Mode)(pair:s.val={i,j}){f h:X→ℂ}(fe:Envelope f)(he:Envelope h):
    connectedFour μ k a D i j s f h=Replica.fieldCovariance μ (fun x=>k x*a x) f h:=by
  let u:=fun x=>k x*a x
  have nn(x):0≤u x:=mul_nonneg (kn x) (ap x).le
  letI:=fibre_prob μ ui nn positive
  have unit (x:X):(unitScale (D x)).part C.quiet=1:=unitScore (by rw [cash];exact Complex.ofReal_ne_zero.mpr (ap x).ne')
  have measured:=integrated_fresh_connected (fibreLaw μ u) (fun x=>unitScale (D x)) unit i j apart s pair f h he fe
    (fun A B r=>unnormalized_post km am kn ap fund cash _ rfl positive (B:=A) (T:=B) fe he r)
  change connectedFour μ k a D i j s f h=_ at measured
  have um:Measurable u:=km.meas.mul am
  rw [fibre_reading μ um nn positive (fun x=>f x*h x),fibre_reading μ um nn positive f,
    fibre_reading μ um nn positive h] at measured
  exact measured

end YM.Integration.FVA1Physical.Exchange.RoseCut
