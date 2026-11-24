import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionFiledBinCovariance
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionTestedCrossing

/-! Explicit finite numerical mesh for the true, locally gauge-invariant
field. This does not refine a physical time or lattice mesh. The error
is paid on the original probability space with any correlated spectator. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Set Finset MeasureTheory Lattice RG Wilson Marker QuadraticLocal
open scoped Classical BigOperators

abbrev OneMesh (M h:ℝ):=Fin (⌊(2*M)/h⌋₊+1)
abbrev ProbeMesh (M h:ℝ):=OneMesh M h × OneMesh M h

def oneLabel (M h x:ℝ):OneMesh M h:=
  ⟨min ⌊(x+M)/h⌋₊ ⌊(2*M)/h⌋₊,Nat.lt_succ_of_le (min_le_right ..)⟩

def labelProbe (M h:ℝ)(v:ℂ):ProbeMesh M h:=(oneLabel M h v.re,oneLabel M h v.im)

def readProbe (M h:ℝ)(i:ProbeMesh M h):ℂ:=⟨(i.1.val:ℝ)*h-M,(i.2.val:ℝ)*h-M⟩

private theorem one_bound (x M h:ℝ)(hp:0<h)(cap:|x|≤M):
    |x-((oneLabel M h x).val*h-M)|≤h:=by
  obtain ⟨neg,top⟩:=abs_le.mp cap
  have typed:0≤(x+M)/h:=div_nonneg (by linarith only [neg]) hp.le
  have ord:⌊(x+M)/h⌋₊≤⌊(2*M)/h⌋₊:=Nat.floor_mono (div_le_div_of_nonneg_right (by linarith only [top]) hp.le)
  have low:=(le_div_iff₀ hp).mp (Nat.floor_le typed)
  have high:=(div_lt_iff₀ hp).mp (Nat.lt_floor_add_one ((x+M)/h))
  simp only [oneLabel,min_eq_left ord]
  rw [abs_of_nonneg (by linarith only [low])]
  linarith only [high]

theorem probe_mesh_cost (M h:ℝ)(hp:0<h)(u:ℂ)(cap:‖u‖≤M):
    ‖u-readProbe M h (labelProbe M h u)‖≤2*h:=by
  have re:=one_bound u.re M h hp ((Complex.abs_re_le_norm u).trans cap)
  have im:=one_bound u.im M h hp ((Complex.abs_im_le_norm u).trans cap)
  exact (Complex.norm_le_abs_re_add_abs_im _).trans ((add_le_add re im).trans_eq (two_mul h).symm)

theorem probe_label_measurable (M h:ℝ):Measurable (labelProbe M h):=by
  have part:Measurable (oneLabel M h):=by
    let clip:ℕ→OneMesh M h:=fun n=>⟨min n ⌊(2*M)/h⌋₊,Nat.lt_succ_of_le (min_le_right ..)⟩
    have paid:Measurable clip:=Measurable.of_discrete
    have floor:Measurable (fun x:ℝ=>⌊(x+M)/h⌋₊):=((measurable_id.add measurable_const).div measurable_const).nat_floor
    exact paid.comp floor
  exact (part.comp Complex.measurable_re).prodMk (part.comp Complex.measurable_im)

/-- Numerical rounding is paid against the original jointly sampled exterior,
including restrictions to events involving any original fine or coarse fields. -/
theorem mesh_observation_exterior {Z:Type*}[MeasurableSpace Z](law:Measure Z)[IsFiniteMeasure law]
    (f:Z→ℂ)(fm:Measurable f)(M h:ℝ)(hp:0<h)(cap:∀z,‖f z‖≤M)
    (E:Set Z)(em:MeasurableSet E)(H:Z→ℂ)(h2:MemLp H 2 law):
    let q:=fun z=>readProbe M h (labelProbe M h (f z))
    Integrable (fun z=>E.indicator H z*(f z-q z)) law ∧
    ‖∫z,E.indicator H z*(f z-q z) ∂law‖≤(2*h)*(Real.sqrt (∫z,‖H z‖^2 ∂law)*Real.sqrt (law.real E)):=by
  intro q
  have qm:Measurable q:=(show Measurable (readProbe M h) from Measurable.of_discrete).comp ((probe_label_measurable M h).comp fm)
  have gap (z:Z):‖f z-q z‖≤2*h:=probe_mesh_cost M h hp _ (cap z)
  have old:Integrable (E.indicator H) law:=(h2.integrable (by norm_num)).indicator em
  have mixed:Integrable (fun z=>(f z-q z)*E.indicator H z) law:=old.bdd_mul (fm.sub qm).aestronglyMeasurable (.of_forall gap)
  refine ⟨by simpa only [mul_comm] using mixed,?_⟩
  obtain ⟨en,bill⟩:=crowd_spectator law E em H h2
  have cash:=norm_integral_le_of_norm_le (en.const_mul (2*h)) (Filter.Eventually.of_forall (fun z=>show
    ‖E.indicator H z*(f z-q z)‖≤(2*h)*E.indicator (fun x=>‖H x‖) z from by
      by_cases inside:z∈E
      · rw [Set.indicator_of_mem inside,Set.indicator_of_mem inside,norm_mul,mul_comm (2*h)]
        exact mul_le_mul_of_nonneg_left (gap z) (norm_nonneg _)
      simp [inside]))
  rw [integral_const_mul] at cash
  exact cash.trans (mul_le_mul_of_nonneg_left bill (by positivity))


variable {G:Gauge}{n:Side}{V T I:Type}[Fintype V][DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

omit [Fintype V] in
/-- The quantizer acts on the bounded regional reading. It is Borel and
uses exactly the original support and its genuine failed inventory. -/
theorem regional_mesh (L:Support n)(a:V)(t:T)(M h:ℝ)(mp:0≤M)(hp:0<h):
    let f:=regionalProbe A L a t M
    let z:=fun U=>labelProbe M h (f U)
    Measurable z ∧ UsesFinal P.p.threshold L z ∧ (∀g U,z (gauge g U)=z U) ∧
      ∀U,‖f U-readProbe M h (z U)‖≤2*h:=by
  intro f z
  obtain ⟨borel,win,rot,cap⟩:=bounded_regional_probe A L a t M mp
  exact ⟨(probe_label_measurable M h).comp borel,fun U W hui flags=>congrArg (labelProbe M h) (win U W hui flags),
    fun g U=>congrArg (labelProbe M h) (rot g U),fun U=>probe_mesh_cost M h hp _ (cap U)⟩

omit [Fintype V] in
/-- A nonlocal, jointly distributed complex exterior is legal for the fee.
The event may also depend on the whole path. The physical/mesh clocks and
the original law are unchanged; only the numerical bounded reading is rounded. -/
theorem regional_mesh_exterior {Z:Type*}[MeasurableSpace Z](law:Measure Z)[IsFiniteMeasure law]
    (π:Z→Config G n)(pm:Measurable π)(L:Support n)(a:V)(t:T)(M h:ℝ)(mp:0≤M)(hp:0<h)
    (E:Set Z)(em:MeasurableSet E)(H:Z→ℂ)(h2:MemLp H 2 law):
    let f:=fun z=>regionalProbe A L a t M (π z)
    let q:=fun z=>readProbe M h (labelProbe M h (f z))
    Integrable (fun z=>E.indicator H z*(f z-q z)) law ∧
    ‖∫z,E.indicator H z*(f z-q z) ∂law‖≤(2*h)*(Real.sqrt (∫z,‖H z‖^2 ∂law)*Real.sqrt (law.real E)):=by
  intro f q
  obtain ⟨meas,_,_,cap⟩:=bounded_regional_probe A L a t M mp
  exact mesh_observation_exterior law f (meas.comp pm) M h hp (fun z=>cap (π z)) E em H h2

end YM.Integration.FVA1Physical.Exchange.RoseCut
