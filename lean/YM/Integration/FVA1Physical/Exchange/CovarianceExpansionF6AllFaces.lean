import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6OriginalExterior
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionPairDetectorPrice

/-! Truncate only the long incident masked regular action on a physical
patch. Its exact nonlinear effect on the connected three-arm reading is
purchased under both normalized real Haar laws before any expansion. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.F6Regular
open Function Filter Finset MeasureTheory Lattice RG YM.Wilson OPE.Therm Marked.Inherited RoseCut
open YM.Integration.FVA1Physical.Replica
open scoped Classical BigOperators
open private subenv from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6RegularCovariance
open private fillPatch_meas from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6OriginalExterior
variable {G:Gauge}{n:Side}
local notation "Fld" => Config G n

def shortDensity (R:Rep G n)(L:Support n)(cut:ℕ)(U:Fld):ℝ:=
  R.eval U*Real.exp (R.activities.additive R.p U-shortRegular R.activities R.p L cut U)

theorem short_density_retains_gas (R:Rep G n)(L:Support n)(cut:ℕ)(U:Fld):
    shortDensity R L cut U=
      Real.exp (R.v*Fintype.card (Site n)-R.path.inChannels R.clip R.p R.beta U-shortRegular R.activities R.p L cut U)*
      R.activities.gas R.p U:=by
  rw [shortDensity,Real.exp_sub,←mul_div_assoc,regular_tilt_density]
  simp only [Real.exp_sub];ring

theorem all_seven_short (H:History G)(sel:H.Selected){N j per:ℕ}(live:j≤N)
    (I:Finset (Edge (Site (H.S.side j per))))(cut:ℕ)(width:1≤(H.rep N per j).p.supportExponent)
    (o:(b:{b:Edge (Site (H.S.side j per)) // b∉I}) → G.El)
    (h:Fin 3 → Config G (H.S.side j per)→ℂ)(eh:∀i,Envelope (h i))(M:Fin 3→ℝ)(mn:∀i,0≤M i)(paid:∀i u,‖h i u‖≤M i):
    let R:=H.rep N per j;let L:=I.image Prod.fst;let J:=fillPatch I o;let μ:=Measure.pi (fun _:↥I=>G.probHaar)
    let F:=physicalProperRows (fun i=>h i ∘ J)
    let a:=fun i=>FrozenRead.meanOn μ (R.eval ∘ J) (F i)
    let b:=fun i=>FrozenRead.meanOn μ (shortDensity R L cut ∘ J) (F i)
    ‖properThree a-properThree b‖≤26*M 0*M 1*M 2 * min 1 (sliceFare R.p (halo 8 L) cut (H.levels.clock.allowance j)):=by
  intro R L J μ F a b
  have law:=(sel.represents N per j live).good
  have positive:=SectorNext.Vacuum.strictly H sel N per j live
  let r:=fun x=>shortRegular R.activities R.p L cut (J x)-R.activities.additive R.p (J x)
  let fee:=sliceFare R.p (halo 8 L) cut (H.levels.clock.allowance j)
  let t:=min 1 fee
  have keep (x y):RoseCut.FiledAction.Kept (J x) (J y) L:=by
    intro e outside;have he:e∉I:=fun hi=>outside (Finset.mem_image.mpr ⟨e,hi,rfl⟩)
    simp only [J,fillPatch,dif_neg he]
  have osc (x y):|r x-r y|≤2*fee:=by
    have step:=(original_short_increment R.activities R.p law.labels width L cut (J x) (J y) (keep x y)).2
    rw [show r x-r y= -((R.activities.additive R.p (J x)-R.activities.additive R.p (J y))-
           (shortRegular R.activities R.p L cut (J x)-shortRegular R.activities R.p L cut (J y))) by dsimp only [r];ring,abs_neg]
    exact step
  have fn:0≤fee:=by have z:=osc 1 1;simp only [sub_self,abs_zero] at z;linarith only [z]
  have exc:pairExcess r t=∅:=by
    apply Set.eq_empty_iff_forall_notMem.mpr;rintro ⟨x,y⟩
    change ¬ t < cap (r x-r y);apply not_lt_of_ge
    apply min_le_min (le_refl 1);exact (div_le_iff₀ (by norm_num : (0:ℝ)<2)).2 (by linarith only [osc x y])
  have jm:=fillPatch_meas I o
  have pull {α:Type}[NormedAddCommGroup α][MeasurableSpace α]{f:Config G (H.S.side j per)→α}(e:Envelope f):Envelope (f ∘ J):=
    ⟨e.meas.comp jm,e.cost.choose,fun x=>e.cost.choose_spec _⟩
  have all:Envelope (R.activities.additive R.p):=⟨R.activities.E_measurable law.labels.regular,(Activities.ESeries law.labels).bound⟩
  have sl (k):Envelope (sliceLog R.activities R.p (halo 8 L) k):=by
    have s:=hit_slice_log R.activities R.p law.labels.boundE law.labels.regular width (halo 8 L) k;exact ⟨s.1,_,s.2⟩
  have sh:Envelope (shortRegular R.activities R.p L cut):=subenv (sl 0) (sl cut)
  have rel:Envelope r:=subenv (pull sh) (pull all)
  have ea:Envelope (R.eval ∘ J):=pull (R.envelope law)
  have eb:Envelope (shortDensity R L cut ∘ J):=pull ((R.envelope law).mul (subenv all sh).exp)
  have pa(x):0<R.eval (J x):=positive _
  have pb(x):0<shortDensity R L cut (J x):=mul_pos (pa _) (Real.exp_pos _)
  have mass {W:(↥I → G.El)→ℝ}(ew:Envelope W)(pw:∀x,0<W x):0<∫x,W x ∂μ:=by
    apply (integral_pos_iff_support_of_nonneg (fun x=>(pw x).le) (ew.integrable μ)).2
    rw [show Function.support W=Set.univ from Set.eq_univ_of_forall (fun x=>(pw x).ne')];simp [μ]
  have change(x):Real.log ((R.eval ∘ J) x)-Real.log ((shortDensity R L cut ∘ J) x)=r x+0:=by
    simp only [Function.comp_apply,shortDensity,Real.log_mul (pa x).ne' (Real.exp_ne_zero _),Real.log_exp,r];ring
  have answer:=pair_excess_seven μ (k:=fun _=>1) measurable_const ea.meas eb.meas (fun _=>zero_le_one) pa pb rel.meas 0 change t (le_min zero_le_one fn)
    (fun i=>h i ∘ J) (fun i=>pull (eh i)) M mn (fun i x=>paid i _)
  simpa only [one_mul,exc,Measure.restrict_empty,integral_zero_measure,zero_div,add_zero] using
    (answer (by simpa only [one_mul] using ea.integrable μ) (by simpa only [one_mul] using eb.integrable μ)
      (by simpa only [one_mul] using mass ea pa) (by simpa only [one_mul] using mass eb pb))

end YM.Integration.FVA1Physical.Exchange.F6Regular
