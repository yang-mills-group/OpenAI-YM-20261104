import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6ActualThermal
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6ScalarThermal
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6MeasuredExterior

/-! The positive, all-fixed-order near-energy comparison used on the
original exterior with its other two physical energy arms. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.F6Regular
open Function Filter Finset MeasureTheory Lattice RG YM.Wilson OPE.Therm Marked.Inherited RoseCut
open scoped Classical BigOperators
open private fibre_prob from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionNormalizedConnected
open private subenv from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6RegularCovariance
open private fillPatch_meas from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6OriginalExterior
open private general_measured from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6MeasuredExterior
open private scalar_ratio from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6PolynomialLaw
open private envelope_pair from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6ThreeArms
variable {G:Gauge}{n:Side}
local notation "Fld" => Config G n

def rawPatch (I:Finset (Edge (Site n)))(f:Fld→ℝ)(w:({b:Edge (Site n)//b∉I} → G.El) → Fld→ℝ)
    (o:({b:Edge (Site n)//b∉I} → G.El)):ℝ:=
  let J:=fillPatch I o;let η:=Measure.pi (fun _:↥I=>G.probHaar)
  (∫x,w o (J x)*f (J x) ∂η)/(∫x,w o (J x) ∂η)

def originalOne (R:Rep G n)(I:Finset (Edge (Site n)))(f:Fld→ℝ):=rawPatch I f (fun _=>R.eval)
def finiteOne (R:Rep G n)(I:Finset (Edge (Site n)))(f:Fld→ℝ)(k:ℕ):=
  rawPatch I f (fun o=>patchTaylorDensity R (fillPatch I o 1) k)

theorem original_one_finite (R:Rep G n){σ C Λ ε ξ:ℝ}(law:R.Lawful σ C Λ ε ξ)(pos:∀u,0<R.eval u)
    (I:Finset (Edge (Site n)))(width:1≤R.p.supportExponent)(f:Fld→ℝ)(fe:Envelope f)(M:ℝ)(fee:∀u,|f u|≤M)(k:ℕ)
    (o:({b:Edge (Site n)//b∉I} → G.El)):
    let L:=I.image Prod.fst;let ω:=((halo 8 L).card:ℝ)*(2*Push.GridApprox.Attach.hitConstant R.p.B*ε)
    ω≤1/4 → |finiteOne R I f k o-originalOne R I f o|≤8*M*ω^(k+1):=by
  intro L ω small
  let J:=fillPatch I o;let η:=Measure.pi (fun _:↥I=>G.probHaar)
  let u:=R.eval ∘ J;let ν:=fibreLaw η u;let d:=fun x=>referenceTilt R (J 1) (J x)
  let K:=fun x=>Real.exp (d x)*tiltTaylor k (-d x)
  have jm:=fillPatch_meas I o
  have est {a:Fld→ℝ}(e:Envelope a):Envelope (a ∘ J):=⟨e.meas.comp jm,e.cost.choose,fun x=>e.cost.choose_spec _⟩
  have ue:Envelope u:=est (R.envelope law)
  have all:Envelope (R.activities.additive R.p):=⟨R.activities.E_measurable law.labels.regular,(Activities.ESeries law.labels).bound⟩
  have de:Envelope d:=subenv (est all) (Envelope.const _)
  have cap(x):|d x|≤ω:=by
    apply RoseCut.FiledAction.funded_edit R.p width law.labels (J x) (J 1)
    intro e outside;have miss:e∉I:=fun hit=>outside (Finset.mem_image.mpr ⟨e,hit,rfl⟩)
    simp only [J,fillPatch,dif_neg miss]
  have zp:0<∫x,u x ∂η:=by
    apply (integral_pos_iff_support_of_nonneg (fun x=>(pos (J x)).le) (ue.integrable η)).2
    rw [show Function.support (fun x=>R.eval (J x))=Set.univ from Set.eq_univ_of_forall (fun x=>(pos (J x)).ne')];simp [η]
  letI:IsProbabilityMeasure ν:=fibre_prob η (ue.integrable η) (fun x=>(pos _).le) zp
  have ans:=scalar_thermal_quotient ν d (f ∘ J) de (est fe) M ω ((abs_nonneg _).trans (cap 1)) small cap (fun x=>fee _) k
  have eng (g:(↥I→G.El)→ℝ):(∫x,g x ∂ν)=(∫x,u x*g x ∂η)/(∫x,u x ∂η):=
    general_measured η ue.meas (fun x=>(pos _).le) g
  have q:(∫x,K x*f (J x) ∂ν)/(∫x,K x ∂ν)=finiteOne R I f k o:=by
    rw [eng,eng,div_div_div_cancel_right₀ zp.ne']
    unfold finiteOne rawPatch;apply congrArg (·/ _);apply integral_congr_ae;filter_upwards with x
    dsimp only [patchTaylorDensity,K,u,d,J,Function.comp_apply];ring
  have raw:=ans.2
  change |(∫x,K x*f (J x) ∂ν)/(∫x,K x ∂ν)-(∫x,f (J x) ∂ν)|≤8*M*ω^(k+1) at raw
  rw [q,eng] at raw
  exact raw

theorem original_exterior_thermal {G:Gauge}(H:History G)(sel:H.Selected){N j per:ℕ}(live:j≤N)
    (I:Finset (Edge (Site (H.S.side j per))))(width:1≤(H.rep N per j).p.supportExponent)
    (A:Config G (H.S.side j per)→ℝ)(ea:Envelope A)(M:ℝ)(bound:∀U,|A U|≤M)(k:ℕ)
    (B C:({b:Edge (Site (H.S.side j per)) // b∉I}→G.El)→ℝ)(eb:Envelope B)(ec:Envelope C):
    let R:=H.rep N per j;let L:=I.image Prod.fst;let μ:=originalExterior H N per j I
    let ω:=((halo 8 L).card:ℝ)*(2*Push.GridApprox.Attach.hitConstant R.p.B*H.levels.clock.allowance j)
    ω≤1/4 →
    |∫o,centeredPair μ B C o*(finiteOne R I A k o-originalOne R I A o) ∂μ|≤
      8*M*ω^(k+1)*(∫o,|centeredPair μ B C o| ∂μ):=by
  intro R L μ ω small
  letI:IsProbabilityMeasure (scene H N per j):=probability sel live
  have proj:Measurable (fun U:Config G (H.S.side j per)=>fun b:{b:Edge (Site (H.S.side j per)) // b∉I}=>U b.1):=by
    apply measurable_pi_lambda;intro b;exact measurable_pi_apply _
  letI:IsProbabilityMeasure μ:=Measure.isProbabilityMeasure_map proj.aemeasurable
  have mn:=envelope_pair μ B C eb ec
  have cap:=original_one_finite R (sel.represents N per j live).good (SectorNext.Vacuum.strictly H sel N per j live) I width A ea M bound k
  rw [←integral_const_mul]
  apply norm_integral_le_of_norm_le (f:=fun o=>centeredPair μ B C o*(finiteOne R I A k o-originalOne R I A o))
    ((mn.integrable μ).norm.const_mul (8*M*ω^(k+1))) ?_
  filter_upwards with o
  rw [Real.norm_eq_abs,abs_mul,mul_comm (8*M*ω^(k+1))]
  exact mul_le_mul_of_nonneg_left (cap o small) (abs_nonneg _)

end YM.Integration.FVA1Physical.Exchange.F6Regular
