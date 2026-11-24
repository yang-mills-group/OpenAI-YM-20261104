import YM.Integration.WilsonPhysicalPositionBornTransition
import YM.Integration.WilsonPositionPrescribedLift

/-! One calibrated physical home supplies the engineering-adjusted position bank
at every dilated set of ordinates in a compact scale interval. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawHome
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize MeasureTheory Next.UVStress
open scoped Topology Classical BigOperators
open private engine from YM.Integration.WilsonPhysicalPositionBornTransition
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(J:ℝ→tower S)(V:Store G)

abbrev positioned := WilsonPositionPrescribedFrame.positioned F J V

def engineering (d:ℕ)(t:ℝ):FieldEnd G d:=
  (fields C.labels d).toLinearMap ∘ₗ Pert.Scale.gear C.labels d t ∘ₗ (fields C.labels d).symm.toLinearMap

def bank (d:ℕ)(r t:ℝ):Prediction G d:=
  recruit (engineering (C:=C) d t)
    (WilsonPhysicalPositionHomeDilation.samples F (positioned F J V) r t d)

def value {d n:ℕ}(v:Fin n→(Bel C.book).Field d)(r t:ℝ)(x:Points n):ℂ:=
  measured F none (positioned F J V r) (d:=fun _=>d) (fun i=>Pert.Scale.gear C.labels d t (v i)) r (t • x)

theorem observed {d n:ℕ}(v:Fin n→Sec G d)(φ:Test n){r t:ℝ}(hr:0<r)(ht:0<t):
    bank F J V d r t n φ v=φ.applyTo (value F J V (fun j=>(fields C.labels d).symm (v j)) r t):=by
  change WilsonPositionPrescribedScreen.hierarchy F (fun _=>positioned F J V r) d (r*t) n φ
    (fun i=>engineering (C:=C) d t (v i))=_
  rw [WilsonPositionPrescribedScreen.actual F _ _ _ _ _ (mul_pos hr ht)]
  apply congrArg φ.applyTo
  funext x
  unfold value measured
  simp only [engineering,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,mul_smul]

theorem pointwise (lead:Leading F J){d n:ℕ}(v:Fin n→(Bel C.book).Field d)
    {I:Type*}{l:Filter I}{r t:I→ℝ}{x:I→Points n}{s:ℝ}{y:Points n}
    (hr:Tendsto r l trail)(ht:Tendsto t l (𝓝 s))(hs:0<s)(hx:Tendsto x l (𝓝 y))(hy:y∈conf n):
    Tendsto (fun i=>value F J V v (r i) (t i) (x i)) l (𝓝 (WickGoal (C:=C) (d:=fun _=>d) v y)):=by
  let X:=(Bel C.book).Field d
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  let A:=WilsonPositionPrescribedLift.field F J V d
  have hA:Tendsto A trail (𝓝 (ContinuousLinearMap.id ℂ ((Bel C.book).Field d))):=
    tendsto_iff_norm_sub_tendsto_zero.mpr (WilsonPositionPrescribedLift.near F J V lead d)
  have arms (j:Fin n):Tendsto (fun i=>A (r i) (Pert.Scale.gear C.labels d (t i) (v j))) l
      (𝓝 (Pert.Scale.gear C.labels d s (v j))):=
    Dash.arcing (X:=ContinuousLinearMap.id ℂ X) (hA.comp hr) (engine ht (tendsto_const_nhds (x:=v j)))
  have read:=WilsonPhysicalPositionBornTransition.several F J lead hr (ht.smul hx) (Work.A05.smul_conf hs hy) arms
  rw [←show WickGoal (C:=C) (d:=fun _=>d) (fun j=>Pert.Scale.gear C.labels d s (v j)) (s•y)=
      WickGoal (C:=C) (d:=fun _=>d) v y from Pert.Scale.points_equ (F:=C.labels) hy v hs.ne']
  exact read

theorem compact (lead:Leading F J){d n:ℕ}(v:Fin n→(Bel C.book).Field d){K:Set (Points n)}
    (compact:IsCompact K)(apart:K⊆conf n){c b δ:ℝ}(hc:0<c)(hδ:0<δ):
    ∀ᶠ r in trail,∀ t∈Icc c b,∀x∈K,
      ‖value F J V v r t x-WickGoal (C:=C) (d:=fun _=>d) v x‖<δ:=by
  let P(r:ℝ)(z:ℝ×Points n):Prop:=‖value F J V v r z.1 z.2-WickGoal (C:=C) (d:=fun _=>d) v z.2‖<δ
  have uniform:=Frame.compact_event ℝ (isCompact_Icc.prod compact) P (l:=trail) (V:=Icc c b ×ˢ K) (by
    rintro ⟨s,y⟩ ⟨hs,hy⟩
    let l:=trail ×ˢ 𝓝 (s,y)
    have hpair:Tendsto (fun z:ℝ×(ℝ×Points n)=>z.2) l (𝓝 (s,y)):=tendsto_snd
    have htime:=continuous_fst.continuousAt.tendsto.comp hpair
    have hspace:=continuous_snd.continuousAt.tendsto.comp hpair
    have pos:=pointwise F J V lead v (l:=l) tendsto_fst htime (hc.trans_le hs.1) hspace (apart hy)
    have free:=((WickGoal_tied (C:=C) (d:=fun _=>d) v (apart hy)).continuousAt.tendsto).comp hspace
    have small:=((pos.sub free).norm).eventually_lt_const (show ‖WickGoal (C:=C) v y-WickGoal (C:=C) v y‖<δ by simpa using hδ)
    exact small)
  filter_upwards [uniform] with r h t ht x hx using h (t,x) ⟨ht,hx⟩

private theorem weight {n:ℕ}(φ:Test n)(a:Points n→ℂ)(δ:ℝ)
    (h:∀x∈tsupport φ,‖a x‖≤δ):‖φ.applyTo a‖≤(∫ x,‖φ x‖)*δ:=by
  unfold Test.applyTo
  rw [←integral_mul_const]
  apply norm_integral_le_of_norm_le
    ((φ.continuous.norm.integrable_of_hasCompactSupport φ.hasCompactSupport.norm).mul_const _)
    (ae_of_all _ fun x=>?_)
  by_cases hz:φ x=0
  · simp [hz]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (h x (subset_closure (mem_support.mpr hz))) (norm_nonneg _)

theorem smeared (lead:Leading F J){d n:ℕ}(v:Fin n→Sec G d)(φ:Test n){c b ε:ℝ}(hc:0<c)(he:0<ε):
    ∀ᶠ r in trail,∀t∈Icc c b,‖bank F J V d r t n φ v-reference G d n φ v‖<ε:=by
  let u(j:Fin n):=(fields C.labels d).symm (v j)
  let mass:=∫ x,‖φ x‖
  have hm:0 ≤ mass:=integral_nonneg fun _=>norm_nonneg _
  let δ:=ε/(mass+1)
  have hδ:0<δ:=div_pos he (by linarith)
  have cost:mass*δ<ε:=calc
    mass*δ<(mass+1)*δ:=mul_lt_mul_of_pos_right (lt_add_one _) hδ
    _=ε:=by dsimp [δ];field_simp
  filter_upwards [compact F J V lead u φ.hasCompactSupport φ.tsupport_subset (b:=b) hc hδ,RG17.positiveLength] with r price hr t ht
  let a:=value F J V u r t
  let w:=WickGoal (C:=C) (d:=fun _=>d) u
  have hw:ContinuousOn w (conf n):=fun x hx=>(WickGoal_tied u hx).continuousAt.continuousWithinAt
  have ha:ContinuousOn a (conf n):=by
    have h:=WilsonOrdinaryPositionPoll.regular F (fun _=>positioned F J V r)
      (fun j=>Pert.Scale.gear C.labels d t (u j)) (mul_pos hr (hc.trans_le ht.1))
    have eq:a=measured F none (positioned F J V r) (d:=fun _=>d) (fun j=>Pert.Scale.gear C.labels d t (u j)) (r*t):=by
      funext x
      simp only [a,value,measured,mul_smul]
    rw [eq]
    exact h
  have base:reference G d n φ v=φ.applyTo w:=by
    apply congrArg φ.applyTo
    funext x
    exact (WilsonPositionPrescribedScreen.zero (C:=C) d n v x).symm
  rw [observed F J V v φ hr (hc.trans_le ht.1),base]
  change ‖φ.applyTo a-φ.applyTo w‖<ε
  rw [←test_sub a w ha hw]
  exact (weight φ (a-w) δ (fun x hx=>(price t ht x hx).le)).trans_lt cost

abbrev Ratio:={t:ℝ // t∈Icc (1/2:ℝ) 1}
abbrev sweep:Filter (ℝ×Ratio):=trail ×ˢ ⊤

theorem original (lead:Leading F J)(d:ℕ):
    (V.survey d).Via (fun z:ℝ×Ratio=>bank F J V d z.1 z.2.val) (u:=sweep):=by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  apply Metric.tendsto_nhds.mpr
  intro ε he
  let W:=(V.survey d).scope i
  let v(k:Fin W.n):=Module.finBasis ℝ (Sec G d) (j k)
  have p:=smeared F J V lead v W.t (b:=1) (c:=1/2) (by norm_num) he
  filter_upwards [(tendsto_fst (f:=trail) (g:=(⊤:Filter Ratio))).eventually p] with z hz
  rw [dist_eq_norm]
  exact hz z.2.val z.2.property

end YM.Integration.WilsonPositionScaleLawHome
end
