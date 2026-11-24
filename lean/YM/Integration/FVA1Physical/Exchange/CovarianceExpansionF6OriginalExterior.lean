import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6RegularCovariance
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionDatedRepBond
import YM.OPE.Therm.Law

/-! The original exterior marginal, its true finite Haar patch and the
numerical weak regular-action response of the three-energy position test.
The exterior arms may be arbitrarily correlated before their centering. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1900000
namespace YM.Integration.FVA1Physical.Exchange.F6Regular
open Function Filter Finset MeasureTheory Lattice RG YM.Wilson OPE.Therm RoseCut
open Marked.Inherited RoseCut.FiledAction OriginalMixedWilson
open scoped Classical BigOperators
open private fibre_prob from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionNormalizedConnected
variable {G:Gauge}{n:Side}
local notation "Fld" => Config G n

def fillPatch (I:Finset (Edge (Site n)))(o:(b:{b:Edge (Site n) // b∉I})→G.El)(u:(b:↥I)→G.El)
    (b:Edge (Site n)):G.El:=if h:b∈I then u ⟨b,h⟩ else o ⟨b,h⟩

private theorem fillPatch_meas (I:Finset (Edge (Site n)))(o:(b:{b:Edge (Site n) // b∉I})→G.El):
    Measurable (fillPatch I o):=by
  apply measurable_pi_lambda;intro b
  by_cases h:b∈I
  · simpa only [fillPatch,dif_pos h] using (measurable_pi_apply (⟨b,h⟩:↥I) : Measurable (fun x:↥I→G.El=>x ⟨b,h⟩))
  simpa only [fillPatch,dif_neg h] using (measurable_const (a:=o ⟨b,h⟩):Measurable (fun _:(↥I→G.El)=>o ⟨b,h⟩))

def tiltedPatch (R:Rep G n)(I:Finset (Edge (Site n)))(o:(b:{b:Edge (Site n) // b∉I})→G.El):Measure (↥I→G.El):=
  let J:=fillPatch I o
  fibreLaw (Measure.pi (fun _:↥I=>G.probHaar)) (fun u=>R.eval (J u)*Real.exp (R.activities.additive R.p (J u)))

theorem regular_tilt_density (R:Rep G n)(W:Fld):
    R.eval W*Real.exp (R.activities.additive R.p W)=
      Real.exp (R.v*Fintype.card (Site n)-R.path.inChannels R.clip R.p R.beta W)*R.activities.gas R.p W:=by
  rw [Rep.eval,mul_right_comm,←Real.exp_add];unfold Rep.exponent;rw [sub_add_cancel]

private theorem tilted_probability (R:Rep G n){σ C Λ ε ξ:ℝ}(law:R.Lawful σ C Λ ε ξ)(pos:∀U,0<R.eval U)
    (I:Finset (Edge (Site n)))(o:(b:{b:Edge (Site n) // b∉I})→G.El):IsProbabilityMeasure (tiltedPatch R I o):=by
  let J:=fillPatch I o
  let μ:=Measure.pi (fun _:↥I=>G.probHaar)
  let w:=fun u=>R.eval (J u)*Real.exp (R.activities.additive R.p (J u))
  have ae:Envelope (R.activities.additive R.p):=⟨R.activities.E_measurable law.labels.regular,(Activities.ESeries law.labels).bound⟩
  have pe:Envelope (fun U=>R.eval U*Real.exp (R.activities.additive R.p U)):=(R.envelope law).mul ae.exp
  have we:Envelope w:=⟨pe.meas.comp (fillPatch_meas I o),pe.cost.choose,fun u=>pe.cost.choose_spec (J u)⟩
  have wp(u):0<w u:=mul_pos (pos (J u)) (Real.exp_pos _)
  have total:0<∫u,w u ∂μ:=by
    apply (integral_pos_iff_support_of_nonneg (fun u=>(wp u).le) (we.integrable μ)).2
    rw [show Function.support w=Set.univ from Set.eq_univ_of_forall (fun u=>(wp u).ne')];simp [μ]
  exact fibre_prob μ (we.integrable μ) (fun u=>(wp u).le) total

/-- A signed first regular insertion on this physical fibre. The reference
filling is fixed before the three field insertions, on the same exterior. -/
def patchInsertion (R:Rep G n)(I:Finset (Edge (Site n)))(D:Fld→ℝ)(f:Fld→ℝ)
    (o:(b:{b:Edge (Site n) // b∉I})→G.El):ℝ:=
  let J:=fillPatch I o
  firstRead (tiltedPatch R I o) (f ∘ J) (fun a=>D (J a)-D (J 1))

def originalExterior (H:History G)(N per j:ℕ)(I:Finset (Edge (Site (H.S.side j per)))):=
  Measure.map (fun U:Config G (H.S.side j per)=>fun b:{b:Edge (Site (H.S.side j per)) // b∉I}=>U b.1)
    (scene H N per j)

/-- Signed F6 covariance tail at any admitted cut, including the first
nonbare date, after averaging over the exact original exterior and both
of its remaining centered arms. No independence of those arms is needed. -/
theorem actual_exterior_first_insertion (H:History G)(sel:H.Selected){N j per:ℕ}(live:j≤N)
    (I:Finset (Edge (Site (H.S.side j per))))(cut:ℕ)(width:1≤(H.rep N per j).p.supportExponent)
    (f:Config G (H.S.side j per)→ℝ)(ef:Envelope f)(M:ℝ)(bound:∀U,|f U|≤M)
    (Y:({b:Edge (Site (H.S.side j per)) // b∉I}→G.El)→ℝ)
    (outer:Integrable Y (originalExterior H N per j I)):
    let R:=H.rep N per j;let L:=I.image Prod.fst;let μ:=originalExterior H N per j I
    let G₀:=patchInsertion R I (R.activities.additive R.p) f
    let G₁:=patchInsertion R I (shortRegular R.activities R.p L cut) f
    |∫o,Y o*(G₀ o-G₁ o) ∂μ|≤4*sliceFare R.p (halo 8 L) cut (H.levels.clock.allowance j)*M*(∫o,|Y o| ∂μ):=by
  intro R L μ G₀ G₁
  have law:=(sel.represents N per j live).good
  have pos:=SectorNext.Vacuum.strictly H sel N per j live
  let fee:=sliceFare R.p (halo 8 L) cut (H.levels.clock.allowance j)
  have point(o):|G₀ o-G₁ o| ≤ 4*fee*M:=by
    let J:=fillPatch I o
    let ν:=tiltedPatch R I o
    letI:IsProbabilityMeasure ν:=tilted_probability R law pos I o
    have fixed(u):RoseCut.FiledAction.Kept (J u) (J 1) L:=by
      intro b hb;have off:b∉I:=fun h=>hb (Finset.mem_image.mpr ⟨b,h,rfl⟩)
      simp only [J,fillPatch,dif_neg off]
    have φ:Envelope (f ∘ J):=⟨ef.meas.comp (fillPatch_meas I o),ef.cost.choose,fun u=>ef.cost.choose_spec _⟩
    have raw:=paid_conditional_insertion ν R.activities R.p law.labels width L cut J (fillPatch_meas I o)
      (J 1) fixed (f ∘ J) φ
    have mn:|∫x,f (J x) ∂ν| ≤ M:=by simpa [←Real.norm_eq_abs,measureReal_def] using
      (norm_integral_le_of_norm_le_const (μ:=ν) (f:=fun x=>f (J x)) (Filter.Eventually.of_forall (fun x=>by simpa only [Real.norm_eq_abs] using bound (J x))))
    have amp:∫x,|f (J x)-∫y,f (J y) ∂ν| ∂ν ≤ 2*M:=by
      apply (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _=>abs_nonneg _)) (integrable_const (2*M)) ?_).trans_eq
      · simp
      filter_upwards with x
      exact (abs_sub ..).trans ((add_le_add (bound _) mn).trans_eq (two_mul _).symm)
    have nonneg:0≤fee:=(norm_nonneg _).trans ((hit_slice_log R.activities R.p law.labels.boundE law.labels.regular width (halo 8 L) cut).2 (J 1))
    exact raw.trans ((mul_le_mul_of_nonneg_left amp (by change 0≤2*fee;positivity)).trans_eq (by ring))
  rw [←integral_const_mul]
  apply norm_integral_le_of_norm_le (f:=fun o=>Y o*(G₀ o-G₁ o)) (outer.norm.const_mul (4*fee*M)) ?_
  filter_upwards with o
  rw [Real.norm_eq_abs,abs_mul,mul_comm (4*fee*M)]
  exact mul_le_mul_of_nonneg_left (point o) (abs_nonneg _)

end YM.Integration.FVA1Physical.Exchange.F6Regular
