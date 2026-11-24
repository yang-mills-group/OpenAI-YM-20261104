import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6PolynomialLaw

/-! The degree is chosen on the actual selected physical history. Both
the finite polynomial vacuum and the original interacting vacuum have their
own true quiet on the same finite Haar patch. -/
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

def referenceTilt (R:Rep G n)(ref u:Fld):ℝ:=R.activities.additive R.p u-R.activities.additive R.p ref

def patchTaylorDensity (R:Rep G n)(ref:Fld)(n:ℕ)(u:Fld):ℝ:=
  let d:=referenceTilt R ref u
  R.eval u*(Real.exp d*tiltTaylor n (-d))

/-- Inspecting the two factors confirms that the independently normalized
finite vacuum retains the exact physical path, original gas and the
physical reference scalar. -/
theorem polynomial_has_original_path (R:Rep G n)(ref u:Fld)(k:ℕ):
    patchTaylorDensity R ref k u=
       Real.exp (R.v*Fintype.card (Site n)-R.path.inChannels R.clip R.p R.beta u-R.activities.additive R.p ref)*
       R.activities.gas R.p u*tiltTaylor k (-referenceTilt R ref u):=by
  rw [patchTaylorDensity,←mul_assoc]
  apply congrArg (·*_)
  rw [referenceTilt,Real.exp_sub,←mul_div_assoc,regular_tilt_density];simp only [Real.exp_sub];ring

theorem actual_seven_thermal (H:History G)(sel:H.Selected){N j per:ℕ}(live:j≤N)
    (I:Finset (Edge (Site (H.S.side j per))))(width:1≤(H.rep N per j).p.supportExponent)
    (o:(b:{b:Edge (Site (H.S.side j per)) // b∉I}) → G.El)(k:ℕ)
    (h:Fin 3 → Config G (H.S.side j per) → ℂ)(eh:∀i,Envelope (h i))(M:Fin 3→ℝ)(mn:∀i,0≤M i)(pay:∀i u,‖h i u‖≤M i):
    let R:=H.rep N per j;let L:=I.image Prod.fst;let J:=fillPatch I o;let μ:=Measure.pi (fun _:↥I=>G.probHaar)
    let ω:=((halo 8 L).card:ℝ)*(2*Push.GridApprox.Attach.hitConstant R.p.B*H.levels.clock.allowance j)
    let v:=fun x=>patchTaylorDensity R (J 1) k (J x);let F:=physicalProperRows (fun i=>h i ∘ J)
    let A:=fun i=>FrozenRead.meanOn μ (R.eval ∘ J) (F i);let B:=fun i=>FrozenRead.meanOn μ v (F i)
    ω≤1/4 → (0<∫x,v x ∂μ) ∧ ‖properThree A-properThree B‖≤26*M 0*M 1*M 2*(4*ω^(k+1)):=by
  intro R L J μ ω v F A B small
  have law:=(sel.represents N per j live).good
  let d:=fun x=>referenceTilt R (J 1) (J x)
  have jm:=fillPatch_meas I o
  have pull {V:Type}[Norm V][MeasurableSpace V]{f:Config G (H.S.side j per) → V}(ef:Envelope f):Envelope (f ∘ J):=
    ⟨ef.meas.comp jm,ef.cost.choose,fun x=>ef.cost.choose_spec _⟩
  have all:Envelope (R.activities.additive R.p):=⟨R.activities.E_measurable law.labels.regular,(Activities.ESeries law.labels).bound⟩
  have de:Envelope d:=subenv (pull all) (Envelope.const _)
  have bound(x):|d x|≤ω:=by
    apply RoseCut.FiledAction.funded_edit R.p width law.labels (J x) (J 1)
    intro e out;have h:e∉I:=fun h=>out (Finset.mem_image.mpr ⟨e,h,rfl⟩)
    simp only [J,fillPatch,dif_neg h]
  exact seven_thermal_polynomial μ (R.eval ∘ J) d (pull (R.envelope law)) (fun x=>SectorNext.Vacuum.strictly H sel N per j live (J x)) de ω ((abs_nonneg (d 1)).trans (bound 1)) small bound
    k (fun i=>h i ∘ J) (fun i=>pull (eh i)) M mn (fun i x=>pay i _)

end YM.Integration.FVA1Physical.Exchange.F6Regular
