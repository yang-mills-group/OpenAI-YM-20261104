import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionGaugeAperture
import YM.Integration.FVA1Physical.CommonCover.CurvatureDampedTariff

/-! Any positive-Haar open-bond patch retains positive regular mass. This
holds for every positive integrable numerical vacuum, independently of any
gauge symmetry it has. No lower bound uniform in volume is accessed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open MeasureTheory Filter Set RG Wilson Lattice Source Labels Multi.Maquette
open scoped Classical BigOperators
open private real_patch_event from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionGaugeAperture
variable {G:Gauge}{f:Side}

theorem patch_collar_positive (e:Lattice.Edge (Site f))(distinct:e.1+Lattice.step e.2≠e.1)
    (D:Set G.El)(dm:MeasurableSet D)(dp:0<G.probHaar.real D)(p:BudgetPoint)(K:Support f):
    let B:=OlderPrice.curvatureCollar (G:=G) p K;let M:=openPatch e D∩B;let μ:=prior G f
    0<μ B ∧ 0<μ M:=by
  intro B M μ
  haveI:μ.IsOpenPosMeasure:=by dsimp only [μ,prior];infer_instance
  obtain ⟨nb,mb,sym⟩:=OlderPrice.collar_geometry (G:=G) p K
  have live:0<μ B:=Measure.measure_pos_of_mem_nhds μ nb
  have pay:=real_patch_event e distinct D dm B mb (fun a U=>sym (endpointGauge e.1 a) U)
    (fun _=>(1:ℝ)) (Envelope.const 1) (fun _ _=>rfl)
  rw [Measure.restrict_restrict mb] at pay
  have cash:μ.real M=G.probHaar.real D*μ.real B:=by
    change μ.real (openPatch e D∩B)=_
    rw [inter_comm]
    simpa using pay
  have priced:0<μ.real M:=cash.trans_gt (mul_pos dp (ENNReal.toReal_pos live.ne' (measure_ne_top _ _)))
  exact ⟨live,(ENNReal.toReal_pos_iff.mp priced).1⟩

theorem live_compartment {X:Type*}[MeasurableSpace X] (μ:Measure X)(M:Set X)(live:0<μ M)
    (z:X→ℝ)(nz:∀x,0<z x)(finite:Integrable z (μ.restrict M)):0<∫x in M,z x ∂μ:=by
  apply (integral_pos_iff_support_of_nonneg (fun x=>(nz x).le) finite).2
  rw [show Function.support z=univ from eq_univ_of_forall fun x=>(nz x).ne',Measure.restrict_apply_univ]
  exact live
end YM.Integration.FVA1Physical.Exchange.RoseCut
