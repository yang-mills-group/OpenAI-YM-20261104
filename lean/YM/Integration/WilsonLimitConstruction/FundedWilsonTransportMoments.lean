import YM.Integration.ActualWilsonConditionalRoots
import YM.Integration.ActualWilsonAbsoluteTransport

/-! Every positive finite Wilson transition regularizes the weighted input on each
held fibre. Consequently its genuine conditional moment bound holds at every
coarse configuration and contracts at every earlier measured marginal. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonTransportMoments
open Function Filter Set MeasureTheory Lattice Wilson RG MergeProof.Accent OPE.Therm
open scoped Classical BigOperators ENNReal
variable {G:Gauge}(C:Family G)(hC:C.Makes){N p j m:ℕ}
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]

include hC in
theorem weighted (hm:m ≤ N){f:Config G (C.side m p) → E}(h:Integrable f (scene C.path N p m)):
    Integrable (fun U=>(C.path.rep N p m).eval U • f U) (prior G _):=by
  let Z:=Wilson.partition G (C.side N p) (C.path.β N p N)
  have nz:Z≠0:=(Wilson.partition_pos _).ne'
  unfold scene at h
  rw [integrable_withDensity_iff_integrable_smul' (dose_env hC.wilson hm).meas.ennreal_ofReal
    (ae_of_all _ fun _=>ENNReal.ofReal_lt_top)] at h
  simp_rw [ENNReal.toReal_ofReal (dose_positive hC.wilson hm _).le,dose,div_eq_inv_mul,mul_smul] at h
  apply (h.smul Z).congr (ae_of_all _ fun U=>?_)
  change Z • (Z⁻¹ • ((C.path.rep N p m).eval U • f U))=_
  rw [smul_smul,mul_inv_cancel₀ nz,one_smul]

include hC in
theorem fibre (hm:m<N)(V:Config G (C.side m p)){f:Config G (C.side (m+1) p) → E}
    (h:Integrable (fun U=>(C.path.rep N p (m+1)).eval U • f U) (prior G _)):
    Integrable f (ActualWilsonConditionalRoots.fibre C (N:=N) V):=by
  unfold ActualWilsonConditionalRoots.fibre
  rw [integrable_withDensity_iff_integrable_smul' (ActualWilsonConditionalRoots.held_density_meas C hC hm V).ennreal_ofReal
    (ae_of_all _ fun _=>ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (ActualWilsonConditionalRoots.strict C hC hm V _).le]
  exact ActualWilsonAbsoluteTransport.slice C h V

private theorem payable {X:Type*}[MeasurableSpace X]{μ:Measure X}{f:X → ℂ}{a:X → ℝ}
    (q:ℕ)(hf:Integrable f μ)(ha:Integrable a μ)(h:∀x,‖f x‖^q ≤ a x):
    Integrable (fun x=>‖f x‖^q) μ:=by
  apply ha.norm.mono' ((continuous_pow q).comp_aestronglyMeasurable hf.aestronglyMeasurable.norm)
  exact ae_of_all _ fun x=>by
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _),Real.norm_of_nonneg ((pow_nonneg (norm_nonneg _) _).trans (h x))]
    exact h x

include hC in
theorem point (hm:m ≤ N)(h:j ≤ m)(f:Config G (C.side m p) → ℂ)(q:ℕ)
    (hf:Integrable f (scene C.path N p m))(hq:Integrable (fun U=>‖f U‖^q) (scene C.path N p m))
    (V:Config G (C.side j p)):
    ‖actualTransport C (N:=N) f h V‖^q ≤ actualTransport C (N:=N) (fun U=>‖f U‖^q) h V:=by
  have hF:=weighted C hC hm hf
  have hP:=weighted C hC hm hq
  induction h using Nat.decreasingInduction with
  | self => simp only [actualTransport_base C hC hm,le_rfl]
  | of_succ i hi ih =>
    let ν:=ActualWilsonConditionalRoots.fibre C (N:=N) V
    letI:IsProbabilityMeasure ν:=ActualWilsonConditionalRoots.probability C hC (hi.trans_le hm) V
    let u:=actualTransport C (N:=N) f hi
    let v:=actualTransport C (N:=N) (fun U=>‖f U‖^q) hi
    have hu:Integrable u ν:=fibre C hC (hi.trans_le hm) V (actualTransport_weighted_integrable_of_integrable C hC hm hF hi)
    have hv:Integrable v ν:=fibre C hC (hi.trans_le hm) V (actualTransport_weighted_integrable_of_integrable C hC hm hP hi)
    have hiq:=payable q hu hv ih
    rw [actualTransport_step C hC hm f hi,actualTransport_step C hC hm _ hi,
      ←ActualWilsonConditionalRoots.average C hC (hi.trans_le hm) V,
      ←ActualWilsonConditionalRoots.average C hC (hi.trans_le hm) V]
    have J:=(convexOn_pow (𝕜:=ℝ) q).map_integral_le (continuous_pow q).continuousOn isClosed_Ici
      (ae_of_all ν fun U=>(norm_nonneg (u U):‖u U‖∈Ici 0)) hu.norm hiq
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm u) q).trans
      (J.trans (integral_mono hiq hv ih))

include hC in
theorem measured (hm:m ≤ N)(h:j ≤ m)(f:Config G (C.side m p) → ℂ)(q:ℕ)
    (hf:Integrable f (scene C.path N p m))(hq:Integrable (fun U=>‖f U‖^q) (scene C.path N p m)):
    Integrable (fun V=>‖actualTransport C (N:=N) f h V‖^q) (scene C.path N p j) ∧
      (∫V,‖actualTransport C (N:=N) f h V‖^q ∂scene C.path N p j) ≤ ∫U,‖f U‖^q ∂scene C.path N p m:=by
  have H:=point C hC hm h f q hf hq
  have F:=weighted C hC hm hf
  have P:=weighted C hC hm hq
  have finF:=actualScene_integrable_of_weighted C hC (h.trans hm) (actualTransport_weighted_integrable_of_integrable C hC hm F h)
  have finP:=actualScene_integrable_of_weighted C hC (h.trans hm) (actualTransport_weighted_integrable_of_integrable C hC hm P h)
  have fin:=payable q finF finP H
  exact ⟨fin,(integral_mono fin finP H).trans_eq (actualScene_transport C hC hm P h)⟩

end YM.Integration.WilsonLimitConstruction.FundedWilsonTransportMoments
end
