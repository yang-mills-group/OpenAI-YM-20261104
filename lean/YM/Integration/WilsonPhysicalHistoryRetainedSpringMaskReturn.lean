import YM.Integration.WilsonPhysicalHistoryKioskHeat

/-! Transport of the local mask error and its pairing with a measured earlier
field under the original Wilson law. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Lattice Wilson RG OPE.Therm MeasureTheory
open scoped Classical Topology
variable {G : Gauge}

theorem spring_mask_return (C : Family G) (law : C.Makes) {N per j : ℕ} (live:j≤N)
    (f : Config G (C.side j per)→ℂ) (measured:Measurable f) {B δ:ℝ}
    (cap:∀U,‖f U‖≤B) (paid:(∫U,‖f U‖ ∂scene C.path N per j)≤δ)
    {k : ℕ} (earlier:k≤j) :
    let F:=actualTransport C (N:=N) f earlier
    let μ:=scene C.path N per k
    Integrable F μ ∧ Integrable (fun U=>‖F U‖^2) μ ∧
      (∫U,‖F U‖ ∂μ)≤δ ∧ (∫U,‖F U‖^2 ∂μ)≤B*δ := by
  intro F μ
  have wn:=ActualWilsonAbsoluteTransport.weighted C law live
    (show Envelope f from ⟨measured,B,cap⟩)
  have h:=actualTransport_weighted_integrable_of_integrable C law live wn earlier
  have ins : Integrable F μ:=actualScene_integrable_of_weighted C law (earlier.trans live) h
  have L1: (∫U,‖F U‖ ∂μ)≤δ:=(ActualWilsonAbsoluteTransport.first C law live wn earlier).trans paid
  have non : 0≤B:=(norm_nonneg (f 1)).trans (cap 1)
  have major := ins.norm.const_mul B
  have small (U) : ‖F U‖^2 ≤ B*‖F U‖ := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (actualTransport_norm_le C law live cap earlier U) (norm_nonneg _)
  have square : Integrable (fun U=>‖F U‖^2) μ := major.mono' (ins.1.norm.pow 2)
    (ae_of_all _ fun U=>by
      change |‖F U‖^2| ≤ B*‖F U‖
      rw [abs_of_nonneg (sq_nonneg ‖F U‖)]
      exact small U)
  refine ⟨ins,square,L1,(integral_mono square major small).trans ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left L1 non

theorem spring_mask_spectator {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω}
    (F H:Ω→ℂ) (mF:AEStronglyMeasurable F μ) (mH:AEStronglyMeasurable H μ)
    (iF:Integrable (fun U=>‖F U‖^2) μ) (iH:Integrable (fun U=>‖H U‖^2) μ)
    {δ:ℝ} (hn:0≤δ) (paid:(∫U,‖F U‖^2 ∂μ)≤δ^2) :
    Integrable (fun U=>H U*F U) μ ∧
    (∫U,‖H U*F U‖ ∂μ)≤Real.sqrt (∫U,‖H U‖^2 ∂μ)*δ := by
  have first : MemLp (fun U=>‖H U‖) 2 μ:=(memLp_two_iff_integrable_sq mH.norm).2 iH
  have second : MemLp (fun U=>‖F U‖) 2 μ:=(memLp_two_iff_integrable_sq mF.norm).2 iF
  have two : ENNReal.ofReal 2=2:=by norm_num
  have holder:=integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (show (0:Ω→ℝ)≤ᵐ[μ] fun U=>‖H U‖ from ae_of_all _ fun _=>norm_nonneg _)
    (show (0:Ω→ℝ)≤ᵐ[μ] fun U=>‖F U‖ from ae_of_all _ fun _=>norm_nonneg _)
    (by rwa [two]) (by rwa [two])
  have cs : (∫U,‖H U‖*‖F U‖ ∂μ)≤Real.sqrt (∫U,‖H U‖^2 ∂μ)*Real.sqrt (∫U,‖F U‖^2 ∂μ):=by
    simpa only [Real.rpow_two,Real.sqrt_eq_rpow,one_div] using holder
  have tested : Integrable (fun U=>H U*F U) μ:=(first.integrable_mul second).mono' (mH.mul mF)
    (ae_of_all _ fun U=>by simp)
  have limit : Real.sqrt (∫U,‖F U‖^2 ∂μ)≤δ:=(Real.sqrt_le_sqrt paid).trans_eq (Real.sqrt_sq hn)
  exact ⟨tested,by simpa only [norm_mul] using cs.trans (mul_le_mul_of_nonneg_left limit (Real.sqrt_nonneg _))⟩

end YM.Integration.OriginalMarkedRunAction
