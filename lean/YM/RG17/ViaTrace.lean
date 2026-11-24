import YM.RG17.Positive

/-! Trace endpoint at finite cost. Read precisely `Shell.Comparison` for
scope of nonfree exclusion; NOT every Poincare representation or arbitrary
large gauge-equivalence identification. Retains centered convention in Y.
Applied AFTER real Ward-from-report finite-order estimate, assuming same
passage/prescription and alignments. Does NOT compute anomaly coefficient
from loops (major missing independent physical/diagram hypotheses).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter MeasureTheory Spec Extraction Table OPE OPE.Orbits
open Points Work.A05 Trace
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book} {F: Final C f S}

lemma fitting {U:Set (Points 2)}(hU:IsOpen U) {x:Points 2}(hx:x∈ U)(hc:x∈ conf 2) :∃ ψ:RealTest 2,(∀ z,0≤ψ z) ∧ 0<(∫ z,ψ z) ∧ tsupport ψ ⊆ U:=by
    obtain ⟨r,hr,H⟩:= Metric.mem_nhds_iff.mp ((hU.inter (conf_open _)).mem_nhds (show x∈U∩conf 2 from ⟨hx,hc⟩))
    let B: ContDiffBump x := ⟨r/4,r/2,by linarith,by linarith⟩
    have hB : tsupport B ⊆ U ∩ conf 2 := B.tsupport_eq ▸ ((Metric.closedBall_subset_ball (show B.rOut<r from half_lt_self hr)).trans H)
    exact ⟨⟨B,B.contDiff,B.hasCompactSupport,hB.trans inter_subset_right⟩,B.nonneg', B.integral_pos,hB.trans inter_subset_left⟩
lemma radial_limit (F:Final C f S) (h:∀ ψ:RealTest 2, Tendsto (fun r=> ∫ x:Points 2,ψ x*pulse F r (span2 x)) home (𝓝 (∫ x:Points 2,ψ x*freeCharge C (span2 x)))): Tendsto (fun r=>pulse F r 1) home (𝓝 (theoryDensity G)):=by
    let c:=freeCharge C; let K:=theoryDensity G
    have he:c 1=K:=by simp [c,K,freeCharge]
    have hC:Tendsto c (𝓝 1) (𝓝 K):= he ▸ continuousAt_const.div (continuousAt_id.pow 8) (by simp)
    let H:= conf 2; have hH:IsOpen H:=conf_open _
    apply tendsto_order.mpr; constructor
    · intro t ht
      obtain ⟨b,hb,hbK⟩:= exists_between ht
      have hs : Tendsto c (𝓝[>] 1) (𝓝 K):= hC.mono_left nhdsWithin_le_nhds
      obtain ⟨x,hx,hx'⟩:= ((hs.eventually (lt_mem_nhds hbK)).and (show ∀ᶠ (i:ℝ) in 𝓝[>] 1,1 < i from self_mem_nhdsWithin)).exists
      have hx0:0<x:=zero_lt_one.trans hx'
      let U:= H ∩ {z|1 < span2 z}∩ {z| b < c (span2 z)}
      have hf:IsOpen U := by
         apply isOpen_iff_mem_nhds.mpr; rintro z ⟨⟨hz,h'⟩,hi⟩
         have hv : ContinuousAt (fun z=> c (span2 z)) z := (free_cont C).continuousAt (hH.mem_nhds hz)
         exact inter_mem (inter_mem (hH.mem_nhds hz) (span_cont.continuousAt.tendsto (lt_mem_nhds h'))) (hv.tendsto (lt_mem_nhds hi))
      have hm: separated x∈H:=offsetConf hx0
      obtain ⟨ψ,hψ,hP,hU⟩:= fitting hf (x:=separated x) (show separated x∈U from ⟨⟨hm,show 1 < span2 (separated x) from hx'.trans_eq (span_sep hx0).symm⟩,(show b < c (span2 (separated x)) from hx.trans_eq (congr_arg c (span_sep hx0).symm))⟩) hm
      let d:=∫ z:Points 2,ψ z; have hpay:Integrable ψ:=ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
      have he: d*t < ∫ z,ψ z * c (span2 z):=
         (mul_lt_mul_of_pos_left hb hP).trans_le <| ((MeasureTheory.integral_mul_const ..).symm.le).trans (MeasureTheory.integral_mono (hpay.mul_const b) (regionReal (free_cont C) ψ) (fun z=> by
           by_cases h:z∈tsupport ψ
           · exact mul_le_mul_of_nonneg_left (show b < c (span2 z) from (hU h).2).le (hψ _)
           simp [image_eq_zero_of_notMem_tsupport h]))
      filter_upwards [positiveLength,(tendsto_order.mp (h ψ)).1 _ he] with r hr hu
      refine lt_of_mul_lt_mul_left (hu.trans_le (show _ ≤ d*pulse F r 1 from ?_)) hP.le
      refine (MeasureTheory.integral_mono (actualInt F hr ψ) (hpay.mul_const (pulse F r 1)) (fun z=>?_)).trans_eq (integral_mul_const ..)
      by_cases h:z∈tsupport ψ; swap
      · simp [image_eq_zero_of_notMem_tsupport h]
      exact mul_le_mul_of_nonneg_left (pulse_le F hr one_pos (show 1<span2 z from (hU h).1.2).le) (hψ _)
    intro t ht
    obtain ⟨b,hb,hbK⟩:= exists_between ht
    have hs : Tendsto c (𝓝[<] 1) (𝓝 K):= hC.mono_left nhdsWithin_le_nhds
    have hpos: ∀ᶠ x in 𝓝[<] (1:ℝ), x>0:=nhdsWithin_le_nhds (lt_mem_nhds zero_lt_one)
    obtain ⟨x,hx,hx',hx0⟩:= ((hs.eventually (gt_mem_nhds hb)).and ((show ∀ᶠ (i:ℝ) in 𝓝[<] 1,i<1 from self_mem_nhdsWithin).and hpos)).exists
    let U:= H ∩ {z|span2 z < 1}∩ {z| c (span2 z) < b}
    have hf:IsOpen U := by
       apply isOpen_iff_mem_nhds.mpr; rintro z ⟨⟨hz,h'⟩,hi⟩
       have hv : ContinuousAt (fun z=> c (span2 z)) z := (free_cont C).continuousAt (hH.mem_nhds hz)
       exact inter_mem (inter_mem (hH.mem_nhds hz) (span_cont.continuousAt.tendsto (gt_mem_nhds h'))) (hv.tendsto (gt_mem_nhds hi))
    have hm: separated x∈H:=offsetConf hx0
    obtain ⟨ψ,hψ,hP,hU⟩:= fitting hf (x:=separated x) (show separated x∈U from ⟨⟨hm,show span2 (separated x) < 1 from (span_sep hx0).trans_lt hx'⟩,(show c (span2 (separated x)) < b from (congr_arg c (span_sep hx0)).trans_lt hx)⟩) hm
    let d:=∫ z:Points 2,ψ z; have hpay:Integrable ψ:=ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
    have he: (∫ z,ψ z * c (span2 z)) < d*t:= (MeasureTheory.integral_mono (regionReal (free_cont C) ψ) (hpay.mul_const b) (fun z=>by
        by_cases h:z∈tsupport ψ
        · exact mul_le_mul_of_nonneg_left (show _ < b from (hU h).2).le (hψ z)
        simp [image_eq_zero_of_notMem_tsupport h])).trans_lt ((integral_mul_const _ _).trans_lt (mul_lt_mul_of_pos_left hbK hP))
    filter_upwards [positiveLength,(tendsto_order.mp (h ψ)).2 _ he] with r hr hu
    refine lt_of_mul_lt_mul_left ((show d*pulse F r 1 ≤ _ from ?_).trans_lt hu) hP.le
    refine ((integral_mul_const _ _).symm.le).trans (MeasureTheory.integral_mono (hpay.mul_const _) (actualInt F hr ψ) (fun z=>?_))
    by_cases h:z∈tsupport ψ; swap
    · simp [image_eq_zero_of_notMem_tsupport h]
    exact mul_le_mul_of_nonneg_left (pulse_le F hr (spanPos (ψ.tsupport_subset h)) (show span2 z < 1 from (hU h).1.2).le) (hψ _)

variable {L:Layout F}(Z:Ledger L)(A:Ports C)(H:Services C f S) (P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (loc:Located L)(V:Tide Z A)(Q:Passage Z A)(t:Handles L)
include Z A H P loc V Q t
lemma leading_trace : Trace.LogLaw F (theoryDensity G) := by
    have hx:= radial_limit F (fun ψ=> alongRealm Z A H P loc V Q t ψ)
    apply (Complex.continuous_ofReal.continuousAt.tendsto.comp (hx.comp tendsto_inv_atTop_nhdsGT_zero)).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    change Complex.ofReal (pulse F r⁻¹ 1) = _ * _; rw [← rest_real F (inv_pos.mpr hr) one_pos,mul_one,discount_eq, inv_inv,Complex.real_smul]
theorem excludes (m:ℕ) (U:F.action.operators.H →ₗᵢ[ℂ] Trace.Shell.Sum m) : ¬ Trace.Shell.Comparison F (meanExact F) U:=
    fun he=> Trace.noComparison_log F (leading_trace Z A H P loc V Q t) (Trace.theoryDensity_pos Z.simple) U he
end YM.RG17
