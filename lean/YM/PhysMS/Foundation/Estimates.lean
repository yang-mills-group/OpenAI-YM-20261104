import YM.PhysMS.Foundation.Readout
import YM.TraceExtension.Atlas.Sink
import YM.OPE.Exchange.Regime

/-! Generic physical comparison estimates, with no Trace calibration constructor dependency. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysMS
open Function Filter Set Spec OPE OPE.Orbits OPE.Nesting Trace.Pilot
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
  (X : Climb.Scaling S) (h : G.Simple) (H : Foundation F R) {n : ℕ}

lemma compact_within (s : Set (Points n)) (hs : IsCompact s) (hz : s ⊆ conf n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ η : ℝ, 0 < η ∧ ∀ x ∈ s, WithinRoom 1 M η x.ofLp 0 := by
  obtain ⟨r,hr,hx⟩:= ((eventually_gt_atTop (0:ℝ)).and (Work.A05.compact_fits hs hz)).exists
  refine ⟨r,hr.le, r⁻¹,by positivity,fun x h=> ⟨fun i=> ?_,fun i j hij=>?_⟩⟩
  · rw [sub_zero,mul_one]; exact (PiLp.norm_apply_le x i).trans (hx h).2
  rw [mul_one]; refine ((hx h).1 i j hij).trans ?_
  unfold cubedist; rw [dist_eq_norm]; exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun k=> PiLp.norm_apply_le (x i-x j) k)

lemma to_log_zoom : Tendsto LogV trail atTop := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
lemma length_rate : RateIs trail LogV id (-1) := by
  rw [show LogV=OPE.run from funext fun x=>Real.log_inv x]; exact loglife tendsto_id

/-- Not just an upper power-log bound for g. Important for measuring the cost after division
    by a coupling remainder tolerance. -/
lemma coupling_rate {g : ℝ → ℝ} (hv : Coupling G g) (h : G.Simple) : RateIs trail LogV g 0 := by
  have hp : RateIs trail LogV LogV 0 := ⟨to_log_zoom.eventually_gt_atTop 0,
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp to_log_zoom⟩
  let f(x:ℝ):= LogV x * g x^(2:ℕ); have hh : 0 < G.slopeConstant⁻¹ := inv_pos.mpr (Gauge.slopeConstant_pos h)
  have he : RateIs trail LogV f 0 := ⟨hv.running.eventually (lt_mem_nhds hh),
    (hv.running.log hh.ne').div_atTop to_log_zoom⟩
  have hx := (he.div hp).rpow (1/2)
  rw [sub_zero,mul_zero] at hx; apply hx.congr
  filter_upwards [hv.positive,hp.pos] with i hi hl
  unfold f; rw [mul_div_cancel_left₀ _ hl.ne', ← Real.sqrt_eq_rpow, Real.sqrt_sq hi.le]

lemma subpower_payment {g : ℝ → ℝ} (hg : Coupling G g) (h : G.Simple) (b ε : ℝ) (he : 0 < ε)
    (A : ℝ) (hA : 0 < A) (N : ℕ) :
    ∀ᶠ r in trail, b * r^ε ≤ A * g r ^ N := by
  have hz:= ((RateLE.const b to_log_zoom).mul ((length_rate.rpow ε).pays to_log_zoom))
  rw [zero_add,mul_neg,mul_one] at hz
  have hh:= ((RateIs.const to_log_zoom hA).mul ((coupling_rate hg h).power N)); rw [mul_zero,zero_add] at hh
  filter_upwards [hh.outweigh hz (neg_lt_zero.mpr he) to_log_zoom] with r hr using (Real.le_norm_self _).trans hr

include X h H
lemma phase_jets_flat (g : ℝ → ℝ) (hg : Coupling G g) (v : Word (C:=C) S n) (j : ℕ)
    (s : Set (Points n)) (hs : IsCompact s) (hz : s ⊆ conf n) (A : ℝ) (hA : 0 < A) (N : ℕ) :
    ∀ᶠ r in trail, ∀ x∈s, ∀ p q : Viewers F,
      ‖iteratedFDeriv ℝ j (value F p v r) x - iteratedFDeriv ℝ j (value F q v r) x‖ ≤ A * g r ^ N := by
  obtain ⟨M,hM,η,hη,hK⟩:= compact_within s hs hz
  filter_upwards [self_mem_nhdsWithin (s:=Ioi (0:ℝ)), phase_jets F R X h H v hM hη zero_lt_one j,
    subpower_payment hg h ((Fintype.card (Fin n × Axis) : ℝ)^j*2) (4-1) (by norm_num) A hA N] with r hr hf hg x hx p q
  rw [← iteratedFDeriv_sub_apply ((value_tied F p v hr (hz hx)).of_le (WithTop.coe_le_coe.mpr le_top))
    ((value_tied F q v hr (hz hx)).of_le (WithTop.coe_le_coe.mpr le_top))]
  exact (hf x (hK x hx) p q).trans (by rwa [← mul_assoc])

/-- In particular the real `scalar` coefficient's prediction problem on these profiles reduces
    to *any one phase* or the vacuum calculation. We do not make this reduction for the
    *positive-output* problem. -/
lemma identity_flat (g : ℝ → ℝ) (hg : Coupling G g) (v : Word (C:=C) S n)
    (s : Set (Points n)) (hs : IsCompact s) (hz : s ⊆ conf n) (A : ℝ) (hA : 0 < A) (N : ℕ) :
    ∀ᶠ r in trail, ∀ x∈s, ∀ q : Viewers F,
      ‖value F q v r x - (r^charge v) • Short.scalar F R (r • x).ofLp v 0‖ ≤ A * g r ^ N := by
  obtain ⟨M,hM,η,hη,hK⟩:= compact_within s hs hz
  filter_upwards [scalar_read F R X h H v hM hη zero_lt_one,subpower_payment hg h 1 (4-1) (by norm_num) A hA N] with r hf hx x he q
  exact (hf x (hK x he) q).trans (by rwa [one_mul] at hx)

end YM.PhysMS
