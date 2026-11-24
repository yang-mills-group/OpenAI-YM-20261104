import YM.Integration.ActualScalarTransport
import YM.Push.SECTOR_MEASURE.Decompose

/-! Absolute first-moment contraction for the original positive Wilson scene, with only a raw density integrability receipt. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonAbsoluteTransport
open Function Filter Set Finset MeasureTheory Lattice Wilson RG OPE.Therm
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G) {N p : ℕ} (hC : C.Makes)

include hC in
theorem norm_weighted {j : ℕ} (hj : j≤N) {f : Config G (C.side j p) → ℂ}
    (hf : Integrable (fun T => (C.path.rep N p j).eval T • f T) (prior G _)) :
    Integrable (fun T => (C.path.rep N p j).eval T • ‖f T‖) (prior G _) := by
  apply hf.norm.congr (ae_of_all _ fun T => ?_)
  change ‖(C.path.rep N p j).eval T • f T‖ = (C.path.rep N p j).eval T • ‖f T‖
  rw [norm_smul,Real.norm_of_nonneg (Multi.AxisShift.chosen_positive hC.wilson hj T).le,smul_eq_mul]

theorem slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {i : ℕ} {f : Config G (C.side (i+1) p) → E}
    (hf : Integrable (fun T => (C.path.rep N p (i+1)).eval T • f T) (prior G _))
    (U : Config G (C.side i p)) :
    Integrable (fun T => actualConditionalDensity C N p i U T • f T) (prior G _) := by
  let op := C.path.levels.clock.op i p
  let β := C.path.β N p (i+1)
  have hs := StepData.push_slice (C.path.levels.transition_mass i p β) U _ hf
  apply (hs.smul ((C.path.rep N p i).eval U)⁻¹).congr (ae_of_all _ fun T => ?_)
  change ((C.path.rep N p i).eval U)⁻¹ • (op.density β T U • ((C.path.rep N p (i+1)).eval T • f T)) =
    (op.density β T U*(C.path.rep N p (i+1)).eval T/(C.path.rep N p i).eval U) • f T
  simp only [smul_smul,div_eq_mul_inv]
  congr 1
  ring

theorem average_sub {i : ℕ} {f g : Config G (C.side (i+1) p) → ℂ}
    (hf : Integrable (fun T => (C.path.rep N p (i+1)).eval T • f T) (prior G _))
    (hg : Integrable (fun T => (C.path.rep N p (i+1)).eval T • g T) (prior G _))
    (U : Config G (C.side i p)) :
    actualAverage C (N:=N) (fun T => f T-g T) U=actualAverage C (N:=N) f U-actualAverage C (N:=N) g U := by
  unfold actualAverage
  simp_rw [smul_sub]
  exact integral_sub (slice C hf U) (slice C hg U)

include hC in
theorem sub {m j : ℕ} (hj : j≤N) {f g : Config G (C.side j p) → ℂ}
    (hf : Integrable (fun T => (C.path.rep N p j).eval T • f T) (prior G _))
    (hg : Integrable (fun T => (C.path.rep N p j).eval T • g T) (prior G _)) (hm : m≤j) :
    actualTransport C (N:=N) (fun T => f T-g T) hm=fun U =>
      actualTransport C (N:=N) f hm U-actualTransport C (N:=N) g hm U := by
  induction hm using Nat.decreasingInduction with
  | self => simp only [actualTransport_base C hC hj]
  | of_succ l hl ih =>
    funext U
    simp only [actualTransport_step C hC hj _ hl,ih]
    exact average_sub C (actualTransport_weighted_integrable_of_integrable C hC hj hf hl)
      (actualTransport_weighted_integrable_of_integrable C hC hj hg hl) U

include hC in
theorem dominated {m j : ℕ} (hj : j≤N) {f : Config G (C.side j p) → ℂ}
    (hf : Integrable (fun T => (C.path.rep N p j).eval T • f T) (prior G _))
    (hm : m ≤ j) (U : Config G (C.side m p)) :
    ‖actualTransport C (N:=N) f hm U‖≤actualTransport C (N:=N) (fun T => ‖f T‖) hm U := by
  have hr := norm_weighted C hC hj hf
  induction hm using Nat.decreasingInduction with
  | self => simp only [actualTransport_base C hC hj,le_rfl]
  | of_succ l hl ih =>
    rw [actualTransport_step C hC hj f hl,actualTransport_step C hC hj (fun T => ‖f T‖) hl]
    have hu := actualTransport_weighted_integrable_of_integrable C hC hj hr hl
    apply norm_integral_le_of_norm_le (slice C hu U)
    exact ae_of_all _ fun T => by
      rw [norm_smul,Real.norm_of_nonneg (actualConditionalDensity_nonneg C hC (hl.trans_le hj) U T),smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (ih T) (actualConditionalDensity_nonneg C hC (hl.trans_le hj) U T)

include hC in
theorem first {m j : ℕ} (hj : j≤N) {f : Config G (C.side j p) → ℂ}
    (hf : Integrable (fun T => (C.path.rep N p j).eval T • f T) (prior G _)) (hm : m ≤ j) :
    ∫ U,‖actualTransport C (N:=N) f hm U‖ ∂scene C.path N p m ≤
      ∫ T,‖f T‖ ∂scene C.path N p j := by
  have hr := norm_weighted C hC hj hf
  have h := actualTransport_weighted_integrable_of_integrable C hC hj hf hm
  have h' := actualTransport_weighted_integrable_of_integrable C hC hj hr hm
  apply (integral_mono (actualScene_integrable_of_weighted C hC (hm.trans hj) h).norm
    (actualScene_integrable_of_weighted C hC (hm.trans hj) h') (dominated C hC hj hf hm)).trans
  exact (actualScene_transport C hC hj hr hm).le

include hC in
theorem weighted {j : ℕ} (hj : j≤N) {f : Config G (C.side j p) → ℂ} (hf : Envelope f) :
    Integrable (fun T => (C.path.rep N p j).eval T • f T) (prior G _) := by
  obtain ⟨hM,b,hb⟩ := hf
  have hi : Integrable f (prior G (C.side j p)) :=
    Integrable.of_bound hM.aestronglyMeasurable b (ae_of_all _ hb)
  exact Push.SectorMeasure.Env.smul_L1 ((C.path.rep N p j).envelope (hC.wilson.represents N p j hj).good) hi

end YM.Integration.ActualWilsonAbsoluteTransport
