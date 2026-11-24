import YM.Integration.PhysicalOPEApproximation
import YM.PhysMS.Frame.Cost

/-! The ordinary physical OPE pays the complete finite-horizon output
inverse. This uses the original detector, Reader packet, Family and frame.
No homogeneous cut, MS candidate identification or perturbative residual
estimate is assumed. The native length power has one full order to spare.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.EngineeringWeightedReadout
open Function Filter Set Spec OPE OPE.Orbits PhysMS Asymptotics Trace.Pilot
open scoped Topology Classical

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {D : ℕ} (U : Detector S D) (J : ℝ → PhysMS.tower S)

/-- The complete finite-horizon detector readout. The entire original
field conversion is inverted, with no homogeneous Reader cut. -/
def wholeReadout (r : ℝ) :
    (Fin U.size → ℂ) →L[ℂ] (Climb.Bel C.book).Field D :=
  (PhysMS.Frame.backward D J r).comp
    (LinearMap.toContinuousLinearMap U.report)

theorem wholeReadout_field (r : ℝ) (z : S.Field D) :
    wholeReadout U J r (fun i => witnessAt S D (U.listen i) z) =
      (J r D).symm z := by
  change (J r D).symm (U.report _) = _
  rw [U.recovered]

/-- A candidate transported by the same complete frame is decoded exactly.
No compatibility with a separately chosen homogeneous projection is used. -/
theorem wholeReadout_frame (r : ℝ) (z : (Climb.Bel C.book).Field D) :
    wholeReadout U J r (fun i => witnessAt S D (U.listen i) (J r D z)) = z := by
  rw [wholeReadout_field, LinearEquiv.symm_apply_apply]

theorem wholeReadout_norm (r : ℝ) (z : Fin U.size → ℂ) :
    ‖wholeReadout U J r z‖ ≤ ‖PhysMS.Frame.backward D J r‖ *
      ‖LinearMap.toContinuousLinearMap U.report‖ * ‖z‖ := by
  have h := (PhysMS.Frame.backward D J r).le_opNorm
    ((LinearMap.toContinuousLinearMap U.report) z)
  exact h.trans ((mul_le_mul_of_nonneg_left
    ((LinearMap.toContinuousLinearMap U.report).le_opNorm z)
    (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm)

variable (H : Leading F J)

include H in
theorem wholeReadout_power (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r in Trace.Pilot.trail, ∀ z : Fin U.size → ℂ,
      ‖wholeReadout U J r z‖ ≤
        ‖LinearMap.toContinuousLinearMap U.report‖ * r ^ (-(D : ℝ) - ε) * ‖z‖ := by
  have hp := (PhysMS.length_rate.rpow (-(D : ℝ) - ε)).outweigh
    (PhysMS.Frame.inverse_rate F D J H) (by nlinarith) PhysMS.to_log_zoom
  filter_upwards [hp] with r hr z
  calc
    ‖wholeReadout U J r z‖ ≤ ‖PhysMS.Frame.backward D J r‖ *
        ‖LinearMap.toContinuousLinearMap U.report‖ * ‖z‖ := wholeReadout_norm U J r z
    _ ≤ r ^ (-(D : ℝ) - ε) * ‖LinearMap.toContinuousLinearMap U.report‖ * ‖z‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hr
          (norm_nonneg (LinearMap.toContinuousLinearMap U.report))) (norm_nonneg z)
    _ = ‖LinearMap.toContinuousLinearMap U.report‖ * r ^ (-(D : ℝ) - ε) * ‖z‖ := by ring

variable (hF : Foundation F R) {I : Type} [Fintype I] {d : I → ℕ}
    (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (M η : ℝ) (hM : 0 ≤ M) (hη : 0 < η)

include H hF hM hη in
/-- The complete horizon inverse loses at most the horizon power. The
genuine OPE residual retains one positive length power after that loss. -/
theorem detectorOPE_whole_readout_power (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r in Trace.Pilot.trail, ∀ x : I → E4,
      WithinRoom r M η x 0 →
      ‖wholeReadout U J r (detectorOPEError F R J v U r x)‖ ≤
        ‖LinearMap.toContinuousLinearMap U.report‖ * r ^ (1 - ε) := by
  have he : 0 < ε / 2 := half_pos hε
  filter_upwards [wholeReadout_power F U J H (ε / 2) he,
    detectorOPE_power F R J H hF v M η hM hη U (ε / 2) he,
    self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with r hr hO hpos x hx
  have hp : 0 < r := hpos
  have hnorm : ‖detectorOPEError F R J v U r x‖ ≤ r ^ ((D : ℝ) + 1 - ε / 2) :=
    (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg hp.le _)).mpr (hO x hx)
  calc
    ‖wholeReadout U J r (detectorOPEError F R J v U r x)‖ ≤
        ‖LinearMap.toContinuousLinearMap U.report‖ * r ^ (-(D : ℝ) - ε / 2) *
          ‖detectorOPEError F R J v U r x‖ := hr _
    _ ≤ ‖LinearMap.toContinuousLinearMap U.report‖ * r ^ (-(D : ℝ) - ε / 2) *
        r ^ ((D : ℝ) + 1 - ε / 2) :=
      mul_le_mul_of_nonneg_left hnorm
        (mul_nonneg (norm_nonneg (LinearMap.toContinuousLinearMap U.report))
          (Real.rpow_nonneg hp.le (-(D : ℝ) - ε / 2)))
    _ = ‖LinearMap.toContinuousLinearMap U.report‖ * r ^ (1 - ε) := by
      rw [mul_assoc, ← Real.rpow_add hp]
      congr 2
      ring

variable (g : ℝ → ℝ) (hg : Coupling G g) (hG : G.Simple)

include H hF hM hη hg hG in
/-- Every fixed coupling order is paid for the whole finite-horizon
output, without a projection or an extra graded-frame compatibility premise. -/
theorem detectorOPE_whole_readout_flat (a : ℝ) (ha : 0 < a) (N : ℕ) :
    ∀ᶠ r in Trace.Pilot.trail, ∀ x : I → E4,
      WithinRoom r M η x 0 →
      ‖wholeReadout U J r (detectorOPEError F R J v U r x)‖ ≤ a * g r ^ N := by
  filter_upwards [detectorOPE_whole_readout_power F R U J H hF v M η hM hη
      (1 / 2) (by norm_num),
    PhysMS.subpower_payment hg hG ‖LinearMap.toContinuousLinearMap U.report‖
      (1 - (1 : ℝ) / 2) (by norm_num) a ha N] with r hO hpay x hx
  exact (hO x hx).trans hpay

include H hF hM hη hg hG in
theorem detectorOPE_whole_readout_flat_along
    {A : Type*} {l : Filter A} (r : A → ℝ)
    (hr : Tendsto r l Trace.Pilot.trail) (x : A → I → E4)
    (hx : ∀ᶠ a in l, WithinRoom (r a) M η (x a) 0) (N : ℕ) :
    (fun a => wholeReadout U J (r a) (detectorOPEError F R J v U (r a) (x a)))
      =o[l] (fun a => g (r a) ^ N) := by
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards [hr.eventually
    (detectorOPE_whole_readout_flat F R U J H hF v M η hM hη g hg hG ε hε N), hx]
    with a ha hx
  exact (ha (x a) hx).trans
    (mul_le_mul_of_nonneg_left (Real.le_norm_self _) hε.le)

end YM.Integration.EngineeringWeightedReadout
