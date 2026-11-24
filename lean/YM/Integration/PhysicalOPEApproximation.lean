import YM.PhysMS.Frame.Faces
import YM.Integration.DetectorPacketReadout
import YM.Integration.DetectorGeometry
import YM.Integration.ReaderRunningExtraction

/-!
The ordinary, finite-output-horizon OPE supplies the first of the two
complete-product residuals used to extract the original Reader coefficients.
The physical fields and all-length frame are unchanged. The length power is
retained explicitly so that a later output-frame inverse can be paid for.
No perturbative or MS prescription comparison is assumed or proved here.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration
open Function Filter Set Spec OPE OPE.Orbits PhysMS Asymptotics Trace.Pilot
open scoped Topology Classical

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (H : Leading F J) (hF : Foundation F R)
    {I : Type} [Fintype I] {d : I → ℕ}
    (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (M η : ℝ) (hM : 0 ≤ M) (hη : 0 < η)

/-- The actual complete-product residual against the fixed finite detector,
with input fields measured in the original all-length frame. -/
def detectorOPEError {D : ℕ} (U : Detector S D) (r : ℝ)
    (x : I → E4) (i : Fin U.size) : ℂ :=
  whole S x (PhysMS.Frame.born J r v) (positions S (U.listen i)).ofLp
    (fun j => (tags S (U.listen i) j).2) -
  witnessAt S D (U.listen i) (R.packet D x (PhysMS.Frame.born J r v) 0)

/-- The native measured OPE row is literally the original running-frame
Reader output used by the independently proved finite Gram extraction. -/
theorem physicalOPE_row_eq_pulledFresh (m : ℕ) (x : I → E4)
    (o : E4) (r : ℝ) :
    PhysMS.Frame.row F R J m x o v r =
      ReaderRunningExtraction.pulledFresh F R J m x
        (PhysMS.Frame.born J r v) o r := rfl

include H hF hM hη in
/-- The native physical OPE theorem applies simultaneously to every actual
finite detector exterior. The input configuration may vary independently
through the whole scaled separated room. -/
theorem detectorOPE_power {D : ℕ} (U : Detector S D) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r in Trace.Pilot.trail, ∀ x : I → E4,
      WithinRoom r M η x 0 → ∀ i : Fin U.size,
        ‖detectorOPEError F R J v U r x i‖ ≤ r ^ ((D : ℝ) + 1 - ε) := by
  obtain ⟨δ, hδ, hc⟩ := detector_uniform_clearance U
  have hs (i : Fin U.size) := PhysMS.Frame.single_report F R J H hF v
    (fun j => (tags S (U.listen i) j).2) D M η δ ε hM hη hδ hε
  filter_upwards [eventually_all.mpr hs] with r hr x hx i
  rw [detectorOPEError, detector_packet_residual F R D x
    (PhysMS.Frame.born J r v) (U.listen i) (U.awake i)]
  exact (hr i x (positions S (U.listen i)).ofLp 0 hx (hc i)).2 none

variable (g : ℝ → ℝ) (hg : Coupling G g) (hG : G.Simple)

include H hF hM hη hg hG in
/-- Every fixed coupling order is dominated by the positive length power
in the actual ordinary OPE residual. This assertion is uniform in the
entire separated input room and over the fixed finite detector. -/
theorem detectorOPE_flat {D : ℕ} (U : Detector S D)
    (a : ℝ) (ha : 0 < a) (N : ℕ) :
    ∀ᶠ r in Trace.Pilot.trail, ∀ x : I → E4,
      WithinRoom r M η x 0 → ∀ i : Fin U.size,
        ‖detectorOPEError F R J v U r x i‖ ≤ a * g r ^ N := by
  have hp : 0 < (D : ℝ) + 1 - 1 / 2 := by
    have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg D
    linarith
  filter_upwards [detectorOPE_power F R J H hF v M η hM hη U (1 / 2)
      (by norm_num),
    PhysMS.subpower_payment hg hG 1 ((D : ℝ) + 1 - 1 / 2) hp a ha N]
    with r hr hp x hx i
  exact (hr x hx i).trans (by simpa only [one_mul] using hp)

include H hF hM hη hg hG in
/-- Independent choices of shrinking input configurations and detector
indices preserve every coupling order along any approaching scale path. -/
theorem detectorOPE_flat_along {D : ℕ} (U : Detector S D)
    {A : Type*} {l : Filter A} (r : A → ℝ)
    (hr : Tendsto r l Trace.Pilot.trail) (x : A → I → E4)
    (hx : ∀ᶠ a in l, WithinRoom (r a) M η (x a) 0)
    (i : A → Fin U.size) (N : ℕ) :
    (fun a => detectorOPEError F R J v U (r a) (x a) (i a)) =o[l]
      (fun a => g (r a) ^ N) := by
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards [hr.eventually
    (detectorOPE_flat F R J H hF v M η hM hη g hg hG U ε hε N), hx]
    with a ha hx
  exact (ha (x a) hx (i a)).trans
    (mul_le_mul_of_nonneg_left (Real.le_norm_self _) hε.le)

end YM.Integration
