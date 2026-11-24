import YM.PhysMS.Frame.Measured
import YM.Next.UV_STRESS.Rates

/-! The original measured position basis has the compact, order-zero
test estimate required by the before-cutoff physical tariff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportPrescribedTests
open Function Filter Set MeasureTheory Extraction Table Climb Ward Next.UVStress PhysMS
open scoped Topology ContDiff Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

theorem measured (F : Spec.Final C f S) (J : ℝ→PhysMS.tower S) (H : PhysMS.Leading F J)
    (z : Zoom) : Approaches z (fun k d => (J (z.r k) d).toLinearMap) := by
  constructor
  intro n v
  let d : Caps n := fun i => (v i).1
  let w : MaxwellSlots C d := fun i => (v i).2
  let col := fun k d => (J (z.r k) d).toLinearMap
  let E := fun k => tested (z.r k) (col k) v-disc v
  have smooth (k) : ContDiffOn ℝ ∞ (E k) (conf n) :=
    (smoothZoom F.room.kernel.smooth _ (z.positive k)).sub (smoothDisc (Maxwell.Free.hierarchy C.labels).smooth v)
  refine ⟨smooth,?_⟩
  intro K compact sep M hM ε hε
  let c := volume.real K+1
  have hc : 0<c := by dsimp [c]; positivity
  let tol := ε/(M*c)
  have htol : 0<tol := div_pos hε (mul_pos hM hc)
  have trace : Tendsto z.r atTop Trace.Pilot.trail :=
    tendsto_nhdsWithin_iff.mpr ⟨z.limits,Eventually.of_forall z.positive⟩
  have fields := trace.eventually (Metric.tendstoUniformlyOn_iff.mp (H.lead n d w 0 K compact sep) tol htol)
  filter_upwards [fields] with k price t supp amp
  have point (x) (hx : x∈K) : ‖E k x‖≤tol := by
    have estimate := price x hx
    rw [dist_comm,dist_eq_norm] at estimate
    have jets : iteratedFDeriv ℝ 0 (PhysMS.measured F none (J (z.r k)) w (z.r k)) x-
        iteratedFDeriv ℝ 0 (WickGoal w) x = iteratedFDeriv ℝ 0
        (PhysMS.measured F none (J (z.r k)) w (z.r k)-WickGoal w) x := by ext v; simp
    rw [jets,norm_iteratedFDeriv_zero] at estimate
    exact estimate.le
  have onK : t.applyTo (E k)=∫ x in K,t x*E k x := by
    rw [← integral_indicator compact.measurableSet]
    apply integral_congr_ae
    refine ae_of_all _ fun x => ?_
    by_cases hx : x∈K
    · simp [hx]
    have ht : t x=0 := image_eq_zero_of_notMem_tsupport fun y => hx (supp y)
    simp [hx,ht]
  rw [onK]
  calc
    _ ≤ (M*tol)*volume.real K := norm_setIntegral_le_of_norm_le_const compact.measure_lt_top (fun x hx =>
      (norm_mul_le ..).trans (mul_le_mul (amp x) (point x hx) (norm_nonneg _) hM.le))
    _ ≤ (M*tol)*c := mul_le_mul_of_nonneg_left (by dsimp [c]; linarith) (mul_nonneg hM.le htol.le)
    _ = ε := by dsimp only [tol]; field_simp

end YM.Integration.WilsonReportPrescribedTests
end

