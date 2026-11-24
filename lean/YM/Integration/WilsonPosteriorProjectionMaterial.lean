import YM.Integration.WilsonPosteriorProjectionBooking
import YM.Integration.FVA1Physical.Wilson.PacketTail
import YM.Integration.WilsonPosteriorProjectionChartRoom
import YM.Integration.WilsonPosteriorProjectionMaterialDegree

/-! Genuine fine Haar income, output degrees, and interpolation collar for
the true packet posterior. These apply even to a rough fine configuration. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionMaterial

open Set Filter Finset MeasureTheory Lattice RG YM.Wilson Precision Tree Exterior Push.Uniform
open MSbar MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage MSbar.Cacao MSbar.Mosaic
open MSbar.Rolling MSbar.Bulk MSbar.Lis MSbar.Bakery.Film MSbar.Midpoint MSbar.Measuring
open FVA1Physical.Wilson FVA1Physical.Round2.Curvature RG01.Kernel
open WilsonPosteriorProjectionBooking
open scoped BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge}

def fine (A : Issue G) (p : ℕ) (g : ℝ) (T : Nesting G A.f) (w : Config G A.f) :=
  clockReading p g T (chartLog g (canoe (S:=A.S) A.F w))

theorem measurable (A : Issue G) (p : ℕ) (g : ℝ) (T : Nesting G A.f) :
    Measurable (fine A p g T) :=
  (clockReading_continuous p g T).measurable.comp
    ((chartLog_meas g).comp (canoe_cont A.F).measurable)

/-- Both chart room and genuine bounded Haar income are uniform before the
volume, origin, forest, signed Wilson bank, or its linear probe is chosen. -/
theorem supplies (p m r : ℕ) : ∀ᶠ y : ℝ in atTop, 2 ≤ y ∧
    (∀ g : ℝ, lensT y g → demand r ≤ room y/g) ∧
    ∀ (A : Issue G) (b : Site A.f) (s : ℕ) (δ g : ℝ) (T : Nesting G A.f),
      δ ≤ 1 → BankPaid b y s p m δ T → lensT y g → |g| ≤ 1 →
      Bounded (prior G A.f) (fun (_ : A.S.Choices) w => ((fine A p g T w : ℝ) : ℂ)) (y^(m+3)) := by
  filter_upwards [eventually_ge_atTop (2:ℝ), WilsonPosteriorProjectionChartRoom.room_price (demand r) (demand_nonneg r),
    packet_global_bound (G:=G) p m] with y large roomPaid physical
  refine ⟨large,roomPaid,?_⟩
  intro A b s δ g T δ1 bank band g1
  refine ⟨fun _ => (Complex.continuous_ofReal.measurable.comp (measurable A p g T)).aestronglyMeasurable, ?_⟩
  intro _ w
  simpa only [fine,Complex.norm_real, Real.norm_eq_abs] using
    (physical b s δ g T δ1 bank band g1 (canoe (S:=A.S) A.F w))


end YM.Integration.WilsonPosteriorProjectionMaterial
end

