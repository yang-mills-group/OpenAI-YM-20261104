import YM.Integration.WilsonReportMixedScale
import YM.Integration.WilsonOrdinaryMixedGram

/-! Numerical price of the actual common finer detector mesh in the physical
coupling, together with the two independently calibrated reflected fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportDetectorMesh
open Filter Set Function Lattice Wilson Extraction Spec Climb PhysMS SharpGram RG17
open OPE.Levy Push.FiniteDetection.Free Trace.Pilot
open PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} {F : Final R.family f S}

theorem small (hG : G.Simple) (pace : WilsonWindowReportingPace.Slow R.kit) {B : ℕ} (hB : 0<B)
    (g : ℝ→ℝ) (hg : Coupling G g) (q : ℕ) {c ε : ℝ} (hc : 0<c) (he : 0<ε) :
    ∀ᶠ r in RG17.home,let m := WilsonMeasuredWindow.stop R.family.path.levels hG B r
      c/(R.family.path.levels.clock.hatBeta m)^(q+1) ≤ ε*g r^q := by
  let m := WilsonMeasuredWindow.stop R.family.path.levels hG B
  let b (r : ℝ) := R.family.path.levels.clock.hatBeta (m r)
  have temp := WilsonPhysicalCutoffCurrency.temperature R hG pace hB g hg
  have inv : ∀ᶠ r in RG17.home,(1/2:ℝ)<b r*g r^2 :=
    temp.eventually (lt_mem_nhds (by norm_num : (1/2:ℝ)<1))
  have zero := Trace.Pilot.Coupling.conforms hG hg
  filter_upwards [inv,hg.positive,zero.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)),
    zero.eventually (gt_mem_nhds (div_pos he hc))] with r fit gp tiny left
  change c/(b r)^(q+1) ≤ _
  have bp : 0<b r := (R.family.path.levels.fits.delayed (m r)).trans' zero_lt_one
  have ab : (b r)⁻¹ ≤ 2*g r^2 := by
    rw [inv_eq_one_div,div_le_iff₀ bp]
    linarith only [fit]
  have invg : (b r)⁻¹ ≤ g r := ab.trans (by nlinarith only [mul_lt_mul_of_pos_right tiny gp])
  have budget : c*g r ≤ ε := by simpa only [mul_comm] using (lt_div_iff₀ hc).mp left |>.le
  calc
    _ = c*((b r)⁻¹)^(q+1) := by rw [inv_pow,div_eq_mul_inv]
    _ ≤ c*(g r)^(q+1) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr bp.le) invg _) hc.le
    _ = (c*g r)*g r^q := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right budget (pow_nonneg gp.le _)

/-- The first slot is normalized at s; reflection and complex conjugation
act on the second slot exactly as in the original real physical Gram. -/
theorem reflected (F : Final R.family f S) (J : ℝ→PhysMS.tower S) (P : Pier.Lair.Present F J) (d : ℕ) :
    ∀ᶠ r in RG17.home,∀ (s : ℝ) (v w : RG17.Free R.family d),
    let u := (J r d).symm (J s d v)
    let w' := (Bel R.family.book).adj (Maxwell.Free.spin_free R.family.labels) d timeAxis w
    WilsonOrdinaryMixedGram.mixed F J d r s v w =
      (S.classMoment S (fun _ : Fin 2=>d) (r • detectors) (fun j=>J r d ((![u,w'] : Fin 2→_) j))).re := by
  filter_upwards [P.scheme F _ d] with r aligned s v w
  rw [WilsonOrdinaryMixedGram.mixed_eq]
  exact Pier.Lair.echo F d _ _ _ aligned _

end YM.Integration.WilsonReportDetectorMesh
end

