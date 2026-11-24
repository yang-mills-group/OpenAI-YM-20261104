import YM.Integration.FVA1Physical.Wilson.HotelChord
import YM.Integration.FVA1Physical.Wilson.HotelBudget

/-! The actual measured probability of the complement of the finite-torus Wilson
chart on a full calibrated hotel, for every uniformly bounded retained field. -/
set_option autoImplicit false
set_option maxHeartbeats 680000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Lis MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bulk
open RGComparison.Core16 MSbar.Whisk MSbar.Rolling MSbar.Cacao Comparison.RG02 Push Push.Uniform SectorNext.Vacuum
open MSbar.Bakery.Portal MSbar.Mosaic
open scoped Classical Topology

variable {G : Gauge}
theorem bounded_hotel_radii (P : Palisade) (J : Voice G) (cle : Clear G J) {D : ℝ} (hD : 0 ≤ D) :
    ∀ᶠ v:ℝ in atTop, ∀ g:ℝ, Mosaic.lensT v g → ∀ z μ:ℝ, 0 ≤ z → z ≤ g*D →
    (z < P.initial → μ ≤ stars P z) →
    let a := J.C*shade G*(μ+room v+z)
    a ≤ J.δ ∧ J.C*a < (LocalH.geom_patch G).choose ∧ J.C*a ≤ g*Mosaic.vol v := by
  let B := J.C * shade G
  let A := B * (ceilingP P+1) * D
  have hC := zero_le_one.trans cle.cost
  have b₀ : 0 ≤ B := mul_nonneg hC (shade_pos G).le
  have lim : 0 ≤ ceilingP P := by unfold ceilingP; positivity
  have a₀ : 0 ≤ A := mul_nonneg (mul_nonneg b₀ (by linarith only [lim])) hD
  have src := hotel_physical_small P J D 0
  simp only [zero_mul,add_zero] at src
  have hsource := src.eventually (eventually_lt_nhds (lt_min zero_lt_one P.first))
  have small := hotel_physical_small P J A B
  have local_ := small.eventually (eventually_lt_nhds cle.dist)
  have chart := (small.const_mul J.C).eventually (eventually_lt_nhds
    (show J.C*0 < (LocalH.geom_patch G).choose by rw [mul_zero]; exact (LocalH.geom_patch G).choose_spec.1))
  filter_upwards [hsource,local_,chart,hotel_scalar (J.C*A) (J.C*B) (mul_nonneg hC a₀) (mul_nonneg hC b₀)]
    with v src inside physical scaled
  intro g band z μ hz zbound center a
  have bound : z ≤ D*(2*cue v) := zbound.trans (by rw [mul_comm g]; exact mul_le_mul_of_nonneg_left band.2 hD)
  have initial : z < P.initial := bound.trans_lt (src.trans_le (min_le_right ..))
  have z1 := bound.trans (src.le.trans (min_le_left ..))
  have μbound := (center initial).trans (sail P hz z1)
  have price : a ≤ A*g+B*room v := by
    have h := mul_le_mul_of_nonneg_left μbound b₀
    have h' := mul_le_mul_of_nonneg_left zbound (mul_nonneg b₀ (by linarith only [lim] : 0 ≤ ceilingP P+1))
    change B*(μ+room v+z) ≤ B*(ceilingP P+1)*D*g+B*room v
    linarith only [h,h']
  have lift := mul_le_mul_of_nonneg_left price hC
  have dominant : A*g+B*room v ≤ A*(2*cue v)+B*room v :=
    add_le_add (mul_le_mul_of_nonneg_left band.2 a₀) le_rfl
  refine ⟨(price.trans dominant).trans inside.le,(lift.trans (mul_le_mul_of_nonneg_left dominant hC)).trans_lt physical,?_⟩
  exact lift.trans ((le_of_eq (by ring)).trans (scaled g band))

/-- An actual conditional probability, on the same hotel as the native
arbitrary-order exceptional estimate. The cutoff precedes period, support,
physical background, forest, tags, and the number of links. -/
theorem calibrated_chart_chance (P : Palisade) (J : Voice G) (cle : Clear G J) {D : ℝ} (hD : 0 ≤ D) :
    ∀ᶠ v:ℝ in atTop, ∀ (A : Mosaic.Issue G) (X Y : Support A.f) (z : Positions (Primary A.c G)),
      ∀ {tag exp σ C δ Λ w : ℝ} {m : ℕ}, Mosaic.lensT v A.fClock → ‖z‖ ≤ A.fClock*D →
      Grants A.v A.pre A.F P m → A.Calibrate J P X Y z v tag exp →
      let coarse := represent (tint G (Exterior.Body 1 A.c) z)
      let μ := vest (priced A.F A.v A.pre.clip A.pre.path) z
      let copy := chambers A.F Y J coarse μ
      let H := hotel A.F X Y J coarse μ (pillow v) (room v)
      Admitted coarse A.pre A.S σ C δ Λ w →
      (∀ U∈H,copy U∈regularInputs A.fClock (Mosaic.vol v)) ∧
      chance A.S A.pre coarse ((copy ⁻¹' regularInputs A.fClock (Mosaic.vol v))ᶜ) ≤ v^exp := by
  filter_upwards [bounded_hotel_radii P J cle hD,eventually_gt_atTop (1:ℝ)] with v radius hv
  intro A X Y z tag exp σ C δ Λ w m band bound give paid coarse μ copy H adm
  have hash := radius A.fClock band ‖z‖ ‖μ‖ (norm_nonneg _) bound (fun hz=>terror A.F A.v P z give le_rfl hz)
  have hg : 0 < A.fClock := (half_pos (inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans hv)))).trans_le band.1
  have hw : 0 ≤ Mosaic.vol v := div_nonneg (sq_nonneg _) (by norm_num)
  have good (U : Config G A.f) (hit : U∈H) : copy U∈regularInputs A.fClock (Mosaic.vol v) :=
    chord_to_regular cle hg hw hash.1 hash.2.1 hash.2.2 _ (hotel_chord cle paid.first hit)
  refine ⟨good,?_⟩
  have mc := (informed A.F X Y J coarse μ cle paid.first.extendsX).1
  have hc := (garden_main A.F X Y J coarse μ cle paid.first.extendsX (A:=pillow v) (B:=room v)).from_here
  exact (c_mono coarse adm (mc (regular_meas _ _)).compl hc.compl
    (fun U bad hit=>bad (good U hit))).trans paid.sails

end YM.Integration.FVA1Physical.Wilson
