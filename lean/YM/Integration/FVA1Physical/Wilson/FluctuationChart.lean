import YM.Integration.FVA1Physical.Wilson.HotelPurchase

/-! The calibrated local posterior remains inside the natural fluctuation
scale when its retained boundary already varies on that scale. The cost of
the next chart is independent of its volume, marked location and forest. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Lis MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bulk
open RGComparison.Core16 MSbar.Whisk MSbar.Rolling MSbar.Cacao Comparison.RG02 Push Push.Uniform SectorNext.Vacuum
open MSbar.Bakery.Portal MSbar.Mosaic
open scoped Classical Topology
variable {G:Gauge}

private theorem room_nonneg {v:ℝ} (hv:1 ≤ v) : 0 ≤ room v := by
  unfold room distance
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hv) _) (Real.log_nonneg hv)) (Real.sqrt_nonneg _)

theorem fluctuation_below_skies (D:ℝ) : ∀ᶠ y:ℝ in atTop,D*room y ≤ skies y := by
  filter_upwards [(Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop D,
    eventually_ge_atTop (1:ℝ)] with y reserve large
  have nonneg:0 ≤ distance y := mul_nonneg (Real.rpow_nonneg (zero_le_one.trans large) _) (Real.log_nonneg large)
  have h:=mul_le_mul_of_nonneg_right reserve (Real.sqrt_nonneg (Real.log y))
  calc D * room y = distance y*(D*Real.sqrt (Real.log y)) := by unfold room;ring
       _ ≤ distance y*(Real.sqrt (Real.log y)*Real.sqrt (Real.log y)) := mul_le_mul_of_nonneg_left h nonneg
       _ = skies y := by rw [Real.mul_self_sqrt (Real.log_nonneg large)];rfl

/-- The Lipschitz price for the physical exponential chart of the next
localized block, with input bounded by a multiple of its actual hotel width. -/
def fluctuationFee (P:Palisade) (J:Voice G) (D:ℝ) :=
  J.C*(J.C*shade G*((ceilingP P+1)*D+1))

theorem fluctuation_radii (P:Palisade) (J:Voice G) (cle:Clear G J) (D:ℝ) :
    ∀ᶠ v:ℝ in atTop,∀ z μ:ℝ,0 ≤ z → z ≤ D*room v →
    (z < P.initial → μ ≤ stars P z) →
    let a:=J.C*shade G*(μ+room v+z)
    a ≤ J.δ ∧ J.C*a < (LocalH.geom_patch G).choose ∧ J.C*a ≤ fluctuationFee P J D*room v := by
  let B:=J.C*shade G
  let C:=B*((ceilingP P+1)*D+1)
  have jc:=zero_le_one.trans cle.cost
  have b₀:0 ≤ B:=mul_nonneg jc (shade_pos G).le
  have c₀:0 ≤ ceilingP P:=by unfold ceilingP;positivity
  have small (C:ℝ): Tendsto (fun v=>C*room v) atTop (𝓝 0) := by
    simpa only [zero_mul,zero_add] using hotel_physical_small P J 0 C
  have src:=(small D).eventually (eventually_lt_nhds (lt_min zero_lt_one P.first))
  have near:=(small C).eventually (eventually_lt_nhds cle.dist)
  have chart:=((small C).const_mul J.C).eventually (eventually_lt_nhds
    (show J.C*0 < (LocalH.geom_patch G).choose by rw [mul_zero];exact (LocalH.geom_patch G).choose_spec.1))
  filter_upwards [src,near,chart] with v start inside physical
  intro z μ hz bound center a
  have initial:=bound.trans_lt (start.trans_le (min_le_right ..))
  have z1:=bound.trans (start.le.trans (min_le_left ..))
  have μbound:=(center initial).trans (sail P hz z1)
  have h:=mul_le_mul_of_nonneg_left μbound b₀
  have t:=mul_le_mul_of_nonneg_left bound (mul_nonneg b₀ (by linarith only [c₀]:0 ≤ ceilingP P+1))
  have price:a ≤ C*room v:=by
    change B*(μ+room v+z) ≤ B*((ceilingP P+1)*D+1)*room v
    linarith only [h,t]
  have lift:=mul_le_mul_of_nonneg_left price jc
  exact ⟨price.trans inside.le,lift.trans_lt physical,lift.trans_eq (by unfold fluctuationFee;dsimp only [B,C];ring)⟩

theorem calibrated_fluctuation_chance (P:Palisade) (J:Voice G) (cle:Clear G J) {D:ℝ} (hD:0 ≤ D) :
    ∀ᶠ v:ℝ in atTop,∀ (A:Mosaic.Issue G) (X Y:Support A.f) (z:Positions (Primary A.c G)),
      ∀ {tag exp σ C δ Λ w:ℝ} {m:ℕ}, Mosaic.lensT v A.fClock → ‖z‖ ≤ D*room v →
      Grants A.v A.pre A.F P m → A.Calibrate J P X Y z v tag exp →
      let coarse:=represent (tint G (Exterior.Body 1 A.c) z)
      let μ:=vest (priced A.F A.v A.pre.clip A.pre.path) z
      let copy:=chambers A.F Y J coarse μ
      let H:=hotel A.F X Y J coarse μ (pillow v) (room v)
      let width:=fluctuationFee P J D*room v/A.fClock
      Admitted coarse A.pre A.S σ C δ Λ w →
      (∀ U∈H,copy U∈regularInputs A.fClock width) ∧
      chance A.S A.pre coarse ((copy ⁻¹' regularInputs A.fClock width)ᶜ) ≤ v^exp := by
  filter_upwards [fluctuation_radii P J cle D,eventually_gt_atTop (1:ℝ)] with v radius hv
  intro A X Y z tag exp σ C δ Λ w m band bound give paid coarse μ copy H width adm
  have rd:=radius ‖z‖ ‖μ‖ (norm_nonneg _) bound (fun hz=>terror A.F A.v P z give le_rfl hz)
  have hg:0<A.fClock := (half_pos (inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans hv)))).trans_le band.1
  have c₀:0 ≤ ceilingP P:=by unfold ceilingP;positivity
  have cost:0 ≤ fluctuationFee P J D:=by unfold fluctuationFee; have:=zero_le_one.trans cle.cost;have:0 ≤ shade G:=(shade_pos G).le;positivity
  have hw:0 ≤ width:=div_nonneg (mul_nonneg cost (room_nonneg hv.le)) hg.le
  have size:A.fClock*width=fluctuationFee P J D*room v:=by dsimp only [width]; field_simp
  have good (U:Config G A.f) (hit:U∈H):copy U∈regularInputs A.fClock width:=
    chord_to_regular cle hg hw rd.1 rd.2.1 (rd.2.2.trans_eq size.symm) _ (hotel_chord cle paid.first hit)
  refine ⟨good,?_⟩
  have mc:=(informed A.F X Y J coarse μ cle paid.first.extendsX).1
  have hc:=(garden_main A.F X Y J coarse μ cle paid.first.extendsX (A:=pillow v) (B:=room v)).from_here
  exact (c_mono coarse adm (mc (regular_meas _ _)).compl hc.compl (fun U bad hit=>bad (good U hit))).trans paid.sails

end YM.Integration.FVA1Physical.Wilson
