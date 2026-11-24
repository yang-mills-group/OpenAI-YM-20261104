import YM.Integration.FVA1Physical.Wilson.HotelCell

/-! Absorb the support of the actual purchased forest into any fixed coupling
slack, before the torus, its site, and all measured couplings in the admitted band. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Mosaic
open scoped Classical Topology

variable (G : Gauge) (P : Patch)
theorem forest_scales {q η : ℝ} (hq : 0<q) (hη : 0<η) :
    ∀ᶠ x:ℝ in atTop, ∀ (f:Side) (b:Site f) (β w:ℝ), 0<w →
      let v := tip G P.L x
      v/2 ≤ β → β≤2*v →
      let g := cue β
      let δ := g^q
      0<g ∧ v^(-q)≤δ ∧ δ≤1/2 ∧
        motionCost G (boxX v b) w*(g^(q+η)/w) ≤ δ := by
  let major := fun x:ℝ=> (((skirt (spotN (tip G P.L x))*81*Fintype.card Axis*Fintype.card G.ColorIndex :ℕ):ℝ)*2)
  have bw : Beam G P.L (fun x=>(spotN (tip G P.L x):ℝ)) := by
    unfold spotN; simp only [Nat.cast_pow]; exact (Beam.shore P.L G).power 4
  have large : Beam G P.L major := by
    unfold major; push_cast
    exact (((((chargesA P _ bw).mul (Beam.coin 81)).mul (Beam.coin _)).mul (Beam.coin _)).mul (Beam.coin 2))
  let v := tip G P.L
  have rise := Work.E09.betaF_growth G P.L
  have grows := (tendsto_rpow_atTop (show 0 < q/2 by positivity)).comp
    (rise.atTop_mul_const (by norm_num : 0 < (1/2:ℝ)))
  filter_upwards [large.tick (η/4) (by positivity),rise.eventually_ge_atTop 4,grows.eventually_ge_atTop 2] with x cap big high
  intro f b β w hw t low up g δ
  have tv : 0<t := by change 0<tip G P.L x; linarith only [big]
  have hb : 0<β := (half_pos tv).trans_le low
  have hsq : t≤β^2 := by nlinarith only [low,big,mul_self_le_mul_self (half_pos tv).le low]
  have hsq' : β≤t^2 := up.trans (by nlinarith only [big,sq_nonneg (t-2)])
  have hg : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr hb)
  have act (s:ℝ) : g^s = β^(-(s/2)) := by
    change ((Real.sqrt β)⁻¹)^s=_
    rw [Real.sqrt_eq_rpow,←Real.rpow_neg hb.le,←Real.rpow_mul hb.le]; congr 1; ring
  have maj : major x≤ g^(-η) := by
    apply (le_abs_self _).trans (cap.trans ?_)
    calc t^(η/4) ≤ (β^2)^(η/4) := Real.rpow_le_rpow tv.le hsq (by positivity)
         _ = g^(-η) := by rw [act,←Real.rpow_natCast β 2,←Real.rpow_mul hb.le]; congr 1; push_cast; ring
  have coeff : (( (boxX t b).card * 81 * Fintype.card Axis * Fintype.card G.ColorIndex :ℕ):ℝ)*2 ≤ major x := by
    have size := Mosaic.caseX b t
    apply mul_le_mul_of_nonneg_right _ zero_le_two
    exact Nat.cast_le.mpr (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ size)))
  refine ⟨hg,?_,?_,?_⟩
  · rw [show δ=β^(-(q/2)) from act q,Real.rpow_neg tv.le,Real.rpow_neg hb.le]
    apply inv_anti₀ (Real.rpow_pos_of_pos hb _)
    apply (Real.rpow_le_rpow hb.le hsq' (by positivity : 0≤ q/2)).trans_eq
    rw [←Real.rpow_natCast t 2,←Real.rpow_mul tv.le]
    congr 1; push_cast; ring
  · change 2 ≤ (t*(1/2))^(q/2) at high
    have hr := Real.rpow_le_rpow (half_pos tv).le low (by positivity : 0≤ q/2)
    rw [show t*(1/2)=t/2 by ring] at high
    have hh : 2≤β^(q/2) := high.trans hr
    rw [show δ=β^(-(q/2)) from act q,Real.rpow_neg hb.le,one_div]
    exact inv_anti₀ (by norm_num) hh
  · have exactWidth : motionCost G (boxX t b) w*(g^(q+η)/w)=(( (boxX t b).card*81*Fintype.card Axis*Fintype.card G.ColorIndex :ℕ):ℝ)*2*g^(q+η) := by
      unfold motionCost; field_simp [hw.ne']
    rw [exactWidth]
    apply (mul_le_mul_of_nonneg_right (coeff.trans maj) (Real.rpow_nonneg hg.le _)).trans_eq
    rw [←Real.rpow_add hg]; congr 1; ring
end YM.Integration.FVA1Physical.Wilson
