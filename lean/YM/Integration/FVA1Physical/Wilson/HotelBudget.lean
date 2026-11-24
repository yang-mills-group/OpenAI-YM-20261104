import YM.MSbar.Mosaic.Extract

/-! The native forest localization bandwidth is strictly inside the scaled
Wilson chart at high inverse coupling on every bounded rescaled background. -/
set_option autoImplicit false
set_option maxHeartbeats 680000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Lis MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock
open scoped Classical Topology
variable {G : Gauge}

private lemma room_eq {v : ℝ} (hv : 1 < v) :
    room v=cue v*(Real.sqrt (Real.log v))^3 := by
  have base : v ^ (-(1 / 2 : ℝ)) = cue v := by
    rw [Real.rpow_neg (zero_le_one.trans hv.le), ←Real.sqrt_eq_rpow]; rfl
  have norm := Real.sq_sqrt (Real.log_pos hv).le
  rw [room,distance,base]
  calc cue v*Real.log v*Real.sqrt (Real.log v) = cue v*(Real.sqrt (Real.log v))^2*Real.sqrt (Real.log v) := by rw [norm]
       _ = _ := by ring

/-- The factor 1/32 of the actual bank is fully retained. The constants are
arbitrary fixed costs and the clock may vary over the entire admitted band. -/
theorem hotel_scalar (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ᶠ v:ℝ in atTop, ∀ g:ℝ, Mosaic.lensT v g →
    A*g+B*room v ≤ g*Mosaic.vol v := by
  have hs : Tendsto (fun v:ℝ=>Real.sqrt (Real.log v)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (1:ℝ),hs.eventually_ge_atTop (max 1 (32*(A+2*B)))] with v hv large
  intro g band
  let t := Real.sqrt (Real.log v)
  have h1 : 1 ≤ t := (le_max_left ..).trans large
  have big : 32*(A+2*B) ≤ t := (le_max_right ..).trans large
  have t₀ : 0 ≤ t := Real.sqrt_nonneg _
  have sq : t^2=Real.log v := Real.sq_sqrt (Real.log_pos hv).le
  have tg := (half_pos (inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans hv)))).trans_le band.1
  have ah : A ≤ A*t^3 := le_mul_of_one_le_right hA (one_le_pow₀ h1)
  have poly : A+2*B*t^3 ≤ t^4/32 := by
    have p := mul_le_mul_of_nonneg_right big (pow_nonneg t₀ 3)
    nlinarith only [p,ah]
  have money : cue v ≤ 2*g := by linarith only [band.1]
  calc A*g+B*room v = A*g+B*(cue v*t^3) := by rw [room_eq hv]
       _ ≤ A*g+B*((2*g)*t^3) := add_le_add_right (mul_le_mul_of_nonneg_left
         (mul_le_mul_of_nonneg_right money (pow_nonneg t₀ 3)) hB) _
       _ = g*(A+2*B*t^3) := by ring
       _ ≤ g*(t^4/32) := mul_le_mul_of_nonneg_left poly tg.le
       _ = g*Mosaic.vol v := by unfold Mosaic.vol Mosaic.hatW Alto.flurry; rw [←sq]; ring

theorem hotel_physical_small (P : Palisade) (J : Voice G) (A B : ℝ) :
    Tendsto (fun v:ℝ=>A*(2*cue v)+B*room v) atTop (𝓝 0) := by
  have H : Tendsto (fun v:ℝ=>v) atTop atTop := tendsto_id
  have ht := (Mosaic.Run.waxing H).1.bouquet H (by norm_num)
  have hb := (Mosaic.height H P J).2.1.bouquet H (by norm_num)
  simpa only [Function.comp_apply,mul_zero,add_zero] using ((ht.const_mul 2).const_mul A).add (hb.const_mul B)

end YM.Integration.FVA1Physical.Wilson
