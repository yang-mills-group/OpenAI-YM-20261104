import YM.Integration.WilsonPhysicalStationObservedGrid
import YM.TraceExtension.Prom.Hill.Tuning

/-! Round an actual normalized detector inside its original middle cell while
the station and its reporting magnification vary together. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickSites
open Filter Set MeasureTheory Lattice Wilson RG Extraction
open Next.Rank Next.Rank.Station
open scoped Topology BigOperators
variable {G:Gauge}(A:Levels G){n:ℕ}{I:Type*}{atI:Filter I}

theorem original (simple:G.Simple)(x:Points n)(hx:x∈generic n)(k:I→ℕ)(b:I→ℝ)
    (late:Tendsto k atI atTop)(width:∀ᶠ i in atI,1≤b i):
    Tendsto (fun i=>tested A (b i) (k i) x) atI (𝓝 x) ∧
    ∀ᶠ i in atI,AllowedSky A (b i) (k i) → FitSky A (b i) (k i) x:=by
  have heat:Tendsto A.clock.monitor atTop atTop:=
    (mag_rate A simple (show (0:ℝ)<1 from zero_lt_one)).congr (fun j=>Real.rpow_one _)
  have gain:Tendsto (fun i=>mag A (b i) (k i)) atI atTop:=by
    apply tendsto_atTop_mono' atI _ (heat.comp late)
    filter_upwards [width,(heat.comp late).eventually_ge_atTop 1] with i room hot
    exact (Real.rpow_one _).symm.trans_le (Real.rpow_le_rpow_of_exponent_le hot room)
  have fine:=tendsto_inv_atTop_zero.comp gain
  have posed:Tendsto (fun i=>tested A (b i) (k i) x) atI (𝓝 x):=by
    apply tendsto_iff_dist_tendsto_zero.mpr
    refine squeeze_zero (fun _=>dist_nonneg) (fun i=>Eq.trans_le
      (congr_arg (fun y=>dist y x) (reading A (b i) (k i) x))
      (Extraction.approximate (inv_pos.mpr (mag_pos ..)) x)) ?_
    simpa only [mul_zero] using! fine.const_mul (4*n:ℝ)
  refine ⟨posed,?_⟩
  have ha (i:Fin n)(j:Axis):∀ᶠ l in atI,8*|tested A (b l) (k l) x i j|≤A.clock.monitor (k l)^2:=by
    have ht:Tendsto (fun l=>8*|tested A (b l) (k l) x i j|) atI (𝓝 (8*|x i j|)):=
      (show Continuous fun z:Points n=>8*|z i j| by fun_prop).continuousAt.tendsto.comp posed
    have he:=((tendsto_pow_atTop (n:=2) (by decide)).comp (heat.comp late))
    exact (ht.eventually (ge_mem_nhds (lt_add_of_pos_right (8*|x i j|) zero_lt_one))).mp
      ((he.eventually_ge_atTop _).mono fun _ h t=>le_trans t h)
  filter_upwards [posed.eventually ((genericOpen n).mem_nhds hx),
    eventually_all.mpr (fun i=>eventually_all.mpr (ha i))] with i genericAt bounded issued
  refine ⟨by rw [anchored];exact Market.vision _ (gap_pos ..) _ genericAt,fun v j=>?_⟩
  rw [anchored]
  change |gap A (b i) (k i)*tested A (b i) (k i) x v j|≤_
  rw [abs_mul,abs_of_nonneg (gap_pos ..).le]
  have h:=mul_le_mul_of_nonneg_left (bounded v j) (gap_pos A (b i) (k i)).le
  have paid:=(le_div_iff₀ (A.S.a_pos (k i))).1 issued.dilation
  unfold gap at *
  linarith only [h,paid]

end YM.Integration.WilsonPhysicalStationMixedWickSites
end
