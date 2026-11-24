import YM.Integration.WilsonPointChildInverseIncome
import YM.Integration.WilsonNeutralAnnouncedPrimaryPrice
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointMatrixCash
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open scoped Topology BigOperators Matrix Classical

variable {G : Gauge} (R : Run G) {d D : ℕ} (wood : Primer.Families R.family)
variable (a : hue G) (depth : d < D) {U : ℕ → ℕ}
variable (grant : WilsonWindowFormalPurchase.Canonical U R.kit)


private theorem numerical (c:ℝ)(c₀:0≤c)(v:ℕ){δ:ℝ}(δ₀:0<δ):
    ∀ᶠβ:ℝ in atTop,c*(2+Real.log β)^v≤β^δ:=by
  let C:=c*2^v
  have C₀:0≤C:=by dsimp [C];positivity
  have little:=(isLittleO_log_rpow_rpow_atTop (v:ℝ) δ₀).def (show 0<(1+C)⁻¹ by positivity)
  filter_upwards [little,Real.tendsto_log_atTop.eventually_ge_atTop 2,eventually_gt_atTop (0:ℝ)] with x h hx xp
  have bound:(Real.log x)^v≤(1+C)⁻¹*x^δ:=by
    change ‖(Real.log x)^(v:ℝ)‖≤(1+C)⁻¹*‖x^δ‖ at h
    simpa only [Real.rpow_natCast,Real.norm_of_nonneg (pow_nonneg (by linarith:0≤Real.log x) _),
      Real.norm_of_nonneg (Real.rpow_nonneg xp.le _)] using h
  calc
    _ ≤ c*(2*Real.log x)^v:=by gcongr;linarith
    _ = C*(Real.log x)^v:=by rw [mul_pow];ring
    _ ≤ (1+C)*((1+C)⁻¹*x^δ):=mul_le_mul (by linarith) bound (by positivity) (by linarith)
    _ = x^δ:=by field_simp

theorem original (simple:G.Simple)(E:ℕ)(paid:WilsonPointChildInverseIncome.Forward R wood a depth E)
    {δ:ℝ}(pos:0<δ):
    ∀ᶠi:ℕ in atTop,∀N:ℕ,i<N→∀(digit:∀j,Site (R.family.S.block j))(b:Letter (R.family.labels.level d)),
      ∑v:Letter (R.family.labels.level d),∑j:Fin (E+1),
        |coeff j.val (WilsonNeutralPointCourse.transfer R wood a depth digit N i v b)|≤
        (R.family.path.levels.clock.hatBeta i)^δ:=by
  let A:=Letter (R.family.labels.level d)
  let fee:ℝ:=(Fintype.card A:ℝ)*(E+1)
  have price:0≤fee:=by dsimp [fee];positivity
  have growth:Tendsto R.alloy.B.a.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
    (R.family.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  have owned (v b:A)(j:Fin (E+1)):∀ᶠi:ℕ in atTop,∀N:ℕ,i<N→∀digit:∀h,Site (R.family.S.block h),
      |coeff j.val (WilsonNeutralPointCourse.transfer R wood a depth digit N i v b)|≤
      (R.family.path.levels.clock.hatBeta i)^δ/(1+fee):=by
    obtain ⟨c,e,c₀,h⟩:=paid v b j (Nat.le_of_lt_succ j.isLt)
    have num:=growth.eventually (numerical ((1+fee)*c) (by positivity) e pos)
    filter_upwards [h,num] with i ht hb N newer digit
    apply (le_div_iff₀ (by positivity:0<1+fee)).mpr
    calc
      _ ≤ (c*(RG16.Lambda R.family.path.levels i)^e)*(1+fee):=mul_le_mul_of_nonneg_right (ht N newer digit) (by positivity)
      _ = (1+fee)*c*(RG16.Lambda R.family.path.levels i)^e:=by ring
      _ ≤ _:=hb
  have all:=Filter.eventually_all.mpr (fun v:A=>Filter.eventually_all.mpr (fun b:A=>
    Filter.eventually_all.mpr (fun j:Fin (E+1)=>owned v b j)))
  filter_upwards [all,growth.eventually_ge_atTop 1] with i hi hp N newer digit b
  calc
    _ ≤ ∑_v:A,∑_j:Fin (E+1),(R.family.path.levels.clock.hatBeta i)^δ/(1+fee):=
      Finset.sum_le_sum (fun v _=>Finset.sum_le_sum (fun j _=>hi v b j N newer digit))
    _ = fee*((R.family.path.levels.clock.hatBeta i)^δ/(1+fee)):=by simp [fee,nsmul_eq_mul];ring
    _ ≤ (1+fee)*((R.family.path.levels.clock.hatBeta i)^δ/(1+fee)):=by gcongr;linarith
    _ = _:=by field_simp

end YM.Integration.WilsonOlderFreshPointMatrixCash
end
