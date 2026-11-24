import YM.Integration.WilsonAddressedCollarWindow
import YM.Integration.WilsonFundedMeasuredWindow

/-! The logarithmic upper stop at the true physical radius, including the reporter and upper overshoots. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedPhysicalCollar
open Filter Real RG OPE Trace.Pilot PhysicalNext.Repeat.Legato WilsonInvariantActionPosition
open private delay from YM.Integration.WilsonAddressedCollarWindow
open scoped Classical Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple) (slow:WilsonWindowReportingPace.Slow R.kit)
local notation "A" => R.family.path.levels
local notation "beta" => R.family.path.levels.clock.hatBeta
local notation "mesh" => R.family.S.a

include slow in
theorem original (v t:ℕ) (vp:0<v) (η:ℝ) (ep:0<η):
    ∀ᶠ r:ℝ in trail,let m:=WilsonMeasuredWindow.stop (A) simple v r
      let u:=berth R t m
      m<u ∧ (beta m)^t ≤ mesh m/mesh u ∧ mesh m/mesh u ≤ (beta m)^t*(beta m)^η ∧
        (beta m)^t ≤ r/mesh u ∧ r/mesh u ≤ (beta m)^t*((beta m)^η)^2:=by
  let e:=η/((v+1:ℕ):ℝ)
  have den:0<((v+1:ℕ):ℝ):=by positivity
  have small:0<e:=div_pos ep den
  have date:=WilsonMeasuredWindow.stop_tendsto (A) simple v vp
  filter_upwards [date.eventually (WilsonAddressedCollarWindow.original R simple slow t ep),
    date.eventually (delay R simple 1 small),Ioc_mem_nhdsGT (R.family.S.a_pos 0)] with r cuts logFee rLive
  let m:=WilsonMeasuredWindow.stop (A) simple v r
  let u:=berth R t m
  have band:=(WilsonFundedMeasuredWindow.all_radii R slow simple vp).2 r rLive.1 rLive.2
  have high:1≤beta m:=(R.family.path.levels.fits.delayed m).le
  have bp:0<beta m:=zero_lt_one.trans_le high
  have mb:1≤RG16.Lambda (A) m:=by
    unfold RG16.Lambda
    linarith [Real.log_nonneg high]
  have stop:1 ≤ r/mesh m:=(one_le_pow₀ mb).trans band.1
  have low:RG16.Lambda (A) m ≤ beta m^e:=by simpa [RG16.Lambda] using logFee
  have mast:(RG16.Lambda (A) m)^(v+1) ≤ (beta m)^η:=by
    apply (pow_le_pow_left₀ (zero_le_one.trans mb) low (v+1)).trans_eq
    rw [←Real.rpow_natCast,←Real.rpow_mul bp.le]
    congr 1
    exact div_mul_cancel₀ _ den.ne'
  have price:0 ≤ mesh m/mesh u:=div_nonneg (R.family.S.a_pos m).le (R.family.S.a_pos u).le
  have betaCost:0 ≤ (beta m)^η:=Real.rpow_nonneg bp.le _
  have move:r/mesh u=(r/mesh m)*(mesh m/mesh u):=by
    field_simp [(R.family.S.a_pos m).ne',(R.family.S.a_pos u).ne']
  refine ⟨cuts.1,cuts.2.1,cuts.2.2,?_,?_⟩
  · rw [move]
    exact cuts.2.1.trans (le_mul_of_one_le_left price stop)
  · rw [move]
    calc
      _ ≤ ((beta m)^η)*((beta m)^t*(beta m)^η):=
        mul_le_mul (band.2.trans mast) cuts.2.2 price betaCost
      _ = _:=by ring

end YM.Integration.WilsonAddressedPhysicalCollar
end
