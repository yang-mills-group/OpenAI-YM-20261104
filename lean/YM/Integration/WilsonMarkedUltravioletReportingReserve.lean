import YM.FullVolume.Cross
import YM.RG05Readout.Many.Pick

/-! One unit of the original support exponent pays for removing every tuning-date
marker weight, with a distance allowed by the original reporting census. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedUltravioletReportingReserve
open Finset Function Filter Lattice Wilson RG Marker Extra.Histories
open RG05Readout.Many PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical
variable {G : Gauge}

theorem calendar (R : Run G) (simple : G.Simple) (p T : ℕ) {ε : ℝ} (eps : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, let A := R.family.path.levels
      let B := (A.budget m).B
      ∃ D : ℕ, D * (4*B+2) + 2*B ≤ B^2 ∧
        ∀ N : ℕ, m ≤ N → ∀ per : ℕ,
          (A.clock.hatBeta m)^T * Real.exp (-(D:ℝ)) ≤
            ε * ((Real.sqrt (R.family.path.rep N per m).beta)⁻¹)^p := by
  let A := R.family.path.levels
  let c : ℝ := (T:ℝ)+(p:ℝ)+1
  have positive : 0 ≤ c := by dsimp [c]; positivity
  have grown := Real.tendsto_log_atTop.comp (Next.Rank.Station.hat_rate A simple)
  filter_upwards [grown.eventually_ge_atTop (max (max 1 (Real.log 2)) (max (-Real.log ε) (8*(c+2))))]
    with m late _ B
  let x := A.clock.hatBeta m
  let z := Real.log x
  let D := ⌈c*z⌉₊
  have one : 1 ≤ z := ((le_max_left 1 (Real.log 2)).trans (le_max_left ..)).trans late
  have two : Real.log 2 ≤ z := ((le_max_right 1 (Real.log 2)).trans (le_max_left ..)).trans late
  have eta : -Real.log ε ≤ z := ((le_max_left (-Real.log ε) (8*(c+2))).trans (le_max_right ..)).trans late
  have wide : 8*(c+2) ≤ z := ((le_max_right (-Real.log ε) (8*(c+2))).trans (le_max_right ..)).trans late
  have z0 : 0 ≤ z := zero_le_one.trans one
  have x0 : 0 < x := zero_lt_one.trans (A.fits.delayed m)
  have dmin : c*z ≤ (D:ℝ) := Nat.le_ceil _
  have dmax : (D:ℝ) ≤ c*z+1 := (Nat.ceil_lt_add_one (mul_nonneg positive z0)).le
  have bmin : z^2 ≤ (B:ℝ) := Nat.le_ceil _
  have bound : ((8*D+8:ℕ):ℝ) ≤ (B:ℝ) := by
    push_cast
    nlinarith only [dmax,bmin,mul_le_mul_of_nonneg_right wide z0,one]
  have cap : 8*D+8 ≤ B := by exact_mod_cast bound
  refine ⟨D,?_,?_⟩
  · calc D*(4*B+2)+2*B ≤ D*(6*B)+2*B :=
            Nat.add_le_add_right (Nat.mul_le_mul_left D (by omega)) _
      _ = (6*D+2)*B := by ring
      _ ≤ B*B := Nat.mul_le_mul_right B (by omega)
      _ = B^2 := by ring
  intro N live per
  let y := (R.family.path.rep N per m).beta
  have low := (R.makes.wilson.represents N per m live).band
  have yp : 0 < y := (half_pos x0).trans_le low.1
  have ylog : Real.log y ≤ Real.log (2*x) := Real.log_le_log yp low.2
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) x0.ne'] at ylog
  have py : (p:ℝ)*Real.log y ≤ (p:ℝ)*(2*z) :=
    mul_le_mul_of_nonneg_left (by change Real.log y ≤ Real.log 2+z at ylog; linarith only [ylog,two]) (Nat.cast_nonneg _)
  have gx : 0 < (Real.sqrt y)⁻¹ := inv_pos.mpr (Real.sqrt_pos.2 yp)
  have glog : Real.log (Real.sqrt y)⁻¹ = -(Real.log y)/2 := by
    rw [Real.log_inv,Real.log_sqrt yp.le]; ring
  have fx : x^T = Real.exp ((T:ℝ)*z) := by
    change x^T = Real.exp ((T:ℝ)*Real.log x)
    rw [←Real.log_pow,Real.exp_log (pow_pos x0 T)]
  change x^T*Real.exp (-(D:ℝ)) ≤ ε*((Real.sqrt y)⁻¹)^p
  rw [fx,←Real.exp_add]
  calc Real.exp ((T:ℝ)*z+ -(D:ℝ)) ≤ Real.exp (Real.log ε+(p:ℝ)*Real.log (Real.sqrt y)⁻¹) := by
            rw [Real.exp_le_exp,glog]
            dsimp only [c] at dmin
            nlinarith only [dmin,eta,py]
    _ = _ := by rw [Real.exp_add,Real.exp_log eps,←Real.log_pow,Real.exp_log (pow_pos gx _)]

theorem weights (C : Family G) (m d k h L : ℕ) {V : Type} [DecidableEq V]
    {J : Census V} (Q : V → ℝ) (qp : ∀ v, 0 < Q v)
    (qf : ∀ v, Q v ≤ (C.path.levels.clock.hatBeta m)^h)
    (s : J.Mode) (cap : s.val.card ≤ L) :
    1 ≤ (C.path.levels.clock.hatBeta m)^((k+h)*L) *
      Poly.toll (fun v => RG05Readout.Many.envelope C m d k (Q v) m) s := by
  let x := C.path.levels.clock.hatBeta m
  have x1 : 1 ≤ x := (C.path.levels.fits.delayed m).le
  have xp : 0 < x := zero_lt_one.trans_le x1
  have width (v : V) : RG05Readout.Many.envelope C m d k (Q v) m = (x^k*Q v)⁻¹ := by
    unfold RG05Readout.Many.envelope RG05Readout.Many.west
    rw [rust_above (le_refl m),one_mul]
    unfold markWidth
    rw [total_middle,mul_inv_rev,div_eq_mul_inv,mul_comm]
  have pos : 0 < ∏ v ∈ s.val, (x^k*Q v) := prod_pos fun v _ => mul_pos (pow_pos xp _) (qp v)
  have cost : (∏ v ∈ s.val, (x^k*Q v)) ≤ x^((k+h)*L) := calc
    _ ≤ ∏ _v ∈ s.val, (x^k*x^h) := prod_le_prod (fun v _ => mul_nonneg (pow_nonneg xp.le _) (qp v).le)
                  (fun v _ => mul_le_mul_of_nonneg_left (qf v) (pow_nonneg xp.le _))
    _ = (x^k*x^h)^s.val.card := prod_const _
    _ = x^((k+h)*s.val.card) := by rw [pow_mul,pow_add]
    _ ≤ x^((k+h)*L) := pow_le_pow_right₀ x1 (Nat.mul_le_mul_left _ cap)
  simp only [Poly.toll,width,Finset.prod_inv_distrib]
  rw [←div_eq_mul_inv]
  exact (le_div_iff₀ pos).mpr (by simpa only [one_mul] using cost)

end YM.Integration.WilsonMarkedUltravioletReportingReserve
