import YM.Integration.WilsonOriginalProjectedCurvatureReportingClock
import YM.Integration.WilsonMovingMentorPageCoupling
import YM.Integration.WilsonMovingMentorHardTemperature

/-! Restore every genuine occupied component at the elected reporting date using
the measured coupling of that date, uniformly in every later upper regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureReportingRefund
open Function Filter Finset Lattice RG Marker Source
open PhysicalNext.Repeat.Legato ConnectedActivityE6 AllOrder QuadraticLocal
open scoped Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)

include simple
theorem original {V:Type} [DecidableEq V] [Fintype V] {C:ℝ} (hC:1≤C) (b q:ℕ) {ε:ℝ} (positive:0<ε) :
    ∀ᶠ m:ℕ in atTop, ∀ Ω:ℝ,1≤Ω →
      Ω≤(R.alloy.B.a.clock.hatBeta (m+1))^(Beaming.grain (R.alloy.B.a.clock.J m)) →
      ∀ (N per:ℕ),m<N → ∀ s:(Stock.census V).Mode,
      let x:=R.alloy.B.a.clock.hatBeta (m+1)
      let g:=Coat.gStep (R.family.path.rep N per (m+1)).beta
      ((C*x^b)*Ω)^s.val.card * g^(q+2*(b*Fintype.card V)+1) ≤ ε*g^q := by
  let cap:=Fintype.card V
  let k:=b*cap
  let fare:=C^cap*(2:ℝ)^k
  have cp:=zero_lt_one.trans_le hC
  have farepos:0<fare:=mul_pos (pow_pos cp _) (pow_pos (by norm_num) _)
  have bought:=WilsonMovingMentorPageCoupling.repaid R simple cap (q+2*k) (div_pos positive farepos)
  filter_upwards [bought] with m week
  intro Ω hΩ high N per live s x g
  have xp:1≤x:=(R.alloy.B.a.fits.delayed (m+1)).le
  have gp:0≤g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have wp:1≤C*x^b*Ω:=one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ xp)) hΩ
  have rooted:=week Ω (zero_le_one.trans hΩ) high N per live
  have heat:=WilsonMovingMentorHardTemperature.measured R (Nat.succ_le_of_lt live) per k q
  change Ω^cap*g^(q+2*k+1)≤(ε/fare)*g^(q+2*k) at rooted
  change g^(q+2*k)*x^k≤g^q*(2:ℝ)^k at heat
  have coins:(C*x^b)^cap=C^cap*x^k:=by rw [mul_pow,←pow_mul]
  calc
    (C*x^b*Ω)^s.val.card*g^(q+2*k+1) ≤ (C*x^b*Ω)^cap*g^(q+2*k+1) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ wp (Finset.card_le_univ _)) (pow_nonneg gp _)
    _ = (C*x^b)^cap*(Ω^cap*g^(q+2*k+1)):=by rw [mul_pow,mul_assoc]
    _ ≤ (C*x^b)^cap*((ε/fare)*g^(q+2*k)) :=
      mul_le_mul_of_nonneg_left rooted (pow_nonneg (mul_nonneg cp.le (pow_nonneg (zero_le_one.trans xp) _)) _)
    _ = (C^cap*(ε/fare))*(g^(q+2*k)*x^k):=by rw [coins]; ring
    _ ≤ (C^cap*(ε/fare))*(g^q*(2:ℝ)^k) :=
      mul_le_mul_of_nonneg_left heat (mul_nonneg (pow_nonneg cp.le _) (div_nonneg positive.le farepos.le))
    _ = ε*g^q:=by dsimp only [fare]; field_simp

end YM.Integration.WilsonOriginalProjectedCurvatureReportingRefund
