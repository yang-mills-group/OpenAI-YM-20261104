import YM.Integration.OriginalPeriodWindingPrice
/-! Finite physical volume pays a winding fee for a prebooked polynomial
width and income on the actual family of torus sides. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPolynomialWinding
open Filter Lattice RG PhysicalNext.Repeat.Legato ActualRunAdmissionClock
open scoped Topology
variable {G:Gauge}

theorem original (R:Run G) (simple:G.Simple) (fund:RG05Preconstruction.ReadoutPurchase R.b)
    (a b c q:ℕ) : ∀ᶠ m:ℕ in atTop, ∀ N per:ℕ, m<N →
    let H:=R.family.path.levels.clock.hatBeta m
    let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
    ∀ ρ:ℝ, 0<ρ → ρ⁻¹ ≤ H^b → H^a*g^(-(c:ℝ))*
      Real.exp (-(ρ*((R.family.side m per).val:ℝ))/8) ≤ g^q := by
  let A:=R.family.path.levels
  let D:ℕ:=a+c+q
  have mesh:=ActualRunQLocalAdmission.actual_preMesh R fund
  filter_upwards [OriginalPeriodWindingPrice.period_power A (b+2),
    actual_inverse_lower R.family simple R.makes mesh,
    (WardBin.bell A simple).eventually_ge_atTop (8*(D:ℝ))] with m side wallet large
  intro N per hN H g ρ positive width
  have hot:0<H:=WardBin.hot A m
  have gp:0<g:=IterationFour.Currency.g_pos R.makes N per (m+1) (by omega)
  have hg:H⁻¹≤g:=wallet N per hN
  have funded:g⁻¹≤H:=by simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hot) hg
  have paid:1≤ρ*H^b:=by
    simpa only [inv_eq_one_div,div_le_iff₀ positive,mul_comm] using width
  have span:H^2≤ρ*((R.family.side m per).val:ℝ):=by
    calc
      _ = 1*H^2:=by ring
      _ ≤ (ρ*H^b)*H^2:=mul_le_mul_of_nonneg_right paid (sq_nonneg _)
      _ = ρ*H^(b+2):=by rw [pow_add];ring
      _ ≤ _:=mul_le_mul_of_nonneg_left (side per) positive.le
  have scale:(D:ℝ)*Real.log H≤ρ*((R.family.side m per).val:ℝ)/8:=by
    have first:=mul_le_mul_of_nonneg_left (Real.log_le_self hot.le) (Nat.cast_nonneg D)
    have second:=mul_le_mul_of_nonneg_right (show 8*(D:ℝ)≤H from large) hot.le
    nlinarith only [first,second,span]
  have tiny:=Real.exp_le_exp.mpr (neg_le_neg scale)
  have invoice:Real.exp (-((D:ℝ)*Real.log H))=(H^D)⁻¹:=by
    rw [Real.exp_neg,←Real.log_pow,Real.exp_log (pow_pos hot D)]
  rw [invoice] at tiny
  have invRate:g^(-(c:ℝ))≤H^c:=by
    rw [Real.rpow_neg gp.le,Real.rpow_natCast,← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr gp.le) funded c
  calc
    _ ≤ H^a*(H^c)*(H^D)⁻¹ :=mul_le_mul (mul_le_mul_of_nonneg_left invRate (pow_nonneg hot.le _))
      (by simpa only [neg_div] using tiny) (Real.exp_pos _).le (by positivity)
    _ = (H⁻¹)^q:=by dsimp [D];rw [pow_add,pow_add,inv_pow];field_simp
    _ ≤ g^q:=pow_le_pow_left₀ (inv_nonneg.mpr hot.le) hg q

end YM.Integration.WilsonOriginalPolynomialWinding
