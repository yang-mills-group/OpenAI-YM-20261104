import YM.Integration.ActualRunQLocalAdmission

/-! Uniform winding charges on the actual purchased trajectory, including
any fixed negative Laurent power. Only one physical period is required, and
the width and prefactor may vary over the whole admitted schedule. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalPeriodWindingPrice
open Filter Function Lattice RG PhysicalNext.Repeat.Legato
open ActualRunAdmissionScales ActualRunAdmissionClock
open scoped Topology

variable {G : Gauge}

/-- Every physical torus has an integral, positive period in continuum units.
The lower bound therefore holds uniformly in the independent period index. -/
theorem period_power (A : Levels G) (d : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ p, A.clock.hatBeta m ^ d ≤ ((A.S.side m p).val : ℝ) := by
  let Z := A.S
  let C := A.clock.bar + G.slopeConstant
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d).comp Z.divergent).mul_const (C^d)
  rw [zero_mul] at h
  filter_upwards [h.eventually_le_const zero_lt_one, Z.divergent.eventually_ge_atTop 1]
    with m hm hm1 p
  have hb : A.clock.hatBeta m ≤ C*Z.scale m := by
    unfold C
    refine le_trans ?_ (add_mul _ _ _).symm.le
    exact add_le_add_left (le_mul_of_one_le_right A.clock.bar_pos.le hm1) _
  apply le_of_mul_le_mul_left (a := Z.a m) _ (Z.a_pos m)
  refine le_trans (b := 1) ?_ ?_
  · refine (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (WardBin.hot A m).le hb d) (Z.a_pos m).le).trans ?_
    rw [Stock.a_log]
    refine le_trans (le_of_eq ?_) hm
    simp only [Function.comp_apply, mul_pow]; ring
  · rw [Schedule.span_side]; exact_mod_cast (Z.period p).pos

/-- A purchase can price any smaller output rate whose reciprocal is covered
by the admitted cost. The full Laurent denominator and any fixed number of
copies of the cost are retained. All quantifiers after the single threshold
are uniform, including the actual cutoff, period and choice of rate. -/
theorem onRun (R : Run G) (hG : G.Simple) (paid : RG05Preconstruction.ReadoutPurchase R.b)
    (a c q : ℕ) : ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N →
    let g := Pert.Asymptotics.regulatorRun R.family N p (m+1)
    let C := admittedCost R.family.path.levels m
    ∀ s : ℝ, 0 < s → s⁻¹ ≤ C →
      C^a * g^(-(c : ℝ)) * Real.exp (-(s/512)*((R.family.side m p).val : ℝ)) ≤ g^q := by
  let A := R.family.path.levels
  let d : ℝ := (a+c+q : ℕ)
  have mesh := ActualRunQLocalAdmission.actual_preMesh R paid
  filter_upwards [period_power A 3, cost_subpower R.family hG R.makes mesh 1 zero_lt_one,
    actual_inverse_lower R.family hG R.makes mesh,
    (WardBin.bell A hG).eventually_ge_atTop (512*d)] with m hside hcost hbeta hlarge N p hN g C s hs hsC
  have hg : 0 < g := IterationFour.Currency.g_pos R.makes N p (m+1) (by omega)
  have hb := WardBin.hot A m
  have hc : C ≤ g⁻¹ := by simpa only [Real.rpow_neg_one] using hcost N p hN
  have hg0 : (A.clock.hatBeta m)⁻¹ ≤ g := hbeta N p hN
  have hrs : g ≤ s := by
    have h := inv_anti₀ (inv_pos.mpr hs) (hsC.trans hc)
    simpa only [inv_inv] using h
  have hsn : (A.clock.hatBeta m)⁻¹ * (A.clock.hatBeta m)^3 ≤
      s * ((R.family.side m p).val : ℝ) :=
    mul_le_mul (hg0.trans hrs) (hside p) (pow_nonneg hb.le _) hs.le
  have hh : (A.clock.hatBeta m)⁻¹*(A.clock.hatBeta m)^3 = (A.clock.hatBeta m)^2 := by
    field_simp [hb.ne']
  rw [hh] at hsn
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hl := (mul_le_mul_of_nonneg_left (Real.log_le_self hb.le) hd0).trans
    (mul_le_mul_of_nonneg_right (show d ≤ A.clock.hatBeta m/512 by linarith) hb.le)
  have hexp : d*Real.log (A.clock.hatBeta m) ≤ s/512*((R.family.side m p).val : ℝ) := by
    nlinarith only [hl, hsn]
  simpa only [neg_mul] using
    flat_product hb hg (zero_le_one.trans (admittedCost_one A m)) hc hg0 a c q hexp

end YM.Integration.OriginalPeriodWindingPrice
end
