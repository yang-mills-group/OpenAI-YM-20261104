import YM.Integration.WilsonReportingDecoratedCurrency

/-! Convert the upper thermal price of a moving short logarithm into the coupling
of the same represented Wilson step. The angular derivative scale is retained. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingLogCurrency
open Filter Lattice RG Wilson PhysicalNext.Repeat.Legato ConnectedActivityE6 Blaze
open scoped Classical Topology

variable {G : Gauge} (R : Run G) (simple : G.Simple)
include simple

theorem physical {a X ε : ℝ} (ha : 0 ≤ a) (hX : X < -(a/2)) (he : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N per, m < N →
      7 * (R.alloy.B.a.clock.hatBeta (m+1))^X ≤
        ε * (Pert.Asymptotics.regulatorRun R.family N per (m+1))^a := by
  let h := a/2
  have hpos : 0 ≤ h := by dsimp [h]; linarith
  have gap : 0 < -X-h := by dsimp [h]; linarith
  have grow := (Next.Rank.Station.hat_rate R.family.path.levels simple).comp (tendsto_add_atTop_nat 1)
  have vanishes := (tendsto_rpow_neg_atTop gap).comp grow
  have tol : 0 < ε * (2:ℝ)^(-h)/7 := by positivity
  filter_upwards [vanishes.eventually_lt_const tol, grow.eventually_gt_atTop (0:ℝ)] with m small warm N per live
  let y := R.alloy.B.a.clock.hatBeta (m+1)
  let b := R.family.path.β N per (m+1)
  change 0 < y at warm
  change y ^ (-(-X-h)) < ε * (2:ℝ)^(-h)/7 at small
  have bpos : 0 < b := Overlay.beta_positive R.makes.wilson live
  have band : b ≤ 2*y := (R.makes.wilson.represents N per (m+1) live).band.2
  have scaled : (2*y)^(-h) ≤ b^(-h) := Real.rpow_le_rpow_of_nonpos bpos band (by linarith)
  have gpower : b^(-h) = (Pert.Asymptotics.regulatorRun R.family N per (m+1))^a := by
    change b^(-h) = ((Real.sqrt b)⁻¹)^a
    rw [Real.inv_rpow (Real.sqrt_nonneg b), Real.sqrt_eq_rpow, ← Real.rpow_mul bpos.le,
      ← Real.rpow_neg bpos.le]
    congr 1; dsimp [h]; ring
  calc 7*y^X = (7*y^(-(-X-h)))*y^(-h) := by
         rw [mul_assoc, ← Real.rpow_add warm]; congr 2; ring
       _ ≤ (ε*(2:ℝ)^(-h))*y^(-h) := by
         exact mul_le_mul_of_nonneg_right (by linarith only [small]) (Real.rpow_nonneg warm.le _)
       _ = ε*(2*y)^(-h) := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) warm.le, mul_assoc]
       _ ≤ ε*b^(-h) := mul_le_mul_of_nonneg_left scaled he.le
       _ = _ := congrArg (ε * ·) gpower

/-- The gap between Spend's paid power and the requested physical order can be
used before choosing the cutoff, the period, or any angular directions. -/
theorem order (p s : ℕ) (ρ : ℝ) (positive : 0 ≤ ρ) (room : 8*((p:ℝ)+1+ρ) < s+1)
    {ε : ℝ} (he : 0 < ε) : ∃ X : ℝ, -((s:ℝ)+1)/16 < X ∧
    ∀ᶠ m : ℕ in atTop, ∀ N per, m<N →
      7*(R.alloy.B.a.clock.hatBeta (m+1))^X ≤
      ε*(Pert.Asymptotics.regulatorRun R.family N per (m+1))^((p:ℝ)+1+ρ) := by
  have gap : -((s:ℝ)+1)/16 < -(((p:ℝ)+1+ρ)/2) := by linarith only [room]
  obtain ⟨X,lo,hi⟩ := exists_between gap
  exact ⟨X,lo,physical R simple (by linarith [Nat.cast_nonneg (α:=ℝ) p]) hi he⟩

end YM.Integration.WilsonMovingLogCurrency
