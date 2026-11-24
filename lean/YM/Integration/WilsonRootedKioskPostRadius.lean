import YM.Integration.WilsonMovingMentorRafflePrice

/-! Before-period coupling price for the radius used by the two actual Kiosk
tapes. The source rank is its full occupied roster on the same Wilson clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedKioskPostRadius
open Filter Function Lattice Wilson RG QuadraticLocal Earn Mentor MintClock AllOrder
open Pressure Push.PriceCompiler PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical Topology

private lemma threshold {x:ℝ} (large:16 ≤ x) : 1+2/Pressure.temp x ≤ x := by
  have xp:0<x:=by linarith
  let f:=Real.sqrt x
  have fp:0<f:=Real.sqrt_pos.mpr xp
  have temp : f⁻¹ ≤ Pressure.temp x :=
    le_mul_of_one_le_right (inv_pos.mpr fp).le (Real.one_le_exp (sq_nonneg _))
  calc
    _ ≤ 1+2*f := by
      rw [div_eq_mul_inv]
      exact add_le_add_right (mul_le_mul_of_nonneg_left
        ((inv_anti₀ (inv_pos.mpr fp) temp).trans_eq (inv_inv _)) zero_le_two) _
    _ ≤ x := by
      have square:f^2=x:=Real.sq_sqrt xp.le
      nlinarith only [square,fp,large]

private lemma wallet {x y A s Ω : ℝ} (one:1 ≤ x) (xy:x ≤ y)
    (cost:0 ≤ A) (localCost:A ≤ x) (sp:0<s) (width:s⁻¹ ≤ x)
    (op:0 ≤ Ω) (top:Ω ≤ y) (n:ℕ):
    Ω^5 + A^n*Ω/s ≤ 2*y^(max 5 (n+2)) := by
  have yp:0 ≤ y := zero_le_one.trans (one.trans xy)
  have byPower : ∀ j ≤ max 5 (n+2), y^j ≤ y^(max 5 (n+2)) :=
    fun j hj=>pow_le_pow_right₀ (one.trans xy) hj
  have start:Ω^5≤y^(max 5 (n+2)) :=
    (pow_le_pow_left₀ op top 5).trans (byPower 5 (le_max_left ..))
  have left:A^n*Ω ≤ y^n*y := mul_le_mul (pow_le_pow_left₀ cost (localCost.trans xy) n)
    top op (pow_nonneg yp _)
  have rest:A^n*Ω/s ≤ y^(max 5 (n+2)) := by
    rw [div_eq_mul_inv]
    have product:=mul_le_mul left (width.trans xy) (inv_pos.mpr sp).le
      (mul_nonneg (pow_nonneg yp n) yp)
    simpa only [Nat.add_assoc, pow_succ] using product.trans
        (show y^n*y*y ≤ y^(max 5 (n+2)) by
          simpa only [pow_succ] using byPower (n+2) (le_max_right ..))
  linarith only [start,rest]

theorem original {G:Gauge} (R:Run G) (simple:G.Simple):
    ∀ᶠ m:ℕ in atTop, let p:=R.alloy.B.a.budget m
      let x:=R.alloy.B.a.clock.hatBeta m
      let y:=R.alloy.B.a.clock.hatBeta (m+1)
      1 ≤ x ∧ x ≤ y ∧ Spill.allOver p ≤ x ∧ (Willow.haloSlack p.B)⁻¹ ≤ x ∧
      ∀ (n:ℕ) (extra Ω:ℝ),0 ≤ Ω →
        Ω ≤ y^(Beaming.grain (R.alloy.B.a.clock.J m)) →
        max (max 1 extra) (Ω^5+(Spill.allOver p)^n*Ω/(Willow.haloSlack p.B)) ≤
          max (max 1 extra) (2*y^(max 5 (n+2))) := by
  let A:=R.alloy.B.a
  have rise : Tendsto A.clock.hatBeta atTop atTop :=
    tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  have slack : ∀ᶠ x:ℝ in atTop,(Willow.haloSlack (Pressure.radiusB x))⁻¹ ≤ x := by
    filter_upwards [Page.tender G (1:Side) zero_lt_one _ (Page.season G (1:Side))] with x paid
    rw [Burn.hat_this] at paid
    exact paid.trans ((min_le_right ..).trans_eq (Real.rpow_one _))
  filter_upwards [rise.eventually_ge_atTop (16:ℝ),rise.eventually slack] with m large booked
  dsimp only
  have tuned : Spes.Market.tuning (R.metals.p.profile (A.clock.J m)) (A.budget m) (A.clock.hatBeta m) := by
    dsimp [A]
    rw [←params_eq R.alloy.B.valid m]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  have forward : A.clock.hatBeta m ≤ A.clock.hatBeta (m+1) := by
    dsimp [A]
    rw [beta_eq R.alloy.B.valid m]
    exact le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos simple).le
      (Real.log_nonneg (Nat.one_le_cast.mpr (R.rolls.L _).property)))
  have one : 1 ≤ A.clock.hatBeta m := by linarith only [large]
  have gross : Spill.allOver (A.budget m) ≤ A.clock.hatBeta m := by
    unfold Spill.allOver
    rw [tuned.1]
    exact threshold large
  have room : (Willow.haloSlack (A.budget m).B)⁻¹ ≤ A.clock.hatBeta m := by
    rw [tuned.2.1]
    exact booked
  refine ⟨one,forward,gross,room,?_⟩
  intro n extra Ω op scale
  have grain:Beaming.grain (A.clock.J m)≤1:=by
    unfold Beaming.grain
    exact (div_le_one (by positivity : 0<(A.clock.J m:ℝ)+1)).mpr
      (by linarith only [show 0 ≤ (A.clock.J m:ℝ) from Nat.cast_nonneg _])
  have top:Ω ≤ A.clock.hatBeta (m+1) := scale.trans
    ((Real.rpow_le_rpow_of_exponent_le (one.trans forward) grain).trans_eq (Real.rpow_one _))
  exact max_le_max_left _ (wallet one forward (zero_le_one.trans (Spill.allOver_ge _))
    gross (Willow.spare_pos _) room op top n)

end YM.Integration.WilsonRootedKioskPostRadius
