import YM.Integration.FVA1Physical.Sources.Round2.SignedHost
import YM.MSbar.Atlas.Apex

/-! The three authenticated nonthermal costs at the two adjacent physical
steps have arbitrarily high power decay, for every fixed stage and finite
source envelope. The threshold is chosen before either period or the test. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Filter Lattice RG YM.Wilson Pressure MSbar MSbar.Heath.Stock ConnectedActivityE6
open scoped Topology
variable {G:Gauge}

theorem signed_cost_decay (L:Side) {τ:ℝ} (pos:0 < τ) (B S u:ℝ) :
    ∀ᶠ x:ℝ in atTop, ∀ (M κ:ℝ), 0 ≤ M → M ≤ S → κ ≤ 1 →
      let y:=tip G L x
      courage G L x*(κ*M)+(B+M)*y^(u-1)+2*Real.exp (-τ*(radiusB y))*M ≤ 3*y^u := by
  have h:u-1 < u:=by linarith
  have vac:=((valor G L (u-1)).mul_right S) u h
  have reg:=((Pole.cape L G pos (u-1)).mul_right (2*S)) u h
  have localCost:Rate G L (u-1) (fun x=>(B+S)*(tip G L x)^(u-1)):=Rate.power.mul_left (B+S)
  filter_upwards [vac,reg,localCost u h,(Work.E09.betaF_growth G L).eventually_ge_atTop 0]
    with x a b c good M κ M0 cap κ1 y
  have m₁:κ*M ≤ S:=(mul_le_of_le_one_left M0 κ1).trans cap
  have v: courage G L x*(κ*M) ≤ y^u:=
    (mul_le_mul_of_nonneg_left m₁ (Real.exp_pos _).le).trans ((le_abs_self _).trans a)
  have w:(B+M)*y^(u-1) ≤ y^u:=(mul_le_mul_of_nonneg_right (add_le_add (le_refl B) cap)
    (Real.rpow_nonneg good _)).trans ((le_abs_self _).trans c)
  have s:Real.exp (-τ*(radiusB y))* (2*M) ≤ y^u:=(mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left cap zero_le_two) (Real.exp_pos _).le).trans ((le_abs_self _).trans b)
  linarith only [v,w,s]

end YM.Integration.FVA1Physical.Round2.Curvature
