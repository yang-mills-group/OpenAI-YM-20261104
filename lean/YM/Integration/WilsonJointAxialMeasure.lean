import YM.Integration.WilsonJointAxialRoster

/-! The angular error for the entire joint roster uses only its genuine finite
plaquette set on the measured normalized Wilson marginal. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonJointAxialMeasure
open Filter Lattice Wilson RG OPE.Therm PhysicalNext.Repeat.Legato
open WilsonJointAxialRoster WilsonRegisteredAffineHalo WilsonRegisteredAxialRates
open WilsonReportingForestAngularFare
open scoped Classical BigOperators Topology

variable {G : Gauge} (R : Run G) {V : Type} [Fintype V]
local notation "β" => R.family.path.levels.clock.hatBeta

theorem count (simple : G.Simple) (p base : ℕ) :
    ∀ᶠ i : ℕ in atTop, ∀ per (o : V → Site (R.family.side i per)),
      ((plaquettes o (radius R p base i)).card:ℝ) ≤ β i := by
  let D := factor p base
  let C := ((Fintype.card V:ℝ)+1)*(2*D+1)^4*(Fintype.card PlaqAxes:ℝ)
  have dp : 0<D := by dsimp [D,factor];positivity
  have cp : 0<C := by dsimp only [C];positivity
  have grow := Next.Rank.Station.hat_rate R.family.path.levels simple
  have small := (Real.isLittleO_pow_log_id_atTop (n:=12)).bound (inv_pos.mpr cp)
  filter_upwards [grow.eventually small,(Real.tendsto_log_atTop.comp grow).eventually_ge_atTop 1] with i budget one
  intro per o
  let s := Real.log (β i)
  let H := radius R p base i
  have sp : 1 ≤ s := one
  have sn : 0 ≤ s := zero_le_one.trans sp
  have sp3 : 1 ≤ s^3 := one_le_pow₀ sp
  have hr : (H:ℝ) ≤ D*s^3 := geometry R p base i one
  have bound : (H+H+1:ℝ)^4 ≤ (2*D+1)^4*s^12 := by
    calc
      _ ≤ ((2*D+1)*s^3)^4 := pow_le_pow_left₀ (by positivity) (by linarith only [hr,sp3]) 4
      _ = _ := by ring
  have card : (plaquettes o H).card ≤
      Fintype.card V*((H+H+1)^4*Fintype.card PlaqAxes) := by
    unfold plaquettes
    apply (Finset.card_biUnion_le ..).trans
    simpa using (Finset.sum_le_sum (s:=(Finset.univ:Finset V))
      (fun v _ => WilsonAxialWindow.count (o v) H))
  have cash : s^12 ≤ C⁻¹*β i := by
    have bp : 0 ≤ β i := zero_le_one.trans (R.family.path.levels.fits.delayed i).le
    change ‖s^12‖ ≤ C⁻¹*‖β i‖ at budget
    simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg sn _),abs_of_nonneg bp] using budget
  have air : ((plaquettes o H).card:ℝ) ≤
      (Fintype.card V:ℝ)*((H+H+1:ℝ)^4*(Fintype.card PlaqAxes:ℝ)) := by exact_mod_cast card
  calc
    _ ≤ _ := air
    _ ≤ ((Fintype.card V:ℝ)+1)*(((2*D+1)^4*s^12)*(Fintype.card PlaqAxes:ℝ)) := by gcongr;linarith
    _ = C*s^12 := by dsimp only [C];ring
    _ ≤ C*(C⁻¹*β i) := mul_le_mul_of_nonneg_left cash cp.le
    _ = β i := by field_simp

theorem missed (simple : G.Simple) (gate : WilsonReportingForestAngularReflection.posted R)
    (p base K : ℕ) :
    ∀ᶠ j : ℕ in atTop, let i := j+1
    ∀ N per, i ≤ N → ∀ o : V → Site (R.family.side i per),
      let X := plaquettes o (radius R p base i)
      (scene R.family.path N per i).real (House.chilly (G:=G) X (angularCut (β i)))ᶜ ≤ (β i)⁻¹^K := by
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (count (V:=V) R simple p base),
    WilsonReportingForestAngularReflection.original R simple gate (K+1)] with j count' rare
  intro i N per live o X
  have bp : 0 < β i := zero_lt_one.trans (R.family.path.levels.fits.delayed i)
  haveI : MeasureTheory.IsProbabilityMeasure (scene R.family.path N per i) := probability (p:=per) R.makes.wilson live
  calc
    _ ≤ (X.card:ℝ)*(β i)⁻¹^(K+1) := House.cool_miss _ (rare N per live) X
    _ ≤ β i*(β i)⁻¹^(K+1) := mul_le_mul_of_nonneg_right (count' per o) (by positivity)
    _ = _ := by rw [pow_succ];field_simp

end YM.Integration.WilsonJointAxialMeasure
