import YM.Integration.WilsonNeutralPrimaryWallet
/-! Restoration of the complete finite lower convolution at every physical
cutoff, with one arbitrarily small coupling-power price per enrolled date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralAnnouncedPrimaryPrice
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open scoped Topology BigOperators Matrix Classical

variable {G : Gauge} (R : Run G) {d D : ℕ} (wood : Primer.Families R.family)
variable (a : hue G) (depth : d < D) {U : ℕ → ℕ}
variable (grant : WilsonWindowFormalPurchase.Canonical U R.kit)

private theorem subpower (c:ℝ)(hc:0≤c)(n:ℕ){δ:ℝ}(pos:0<δ):
    ∀ᶠ x:ℝ in atTop,c*Borough.ageZ x^n ≤ x^δ:=by
  have small:=(isLittleO_log_rpow_rpow_atTop (n:ℝ) pos).def (show 0<1/(1+c) by positivity)
  filter_upwards [small,Real.tendsto_log_atTop.eventually_ge_atTop 1,eventually_gt_atTop (0:ℝ)]
    with x h hl hx
  have lp:0<Real.log x:=by linarith
  have zp:0≤Borough.ageZ x:=by
    unfold Borough.ageZ;have:=Real.log_nonneg hl;linarith
  have zl:Borough.ageZ x ≤ Real.log x:=by
    unfold Borough.ageZ;linarith [Real.log_le_sub_one_of_pos lp]
  have val:(Real.log x)^n ≤ (1/(1+c))*x^δ:=by
    change ‖(Real.log x)^(n:ℝ)‖ ≤ (1/(1+c))*‖x^δ‖ at h
    simpa only [Real.rpow_natCast,Real.norm_of_nonneg (pow_nonneg lp.le _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)] using h
  calc
    _ ≤ c*(Real.log x)^n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ zp zl _) hc
    _ ≤ (1+c)*((1/(1+c))*x^δ) := mul_le_mul (by linarith) val (by positivity) (by positivity)
    _ = _:=by field_simp

include grant in
theorem original (simple:G.Simple)(o:Loc G 1)(E:ℕ){δ:ℝ}(pos:0<δ):
    ∀ᶠ i:ℕ in atTop,∀ N : ℕ,i<N → ∀ b:Letter (R.family.labels.level d),
    ∑ u : Letter (R.family.labels.level d),∑ ν : Fin (E+1),
      |coeff ν.val (Primer.fieldStep R.family a wood depth N i u b)| ≤
      (R.family.path.levels.clock.hatBeta i)^δ:=by
  let A:=Letter (R.family.labels.level d)
  let fee:ℝ:=(Fintype.card A:ℝ)*(E+1)
  have price:0≤fee:=by dsimp [fee];positivity
  obtain ⟨k,bank⟩:=WilsonNeutralPrimaryWallet.dated R wood a depth grant simple o E
  have growth:Tendsto R.alloy.B.a.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
    (R.family.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  have owned (u b:A)(ν:Fin (E+1)):
      ∀ᶠ i:ℕ in atTop,∀ N:ℕ,i<N →
      |coeff ν.val (Primer.fieldStep R.family a wood depth N i u b)| ≤
        (R.family.path.levels.clock.hatBeta i)^δ/(1+fee):=by
    obtain ⟨c,n,hc,sale⟩:=bank u b ν.val (by omega)
    have z:=growth.eventually (subpower ((1+fee)*c) (by positivity) n pos)
    filter_upwards [z,eventually_ge_atTop k] with i h past N newer
    apply (le_div_iff₀ (by positivity:0<1+fee)).mpr
    calc
      _ ≤ (c*Borough.ageZ (R.family.path.levels.clock.hatBeta i)^n)*(1+fee):=
        mul_le_mul_of_nonneg_right (sale i past N newer) (by positivity)
      _ = (1+fee)*c*Borough.ageZ (R.family.path.levels.clock.hatBeta i)^n:=by ring
      _ ≤ _:= h
  have all:= Filter.eventually_all.mpr (fun u:A=>Filter.eventually_all.mpr
    (fun b:A=>Filter.eventually_all.mpr (fun ν:Fin (E+1)=>owned u b ν)))
  filter_upwards [all,growth.eventually_ge_atTop 1] with i hi hp N newer b
  calc
    _ ≤ ∑ _u:A,∑ _ν:Fin (E+1),(R.family.path.levels.clock.hatBeta i)^δ/(1+fee):=
      Finset.sum_le_sum (fun u _=>Finset.sum_le_sum (fun ν _=>hi u b ν N newer))
    _ = fee*((R.family.path.levels.clock.hatBeta i)^δ/(1+fee)):=by
      simp [fee,nsmul_eq_mul];ring
    _ ≤ (1+fee)*((R.family.path.levels.clock.hatBeta i)^δ/(1+fee)):=by
      gcongr;linarith
    _ = _:=by field_simp

include grant in
theorem funded (simple:G.Simple)(o:Loc G 1)(E:ℕ){δ:ℝ}(pos:0<δ):
    ∀ᶠ i:ℕ in atTop,∀ N:ℕ,i<N → ∀ b:Letter (R.family.labels.level d),
    ∀ rentals:Letter (R.family.labels.level d)→Fin (E+1)→ℝ,∀ C:ℝ,0≤C →
    (∀u ν,rentals u ν≤C) →
    ∑ u : Letter (R.family.labels.level d),∑ ν : Fin (E+1),
      |coeff ν.val (Primer.fieldStep R.family a wood depth N i u b)| * rentals u ν ≤
      (R.family.path.levels.clock.hatBeta i)^δ*C:=by
  filter_upwards [original R wood a depth grant simple o E pos] with i hi N newer b rental C paid bound
  calc
    _ ≤ ∑ u : Letter (R.family.labels.level d),∑ ν : Fin (E+1),
         |coeff ν.val (Primer.fieldStep R.family a wood depth N i u b)| * C:=
      Finset.sum_le_sum (fun u _=>Finset.sum_le_sum (fun ν _=>mul_le_mul_of_nonneg_left (bound u ν) (abs_nonneg _)))
    _ = (∑ u : Letter (R.family.labels.level d),∑ ν : Fin (E+1),
         |coeff ν.val (Primer.fieldStep R.family a wood depth N i u b)|)*C:=by simp only [Finset.sum_mul]
    _ ≤ _:=mul_le_mul_of_nonneg_right (hi N newer b) paid

end YM.Integration.WilsonNeutralAnnouncedPrimaryPrice
end
