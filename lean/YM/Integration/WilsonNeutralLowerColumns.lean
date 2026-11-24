import YM.Integration.WilsonNeutralFiledFieldReversion

/-! The receiving signed matrix on its full normalized finite Wilson field
bank, with each numerical coefficient and Laurent lag kept separately. The
same proof reads the lower field at the common cap or its native slot count. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralLowerColumns
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep WilsonNeutralFiledFieldReversion
open scoped Topology BigOperators Matrix Classical
variable {G : Gauge} (R : Run G) {d D : ℕ} (wood : Primer.Families R.family)
variable (a : hue G) (depth : d < D) {U : ℕ → ℕ}
variable (grant : WilsonWindowFormalPurchase.Canonical U R.kit)

include grant in
private theorem forms (N i:ℕ)(simple : G.Simple)(o : Loc G 1)(hi:i≤N)
    (front:d≤R.family.path.levels.clock.J (i+1))(u:Letter (R.family.labels.level d)):
    Wade o (Primer.fieldCoeffs R.family a wood depth N i u) (Pose.slots (R.family.labels.level d) u):=by
  rw [←WilsonNeutralAppointedForestStep.column R wood a depth grant]
  exact ((WilsonRunFormalMarkedStep.normalized R wood a depth simple o N i hi front).officers u).fare

include grant in
theorem assembled (N i:ℕ)(simple:G.Simple)(o:Loc G 1)(hi:i≤N)
    (front:d≤R.family.path.levels.clock.J (i+1))(n:Side)
    (b:Letter (R.family.labels.level d))(f:Studio D):
    after R wood a depth N i b f n =
    ∑ u:Letter (R.family.labels.level d),
      Wine.worm (wire G n) (Primer.fieldStep R.family a wood depth N i u b) *
      Kemp.banner d (Primer.fieldCoeffs R.family a wood depth N i u f) n:=by
  let Y:=Primer.fieldCoeffs R.family a wood depth N i
  let S:=Primer.fieldStep R.family a wood depth N i
  have H (u:Letter (R.family.labels.level d)) : Wade o (Y u) d :=
    (forms R wood a depth grant N i simple o hi front u).through (Pose.slotsFits _ u)
  calc
    _ = ∑ u: Letter (R.family.labels.level d),Kemp.banner d ((launch (S u b) (Y u)) f) n :=
      (Rial.flags_sum Finset.univ (fun u=>launch (S u b) (Y u)) o
        (fun u _=> (H u).launch (S u b)) f n).2
    _ = _ := Finset.sum_congr rfl fun u _=> Kemp.banner_mul (H u) f (S u b) n

include grant in
theorem original (N i:ℕ)(simple:G.Simple)(o:Loc G 1)(hi:i≤N)
    (front:d≤R.family.path.levels.clock.J (i+1))(n:Side)
    (b:Letter (R.family.labels.level d))(f:Studio D)(e:ℕ)(B:wire G n→ℝ):
    MvPolynomial.eval B (coeff e (after R wood a depth N i b f n)) =
      ∑ u:Letter (R.family.labels.level d), ∑ v ∈ (_root_.Finset.HasAntidiagonal.antidiagonal e : Finset (ℕ×ℕ)),
        coeff v.1 (Primer.fieldStep R.family a wood depth N i u b) *
        MvPolynomial.eval B (coeff v.2 (Kemp.banner d (Primer.fieldCoeffs R.family a wood depth N i u f) n)):=by
  rw [assembled R wood a depth grant N i simple o hi front n b f]
  simp only [map_sum,PowerSeries.coeff_mul,Wine.worm,PowerSeries.coeff_map,map_mul,MvPolynomial.eval_C]

include grant in
theorem native (N i:ℕ)(simple:G.Simple)(o:Loc G 1)(hi:i≤N)
    (front:d≤R.family.path.levels.clock.J (i+1))(n:Side)
    (b:Letter (R.family.labels.level d))(f:Studio D)(e:ℕ)(B:wire G n→ℝ):
    MvPolynomial.eval B (coeff e (after R wood a depth N i b f n)) =
      ∑ u:Letter (R.family.labels.level d), ∑ v ∈ (_root_.Finset.HasAntidiagonal.antidiagonal e : Finset (ℕ×ℕ)),
        coeff v.1 (Primer.fieldStep R.family a wood depth N i u b) *
        MvPolynomial.eval B (coeff v.2 (Kemp.banner (Pose.slots (R.family.labels.level d) u)
          (Primer.fieldCoeffs R.family a wood depth N i u f) n)):=by
  rw [original R wood a depth grant N i simple o hi front n b f e B]
  refine Finset.sum_congr rfl fun u _=> Finset.sum_congr rfl fun v _=> ?_
  have h:=Pose.slotsFits (R.family.labels.level d) u
  have same:=Kemp.sail (Primer.fieldCoeffs R.family a wood depth N i u f)
    (Pose.slots _ u) ((forms R wood a depth grant N i simple o hi front u).1 f) v.2 (d-Pose.slots _ u) n
  rw [Nat.add_sub_of_le h] at same
  rw [same]

end YM.Integration.WilsonNeutralLowerColumns
end
