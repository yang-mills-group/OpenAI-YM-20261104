import YM.Integration.WilsonNeutralSourceParity
import YM.Push.STRESS_FLUX.Low
/-! For a simple gauge group the full low physical label space consists
of a scalar and curvature bilinears. On this whole space the first
coupling coefficient of the independently received program is zero. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralBilinearTransfer
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open scoped Topology BigOperators Matrix Classical

variable {G : Gauge} (R : Run G) {d D : ℕ} (wood : Primer.Families R.family)
variable (a : hue G) (depth : d < D) {U : ℕ → ℕ}
variable (grant : WilsonWindowFormalPurchase.Canonical U R.kit)

private theorem reflect_monomial (J:Labels.Jet G)(v:Labels.Key G→₀ℕ)(c:ℂ):
    Labels.read (-J) (MvPolynomial.monomial v c)=
      (-1:ℂ)^(v.sum fun _ n=>n)*Labels.read J (MvPolynomial.monomial v c):=by
  have flip (u:Labels.Key G):Labels.coord (-J) u=(-1:ℂ)*Labels.coord J u:=by
    simp [Labels.coord]
  simp only [Labels.read,MvPolynomial.aeval_monomial,flip,Finsupp.prod,Finsupp.sum,mul_pow,
    Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  ring

private theorem reflected {p:Labels.Label G d}{m:ℕ×ℕ}(hp:p∈Labels.Grade m)(J:Labels.Jet G):
    Labels.read (-J) p.val=(-1:ℂ)^m.2*Labels.read J p.val:=by
  have terms : ∀ v∈p.val.support,
      Labels.read (-J) (MvPolynomial.monomial v (MvPolynomial.coeff v p.val)) =
      (-1:ℂ)^m.2 * Labels.read J (MvPolynomial.monomial v (MvPolynomial.coeff v p.val)):=by
    intro v hv
    have grade:=(Labels.pure_grade m p).1 hp (MvPolynomial.mem_support_iff.mp hv)
    rw [Labels.weight_slot] at grade
    have total : (v.sum fun _ n=>n)=m.2:=congrArg Prod.snd grade
    rw [reflect_monomial,total]
  conv_lhs => rw [p.val.as_sum,map_sum]
  conv_rhs => rw [p.val.as_sum,map_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl terms

theorem even_slots (simple:G.Simple)(low:d≤5)(F:Frame G d)(x:Letter F):
    (Pose.slots F x)%2=0:=by
  let i:=mint F x
  let v:= F.basis i
  obtain ⟨A,sym,_,actual⟩:=StressFlux.low low v
  have vanish:=StressFlux.Low.linear_invariant simple (StressFlux.Low.covariance sym actual)
  by_contra odd
  have odd':(F.grades i).2%2=1:=by change (Pose.slots F x)%2=1;omega
  apply F.basis.ne_zero i
  apply Subtype.ext
  apply Labels.eval_ext
  intro J
  have e:=reflected (F.pure i) J
  have eq:Labels.read (-J) v.val=Labels.read J v.val:=by
    simp only [actual,StressFlux.Low.eval,vanish,LinearMap.zero_apply,Pi.neg_apply,map_neg,
      LinearMap.neg_apply,neg_neg,neg_zero]
  rw [(Nat.odd_iff.mpr odd').neg_one_pow,←eq] at e
  change Labels.read J v.val=0
  rw [←eq]
  linear_combination (1/2:ℂ)* e

include grant in
theorem original (N i:ℕ)(simple:G.Simple)(o:Loc G 1)(hi:i<N)
    (front:d≤R.family.path.levels.clock.J (i+1))(low:d≤5)
    (x y:Letter (R.family.labels.level d)):
    coeff 1 (Primer.fieldStep R.family a wood depth N i x y)=0:=
  WilsonNeutralSourceParity.first R wood a depth grant N i simple o hi front x y
    ((even_slots simple low _ x).trans (even_slots simple low _ y).symm)

end YM.Integration.WilsonNeutralBilinearTransfer
end
