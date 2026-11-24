import YM.Integration.WilsonNeutralFiledFieldReversion
import YM.Integration.WilsonNeutralAddressedPreimages

/-! Revert the entire sum of the independently placed fine fields in the
measured coupling, retaining every homogeneous angular and scalar term. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralRevertedPreimages
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Topology BigOperators Matrix Classical


variable {G:Gauge} {d D:ℕ} (R:Run G) (wood:Primer.Families R.family) (a:hue G)
variable (depth:d<D) {U:ℕ→ℕ} (grant:WilsonWindowFormalPurchase.Canonical U R.kit)


open WilsonNeutralAddressedPreimages (child)
open WilsonNeutralFiledFieldReversion (before after kinetic)

include grant in
theorem at_parent (N i:ℕ)(hs:G.Simple)(o:Loc G 1)(live:i < N)(hd:d≤R.family.path.levels.clock.J (i+1))
    (n:Side)(b:Letter (R.family.labels.level d))(f:Studio D):
    let A:=destination R.family.path.levels N i
    PowerSeries.C (MvPolynomial.C (Kemp.aven A.L d)) *
        ∑ x:Site A.L,Kemp.banner d (child R wood a depth N i b f x) n=
      before R wood a depth N i b f n:=by
  intro A
  ext1 e
  apply MvPolynomial.funext
  intro B
  simp only [coeff_C_mul,map_mul,MvPolynomial.eval_C,map_sum]
  exact WilsonNeutralAddressedPreimages.original R wood a depth grant N i hs o live hd n b f e B

private theorem scalar {V:Type}[Fintype V](H J:Pence)(r:ℝ):
    canter H J V (PowerSeries.C (MvPolynomial.C r))=PowerSeries.C (MvPolynomial.C r):=by
  rw [Wine.canter_C]
  simp

include grant in
theorem original (N i:ℕ)(hs:G.Simple)(o:Loc G 1)(live:i < N)(hd:d≤R.family.path.levels.clock.J (i+1))
    (per:ℕ)(b:Letter (R.family.labels.level d))(f:Studio D):
    let A:=destination R.family.path.levels N i
    let n:=R.family.side i per
    let H:=kinetic R wood a N i
    PowerSeries.C (MvPolynomial.C (Kemp.aven A.L d)) *
        ∑ x:Site A.L,Wine.canter (bookH H) (bookU H) (wire G n)
               (Kemp.banner d (child R wood a depth N i b f x) n)=
      after R wood a depth N i b f n:=by
  intro A n H
  have all:=congrArg (Wine.canter (bookH H) (bookU H) (wire G n))
    (at_parent R wood a depth grant N i hs o live hd n b f)
  refine Eq.trans ?_ (WilsonNeutralFiledFieldReversion.original R wood a depth grant N i hs o live hd per b f)
  simpa only [map_mul,map_sum,scalar] using all

end YM.Integration.WilsonNeutralRevertedPreimages
end
