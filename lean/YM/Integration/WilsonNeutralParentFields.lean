import YM.Integration.WilsonNeutralRevertedPreimages
import YM.Integration.WilsonNeutralAddressedPreimages

/-! Revert the entire sum of the independently placed fine fields in the
measured coupling, retaining every homogeneous angular and scalar term. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralParentFields
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
theorem original (N i:ℕ)(hs:G.Simple)(o:Loc G 1)(live:i < N)(hd:d≤R.family.path.levels.clock.J (i+1))
    (per:ℕ)(b:Letter (R.family.labels.level d))(f:Studio D)(e:ℕ)
    (B:wire G (R.family.side i per)→ℝ)(stamp:ℂ)
    (field:Site (R.family.path.levels.S.block i)→ℂ)
    (received:∀z,field z=stamp*(MvPolynomial.eval B (coeff e
      (canter (bookH (kinetic R wood a N i)) (bookU (kinetic R wood a N i)) (wire G (R.family.side i per))
          (Kemp.banner d (child R wood a depth N i b f z) (R.family.side i per)))):ℝ)):
    (Kemp.aven (R.family.path.levels.S.block i) d:ℂ)*∑z,field z=
      stamp*(MvPolynomial.eval B (coeff e (after R wood a depth N i b f (R.family.side i per))):ℝ):=by
  let n:=R.family.side i per
  let H:=kinetic R wood a N i
  let q (z:Site (R.family.path.levels.S.block i)):=canter (bookH H) (bookU H) (wire G n)
     (Kemp.banner d (child R wood a depth N i b f z) n)
  have joint:=WilsonNeutralRevertedPreimages.original R wood a depth grant N i hs o live hd per b f
  have read:=congrArg (fun P:Pap (wire G n)=>MvPolynomial.eval B (coeff e P)) joint
  try dsimp only at read
  simp only [coeff_C_mul,map_mul,MvPolynomial.eval_C,map_sum] at read
  simp_rw [received]
  rw [←Finset.mul_sum,mul_left_comm]
  congr 1
  exact_mod_cast read

end YM.Integration.WilsonNeutralParentFields
end
