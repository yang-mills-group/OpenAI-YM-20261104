import YM.Integration.WilsonNeutralAddressedPreimages

/-! Exact coupling and field substitution on the complete measured finite-horizon
single letter. All angular ranks, including the scalar, are kept in the
original independently normalized field matrix. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralFiledFieldReversion
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Topology BigOperators Matrix Classical


variable {G:Gauge} {d D:ℕ} (R:Run G) (wood:Primer.Families R.family) (a:hue G)
    (depth:d<D) {U:ℕ→ℕ} (grant:WilsonWindowFormalPurchase.Canonical U R.kit)

def before (N i:ℕ)(b:Letter (R.family.labels.level d))(f:Studio D)(n:Side):Pap (wire G n):=
  let A:=destination R.family.path.levels N i
  let w:=Primer.densityCoeff R.family wood a N (i+1)
  let Y:=Primer.fieldCoeffs R.family a wood depth N (i+1)
  Kemp.banner d (Kemp.quick A (wood i) w (Y b) R.metals.O (R.family.path.levels.blocks i 0).branches
    (Elm.growL R.family.path.levels i) d d f) n

def after (N i:ℕ)(b:Letter (R.family.labels.level d))(f:Studio D)(n:Side):Pap (wire G n):=
  Kemp.banner d ((Roof.larch (Primer.fieldCoeffs R.family a wood depth N i)
    (Primer.fieldStep R.family a wood depth N i)) b f) n

def kinetic (N i:ℕ):Pence:=
  let A:=destination R.family.path.levels N i
  let w:=Primer.densityCoeff R.family wood a N (i+1)
  Roof.epoch a A (wood i) R.family.path.levels.clock.kernel w R.metals.O (R.family.path.levels.blocks i 0).branches

private theorem coefficient_ext {J:Type}[Fintype J]{V W:Pap J}
    (equal:∀ e r,rancho V e r=rancho W e r):V=W:=by
  apply PowerSeries.ext
  intro e
  apply MvPolynomial.ext
  intro u
  have eq:=congrArg (MvPolynomial.coeff u) (congrArg (facade u.degree) (equal e u.degree))
  simpa only [rancho,marble_grade,MvPolynomial.coeff_homogeneousComponent,eq_self,ite_true] using eq

include grant in
/-- Each degree after the one genuine reversal is the native filed lower column
times its actual full fieldStep matrix, including nilpotent and unit rows. -/
theorem original (N i:ℕ)(hs:G.Simple)(o:Loc G 1)(live:i<N)(hd:d≤R.family.path.levels.clock.J (i+1))
    (per:ℕ)(b:Letter (R.family.labels.level d))(f:Studio D):
    let n:=R.family.side i per
    let H:=kinetic R wood a N i
    canter (bookH H) (bookU H) (wire G n) (before R wood a depth N i b f n)=
      after R wood a depth N i b f n := by
  intro n H
  let S:=R.family.path.levels.S
  let A:=destination R.family.path.levels N i
  let K:=R.family.path.levels.clock.kernel
  let m:=WilsonNeutralReceivedCoverLimit.multiplicity S i n
  let F:=fun z:Side=>Reef.floor K A (wood i) z
  let t (z:Side):(primary A.patch K z).Choices:=Classical.arbitrary _
  haveI:NeBot (coverFilter S i n):=coverFilter_neBot R.kit.floor _ _
  apply coefficient_ext
  intro e r
  funext v
  rw [Wine.stamp_book]
  simp only [Wine.stamp,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  change ∑k∈Finset.range (e+1),Wine.bill (bookH H) (bookU H) e k r*rancho (before R wood a depth N i b f n) k r v=_
  have term (k:ℕ):=WilsonNeutralReceivedCoverLimit.original R wood a depth grant N i hs o live hd n F t b f k r v
  have together:=tendsto_finsetSum (s:=Finset.range (e+1))
    (fun k _=>(tendsto_const_nhds (x:=Wine.bill (bookH H) (bookU H) e k r)).mul (term k))
  have filed:= (WilsonNeutralAppointedForestStep.measured R wood a depth grant N i hs o live hd per F t b f e r v).comp
    (WilsonNeutralReceivedCoverLimit.growing S i n)
  exact tendsto_nhds_unique together filed

end YM.Integration.WilsonNeutralFiledFieldReversion
end
