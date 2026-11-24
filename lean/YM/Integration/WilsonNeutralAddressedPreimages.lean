import YM.Integration.WilsonNeutralDisplacedObserved

/-! The finite sum of actual fine predecessors, with the original joint
test evaluated at each residue, reproduces the full unreverted field.
Both limits use one Wilson course, held potential and quiet divisor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonNeutralAddressedPreimages
open FormalBulk08 Matrix Laurent Precision Exterior PowerSeries Lattice RG Wilson Tree Stationary
open Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Filter Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Dawn Wine Rial Roof Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato Next.Foundations
open WilsonRunFormalMarkedStep WilsonNeutralNormalizedForestStep
open FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame Shingle
open scoped Topology BigOperators Matrix Classical


variable {G:Gauge} {d D:ℕ} (R:Run G) (wood:Primer.Families R.family) (a:hue G)
variable (depth:d<D) {U:ℕ→ℕ} (grant:WilsonWindowFormalPurchase.Canonical U R.kit)

def child (run:Run G) (routes:Primer.Families run.family) (col:hue G) (Dfit:d<D)
    (N i:ℕ)(b:Letter (run.family.labels.level d))(f:Studio D)(x:Site (destination run.family.path.levels N i).L):Pot G:=
  let A:=destination run.family.path.levels N i
  let w:=Primer.densityCoeff run.family routes col N (i+1)
  let Y:=Primer.fieldCoeffs run.family col routes Dfit N (i+1)
  let test:=Dawn.throughW x D (Elm.growL run.family.path.levels i) f
  Kemp.braise A (routes i) w (Kemp.work (lift x) (Y b test)) run.metals.O
    (run.family.path.levels.blocks i 0).branches d

theorem finite (N i:ℕ)(n M:Side)(F:Forest (primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel M).ratio)
    (t:(primary (destination R.family.path.levels N i).patch R.family.path.levels.clock.kernel M).Choices)
    (h:wire G M→wire G n)(B:wire G n→ℝ)(b:Letter (R.family.labels.level d))(f:Studio D)(e:ℕ):
    let A:=destination R.family.path.levels N i
    MvPolynomial.eval B (MvPolynomial.rename h (coeff e (WilsonNeutralAppointedForestStep.integral R wood a depth N i M F t b f)))=
      Kemp.aven A.L d * ∑x:Site A.L,MvPolynomial.eval B (MvPolynomial.rename h
        (coeff e (WilsonNeutralDisplacedAngular.reading R wood a depth N i M F t b
          (Dawn.throughW x D (Elm.growL R.family.path.levels i) f) (wrap _ (lift x))))) := by
  intro A
  dsimp only [WilsonNeutralAppointedForestStep.integral,WilsonNeutralDisplacedAngular.reading]
  rw [coeff_C_mul,map_mul,MvPolynomial.rename_C,map_mul,MvPolynomial.eval_C]
  simp only [map_sum]
  rfl

include grant in
theorem original (N i:ℕ)(hs:G.Simple)(o:Loc G 1)(live:i<N)(hd:d≤R.family.path.levels.clock.J (i+1))
    (n:Side)(b:Letter (R.family.labels.level d))(f:Studio D)(e:ℕ)(B:wire G n→ℝ):
    let A:=destination R.family.path.levels N i
    let w:=Primer.densityCoeff R.family wood a N (i+1)
    let Y:=Primer.fieldCoeffs R.family a wood depth N (i+1)
    let pre:=Kemp.quick A (wood i) w (Y b) R.metals.O (R.family.path.levels.blocks i 0).branches
      (Elm.growL R.family.path.levels i) d d
    Kemp.aven A.L d*∑x:Site A.L,MvPolynomial.eval B (coeff e (Kemp.banner d (child R wood a depth N i b f x) n))=
      MvPolynomial.eval B (coeff e (Kemp.banner d (pre f) n)):=by
  intro A w Y pre
  haveI:NeBot (coverFilter R.family.path.levels.S i n):=coverFilter_neBot R.kit.floor _ _
  let m:=WilsonNeutralReceivedCoverLimit.multiplicity R.family.path.levels.S i n
  let K:=R.family.path.levels.clock.kernel
  let F:=fun s:Side=>Reef.floor K A (wood i) s
  let t (s:Side):(primary A.patch K s).Choices:=Classical.arbitrary _
  let f₀ (x:Site A.L):=Dawn.throughW x D (Elm.growL R.family.path.levels i) f
  let read (x:Site A.L)(c:Covers R.family.path.levels.S i n):=MvPolynomial.eval B (MvPolynomial.rename (Shore.tray (m c) n)
    (coeff e (WilsonNeutralDisplacedAngular.reading R wood a depth N i (m c*n) (F _) (t _) b (f₀ x) (wrap _ (lift x)))))
  let value (x:Site A.L):=MvPolynomial.eval B (coeff e (Kemp.banner d (child R wood a depth N i b f x) n))
  have each (x:Site A.L):Tendsto (read x) (coverFilter R.family.path.levels.S i n) (𝓝 (value x)):=
    WilsonNeutralDisplacedObserved.observed R wood a depth grant N i hs o live hd n F t b (f₀ x) x e B
  have joined:=tendsto_finsetSum (s:=Finset.univ) (fun x _=>each x)
  have full:=WilsonNeutralObservedCover.original R wood a depth grant N i hs o live hd n F t b f e B
  apply tendsto_nhds_unique (tendsto_const_nhds.mul joined)
  apply full.congr' _
  exact .of_forall (fun c=>finite R wood a depth N i n (m c*n) (F _) (t _) (Shore.tray (m c) n) B b f e)

end YM.Integration.WilsonNeutralAddressedPreimages
end
