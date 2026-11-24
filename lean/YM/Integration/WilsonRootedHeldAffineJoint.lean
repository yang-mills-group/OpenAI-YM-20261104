import YM.Integration.WilsonRootedHeldAffineDeposit
import YM.Integration.WilsonRootedHeldAffineExponent
import YM.Integration.WilsonPhysicalHistoryRetainedSpringRosterFiled

/-! Original Haar–Gaussian joint integration of the previous filed site,
    against the unaltered signed vertices of this same physical sector. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedHeldAffineJoint
open Function Lattice Wilson RG Tree Pressure Finset Filter MeasureTheory
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ConnectedActivityE6 Coat Blaze Matter Greenbelt
open RG.Supply RG.Shoot Input Org Push Push.PriceCompiler Precision SectorMeasure Oriented
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Physical
open WilsonLimitConstruction OriginalMarkedRunAction WilsonRootedHeldAffineDeposit
open scoped Topology BigOperators Classical
variable {G:Gauge}

private theorem integrate {Ω:Type} [MeasurableSpace Ω] (ν:Measure Ω)(W E:Ω→ℝ)(f:Ω→ℂ)
    {M b B:ℝ}(m:Measurable f)(fbound:∀u,‖f u‖≤M)(inW:Integrable W ν)(e:Measurable E)
    (ebound:∀u,|E u|≤b)(m0:0≤M)(b0:0≤b)(bill:∫u,‖W u‖ ∂ν≤B):
    let Q:=fun u=>f u*(E u:ℂ)*(W u:ℂ)
    Integrable Q ν ∧ (∫u,‖Q u‖ ∂ν)≤M*b*B:=by
  intro Q
  have qMeas:AEStronglyMeasurable Q ν:=(m.aestronglyMeasurable.mul
    (Complex.continuous_ofReal.measurable.comp e).aestronglyMeasurable).mul
    (Complex.continuous_ofReal.comp_aestronglyMeasurable inW.aestronglyMeasurable)
  have qle(u):‖Q u‖≤(M*b)*‖W u‖:=by
    simp only [Q,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (fbound u) (ebound u) (abs_nonneg _) m0) (abs_nonneg _)
  have hp:Integrable Q ν:=(inW.norm.const_mul (M*b)).mono' qMeas (Eventually.of_forall qle)
  refine ⟨hp,(integral_mono hp.norm (inW.norm.const_mul (M*b)) qle).trans ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left bill (mul_nonneg m0 b0)

variable (R:Run G){N per m:ℕ}(P:FundedCensusVacuum.Station R N per m)
local notation "A₀" => R.alloy.B.a
local notation "Sₘ" => R.alloy.B.a.clock.op m per
local notation "Tₘ" => Pressure.Testing.ships R.alloy.B N m per
local notation "J₁" => R.alloy.B.a.clock.J (m+1)
local notation "J₀" => R.alloy.B.a.clock.J m
local notation "xₘ" => R.alloy.B.a.clock.hatBeta m
local notation "oₘ" => R.kit.shape.o J₁ J₀
local notation "Y₁" => R.family.path.rep N per (m+1)
local notation "Qₘ" => R.kit.target J₁ J₀
local notation "Wₘ" => R.kit.walls J₁ J₀

/-- All temperatures, actions, primed Haar ratios and support prices are the
    same as those of the enrolled physical program. The test may couple every
    held compact link and every Gaussian coordinate. -/
theorem original (paid:WilsonRootedHeldAffineWallet.Eligible R.kit)(χ:Chi)
    (V:Config G (R.family.side m per)) (p:Molecule Sₘ) (i:Greenbelt.Reserve Sₘ)(tag:(Sₘ).Choices)
    (Z:SeriesA G){σ D:ℝ}(hs:0<σ)(draw:Draw Z σ D)(a:PrismA G)(ha:a∈Z)(x:Site (R.family.side (m+1) per))
    (through:ℕ)(l:Finset ℕ)(test:(Greenbelt.allot i).Slice G×Air (R.family.side (m+1) per) G→ℂ)
    {M:ℝ}(m0:0≤M)(meas:Measurable test)(testM:∀u,‖test u‖≤M):
    let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
    let ratio:=finitePitch R N (m+1) through g
    let X:=(planted (Greenbelt.prism Tₘ xₘ χ (oₘ).K V (allot i)) p).taggedL tag
    let ν:=((allot i).order G).prod X.dice
    let err:=exchange X a x (Y₁).beta g ratio
    let fee:=|siteWeight a g ratio| *(D*WilsonRootedHeldPacketGerm.tariff G (a.rise+2) 1 σ)*
      (betaF G xₘ (R.rolls.L J₁))^(-(J₀:ℝ))
    let Q:=fun u=>test u*(err u:ℂ)*(X.body Y₁ (Qₘ).table Wₘ (oₘ).a l (Qₘ).halo p u:ℂ)
    Integrable Q ν ∧ (∫u,‖Q u‖ ∂ν)≤M*fee*∏k∈p,P.guide.text k:=by
  intro g ratio X ν err fee Q
  have aDraw:=draw.2 a ha
  have manifest:X.manifest:=planted_valid _ _
  have trueE:Measurable err:=measured X P.guide.laws.data.access P.guide.laws.data.funds.funds a aDraw hs x _ g ratio
  have tnn:0≤D*WilsonRootedHeldPacketGerm.tariff G (a.rise+2) 1 σ:=
    (WilsonRootedHeldPacketGerm.directions X a aDraw hs 1 x 1 0).nonneg
  have eBound (u:(allot i).Slice G×Air (R.family.side (m+1) per) G):|err u|≤fee:=by
    apply (compared X a aDraw hs x _ g ratio u).trans
    exact mul_le_mul_of_nonneg_left
      (WilsonRootedHeldAffineStation.original R P paid χ V p i tag u.1).2.2 (mul_nonneg (abs_nonneg _) tnn)
  have e0:0≤fee:=(abs_nonneg _).trans (eBound (1,0))
  exact integrate ν _ err test meas testM (P.guide.integrated X rfl rfl manifest l p) trueE eBound m0 e0
    (P.guide.statements X rfl rfl manifest l p)

end YM.Integration.WilsonRootedHeldAffineJoint
