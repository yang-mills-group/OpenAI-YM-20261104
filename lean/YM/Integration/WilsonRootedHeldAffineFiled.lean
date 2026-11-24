import YM.Integration.WilsonRootedHeldAffineRate

/-! Actual previous independent deposits on the original running torus.
    The nonflat variable, complete hard exterior and tested correlation are
    chosen only after the shared date and the previous path width. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedHeldAffineFiled
open Filter Lattice Wilson RG Tree Pressure Finset MeasureTheory
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ConnectedActivityE6 Coat Blaze Matter Greenbelt
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open Push Push.PriceCompiler Precision SectorMeasure Oriented
open RG.Supply RG.Shoot Input Org GapsLocal.Renew
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Physical WilsonLimitConstruction OriginalMarkedRunAction WilsonRootedHeldAffineDeposit
open scoped Topology BigOperators Classical
variable {G:Gauge}

def Tested (R:Run G)(m N through q:ℕ)(ε:ℝ)(Z:SeriesA G):Prop:=
  ∀per:ℕ,∀P:FundedCensusVacuum.Station R N per m,let A:=R.alloy.B.a;let S:=A.clock.op m per
    let T:=Pressure.Testing.ships R.alloy.B N m per;let k:=A.clock.J (m+1);let j:=A.clock.J m
    let Q:=R.kit.target k j;let o:=R.kit.shape.o k j;let Y:=R.family.path.rep N per (m+1)
    let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
    ∀(χ:Chi)(V:Config G (R.family.side m per))(p:Molecule S)(i:Greenbelt.Reserve S)(tag:S.Choices)
      (a:PrismA G),a∈Z→∀(x:Site (R.family.side (m+1) per))(l:Finset ℕ)
      (f:(allot i).Slice G×Air (R.family.side (m+1) per) G→ℂ),Measurable f→∀M:ℝ,0≤M→(∀u,‖f u‖≤M)→
      let X:=(planted (Greenbelt.prism T (A.clock.hatBeta m) χ o.K V (allot i)) p).taggedL tag
      let ν:=((allot i).order G).prod X.dice
      let err:=exchange X a x Y.beta g (finitePitch R N (m+1) through g)
      let value:=fun u=>f u*(err u:ℂ)*(X.body Y Q.table (R.kit.walls k j) o.a l Q.halo p u:ℂ)
      Integrable value ν ∧ (∫u,‖value u‖ ∂ν)≤M*(ε*g^q)*∏b∈p,P.guide.text b

theorem original (R:Run G)(simple:G.Simple)(before:WilsonRootedHeldAffineWallet.Eligible R.kit)
    (slow:WilsonWindowReportingPace.Slow R.kit)(held:WilsonFundedWindowCompany.PhysicalInputs R.kit)
    (mark:Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (cash:Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay)(d:ℕ)(v:ℕ→Gear G→ℝ)
    (rows:FundedMarkedCoverRows.prices v R.kit)(paths:FundedOriginalVacuumPaths.prices R.kit)(e q:ℕ)
    {ε:ℝ}(ep:0<ε):
    ∃credit:Credit,∀ᶠm:ℕ in atTop,let V:=R.family.path.levels
      ∃σ:ℝ,0<σ ∧ σ⁻¹≤ zz V (m+1) ∧ ∀N:ℕ,m+1<N→
      let D:=credit.buy (zz V (m+1))+zz V (m+1)*V.clock.loopCap (m+1)
      ∃Z:SeriesA G,(∀a∈Z,3≤a.grade) ∧ fromBefore Z (3+e) ∧ Z.length≤ meterPre (3+e) ∧
      Draw Z σ D ∧ RunFundedPeriodAction.PeriodData Z (2+e) σ D ∧
        (∀ k<3+e,∀ n:Side,∀l,Blue.mix (pace (pitch V R.metals.O N (m+1)))
          (front (R.alloy.B.kin.path N (m+1)) (V.params (m+1)).clip n+sands Z n) k (l+1)=
            lagoon (freshet V R.metals.O N (m+1) k (l+1)) n) ∧ Tested R m N (2+e) q ε Z:=by
  obtain ⟨C,record⟩:=cofinal_filed_roster R simple slow held mark cash d v rows paths e 1 q ep (η:=1) zero_lt_one
  refine ⟨C,?_⟩
  filter_upwards [record,WilsonRootedHeldAffineRate.original R simple C v rows (2+e) (3+e) q ep] with m old fiscal
  intro V
  obtain ⟨σ,sp,width,earned⟩:=old
  refine ⟨σ,sp,width,?_⟩
  intro N later D
  obtain ⟨Z,grade,previous,len,draw,received,genuine,-⟩:=earned N later
  refine ⟨Z,grade,previous,len,draw,received,genuine,?_⟩
  intro per P A S T k j Q o Y g χ V p i tag a ha x l f mf M Mp hb X ν err value
  have amount:=fiscal N per later σ sp width Z draw a ha (previous a ha).le
  obtain ⟨ok,price⟩:=WilsonRootedHeldAffineJoint.original R P before χ V p i tag Z sp draw a ha x (2+e) l f Mp mf hb
  exact ⟨ok,price.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left amount Mp)
    (Finset.prod_nonneg fun _ _=>P.guide.positive _))⟩

end YM.Integration.WilsonRootedHeldAffineFiled
