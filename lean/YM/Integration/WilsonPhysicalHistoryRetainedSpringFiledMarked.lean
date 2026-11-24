import YM.Integration.WilsonPhysicalHistoryRetainedSpringFiledJoint
import YM.Integration.WilsonPhysicalHistoryRetainedSpringFundedMarked

/-! A single regulated period list gives the chamber estimate for both
bounded and moment-controlled marked cofactors without refiling a source. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open LocalComparison Marker Global FullQLocal Comparison.RG02 Comparison.RG02.Assembly
open IterationFour IterationFour.Vacuum
open Function Filter Finset Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree MeasureTheory
open ConnectedActivityE6 ConnectedActivityE6.Coat
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure
open Bloch Laurent RG.Supply Extra.Histories GapsLocal.Renew
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Opera
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Physical WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Bank.Bloom WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open WilsonCoeffUV.Fk Next.Foundations WilsonLimitConstruction WilsonStartup PowerSeries
open scoped Topology BigOperators Classical
variable {G : Gauge}

theorem cofinal_filed_marked (R : Run G) (simple : G.Simple) (held : WilsonFundedWindowCompany.PhysicalInputs R.kit)
    (mark : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (checkoutPrice : Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay) (d : ℕ)
    (v : ℕ→Gear G→ℝ) (rows : FundedMarkedCoverRows.prices v R.kit)
    (paths : FundedOriginalVacuumPaths.prices R.kit) (e vertices order : ℕ) {ε η : ℝ} (ep : 0<ε) (hp : 0<η) :
    ∃ credit : Credit, ∀ᶠ m : ℕ in atTop,
      let V:=R.family.path.levels
      ∃ σ : ℝ, 0<σ ∧ σ⁻¹≤zz V (m+1) ∧ ∀ N : ℕ, (later : m+1<N) →
      let C:=credit.buy (zz V (m+1))+zz V (m+1)*V.clock.loopCap (m+1)
      let K:=R.alloy.B.kin.path N (m+1)
      let B:=(V.params (m+1)).clip
      ∃ Z : SeriesA G, (∀ a∈Z,3≤a.grade) ∧ fromBefore Z (3+e) ∧ Z.length ≤ meterPre (3+e) ∧
        Draw Z σ C ∧ RunFundedPeriodAction.PeriodData Z (2+e) σ C ∧
        (∀ k<3+e,∀ n : Side,∀ l,Blue.mix (pace (pitch V R.metals.O N (m+1)))
          (front K B n+sands Z n) k (l+1)=lagoon (freshet V R.metals.O N (m+1) k (l+1)) n) ∧
        JointEstimate R m N Z (2+e) vertices order ε η ∧
        MarkedJointEstimate R m N Z (2+e) vertices order ε η ∧
        ∀ n : ℕ,
        let A:=R.alloy.B.a
        let k:=A.clock.J (m+1)
        let j:=A.clock.J m
        let P:=R.family.path.rep N n (m+1)
        let Q:=approximation R (p:=n) later d
        let δ:=(Real.sqrt 2*Pert.Asymptotics.regulatorRun R.family N n (m+2))^(d+1)
        let S:=A.clock.op m n
        let T:=Pressure.Testing.ships R.alloy.B N m n
        let D:=R.kit.target k j
        let W:=R.kit.walls k j
        let a:=(R.kit.shape.o k j).a
        ∃ (H : Guide R.alloy.B R.kit.shape N m n P) (b : ℕ→ℝ),
        (∀ w,SumBudget (fun i=>if (P.activities.reg i).site=w then P.p.mass (P.activities.reg i).support (b i) else 0) δ) ∧
        ∀ {F : Forest S.ratio} (X : Coat T F), X.x=A.clock.hatBeta m → X.width=(R.kit.shape.o k j).K → X.manifest →
        ∀ (x : Site (R.family.side (m+1) n)) (l : Finset ℕ) (p : Molecule S)
          (f : F.Slice G × Air (R.family.side (m+1) n) G→ℂ),
          Measurable f → ∀ M : ℝ, 0≤M → (∀ t,‖f t‖≤M) →
          let g:=Pert.Asymptotics.regulatorRun R.family N n (m+1)
          let obs:=fun t : F.Slice G × Air (R.family.side (m+1) n) G=>
            f t*(springAt R N n (m+1) (2+e) Z g x
              ((X.wrapY t.1).input ((X.wrapY t.1).liftA P.beta t.2)):ℂ)
          let err:=fun w : Head S=>(5/2:ℝ)*regularFee S b w
          let ν:=(F.order G).prod X.dice
          ‖(∫ t,obs t*(X.body P D.table W a l D.halo p t:ℂ) ∂ν)-
             ∫ t,obs t*(X.body Q D.table W a l D.halo p t:ℂ) ∂ν‖ ≤
            (M*springSiteBill R N (m+1) (2+e) Z g C)*
              (H.alarms^(blaze p).card*insertedCost (fun w=>H.fair w+err w) err p.toList) := by
  obtain ⟨credit,financial⟩:=cofinal_filed_joint R simple held mark checkoutPrice d v rows paths e vertices order ep hp
  refine ⟨credit,?_⟩
  filter_upwards [financial,funded_marked R simple v rows credit (3+e) (2+e) vertices order ep hp]
    with m before paid
  obtain ⟨σ,hs,clock,offer⟩:=before
  refine ⟨σ,hs,clock,?_⟩
  intro N later C K B
  obtain ⟨Z,grades,origin,length,draw,period,correct,bounded,measured⟩:=offer N later
  exact ⟨Z,grades,origin,length,draw,period,correct,bounded,
    paid N later σ hs clock Z draw (fun a ha=>(origin a ha).le),measured⟩

end YM.Integration.OriginalMarkedRunAction
