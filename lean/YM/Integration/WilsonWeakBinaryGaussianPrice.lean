import YM.Integration.WilsonWeakBinaryGaussian
import YM.Integration.WilsonReceivedOrdinaryPanel
import YM.Integration.WilsonOriginalPointCompactSalary

/-! Ordinary Wilson moments on the same enrolled post as the independently registered finite Gaussian. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonWeakBinaryGaussianPrice
open Filter Finset Multi Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Order
open Extra.Trajectories ConnectedActivityE6 WilsonIndependentOrdinaryPairGrade
open scoped Classical BigOperators Topology

open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary QuadraticLocal.Affinity
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision Tree Exterior PhysicalNext.Repeat.Legato
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada FVA1Physical.TwoReset
open WilsonVacuumPreResetStationaryChange WilsonOriginalPrimerReplicatedInk PhysicalForestMarkedRay PhysicalForestRay
open FreeResolvent WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonOriginalPointCompactRoster WilsonOriginalThreeCopiedCharts
open scoped Classical BigOperators ContDiff Topology
open LocalComparison Comparison.RG02.Cumulants Comparison.RG02.Assembly Order AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalThreePurchasedRays (prescribed)
attribute [local instance] Gauge.frobInner

local notation "J" => Stock.census (Fin 3)

theorem charts {G:Gauge}{n:Side}{ι₀ ι₁:Type}{p₀ p₁:Passport n (Fin 3)}
    {actors:Fin 3 → Set ℂ}{M₀:ι₀ → Row p₀ (J) G (Wallet actors)}{M₁:ι₁ → Row p₁ (J) G (Wallet actors)}
    (same:p₀=p₁)(names:ι₀=ι₁)(word:HEq M₀ M₁)(grades:Fin 3 → ℕ)(L:Layout G)(tape:Finset Age)
    (x:Wallet actors):
    Air.craft M₀ (fun j=>(M₀ j).paint x) grades L tape=Air.craft M₁ (fun j=>(M₁ j).paint x) grades L tape:=by
  subst p₁
  subst ι₁
  cases eq_of_heq word
  rfl

theorem original {G : Gauge} (R : Run G) (simple : G.Simple)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ → ℕ)
    (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b → 
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
    (grades : Fin 3 → ℕ) (q depth order shelf k slots : ℕ)
    (deep : 2*(q+1)+8 ≤ order) (aged : q+4 ≤ 3*k+2) (H cap : ℝ) (hc : 0 ≤ cap) {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ i : ℕ in atTop,
    ∀ {m N per : ℕ} (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
      (_fit : k ≤ R.alloy.B.a.clock.J i) (Q : D.Tab R.rolls)
      (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
      (_course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
      (books : Mentor.Offices.Books D R.rolls Q φ) (law : VowsR.LawScroll G φ)
      (_enrolled : VowsR.Chamber law R.kit D Q books) (_fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
      (hi : m ≤ i) (cut : i < N)

      (ahead:Mentor.Forecast D R.rolls Q φ books) {I:Type} [Fintype I] {σ:ℝ}
      (owner:I → Fin 3)(sites:Fin 3 → Site (fine R i per))
      (T:(l:I) → WilsonOlderFreshGraphSlate.Copy G (grades (owner l)) order σ)
      (actors:Fin 3 → Set ℂ)(charge:I → ℂ)
      (_bounded:∀v (a:ℂ),a∈actors v → ‖a‖ ≤ 1)(_hs:0<σ)
      (_enoughSeats:3 ≤ slots)(_allow:(∑v:Fin 3,grades v) ≤ shelf)
      (physical:Wallet actors → Config G (R.family.side (i+1) per) → Poly (J))
      (P:WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors
          (fun _=>(⊥:Submodule ℝ ℂ)) grades order shelf slots i hi physical)
      (_passport:P.passport=Passport.point sites)(_index:P.modelIndex=Index owner grades T)
      (_matches:HEq P.model (rows owner grades sites T actors charge))
      (Z:I → (m:Side) → Site m → PChart G m)
      (_shell:∀l n y,shellK (grades (owner l)) (Z l n y))(_pure:∀l n y j,Pure (Z l n y j))
      (_matched:∀l,WilsonOriginalPrimerStampedRay.Matched (T l) (Z l))
      {quiet:ℕ → SeriesA G}{τ cash:ℝ}
      (_realQuiet:Read R N m (Burn.horizon k) quiet π Γ)
      (_legal:Legal (Step.tape (Burn.horizon k+2)) (π (i+1)))
      (_posted:Issued R N (i+1) (Burn.horizon k) (quiet (i+1)) τ cash)
      (_visible:order ≤ Burn.horizon k+2)
      (x:Wallet actors)(b:Stationary.Link G (R.family.side i per)),
      let g:=Coat.gStep (R.family.path.rep N per (i+1)).beta
      let room:=R.family.path.levels.budget i
      let angle:=Stationary.arm G (R.family.side i per) 1 b
      ∀ z:ℝ, |z| ≤ |H| *(Real.log (R.family.path.levels.clock.hatBeta i))^depth*((room.B:ℝ)^2*room.threshold)/g → 
        (∀e,‖Exterior.collect G angle e‖ ≤ cap*|z|) → 
        let U:=Integral.sample g angle
        flags (Ψ i).p.threshold U=∅ → 
        ∀ (F:Forest (step R i per).ratio)(tag:(step R i per).Choices),
        let Z₀:=fun ξ=>WilsonOriginalThreeGaussianIncome.value owner sites actors charge R N i per cut F
          (dvd_refl _) x Z angle ξ order
        let Q₀:=(model R N i per cut).covariance F tag
        let W:=WilsonOriginalGaussianPaidTable.table (Board (J) order) Q₀ Z₀
        let Y:=(((Ψ i).eval U:ℂ)⁻¹) • LocalComparison.actualPush R.family N per i (physical x) U
        let E:=(8*(budgetR R i)^slots)*P.rent+ε*g^q
        (∀s,MeasureTheory.Integrable (WilsonOriginalGaussianPaidTable.presented (Board (J) order) Z₀ s) (Gaussian.cloud Q₀)) ∧
        ∀(s:(J).Mode)(u:ℕ),s.val.card+u ≤ order+1 → 
          Poly.toll P.w s * ‖Y.part s-(Order.value (g:ℂ) (Order.ratio W)).part s‖ ≤ 
            (∑h∈shards (J) s,(h.val.card:ℝ)*E*(g⁻¹+E)^h.val.card)+g^u*(shards (J) s).card := by
  filter_upwards [WilsonReceivedOrdinaryPanel.original R simple D φ width grades q depth order shelf k
    slots deep aged H cap hc ep] with i ready
  intro m N per hk fit Q π Γ Ψ course books law enrolled fund hi cut ahead I instI σ owner sites T actors charge
    bounded hs enoughSeats allow physical P passport index same Z shell pure matched quiet τ cash realQuiet legal posted visible
    x b g room angle z hz inside U healthy F tag Z₀ Q₀ W Y E
  have physicalPrice:=ready hk fit Q π Γ Ψ course books law enrolled fund hi cut ahead actors
    (fun _=>(⊥:Submodule ℝ ℂ)) physical P x b z hz inside healthy F tag
  have book:=WilsonOriginalPointCompactSalary.stocks owner grades sites T actors charge hs.le P.w
    P.salary.positive bounded order slots shelf le_rfl enoughSeats allow
  obtain ⟨ratioEq,_,integrable⟩:=WilsonWeakBinaryGaussian.original R N i per cut F tag owner grades sites T
    actors charge x Z book hs hs bounded legal shell pure matched realQuiet hi posted b order le_rfl visible
  have filed:=charts passport index same grades (π (i+1)) (Step.tape (Burn.horizon k+2)) x
  refine ⟨integrable,?_⟩
  intro s u kept
  have priced:=physicalPrice s u kept
  rw [filed] at priced
  rw [←ratioEq]
  exact priced

end YM.Integration.WilsonWeakBinaryGaussianPrice
end
