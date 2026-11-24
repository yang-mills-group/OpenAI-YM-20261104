import YM.Integration.WilsonPhysicalHistoryRetainedSpringRankFiled
import YM.Integration.WilsonRegisteredFiledOccurrence
/-! A single original nonbare filing pays the signed complete action insertion
before the period, both reporting fields, all three sites and the lower sample. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonRegisteredFiledInvoice
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
open OriginalMarkedRunAction WilsonInvariantActionPriorHearing WilsonInvariantActionRegisteredHearing
variable {G : Gauge}

def Invoice (R : Run G) (m N r : ℕ) (Z : SeriesA G) (c : ℝ) : Prop :=
  ∀ per, ∀ (interior : m+1<N),
    let g := Pert.Asymptotics.regulatorRun R.family N per (m+1)
    let P := R.family.path.rep N per (m+1)
    let live : m<N := Nat.lt_trans (Nat.lt_succ_self m) interior
    ∀ x : Site (R.family.side (m+1) per),
      ∃ W : readings (Config G (R.family.side m per) × Config G (R.family.side (m+1) per)),
        (∀ q, W.val q = -springAt R N per (m+1) r Z g x q.2 ∧
          ‖W.val q‖ ≤ springSiteBill R N (m+1) r Z g c ∧
          HasDerivAt (fun t : ℝ => Real.exp (P.exponent q.2)*P.activities.gas P.p q.2*
            (1-t*springAt R N per (m+1) r Z g x q.2)) (P.eval q.2*W.val q) 0) ∧
        ∀ (birth : R.family.ref 4 ≤ m+1) (v w : R.family.label 4)
          (o z : Site (R.family.side (m+1) per)) (η χ : ℂ→L[ℝ]ℝ),
          let A := filed R live birth v o η
          let B := filed R live birth w z χ
          HasDerivAt (fun t : ℝ => covariance (reweighted (joint R (p:=per) live) W t) A B)
            (receipts R live A B W) 0

theorem issued (R : Run G) (m N r : ℕ) (Z : SeriesA G) {σ c : ℝ} (hs : 0<σ)
    (draw : Draw Z σ c) : Invoice R m N r Z c := by
  intro per interior g P live x
  let W := WilsonRegisteredFiledOccurrence.vertex R interior r Z hs draw g x
  refine ⟨W, ?_, ?_⟩
  · intro q
    have info := WilsonRegisteredFiledOccurrence.density R interior r Z hs draw g x q
    exact ⟨rfl, info.2.2, info.1⟩
  · intro birth v w o z η χ
    exact WilsonRegisteredFiledOccurrence.original R interior birth v w o z x η χ r Z hs draw g

theorem purchased (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (held : WilsonFundedWindowCompany.PhysicalInputs R.kit)
    (mark : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (checkoutPrice : Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay) (d : ℕ)
    (v : ℕ→Gear G→ℝ) (rows : FundedMarkedCoverRows.prices v R.kit)
    (paths : FundedOriginalVacuumPaths.prices R.kit) (e vertices order load : ℕ) {ε η : ℝ} (ep : 0<ε) (hp : 0<η) :
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
        RootedSpringBounds R m N Z (2+e) (3+e) load order ε η ∧
        Invoice R m N (2+e) Z C := by
  obtain ⟨credit, late⟩ := cofinal_filed_spring_polynomials R simple slow held mark checkoutPrice d
    v rows paths e vertices order load ep hp
  refine ⟨credit, ?_⟩
  filter_upwards [late] with m stage
  obtain ⟨σ, hs, width, allN⟩ := stage
  refine ⟨σ, hs, width, ?_⟩
  intro N interior
  obtain ⟨Z, faces, before, count, draw, actual, separate, _, _, _, _, rooted, _⟩ := allN N interior
  exact ⟨Z, faces, before, count, draw, actual, separate, rooted, issued R m N (2+e) Z hs draw⟩

end YM.Integration.WilsonRegisteredFiledInvoice
