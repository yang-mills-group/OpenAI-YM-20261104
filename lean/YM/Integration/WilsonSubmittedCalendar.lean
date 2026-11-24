import YM.Integration.WilsonSubmittedLeadingPeriod

/-! One original pre-election reserves every eventually active quiet coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonSubmittedCalendar
open WilsonLimitConstruction Function Filter Gauge Pressure Precision Tree Stationary
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open AllOrder AllOrder.Ker AllOrder.Haiku AllOrder.Floe.Step
open WilsonCoeffUV.Bank.Mosaic PertExtension.Series PowerSeries
open Finset Lattice RG WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer
open WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Winding
open Next.Foundations PhysicalNext.Repeat.Legato ActualRunAdmissionScales
open WilsonVacuumPreResetFiniteHeatCourse WilsonVacuumPreResetDatedDeposit WilsonVacuumPreResetTorusDeposit
open WilsonVacuumPreResetTorusGrade WilsonCoeffUV.Wheel WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Ticket
open AllOrder.Floe AllOrder.Ker Primitives.TwoWave.RealSlice
open scoped BigOperators Classical
variable {G:Gauge}


theorem original (G:Gauge):∃v:ℕ→Gear G→ℝ,∃d:ℕ→ℕ,∀(R:Run G),G.Simple→
    RG05Preconstruction.ReadoutPurchase R.b→FundedMarkedCoverRows.prices v R.kit→
    ∀i:ℕ,∀ᶠj:ℕ in atTop,WilsonSubmittedPeriodSeam.Bill R i (d i) j:=by
  classical
  choose f d grant using fun (i:ℕ) (r:Fin (i+2))=>
    WilsonVacuumPreResetFiniteHeatCourse.fresh G i i (r:ℕ) le_rfl
  let v(k:ℕ)(g:Gear G):ℝ:=∑i∈Finset.range (k+1),∑r:Fin (i+2),|f i r k g|
  refine ⟨v,fun i=>∑r,d i r,?_⟩
  intro R simple reading paid i
  let L:=R.family.path.levels
  have grows:Tendsto (fun j:ℕ=>L.clock.J (j+1)) atTop atTop:=L.fits.deep.comp (tendsto_add_atTop_nat 1)
  have dates:∀ᶠj:ℕ in atTop,∀r:Fin (i+2),_:=
    (Filter.eventually_all).mpr fun r=>grant i r R simple reading
  filter_upwards [dates,FundedMarkedCoverRows.realm R simple v paid 0 (fun _=>0) (fun _=>1)
    (fun _=>by decide) i 0 0,grows.eventually_ge_atTop i] with j banks realm active
  obtain ⟨Q,draws,coupling,clock,anchor,_,_,_,budget⟩:=realm
  have hj:Q.anchor≤j:=anchor.le
  obtain ⟨_,_,cash⟩:=budget j le_rfl hj
  apply WilsonSubmittedPeriodSeam.at_date R i _ j simple
  apply WilsonFiledPeriodSeam.at_date R i _ j simple
  intro N p later r hr x
  let a:Fin (i+2):=⟨r,hr⟩
  let k:=L.clock.J (j+1)
  let g:Gear G:=(Q.mint j hj).gear
  have bound:f i a k g≤v k g:=((le_abs_self _).trans (Finset.single_le_sum
    (f:=fun s:Fin (i+2)=>|f i s k g|) (fun b _=>abs_nonneg _) (Finset.mem_univ a))).trans
    (Finset.single_le_sum (f:=fun i=>∑s:Fin (i+2),|f i s k g|)
      (fun z _=>Finset.sum_nonneg (fun b _=>abs_nonneg _)) (Finset.mem_range.mpr (by omega)))
  have h:=(banks a) Q hj draws coupling clock (bound.trans cash) N p later x
  rw [clock] at h
  exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (admittedCost_one R.family.path.levels j)
    (Finset.single_le_sum (fun b _=>Nat.zero_le (d i b)) (Finset.mem_univ a))) (Real.exp_nonneg _))

theorem funded.{u} (simple:G.Simple){ε:ℝ}(hε:0<ε)
    (P:FundedCompanySelection.Prediction G)(hP:FundedPredictionSupply.AllPrices (@P)):
    ∃(R:Run G)(T:Campaign R)(W:Campaign.Pillars R T)(d:ℕ→ℕ),
      P R.kit ∧ NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} simple ε W ∧
      ∀i:ℕ,∀ᶠj:ℕ in atTop,WilsonSubmittedPeriodSeam.Bill R i (d i) j:=by
  obtain ⟨v,d,call⟩:=original G
  obtain ⟨R,T,W,paid,partner,plateau,actual⟩:=FundedMarkedCoverRows.original.{u} simple hε v (@P) hP
  exact ⟨R,T,W,d,partner,plateau,actual,call R simple actual.2.2.2.2.2.2.1 paid⟩

end YM.Integration.WilsonSubmittedCalendar
end
