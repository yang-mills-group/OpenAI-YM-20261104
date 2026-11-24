import YM.Integration.WilsonPointChildFiniteStage
import YM.Integration.WilsonVacuumPreResetFiniteHeatHierarchy
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildWindingHistory
open Filter Function Finset YM FormalBulk08 Lattice RG Laurent Next.Foundations PhysicalNext.Repeat.Legato
open Reef Flat Stationary Dawn Pose Kemp Palm Shore Mesa Wine Quire Roof Lotus Sierra Gorge Dove Rial Rift Lava
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep WilsonPointChildFiledPress
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped ContDiff BigOperators Topology Classical ENNReal
open Function Filter Finset Matrix Lattice Wilson RG Laurent PowerSeries Work.F08
open FormalBulk08 Flat Reef Jets Orb Wick Stationary Series Shore Gorge Lotus Mesa Rift Lava Dawn Kemp Roof Sierra Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open YM Next.Foundations PhysicalNext.Repeat.Legato Pose Palm Quire Wine Dove WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Classical Topology BigOperators ContDiff
open WilsonCoeffUV.Bank.Carp WilsonPointChildPairedHistory
open WilsonPointChildCoveredRead (directions)
open Function Filter Finset Lattice RG Wilson Laurent Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Ticket
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open WilsonVacuumPreResetFiniteHeatTable (table)
open WilsonMarkedIndependentNormalizedWallet (gap)
open WilsonMarkedIndependentNormalizedScale (rate)
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
open Borough
open WilsonPointChildFiledSalary (inverseCost)
open WilsonPointChildFiniteRestamp (difference)
open WilsonPointChildCoverStep (routes)
open WilsonVacuumPreResetFiniteHeatFinance (gross)
open WilsonVacuumPreResetFiniteHeatTable (table)
open WilsonMarkedIndependentNormalizedScale (rate)
open WilsonCoeffUV.Bank.Carp
open WilsonPointChildFiniteStage (Gap)
variable {G:Gauge}{d D:ℕ}

theorem birth (R:Run G)(u:G.ColorIndex)(depth:d<D)(o:Loc G 1)(N per E:ℕ):
    Gap R u depth N N per E (rate R.family.path.levels N per):=by
  intro v p e _ r x
  have top:=Roof.topC o (R.family.labels.level d) (R.family.localSection d) R.family.params
    (R.makes.sections d) (Next.Foundations.valuation G d) depth
  have law:=WilsonPointChildFoldedField.print
    (clef_through (top.officers v) (slotsFits _ v)) (physical p) (R.family.side N per) e r
  have zero:difference (ledger R u depth N 0 N v p) (R.family.side N per) e r x=0:=
    sub_eq_zero.mpr (congrFun law x)
  rw [Nat.sub_self,zero,abs_zero]
  exact mul_nonneg (by positivity) (Real.exp_pos _).le

/-- The cutoff-independent absolute slope at a nominated reporting date for
one physical digit itinerary pinned at zero at every fine subdivision. -/
theorem original (G:Gauge)(E d:ℕ):∃v:ℕ → Gear G → ℝ,∀(R:Run G),G.Simple → 
    RG05Preconstruction.ReadoutPurchase R.b → ∀cash:ℕ → Gear G → ℝ,FundedMarkedCoverRows.prices cash R.kit →
    (∀ᶠj:ℕ in atTop,∀I,v (R.family.path.levels.clock.J (j+1)) I ≤ cash (R.family.path.levels.clock.J (j+1)) I) → 
    WilsonPointChildFiledTest.Filed R → ∀(u:G.ColorIndex){D:ℕ}(depth:d<D)(o:Loc G 1)
    (_tags:∀i n,(Flat.primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices),
    WilsonPointChildWidthHistory.Income R (routes R) u depth o E → 
    ∀ᶠm:ℕ in atTop,∀N per,m ≤ N → 
    table R.family.path.levels R.metals.O E N m (R.family.side m per)
      (WilsonVacuumPreResetFiniteHeatScale.rate R.family.path.levels m per) ∧
    Gap R u depth N m per E (rate R.family.path.levels m per):=by
  obtain ⟨u,stage⟩:=WilsonPointChildFiniteStage.original G E d
  obtain ⟨v,vacuum⟩:=WilsonVacuumPreResetFiniteHeatStep.original G E
  let pay(j:ℕ)(I:Gear G):=|u I|+|v j I|
  refine ⟨pay,?_⟩
  intro R simple reading received paid fileprice file z D depth o tags inverse
  let A:=R.family.path.levels
  obtain ⟨k₀,marked⟩:=eventually_atTop.mp (stage R simple file z depth o received paid tags inverse)
  obtain ⟨k₁,price⟩:=eventually_atTop.mp (vacuum R simple reading)
  obtain ⟨k₂,cover⟩:=eventually_atTop.mp fileprice
  filter_upwards [eventually_ge_atTop (max (max k₀ k₁) k₂),FundedMarkedCoverRows.realm R simple received paid 0 (fun _=>0)
    (fun _=>1) (fun _=>by decide) E 0 0] with m ready election
  obtain ⟨Q,draws,O,clock,anchor,_,_,_,book⟩:=election
  intro N per live
  have down(h:ℕ):∀j,m ≤ j → j+h=N → 
      table A R.metals.O E N j (R.family.side j per) (WilsonVacuumPreResetFiniteHeatScale.rate A j per) ∧
      Gap R z depth N j per E (rate A j per):=by
    induction h with
    | zero=>
      intro j _ enddate
      have eq:j=N:=by omega
      subst j
      exact ⟨WilsonVacuumPreResetFiniteHeatTable.top R E N (R.family.side N per) (Real.exp_pos _).le,
        birth R z depth o N per E⟩
    | succ h ih=>
      intro j hj live'
      have liveJ:j<N:=by omega
      have prior:=ih (j+1) (by omega) (by omega)
      have here:Q.anchor ≤ j:=anchor ▸ hj
      obtain ⟨_,_,cash⟩:=book j hj here
      let I:=(Q.mint j here).gear
      let t:=A.clock.J (j+1)
      have mk:u I ≤ pay t I:=(le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
      have vc:v t I ≤ pay t I:=(le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
      have use:pay t I ≤ Q.cash Credit.leanC j:=(cover j (by omega) I).trans cash
      exact ⟨price j (by omega) Q here draws O clock (vc.trans use) N per liveJ prior.1,
        marked j (by omega) Q here draws O clock (mk.trans use) N per liveJ prior.1 prior.2⟩
  exact down (N-m) m le_rfl (by omega)

end YM.Integration.WilsonPointChildWindingHistory
