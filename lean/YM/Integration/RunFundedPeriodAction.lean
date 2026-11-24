import YM.Integration.FundedCorrectedPeriod
import YM.Integration.FundedOriginalVacuumPaths

/-! The independent correction supplied by the actual running kinetic history
has one finite physical list at every period, through its purchased grade. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.RunFundedPeriodAction
open Filter Function Lattice RG RG.Supply Precision Next.Foundations Wilson Tree Marker
open PhysicalNext PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Physical
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Bloom WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Soil WilsonCoeffUV.Fk
open WilsonLimitConstruction WilsonStartup IterationFour.Vacuum WilsonCoeffUV.Blue PowerSeries
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge}

structure PeriodData (Z : SeriesA G) (t : ℕ) (σ C : ℝ) : Prop where
  coefficients (n : Side) : X^2 * flash (sands Z n) = FundedPeriodAction.formal n Z
  grades (n : Side) (B : BudgetPoint) :
    IterationFour.Vacuum.Render.gradings (Z.map (FundedCorrectedPeriod.piece n B σ C)) t
  restored (n : Side) (B : BudgetPoint) (g : ℝ) (U : Config G n) :
    ActualGradedVacuum.restored (Z.map (FundedCorrectedPeriod.piece n B σ C)) g U =
      FundedPeriodAction.rendered n Z g U
  paid (n : Side) (hn : 20<n.val) (B : BudgetPoint)
    (hB : B.supportExponent/B.B ≤ σ/4) (hc : 2≤B.B) (A : Activities G n)
    (hA : ∀ s b,A.Moves s b) :
    IterationFour.Vacuum.Render.permits (Z.map (FundedCorrectedPeriod.piece n B σ C)) B
  masked (n : Side) (B : BudgetPoint) (hB : B.supportExponent/B.B ≤ σ/4)
    (hc : 2≤B.B) (A : Activities G n) {V : Type} [DecidableEq V] (K : Census V) (X : V→Type)
    (g : ℝ) (U : Config G n) :
    IterationFour.Vacuum.Render.renders (IterationFour.Vacuum.Render.prefactor g) B U
      (Z.map (FundedCorrectedPeriod.piece n B σ C)) =
      (Z.map fun a => g^((a.grade:ℤ)-(a.rise+2:ℕ)) * PhysicalNext.Repeat.Song.billOf B a.cells U).sum +
      (Z.map fun a => g^((a.grade:ℤ)-(a.rise+2:ℕ)) * FundedCorrectedPeriod.residual B K X a U).sum

theorem realized (Z : SeriesA G) {t : ℕ} {σ C : ℝ} (hG : G.Simple) (hσ : 0<σ)
    (h : Draw Z σ C) (hg : ∀ a∈Z,3≤a.grade) (ht : fromBefore Z (t+1)) :
    PeriodData Z t σ C where
  coefficients n := FundedPeriodAction.packets n hσ Z h
  grades n B := by
    intro p hp
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    exact ⟨hg a ha,Nat.le_of_lt_succ (ht a ha)⟩
  restored n B g U := FundedCorrectedPeriod.restored Z h (fun a ha=>by have := hg a ha; omega) hσ B g U
  paid n hn B hB hc A hA := FundedCorrectedPeriod.permits Z h hG hn B hσ hB hc A hA
  masked n B hB hc A _ _ K X g U := FundedCorrectedPeriod.masked_list Z h
    (fun a ha=>by have := hg a ha; omega) B hσ hB hc A K X g U

theorem fromRun (R : Run G) (hG : G.Simple) (v : ℕ→Gear G→ℝ)
    (hc : FundedMarkedCoverRows.prices v R.kit) (paid : FundedOriginalVacuumPaths.prices R.kit)
    (e : ℕ) : ∃ W : Credit, ∀ᶠ m : ℕ in atTop,
    let A := R.family.path.levels
    ∃ p : 5 ≤ A.clock.J (m+1),
      let s := min (crestM A m p) (A.params m).width
      let u := untilWidth G e s (lt_min (spatter G _ _ _ _ p).1 (A.params m).width_pos)
      0<u ∧ u⁻¹≤zz A m ∧ ∀ N, m≤N →
        let H := R.alloy.B.kin.path N m
        let B := (A.params m).clip
        let P := actionW A R.metals.O N m
        let C := W.buy (zz A m)+zz A m*A.clock.loopCap m
        ∃ Z : SeriesA G, (∀ a∈Z,3≤a.grade) ∧ fromBefore Z (3+e) ∧
          Z.length ≤ meterPre (3+e) ∧ Draw Z u C ∧
          (∀ j<3+e,(breast H B+sandLift Z) j=P j ∧
            ∀ n : Side, ∀ r,(front H B n+sands Z n) j (r+1)=lagoon (P j (r+1)) n) ∧
          PeriodData Z (2+e) u C := by
  obtain ⟨W,hw⟩ := FundedOriginalVacuumPaths.corrections R hG v hc paid e
  refine ⟨W,?_⟩
  filter_upwards [hw] with m hm
  obtain ⟨p,hu,hs,hN⟩ := hm
  refine ⟨p,hu,hs,?_⟩
  intro N hn
  obtain ⟨Z,hg,ht,hl,hp,h⟩ := hN N hn
  refine ⟨Z,hg,ht,hl,hp,h,realized (t:=2+e) Z hG hu hp hg ?_⟩
  rw [show 2+e+1=3+e by omega]
  exact ht

end YM.Integration.RunFundedPeriodAction
