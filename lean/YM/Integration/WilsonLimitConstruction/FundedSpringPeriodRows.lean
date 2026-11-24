import YM.Integration.RunFundedPeriodAction
import YM.Integration.WilsonLimitConstruction.FundedSpringCoverRegrade

/-! The genuine periodized Wilson vacuum cover with a funded coarse
realizing list, before the choice of cutoff, torus or inspected field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedSpringPeriodRows
open Filter Function Lattice RG RG.Supply Precision Next.Foundations Wilson Tree
open PhysicalNext PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Physical
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Bloom WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Soil WilsonCoeffUV.Fk
open WilsonLimitConstruction WilsonStartup IterationFour.Vacuum WilsonCoeffUV.Blue PowerSeries
open scoped Topology BigOperators ContDiff Classical
open Finset PowerSeries WilsonCoeffUV.Blue
variable {G : Gauge}
variable (R : Run G) (hG : G.Simple) (N m : ℕ) (hm : m<N)
local notation "A₀" => R.family.path.levels
local notation "O₀" => R.metals.O
local notation "a₀" => pace (pitch (A₀) (O₀) N m)

include hG hm in
/-- Periodization commutes with the exact native inverse chart on every
paid positive-valence row. All terms are absolutely summable at a common
strictly positive minimum of their true finitely many decay rates. -/
theorem regraded (n : Side) (Q : PChart G n) (k l : ℕ)
    (source : ∀ i≤k,Q i (l+1)=lagoon (actionW (A₀) (O₀) N m i (l+1)) n) :
    Blue.mix (a₀) Q k (l+1)=lagoon (freshet (A₀) (O₀) N m k (l+1)) n := by
  let old := actionW (A₀) (O₀) N m
  have available (i : ℕ) : ∃ s C : ℝ,0<s ∧ Amber terrain s C (old i (l+1)) :=
    (catchment (A₀) (O₀) hG R.alloy.B.ratio hm.le).paid i (l+1)
  choose σ C hσ hC using available
  have hn : (range (k+1)).Nonempty := ⟨0,mem_range.mpr (by omega)⟩
  let s := (range (k+1)).inf' hn σ
  have hs : 0<s := by simpa only [s,Finset.lt_inf'_iff] using
    (show ∀ i∈range (k+1),0<σ i from fun i _ =>hσ i)
  let fee (i : ℕ) := coeff (k-i) ((a₀)^i*((a₀)⁻¹)^(l+1))
  have widths (i : ℕ) (hi : i ∈ range (k+1)) :
      ∃c:ℝ,Amber terrain s c (fee i • old i (l+1)) :=
    ⟨_,((hC i).mono (Finset.inf'_le σ hi)).smul (fee i)⟩
  rw [←FundedSpringCoverRegrade.physical R hG N m hm k l]
  change (∑i∈range (k+1),fee i • Q i (l+1)) =
    lagoon (∑i∈range (k+1),fee i • old i (l+1)) n
  rw [lagoon_join (range (k+1)) widths hs n]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lagoon_scalar,source i (by have e:=mem_range.mp hi;omega)]

include hG in
/-- The chosen signed finite-period correction prices the original local
Plan on this very Run. The decay rate precedes N, and the entire list Z
precedes the actual torus, tensor components and the analogue of F. -/
theorem funded (v : ℕ→Gear G→ℝ) (hc : FundedMarkedCoverRows.prices v R.kit)
    (paid : FundedOriginalVacuumPaths.prices R.kit) (e : ℕ) :
    ∃ W : Credit,∀ᶠ m : ℕ in Filter.atTop,
      ∃s : ℝ, 0<s ∧ s⁻¹≤zz (A₀) m ∧ ∀N : ℕ,m<N →
        let K := W.buy (zz (A₀) m)+zz (A₀) m*(A₀).clock.loopCap m
        let H := R.alloy.B.kin.path N m
        let B := ((A₀).params m).clip
        ∃Z : SeriesA G,(∀a∈Z,3≤a.grade) ∧ fromBefore Z (3+e) ∧
          Z.length ≤ meterPre (3+e) ∧ Draw Z s K ∧
          RunFundedPeriodAction.PeriodData Z (2+e) s K ∧
          ∀k<3+e,∀n : Side,∀l,
            Blue.mix (pace (pitch (A₀) (O₀) N m)) (front H B n+sands Z n) k (l+1)=
              lagoon (freshet (A₀) (O₀) N m k (l+1)) n := by
  obtain ⟨W,hw⟩ := RunFundedPeriodAction.fromRun R hG v hc paid e
  refine ⟨W,?_⟩
  filter_upwards [hw] with m hm
  obtain ⟨p,hu,hs,hN⟩ := hm
  refine ⟨_,hu,hs,?_⟩
  intro N later
  obtain ⟨Z,hg,ht,hl,hD,hmatch,D⟩ := hN N later.le
  refine ⟨Z,hg,ht,hl,hD,D,?_⟩
  intro k hk n l
  exact regraded R hG N m later n _ k l fun i hi => (hmatch i (hi.trans_lt hk)).2 n l

end YM.Integration.WilsonLimitConstruction.FundedSpringPeriodRows
