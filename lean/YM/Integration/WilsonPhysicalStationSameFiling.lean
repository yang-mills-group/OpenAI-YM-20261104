import YM.Integration.WilsonPhysicalStationFiledAdjustment
import YM.Integration.WilsonPhysicalStationRegisteredDiagonal

/-! The two genuine reporting tables may have the same stopping date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationSameFiling
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus MergeProof Matric Gram
open PhysicalNext.Repeat.Legato Bandage Campaign
open Next.Foundations OPE Work.G08
open Next.Rank Next.Rank.East Next.Rank.Price MergeProof.East
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress
open Trace.Physical.GermGraph
open WilsonPhysicalStationFactoryGerm (incoming)
open WilsonPhysicalStationRawReading (err eng)
open WilsonPhysicalStationFineCorrection (measured)
open WilsonPhysicalStationRegisteredDiagonal (ratio ceiling)
open scoped BigOperators Classical Topology

variable {G:Gauge} (R:Run G) {T:Campaign R} (L:Pillars R T) {f:Extraction.Order} {S:Table R.family.book}
  (fac:Facilities R.family f S) {H:(Bel R.family.book).Hierarchy}
  {D D':ℕ} (A:Vane R.family D) (B:Vane R.family D') {N p:ℕ}
  (h e:ℕ) (da:h<D+1) (db:h<D'+1)
local notation "a₀" => (⟨h,da⟩:Fin (D+1))
local notation "b₀" => (⟨h,db⟩:Fin (D'+1))
local notation "L₀" => R.family.path.levels
local notation "F₀" => R.family.labels.level h
local notation "μ" => (F₀).coeffSize
local notation "P₀" => Columns.low (F₀) e
local notation "K₀" => R.family.factory h N p
local notation "C₀" => ((L₀).params A.k).columns
local notation "C₁" => ((L₀).params B.k).columns
local notation "δ₀" => barunit (R.family.S.block A.k)
local notation "D₀" => (F₀).scaled (ratio R A.k)

include fac in
theorem original (ca:A.checked f H D) (cb:B.checked f H D') (dates:B.k=A.k)
    (top:A.k<N) (he:e<h) (gate:(C₀)*err R A.k≤1/2) (y:R.family.label h)
    (hom:(P₀) (B.R N p (b₀) y)=0):
    let a:=measured R B (b₀) N p y
    ∃ w:R.family.label h,(P₀) w=w ∧
      (P₀) (A.R N p (a₀) (y-(K₀).terminal w))=0 ∧
      μ (Columns.trace R.family h N p A.k w) ≤ 2*(C₀)*
        μ (measured R A (a₀) N p y-a) ∧
      μ (measured R A (a₀) N p (y-(K₀).terminal w)-a) ≤
         (1+2*(C₀)*(1+err R A.k))*(2*err R A.k)*μ (incoming R h N p y A.k).x := by
  intro a
  have horizontal:(P₀) a=0:=by change (P₀) (eng R h B.k • _)=0;rw [map_smul,hom,smul_zero]
  have fine:=WilsonPhysicalStationRawReading.original R B (b₀) y (p:=p) cb (dates ▸ top)
  have coarse:=WilsonPhysicalStationRawReading.original R A (a₀) y (p:=p) ca top
  let v:=(incoming R h N p y A.k).x
  let b:=measured R A (a₀) N p y
  change μ ((incoming R h N p y B.k).x-a) ≤ err R B.k*μ (incoming R h N p y B.k).x at fine
  rw [dates] at fine
  change μ (v-b)≤err R A.k*μ v at coarse
  have paid:μ (b-a)≤2*err R A.k*μ v:=by
    have tri:=WilsonPhysicalStationFineCorrection.sizes R (a₀) b v a
    rw [WilsonPhysicalStationFineCorrection.reverse R (a₀) b v] at tri
    linarith only [tri,coarse,fine]
  obtain ⟨w,hw,actual,salary,restored⟩:=
    WilsonPhysicalStationFiledAdjustment.original R fac A (a₀) e (p:=p) ca top he gate y a horizontal
  refine ⟨w,hw,actual,salary,?_⟩
  have nonneg: 0≤1+2*(C₀)*(1+err R A.k):=
    add_nonneg zero_le_one (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans ((L₀).params A.k).columns_ge))
      (add_nonneg zero_le_one (Real.exp_pos _).le))
  exact restored.trans ((mul_le_mul_of_nonneg_left paid nonneg).trans_eq (by ring))

end YM.Integration.WilsonPhysicalStationSameFiling
end
