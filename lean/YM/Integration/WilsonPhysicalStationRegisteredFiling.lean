import YM.Integration.WilsonPhysicalStationAdjacentFare

/-! Both true reporting tables and the signed registered one-step operator.
The two lower vectors remain on the same physical factory plane. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationRegisteredFiling
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
open WilsonPhysicalStationAdjacentFare (fare)
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

def rate (m k h:ℕ) : ℝ :=
  let a:=R.family.path.levels
  (1+2*(a.params m).columns*(1+err R m))*
    fare (ceiling (R.family.labels.level h) (ratio R m)) (barunit (R.family.S.block m))
      (err R m) (err R k) (a.params k).columns

include L fac in
theorem original (hg:G.Simple) (ca:A.checked f H D) (cb:B.checked f H D') (dates:B.k=A.k+1)
    (top:B.k<N) (horizon:h=e+1)
    (gate:(C₀)*err R A.k≤1/2) (y:R.family.label h)
    (hom:(P₀) (B.R N p (b₀) y)=0):
    let v:=(incoming R h N p y B.k).x
    let goal:=(D₀) (measured R B (b₀) N p y)
    ∃ z w:R.family.label h,(P₀) z=z ∧ (P₀) w=w ∧
      (P₀) (incoming R h N p (y-(K₀).terminal z) B.k).x=0 ∧
      (P₀) (A.R N p (a₀) (y-(K₀).terminal (z+w)))=0 ∧
      μ (Columns.trace R.family h N p B.k z) ≤ (C₁)*err R B.k*μ v ∧
      μ (Columns.trace R.family h N p A.k w) ≤ 2*(C₀)*
        μ (measured R A (a₀) N p (y-(K₀).terminal z)-goal) ∧
      μ (measured R A (a₀) N p (y-(K₀).terminal (z+w))-goal) ≤ rate R A.k B.k h*μ v := by
  intro v goal
  have he:e<h:=by omega
  have live:A.k<N:=by omega
  obtain ⟨z,hz,atK,fine,corr⟩:=WilsonPhysicalStationFineCorrection.original R fac B (b₀) e (p:=p) cb top he y hom
  let y₁:=y-(K₀).terminal z
  obtain ⟨_,_,registered⟩:=WilsonPhysicalStationRegisteredDiagonal.original R L (p:=p) hg (ca.early (a₀)) live e horizon
  have edge: μ ((incoming R h N p y₁ A.k).x-(D₀) (incoming R h N p y₁ B.k).x) ≤ (δ₀)*μ (incoming R h N p y₁ B.k).x := by
    rw [dates] at atK ⊢
    exact (registered y₁ atK).2
  have older:=WilsonPhysicalStationRawReading.original R A (a₀) y₁ (p:=p) ca live
  have newer:=WilsonPhysicalStationRawReading.original R B (b₀) y (p:=p) cb top
  have payment:=WilsonPhysicalStationAdjacentFare.original (F₀) (ratio R A.k)
    (ck:=(C₁)) (em:=err R A.k) (ek:=err R B.k) (δ:=(δ₀)) (Real.exp_pos _).le (by unfold barunit puffs;positivity)
    (measured R B (b₀) N p y) (measured R A (a₀) N p y₁) v (incoming R h N p y₁ B.k).x
    (incoming R h N p y₁ A.k).x newer corr edge older
  have horizontal:(P₀) goal=0:=by
    ext i
    by_cases hi:((F₀).grades i).1≤e
    · have data:=congrFun hom i
      have si:B.R N p (b₀) y i=0:=by simpa [Columns.low_apply,hi] using data
      simp [Columns.low_apply,hi,goal,Frame.scaled_apply,measured,si]
    · simp [Columns.low_apply,hi]
  obtain ⟨w,hw,actual,salary,restored⟩:=
    WilsonPhysicalStationFiledAdjustment.original R fac A (a₀) e (p:=p) ca live he gate y₁ goal horizontal
  have written:y-(K₀).terminal (z+w)=y₁-(K₀).terminal w:=by dsimp [y₁];rw [map_add,sub_add_eq_sub_sub]
  refine ⟨z,w,hz,hw,atK,by rw [written];exact actual,fine,salary,?_⟩
  rw [written]
  have nonneg: 0≤1+2*(C₀)*(1+err R A.k):=
    add_nonneg zero_le_one (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans ((L₀).params A.k).columns_ge))
      (add_nonneg zero_le_one (Real.exp_pos _).le))
  exact restored.trans ((mul_le_mul_of_nonneg_left payment nonneg).trans_eq (by unfold rate;ring))

end YM.Integration.WilsonPhysicalStationRegisteredFiling
end
