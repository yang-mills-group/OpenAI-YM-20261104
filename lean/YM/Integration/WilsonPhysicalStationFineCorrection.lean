import YM.Integration.WilsonPhysicalStationFiledPlane
import YM.Integration.WilsonPhysicalStationFiledGate
import YM.Integration.WilsonPhysicalStationThermalStart

/-! The finer filed source is tested first on the true factory lower plane. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationFineCorrection
open Function Filter RG Wilson MergeProof Labels Source Lattice OPE Work.G08
open Next.Rank Next.Rank.East Next.Rank.Price MergeProof.East
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonPhysicalStationFactoryGerm (incoming)
open WilsonPhysicalStationRawReading (err eng)
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
    (fac:Facilities R.family f S) {H:(Bel R.family.book).Hierarchy}
    {D:ℕ} (A:Vane R.family D) (d:Fin (D+1)) {N p:ℕ} (e:ℕ)
local notation "F₀" => R.family.labels.level d
local notation "μ" => (F₀).coeffSize
local notation "C₀" => (R.family.path.levels.params A.k).columns
local notation "K₀" => R.family.factory d N p
local notation "T₀" => Columns.trace R.family d N p A.k
local notation "P₀" => Columns.low (F₀) e
local notation "M₀" => Station.mag R.family.path.levels A.b A.k

def measured (N p:ℕ) (y:R.family.label d) : R.family.label d :=
  eng R d A.k • (A.R N p d) y

theorem refile (check:A.checked f H D) (top:A.k<N) (y w:R.family.label d) :
    (incoming R d N p (y-(K₀).terminal w) A.k).x =
      (incoming R d N p y A.k).x-(T₀) w := by
  rw [WilsonPhysicalStationLowerPlane.refiles]
  let field : (F₀).Coeff →ₗ[ℂ] (F₀).Coeff :=
    (Columns.linTrace (C:=R.family) (d:=d.val) (N:=N) (p:=p) R.makes (check.early d) top.le).mk' (T₀)
  exact field.map_sub ((K₀).terminal.symm y) w

theorem sizes (x u v:(F₀).Coeff) : μ (x-v) ≤ μ (x-u)+μ (u-v) := by
  simpa using Extra.Histories.Size.add (F₀) (x-u) (u-v)

theorem reverse (x u:(F₀).Coeff) : μ (x-u)=μ (u-x) := by
  unfold Frame.coeffSize;apply Finset.sum_congr rfl
  intro i _
  exact norm_sub_rev _ _

include fac in
theorem original (ca:A.checked f H D) (top:A.k<N) (he:e<d.val)
    (y:R.family.label d) (horizontal:(P₀) (A.R N p d y)=0) :
    let a:=measured R A d N p y
    let v:=(incoming R d N p y A.k).x
    ∃ z:R.family.label d,(P₀) z=z ∧
      (P₀) (incoming R d N p (y-(K₀).terminal z) A.k).x=0 ∧
      μ ((T₀) z) ≤ (C₀)*err R A.k*μ v ∧
      μ ((incoming R d N p (y-(K₀).terminal z) A.k).x-a) ≤ (1+(C₀))*err R A.k*μ v := by
  intro a v
  obtain ⟨_,_,_,budget⟩:=fac.purchase
  let T:=budget.toTableTickets
  obtain ⟨z,hz,exactLow⟩:=Columns.reaches (p:=p) T R.makes v he (ca.early d) top.le
  have cone:=Columns.entire_cone (p:=p) T R.makes hz he (ca.early d) top.le
  rw [exactLow] at cone
  have paid:=WilsonPhysicalStationRawReading.original R A d y (p:=p) ca top
  change μ (v-a) ≤ err R A.k*μ v at paid
  have low:(P₀) a=0:=by change (P₀) (eng R d A.k • _)=0;rw [map_smul,horizontal,smul_zero]
  have size:μ ((P₀) v) ≤ μ (v-a):=by
    have h:(P₀) (v-a)=(P₀) v:=by rw [map_sub,low,sub_zero]
    rw [← h];exact Columns.size_low .. 
  have bill:μ ((T₀) z) ≤ (C₀)*err R A.k*μ v:=
    (cone.trans (mul_le_mul_of_nonneg_left (size.trans paid)
      (zero_le_one.trans ((R.family.path.levels.params A.k).columns_ge)))).trans_eq (by ring)
  refine ⟨z,hz,?_,bill,?_⟩
  · rw [refile R A d ca top y z,map_sub,exactLow,sub_self]
  · rw [refile R A d ca top y z]
    change μ (v-(T₀) z-a) ≤ _
    have eq:v-(T₀) z-a=(v-a)-(T₀) z:=by abel
    rw [eq]
    exact ((Columns.size_sub ..).trans (add_le_add paid bill)).trans_eq (by ring)

theorem entered (ca:A.checked f H D) (top:A.k<N) (s:R.family.label d)
    (horizontal:(P₀) s=0) :
    (P₀) (A.R N p d (WilsonPhysicalStationThermalStart.entered R A d (p:=p) ca top s))=0 := by
  have filed : A.R N p d (WilsonPhysicalStationThermalStart.entered R A d (p:=p) ca top s) =
      (F₀).scaled (shrink R.family A.k N p)⁻¹ (weightTag R.family d (M₀) s) :=
    (WilsonPhysicalStationTableJump.table R A d (p:=p) ca top).apply_symm_apply _
  rw [filed];ext i
  by_cases hi:((F₀).grades i).1≤e
  · have point:=congrFun horizontal i
    have si:s i=0:=by simpa [Columns.low,hi] using point
    simp [Columns.low,hi,Frame.scaled,weightTag,si]
  · simp [Columns.low,hi]

end YM.Integration.WilsonPhysicalStationFineCorrection
end
