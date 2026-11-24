import YM.Integration.WilsonPhysicalStationFineCorrection
import YM.Integration.WilsonPhysicalStationFiledGate
import YM.Integration.WilsonPhysicalStationThermalStart

/-! The finer filed source is tested first on the true factory lower plane. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationFiledAdjustment
open Function Filter RG Wilson MergeProof Labels Source Lattice OPE Work.G08
open Next.Rank Next.Rank.East Next.Rank.Price MergeProof.East
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonPhysicalStationFactoryGerm (incoming)
open WilsonPhysicalStationRawReading (err eng)
open WilsonPhysicalStationFineCorrection (measured reverse sizes)
open WilsonPhysicalStationFiledSlope (testing)
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

include fac in
theorem original (ca:A.checked f H D) (top:A.k<N) (he:e<d.val)
    (gate:(C₀)*err R A.k≤1/2)
    (y a:R.family.label d) (horizontal:(P₀) a=0):
    let b:=measured R A d N p y
    ∃ w:R.family.label d,(P₀) w=w ∧ (P₀) (A.R N p d (y-(K₀).terminal w))=0 ∧
      μ ((T₀) w) ≤ 2*(C₀)*μ (b-a) ∧
      μ (measured R A d N p (y-(K₀).terminal w)-a) ≤
        (1+2*(C₀)*(1+err R A.k))*μ (b-a) := by
  intro b
  obtain ⟨w,lower,same⟩:=WilsonPhysicalStationFiledPlane.reaches R fac A d e (p:=p) ca top he gate b
  have issued:=WilsonPhysicalStationFiledSlope.original R fac A d e (p:=p) ca top he gate w lower
  rw [same] at issued
  have low:(P₀) (b-a)=(P₀) b:=by rw [map_sub,horizontal,sub_zero]
  have fee:μ ((T₀) w) ≤ 2*(C₀)*μ (b-a) := by
    rw [← low] at issued
    exact issued.trans (mul_le_mul_of_nonneg_left (Columns.size_low ..)
      (mul_nonneg (by norm_num) (zero_le_one.trans (R.family.path.levels.params A.k).columns_ge)))
  refine ⟨w,lower,?_,fee,?_⟩
  · change (P₀) (eng R d A.k • (A.R N p d) ((K₀).terminal w))=
      (P₀) (eng R d A.k • (A.R N p d) y) at same
    simp only [map_smul] at same
    rw [map_sub,map_sub,sub_eq_zero]
    exact (smul_right_injective _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos _).ne')) same).symm
  let t:=testing R A d N p w
  have raw:=WilsonPhysicalStationFiledSlope.fee R A d (p:=p) ca top w
  change μ ((T₀) w-t) ≤ err R A.k*μ ((T₀) w) at raw
  have cost:μ t ≤ (1+err R A.k)*μ ((T₀) w):=by
    have tri:=Columns.size_sub (F₀) ((T₀) w) ((T₀) w-t)
    rw [sub_sub_cancel] at tri
    linarith only [tri,raw]
  have body:measured R A d N p (y-(K₀).terminal w)-a=(b-a)-t:=by
    change eng R d A.k • (A.R N p d) (y-(K₀).terminal w)-a=(eng R d A.k • (A.R N p d) y-a)-eng R d A.k • (A.R N p d) ((K₀).terminal w)
    rw [map_sub,smul_sub];abel
  rw [body]
  have cash: μ t ≤ (1+err R A.k)*(2*(C₀)*μ (b-a)):=
    cost.trans (mul_le_mul_of_nonneg_left fee (add_nonneg zero_le_one (Real.exp_pos _).le))
  exact ((Columns.size_sub ..).trans (add_le_add le_rfl cash)).trans_eq (by ring)

end YM.Integration.WilsonPhysicalStationFiledAdjustment
end
