import YM.Integration.WilsonPhysicalStationFiledSlope

/-! Exact lower-component subtraction in the declared unscaled table. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationFiledPlane
open Function Set Filter RG Wilson MergeProof Labels Source Lattice OPE Work.G08
open Next.Rank Next.Rank.East Next.Rank.Price MergeProof.East
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph PhysicalNext.Repeat.Legato.Bandage
open WilsonPhysicalStationFactoryGerm (incoming)
open WilsonPhysicalStationRawReading (err eng)
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
local notation "B₀" => testing R A d N p

include fac in
theorem reaches (check:A.checked f H D) (top:A.k<N) (he:e<d.val)
    (gate:(C₀)*err R A.k ≤ 1/2) (target:R.family.label d):
    ∃ u:R.family.label d,(P₀) u=u ∧ (P₀) ((B₀) u)=(P₀) target := by
  obtain ⟨_,_,_,budget⟩:=fac.purchase
  let M:=LinearMap.range (P₀)
  have fixed (u:M) : (P₀) u.val=u.val := by
    obtain ⟨b,z,hz⟩:=u
    change (P₀) b=b
    rw [← hz];exact Columns.project ..
  let ear:Module.End ℂ M:=(P₀).rangeRestrict.comp ((B₀).comp M.subtype)
  have onto:Surjective ear:=LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp
    (LinearMap.ker_eq_bot'.mpr (fun u hu=>?_)))
  · obtain ⟨u,hu⟩:=onto ((P₀).rangeRestrict target)
    exact ⟨u.val,fixed u,congrArg Subtype.val hu⟩
  have blank:(P₀) ((B₀) u.val)=0:=congrArg Subtype.val hu
  have price:=WilsonPhysicalStationFiledSlope.original R fac A d e (p:=p) check top he gate u.val (fixed u)
  have zero:(T₀) u.val=0:=by
    apply size_separates (F₀)
    rw [blank] at price
    simpa [Frame.coeffSize] using price
  have shrunk:=Columns.top_shrunk (p:=p) budget.toTableTickets R.makes (fixed u) he (check.early d) top.le
  rw [zero] at shrunk
  apply Subtype.ext; apply size_separates (F₀)
  have money:0 < (R.family.S.a A.k/R.family.S.a N)^(d.val-e):=
    pow_pos (div_pos (R.family.S.a_pos A.k) (R.family.S.a_pos N)) _
  exact nonpos_of_mul_nonpos_right (by simpa [Frame.coeffSize] using shrunk) money

include fac in
theorem original (check:A.checked f H D) (top:A.k<N) (he:e<d.val)
    (gate:(C₀)*err R A.k ≤ 1/2) (y:R.family.label d)
    (horizontal:(P₀) (incoming R d N p y A.k).x=0) :
    ∃ u:R.family.label d,(P₀) u=u ∧
      (P₀) ((A.R N p d) (y-(K₀).terminal u))=0 ∧
        μ ((T₀) u) ≤ 2*(C₀)*err R A.k*μ (incoming R d N p y A.k).x := by
  let x:=(incoming R d N p y A.k).x
  let b:=eng R d A.k • (A.R N p d) y
  have paid:=WilsonPhysicalStationRawReading.original R A d y (p:=p) check top
  change μ (x-b) ≤ err R A.k*μ x at paid
  change (P₀) x=0 at horizontal
  obtain ⟨u,hu,same⟩:=reaches R fac A d e (p:=p) check top he gate b
  refine ⟨u,hu,?_,?_⟩
  · change (P₀) (eng R d A.k • (A.R N p d) ((K₀).terminal u))=
      (P₀) (eng R d A.k • (A.R N p d) y) at same
    simp only [map_smul] at same
    rw [map_sub,map_sub,sub_eq_zero]
    exact (smul_right_injective _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos _).ne')) same).symm
  · have deduction:=WilsonPhysicalStationFiledSlope.original R fac A d e (p:=p) check top he gate u hu
    rw [same] at deduction
    have difference:(P₀) b= -((P₀) (x-b)):=by rw [map_sub,horizontal,zero_sub,neg_neg]
    have size: μ ((P₀) b) ≤ μ (x-b):=calc
      _ = μ ((P₀) (x-b)):=by rw [difference]; simp only [Frame.coeffSize,Pi.neg_apply,norm_neg]
      _ ≤ _:=Columns.size_low ..
    calc
      _ ≤ 2*(C₀)*μ ((P₀) b) := deduction
      _ ≤ 2*(C₀)*(err R A.k*μ x):=mul_le_mul_of_nonneg_left (size.trans paid)
        (mul_nonneg (by norm_num) (zero_le_one.trans (R.family.path.levels.params A.k).columns_ge))
      _ = _:=by ring

end YM.Integration.WilsonPhysicalStationFiledPlane
end
