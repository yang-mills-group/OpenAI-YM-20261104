import YM.Integration.WilsonPhysicalStationRawReading
import YM.OPE.Columns.Plane

/-! A raw table error can leak below the chosen engineering grade.
Separate that signed error before dividing by the measuring magnification. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationHorizontalWallet
open Function Filter Finset Lattice RG Wilson Cells Labels Source Next.Rank Next.Rank.East Next.Rank.Price
open MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonPhysicalStationRawReading (err eng)
open WilsonPhysicalStationFactoryGerm (incoming)
open scoped Classical BigOperators
variable {G:Gauge} {h:ℕ} (F:Frame G h)

def normAt (t:ℝ) (x:F.Coeff) : ℝ := ∑ a,t^(F.grades a).1*‖x a‖

theorem budget (t:ℝ) (ht:0 ≤ t) (ht':t ≤ 1) (x z:F.Coeff)
    (horizontal:∀ a,(F.grades a).1<h → x a=0) :
    normAt F t z ≤ t^h*F.coeffSize x + F.coeffSize (x-z) := by
  unfold normAt Frame.coeffSize; rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro a _
  have pay:t^(F.grades a).1*‖x a-z a‖ ≤ ‖x a-z a‖ :=
    mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ ht ht')
  have exactRow:t^(F.grades a).1*‖x a‖ = t^h*‖x a‖ := by
    by_cases H:(F.grades a).1=h
    · rw [H]
    · rw [horizontal a (lt_of_le_of_ne (F.bound a) H)]; simp
  have triangle : ‖z a‖ ≤ ‖x a‖ + ‖x a-z a‖ := by
    simpa only [sub_sub_cancel] using norm_sub_le (x a) (x a-z a)
  calc
    _ ≤ t^(F.grades a).1*(‖x a‖+‖x a-z a‖) := mul_le_mul_of_nonneg_left triangle (pow_nonneg ht _)
    _ = t^h*‖x a‖ + t^(F.grades a).1*‖x a-z a‖ := by rw [mul_add,exactRow]
    _ ≤ _ := add_le_add (le_refl _) pay

theorem fromLower (e:ℕ) (x:F.Coeff) (zero:OPE.Columns.low F e x=0)
    (horizon:h=e+1) (a:F.Index) (low:(F.grades a).1<h) : x a=0 := by
  have h' : (F.grades a).1 ≤ e := by omega
  simpa [OPE.Columns.low_apply,h'] using congrFun zero a

variable (R:Run G) {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}
    {D:ℕ} (A:Vane R.family D) (d:Fin (D+1)) {N p:ℕ}
local notation "F₀" => R.family.labels.level d
local notation "M₀" => Station.mag R.family.path.levels A.b A.k

theorem original (check:A.checked f H D) (top:A.k<N) (y:R.family.label d) (enlarged:1 ≤ M₀)
    (horizontal:∀ a,((F₀).grades a).1<d.val → (incoming R d N p y A.k).x a=0) :
    ‖eng R d A.k‖ * normAt (F₀) (M₀)⁻¹ (A.R N p d y) ≤
      ((M₀)⁻¹^d.val + err R A.k)*(F₀).coeffSize (incoming R d N p y A.k).x := by
  let x:=(incoming R d N p y A.k).x
  have pos:=Station.mag_pos R.family.path.levels A.b A.k
  have cost:=budget (F₀) (M₀)⁻¹ (inv_nonneg.mpr pos.le) (inv_le_one_of_one_le₀ enlarged)
    x (eng R d A.k • A.R N p d y) horizontal
  have fee:=WilsonPhysicalStationRawReading.original R A d y (p:=p) check top
  have normed (v:(F₀).Coeff) (c:ℂ) : normAt (F₀) (M₀)⁻¹ (c • v)=‖c‖*normAt (F₀) (M₀)⁻¹ v := by
    simp only [normAt,Pi.smul_apply,norm_smul,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [normed] at cost
  exact cost.trans ((add_le_add (le_refl _) fee).trans_eq (by rw [add_mul]))

end YM.Integration.WilsonPhysicalStationHorizontalWallet
end
