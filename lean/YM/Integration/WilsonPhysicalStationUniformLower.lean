import YM.Integration.WilsonPhysicalStationWeightedAxis
import YM.Integration.WilsonPhysicalStationReferenceSalary
import YM.Integration.WilsonPhysicalStationDetectorCurrency
import YM.Integration.WilsonPhysicalStationLowerImage

/-! Physical lower subtractions are genuine bounded terminal columns on
the reporter's fixed table.  The common bound precedes cutoff and period. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationUniformLower
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
open WilsonPhysicalStationRegisteredFiling (rate)
open WilsonPhysicalStationThermalStart (entered)
open WilsonPhysicalStationThermalCoordinates (filed)
open WilsonPhysicalStationEndCurrency (row charge)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationWeightedAxis (purse)
open WilsonPhysicalStationDatedSalary (span datedMass)
open scoped BigOperators Classical Topology

variable {G:Gauge} (R:Run G) {T:Campaign R} (L:Pillars R T) {f:Extraction.Order} {S:Table R.family.book}
  (fac:Facilities R.family f S) {H:(Bel R.family.book).Hierarchy}
  {D D':ℕ} (A:Vane R.family D) (B:Vane R.family D') {N p:ℕ}
  (h e:ℕ) (da:h  <  D+1) (db:h  <  D'+1)
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

local notation "M₀" => Station.mag (L₀) A.b A.k
local notation "M₁" => Station.mag (L₀) B.b B.k


local notation "t₀" => (shrink R.family A.k N p)⁻¹
local notation "t₁" => (shrink R.family B.k N p)⁻¹


def peak (k:ℕ) (q:ℕ):ℝ:=(2*(L₀).clock.monitor k)^q
def room (m k h q:ℕ) (a b:ℝ):ℝ:=
  ((R.family.S.a k*b)/(R.family.S.a m*a))^h*peak R k q
def allowance (m k h q:ℕ)(a b:ℝ):ℝ:=
  span R (R.family.ref h) k^(h+1)*(2*((R.family.S.a k*b)^h*peak R k q))+
  span R (R.family.ref h) m^(h+1)*(4*(R.family.S.a m*a)^h*
    (((Fintype.card (R.family.labels.level h).Index:ℝ)*rate R m k h+(ratio R m)^q)*room R m k h q a b))

private theorem half {x c:ℝ} (pos:0 ≤ x)(one:1 ≤ c)(paid:c*x ≤ 1/2):
    (1/2:ℝ) ≤ 1-x:=by
  have le:x ≤ c*x:=le_mul_of_one_le_left pos one
  linarith only [le,paid]

private theorem double {x y c:ℝ} (pos:0 ≤ x)(one:(1/2:ℝ) ≤ c)(paid:c*x ≤ y): x ≤ 2*y:=by
  have f:=mul_le_mul_of_nonneg_right one pos
  linarith only [f,paid]

theorem original (ca:A.checked f H D) (cb:B.checked f H D')
    (dates:B.k=A.k+1) (top:B.k < N) (horizon:h=e+1)
    (gate:(C₀)*err R A.k ≤ 1/2) (next:(C₁)*err R B.k ≤ 1/2) (a:(F₀).Index) (weight:((F₀).grades a).1=h)
    (W:R.family.label h) :
    let s:R.family.label h:=Pi.single a 1
    let y:=entered R B (b₀) (p:=p) cb top s
    let Z:=y-(K₀).terminal W
    let q:=((F₀).grades a).2
    let χ:ℂ:=signal R N p A.k B.k h q (M₀) (M₁)
    (P₀) (A.R N p (a₀) Z)=0 →
    (∀i:(F₀).Index,(1-err R B.k)*‖filed R A (a₀) N p Z i-χ*s i‖*(t₀)^((F₀).grades i).2 ≤ 
      rate R A.k B.k h*purse R N p A.k B.k h q (M₀) (M₁)) →
    ‖(K₀).terminal W‖ ≤ allowance R A.k B.k h q (M₀) (M₁):=by
  intro s y Z q χ cleared cells
  let r:=R.family.ref h
  let source:=((R.family.S.a B.k)*(M₁))^h*peak R B.k q
  let wallet:=room R A.k B.k h q (M₀) (M₁)
  let cost:=rate R A.k B.k h
  let use:=(Fintype.card (F₀).Index:ℝ)*cost+(ratio R A.k)^q
  let factor:=(R.family.S.a A.k*(M₀))^h
  have live:A.k < N:=by omega
  have cA:=half (Real.exp_pos _).le ((L₀).params A.k).columns_ge gate
  have cB:=half (Real.exp_pos _).le ((L₀).params B.k).columns_ge next
  have pos:0 ≤ (t₀):=(inv_pos.mpr (shrink_pos R.family R.makes live.le p)).le
  have newer:0 ≤ (t₁):=(inv_pos.mpr (shrink_pos R.family R.makes top.le p)).le
  have hot:(t₁)^q ≤ peak R B.k q:=pow_le_pow_left₀ newer (shrink_min R.family R.makes top.le p) q
  have magnify:0 ≤ ((R.family.S.a B.k)*(M₁))^h:=pow_nonneg (mul_nonneg (R.family.S.a_pos _).le (Station.mag_pos ..).le) _
  have income:purse R N p A.k B.k h q (M₀) (M₁) ≤ wallet:=mul_le_mul_of_nonneg_left hot (pow_nonneg
    (div_nonneg (mul_nonneg (R.family.S.a_pos _).le (Station.mag_pos ..).le)
      (mul_nonneg (R.family.S.a_pos _).le (Station.mag_pos ..).le)) _)
  have topPaid:=WilsonPhysicalStationEndpointFactor.start R B (b₀) (p:=p) cb top a
  rw [weight] at topPaid
  have cap:row R h N p B.k h q (M₁) ≤ source:=by
    change _ ≤ (R.family.S.a B.k*(M₁))^h*peak R B.k q
    unfold row;rw [mul_pow]
    rw [mul_pow] at magnify
    exact (le_of_eq (by ring)).trans (mul_le_mul_of_nonneg_left hot magnify)
  have high:datedMass R h N p y B.k ≤ 2*source:=double (size_nonneg ..) cB (topPaid.trans cap)
  have bag:=WilsonPhysicalStationReferenceSalary.bag a (filed R A (a₀) N p Z) χ (fun i=>( (F₀).grades i).2)
    (WilsonPhysicalStationFiledGate.refund R B) pos
    (WilsonPhysicalStationWeightedAxis.principal R A B h da (p:=p) dates top q) cells
  let w:= ∑i,‖filed R A (a₀) N p Z i‖*(t₀)^((F₀).grades i).2
  have wu:0 ≤ use:=by
    have pay:=WilsonPhysicalStationWeightedAxis.positive R A.k B.k h
    have θ:=div_nonneg ((L₀).budget A.k).threshold_pos.le ((L₀).budget (A.k+1)).threshold_pos.le
    change 0 ≤ (Fintype.card (F₀).Index:ℝ)*rate R A.k B.k h+(ratio R A.k)^q
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) pay) (pow_nonneg θ _)
  have w₀:0 ≤ w:=sum_nonneg fun _ _=>mul_nonneg (norm_nonneg _) (pow_nonneg pos _)
  have debit:w ≤ 2*(use*wallet):=double w₀ cB (bag.trans (mul_le_mul_of_nonneg_left income wu))
  have register:=WilsonPhysicalStationReferenceSalary.coffer R A (a₀) e (p:=p) live.le horizon Z cleared
  change μ (measured R A (a₀) N p Z)=factor*w at register
  have f₀:0 ≤ factor:=pow_nonneg (mul_nonneg (R.family.S.a_pos _).le (Station.mag_pos ..).le) _
  let v:= (incoming R h N p Z A.k).x
  have pay:=WilsonPhysicalStationRawReading.original R A (a₀) Z (p:=p) ca live
  change μ (v-measured R A (a₀) N p Z) ≤ err R A.k*μ v at pay
  have eqn:=Extra.Histories.Size.add (F₀) (v-measured R A (a₀) N p Z) (measured R A (a₀) N p Z)
  rw [sub_add_cancel,register] at eqn
  have old:(1-err R A.k)*μ v ≤ factor*w:=by linarith only [eqn,pay]
  have low:datedMass R h N p Z A.k ≤ 4*factor*(use*wallet):=
    (double (size_nonneg ..) cA old).trans
      ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left debit f₀) (by norm_num:0 ≤ (2:ℝ))).trans_eq (by ring))
  have H₁:=WilsonPhysicalStationReferenceSalary.original R h B.k N p y (cb.early (b₀)) top.le
  have H₀:=WilsonPhysicalStationReferenceSalary.original R h A.k N p Z (ca.early (a₀)) live.le
  have scale (i:ℕ):0 ≤ span R r i^(h+1):=pow_nonneg (div_nonneg (R.family.S.a_pos _).le (R.family.S.a_pos _).le) _
  have res:=norm_sub_le y Z
  rw [show y-Z=(K₀).terminal W by exact sub_sub_cancel ..] at res
  exact res.trans (add_le_add (H₁.trans (mul_le_mul_of_nonneg_left high (scale B.k)))
    (H₀.trans (mul_le_mul_of_nonneg_left low (scale A.k))))

end YM.Integration.WilsonPhysicalStationUniformLower
end
