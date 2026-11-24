import YM.Integration.WilsonPhysicalStationWeightedAxis
import YM.Integration.WilsonPhysicalStationCoincidentEntry

/-! Retain every raw filed coordinate, including the physical lower correction, at two distinct hearings of the same original date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationCoincidentAxis
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
open scoped BigOperators Classical Topology

variable {G:Gauge} (R:Run G) {T:Campaign R} (L:Pillars R T) {f:Extraction.Order} {S:Table R.family.book}
  (fac:Facilities R.family f S) {H:(Bel R.family.book).Hierarchy}
  {D D':ℕ} (A:Vane R.family D) (B:Vane R.family D') {N p:ℕ}
  (h e:ℕ) (da:h < D+1) (db:h < D'+1)
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

open WilsonPhysicalStationWeightedAxis (purse exchange)
open WilsonPhysicalStationCoincidentEntry (rent)
open WilsonPhysicalStationMeasuredCash (aperture)

theorem principal (dates:B.k=A.k) (top:B.k < N) (q:ℕ):
    (1-err R B.k)*‖(aperture R A.k B.k h (M₀) (M₁):ℂ)‖*(t₀)^q ≤
    1*purse R N p A.k B.k h q (M₀) (M₁):=by
  have z:0 ≤ aperture R A.k B.k h (M₀) (M₁):=pow_nonneg (div_nonneg
    (mul_nonneg (R.family.S.a_pos _).le (Station.mag_pos ..).le)
    (mul_nonneg (R.family.S.a_pos _).le (Station.mag_pos ..).le)) _
  have hp:0 ≤ (t₀)^q:=pow_nonneg (inv_pos.mpr (shrink_pos R.family R.makes (show A.k ≤ N by omega) p)).le _
  rw [Complex.norm_real,Real.norm_of_nonneg z,one_mul]
  calc
    _ ≤ (aperture R A.k B.k h (M₀) (M₁))*(t₀)^q:=by
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left z (sub_le_self _ (Real.exp_pos _).le)) hp
    _ = _:=by unfold WilsonPhysicalStationMeasuredCash.aperture purse; rw [dates]

include fac in
theorem original (ca:A.checked f H D) (cb:B.checked f H D')
    (dates:B.k=A.k) (top:B.k < N) (horizon:h=e+1)
    (gate:(C₀)*err R A.k ≤ 1/2) (a:(F₀).Index) (weight:((F₀).grades a).1=h):
    let s:R.family.label h:=Pi.single a 1
    let y:=entered R B (b₀) (p:=p) cb top s
    let q:=((F₀).grades a).2
    ∃ W:R.family.label h,(P₀) W=W ∧ (P₀) (A.R N p (a₀) (y-(K₀).terminal W))=0 ∧
      ∀ i:(F₀).Index, (1-err R B.k)*‖filed R A (a₀) N p (y-(K₀).terminal W) i-
        (aperture R A.k B.k h (M₀) (M₁):ℂ)*s i‖*(t₀)^((F₀).grades i).2  ≤ 
        rent R A.k *purse R N p A.k B.k h q (M₀) (M₁):=by
  intro s y q
  have room:A.k ≤ N:=by omega
  have heat:0 < t₀:=inv_pos.mpr (shrink_pos R.family R.makes room p)
  obtain ⟨W,low,cleared,receipt⟩:=WilsonPhysicalStationCoincidentEntry.original R fac A B h e da db (p:=p)
    ca cb dates top horizon gate a weight
  refine ⟨W,low,cleared,?_⟩
  intro i
  by_cases atTop:((F₀).grades i).1=h
  · let j:=((F₀).grades i).2
    have buy:=mul_le_mul_of_nonneg_right (receipt i atTop) (pow_nonneg heat.le j)
    rw [mul_assoc (rent R A.k),exchange R A B h (p:=p) room q j] at buy
    change (1-err R B.k)*‖_-(aperture R A.k B.k h (M₀) (M₁):ℂ)*s i‖*(t₀)^j  ≤  _
    exact buy
  · have dead:=WilsonPhysicalStationHorizontalWallet.fromLower (F₀) e _ cleared horizon i
      (lt_of_le_of_ne ((F₀).bound i) atTop)
    have filedZero:filed R A (a₀) N p (y-(K₀).terminal W) i=0:=by
      change (_:ℂ)^_*((_:ℂ)*A.R N p (a₀) (y-(K₀).terminal W) i)=0
      rw [dead,mul_zero,mul_zero]
    have empty:s i=0:=Pi.single_eq_of_ne (show i≠a by rintro rfl;exact atTop weight) _
    rw [filedZero,empty,mul_zero,sub_zero,norm_zero,mul_zero,zero_mul]
    apply mul_nonneg (WilsonPhysicalStationCoincidentEntry.earned R _)
    exact mul_nonneg (pow_nonneg (div_nonneg (mul_nonneg (R.family.S.a_pos _).le (Station.mag_pos ..).le)
      (mul_nonneg (R.family.S.a_pos _).le (Station.mag_pos ..).le)) _) (pow_nonneg (inv_pos.mpr (shrink_pos R.family R.makes top.le p)).le _)

end YM.Integration.WilsonPhysicalStationCoincidentAxis
end
