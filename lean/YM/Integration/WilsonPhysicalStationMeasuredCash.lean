import YM.Integration.WilsonPhysicalStationMeasuredEar
import YM.Integration.WilsonIndependentRegisteredActuators
import YM.Integration.WilsonPhysicalStationObservedEntry
import YM.Integration.WilsonPhysicalStationResidualWallet
import YM.Integration.WilsonPhysicalStationDetectorCurrency

/-! One actual station ratio pays the thermal weight once at the final
detector. The homogeneous geometric and kinetic factors remain explicit. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMeasuredCash
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
open WilsonPhysicalStationThermalPair (cell)
open WilsonPhysicalStationTableJump (pair)
open Next.Rank Next.Rank.Tapes Next.Rank.Tapes.West Rise Alarm Paint Next.Rank.Station Glimmer
open Ward MergeProof.Accent Next.Rank.Ribbon
open scoped BigOperators Classical Topology

variable {G:Gauge} (R:Run G) {T:Campaign R} (L:Pillars R T) {f:Extraction.Order} {S:Table R.family.book}
  (fac:Facilities R.family f S) {H:(Bel R.family.book).Hierarchy}
  {D D':ℕ} (A:Vane R.family D) (B:Vane R.family D') {N p:ℕ}
  (h e:ℕ) (da:h   <   D+1) (db:h   <   D'+1)
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



open WilsonPhysicalStationObservedEntry (born)
open WilsonPhysicalStationSelectedLower (Receipt)
local notation "T₀" => (L₀).clock.monitor A.k


open WilsonPhysicalStationMeasuredEar (signed)
def aperture (m k h:ℕ)(a b:ℝ):ℝ:=((R.family.S.a k*b)/(R.family.S.a m*a))^h

theorem unbrake {E x P U fee z:ℝ} (q Q:ℕ)(fit:q ≤ Q)(ep:0 ≤ E)(amount:0 ≤ x)(money:0 ≤ fee)
    (room:1 ≤ P)(up:0 ≤ U)(advance:U ≤ 6*P)(slack:1/2 ≤ 1-z)
    (paid:(1-z)*x*P^Q ≤  E*U^q*fee) : x ≤ 2*E*6^q*fee:=by
  have hp:0 < P:=by linarith
  have paid':(1/2)*x*P^Q ≤ E*U^q*fee:=by
    apply le_trans _ paid
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right slack amount) (pow_nonneg hp.le _)
  have raised:U^q ≤ 6^q*P^Q:=by
    calc
     U^q ≤ (6*P)^q:=pow_le_pow_left₀ up advance _
     _=6^q*P^q:=mul_pow ..
     _ ≤ 6^q*P^Q:=mul_le_mul_of_nonneg_left (pow_le_pow_right₀ room fit) (by positivity)
  have pay:=paid'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left raised ep) money)
  have finished:x*P^Q ≤ (2*E*6^q*fee)*P^Q:=by nlinarith only [pay]
  exact le_of_mul_le_mul_right finished (pow_pos hp Q)

theorem original (cb:B.checked f H D')(dates:B.k=A.k+1)
    (top:B.k < N)(a:(F₀).Index)(W:R.family.label h)(x:Points 2)(z:(standard R.family).Field h)
    (Q:ℕ)(fit:((F₀).grades a).2 ≤ Q)(bill κ:ℝ)(money:0 ≤ bill)(large:4 ≤ T₀)
    (gate:(C₁)*err R B.k ≤ 1/2)
    (heated:shrink R.family A.k N p ≤ 6*shrink R.family B.k N p)
    (ear:signed R A B h da db (p:=p) cb top a W x z Q bill κ):
    let q:=((F₀).grades a).2
    let E:=aperture R A.k B.k h (M₀) (M₁)
    let Γ:=born R h (tested (L₀) A.b A.k x) z
    let ρ:=rate R A.k B.k h
    let χ:ℂ:=signal R N p A.k B.k h q (M₀) (M₁)
    let y:=entered R B (b₀) (p:=p) cb top (Pi.single a 1)
    let actual:=WilsonPhysicalStationTableJump.pair R (a₀) N p A.k (choose (L₀) A.b A.k x)
      (y-(K₀).terminal W) (A.wheel.atCut (N,p) (a₀) z)
    ‖actual-χ*Γ a‖ ≤ 2*E*6^q*
      (bill*4^Q*(T₀)^(-κ)*((ratio R A.k)^q+Fintype.card (F₀).Index*ρ)+ρ*∑i,‖Γ i‖):=by
  intro q E Γ ρ χ y actual
  have live:A.k < N:=by omega
  obtain ⟨pos,_,gain⟩:=WilsonPhysicalStationDetectorCurrency.original R p live.le
  have next:=shrink_pos R.family R.makes top.le p
  have now:=shrink_pos R.family R.makes live.le p
  have act:t₁ ≤ 6*t₀:=by
    rw [←one_div,←div_eq_mul_inv]
    exact (div_le_div_iff₀ next now).2 (by simpa using heated)
  have half:1/2 ≤ 1-err R B.k:=by
    have z:0 ≤ err R B.k:=(Real.exp_pos _).le
    have one:=((L₀).params B.k).columns_ge
    linarith only [gate,le_mul_of_one_le_left z one]
  have geometry:0 ≤ E:=pow_nonneg
    (div_nonneg (mul_nonneg (R.family.S.a_pos _).le (Station.mag_pos ..).le)
      (mul_nonneg (R.family.S.a_pos _).le (Station.mag_pos ..).le)) _
  have rnon:0 ≤ ρ:=WilsonPhysicalStationWeightedAxis.positive R ..
  have tnon:0 ≤ ratio R A.k:=div_nonneg ((L₀).budget _).threshold_pos.le ((L₀).budget _).threshold_pos.le
  have tot:0 ≤ ∑i,‖Γ i‖:=Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  have polar:0 ≤ (T₀)^(-κ):=Real.rpow_nonneg (Real.exp_pos _).le _
  apply unbrake q Q fit geometry (norm_nonneg _) (by positivity) (P:=t₀) (U:=t₁) (z:=err R B.k)
    (by linarith only [large,gain]) (inv_pos.mpr next).le act half
  exact ear

end YM.Integration.WilsonPhysicalStationMeasuredCash
end
