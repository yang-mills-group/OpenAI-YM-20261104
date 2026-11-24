import YM.Integration.WilsonPhysicalStationRestoredEntry

/-! The actual equal-weight filed coordinate with one end compensation.
The physical kinetic ratio is kept at this same cutoff and period. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationWeightedAxis
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

def purse (N p m k h q:ℕ) (a b:ℝ):ℝ:=
  ((R.family.S.a k*b)/(R.family.S.a m*a))^h * ((shrink R.family k N p)⁻¹)^q

theorem exchange (top:A.k ≤ N) (q z:ℕ):
    charge R h N p A.k B.k h q z (M₀) (M₁)*(t₀)^z=
      purse R N p A.k B.k h q (M₀) (M₁):=by
  have spacing:0 < R.family.S.a A.k:=R.family.S.a_pos _
  have magnifier:0 < (M₀):=Station.mag_pos ..
  have regulator:0 < t₀:=inv_pos.mpr (shrink_pos R.family R.makes top p)
  unfold WilsonPhysicalStationEndCurrency.charge row purse
  rw [div_pow,mul_pow,mul_pow]
  field_simp
  exact mul_div_cancel_right₀ _ (pow_ne_zero z (one_div_pos.mpr (shrink_pos R.family R.makes top p)).ne')

theorem positive (m k h:ℕ):0 ≤ rate R m k h:=by
  have cm:0 ≤ ((L₀).params m).columns:=zero_le_one.trans ((L₀).params m).columns_ge
  have cn:0 ≤ ((L₀).params k).columns:=zero_le_one.trans ((L₀).params k).columns_ge
  have e₀:0 ≤ err R m:=(Real.exp_pos _).le
  have e₁:0 ≤ err R k:=(Real.exp_pos _).le
  have δ:0 ≤ barunit (R.family.S.block m):=by unfold barunit puffs;positivity
  have cap:=WilsonPhysicalStationRegisteredDiagonal.ceiling_nonneg ((R.family.labels.level h)) (ratio R m)
  change 0 ≤ (1+2*((L₀).params m).columns*(1+err R m))*((err R m*(ceiling _ (ratio R m)+_)+_)*
    (1+err R k+(1+((L₀).params k).columns)*err R k)+ceiling _ (ratio R m)*((1+((L₀).params k).columns)*err R k))
  positivity

include da in
theorem principal (dates:B.k=A.k+1) (top:B.k < N) (q:ℕ):
    (1-err R B.k)*‖(signal R N p A.k B.k h q (M₀) (M₁):ℂ)‖*(t₀)^q ≤ 
      (ratio R A.k)^q*purse R N p A.k B.k h q (M₀) (M₁):=by
  let χ:=signal R N p A.k B.k h q (M₀) (M₁)
  have actual:=WilsonPhysicalStationRestoredEntry.factor R A B h da (p:=p) dates top q
  have o:=WilsonPhysicalStationEndpointFactor.row_pos R A (a₀) (p:=p) (show A.k ≤ N by omega) h q
  have signalpos:0 ≤ χ:=by
    dsimp [χ,signal]; exact mul_nonneg (pow_nonneg (div_nonneg (mul_nonneg (R.family.S.a_pos _).le (Station.mag_pos ..).le)
      (mul_nonneg (R.family.S.a_pos _).le (Station.mag_pos ..).le)) _) (pow_nonneg
        (div_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_nonneg.mpr (Real.sqrt_nonneg _))) _)
  have id:χ=(ratio R A.k)^q*charge R h N p A.k B.k h q q (M₀) (M₁):=by
    unfold WilsonPhysicalStationEndCurrency.charge
    apply (mul_left_cancel₀ o.ne')
    calc
      _= (ratio R A.k)^q*row R h N p B.k h q (M₁):=actual
      _=_:=by field_simp
  have refund:1-err R B.k ≤ 1:=sub_le_self _ (Real.exp_pos _).le
  change (1-err R B.k)*‖(χ:ℂ)‖*(t₀)^q ≤ _
  rw [Complex.norm_real,Real.norm_of_nonneg signalpos]
  have paid:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right refund signalpos)
    (pow_nonneg (inv_pos.mpr (shrink_pos R.family R.makes (show A.k ≤ N by omega) p)).le q)
  rw [one_mul] at paid
  apply paid.trans_eq
  rw [id,mul_assoc,exchange R A B h (p:=p) (show A.k ≤ N by omega) q q]

include L fac in
theorem original (hg:G.Simple) (ca:A.checked f H D) (cb:B.checked f H D')
    (dates:B.k=A.k+1) (top:B.k < N) (horizon:h=e+1)
    (gate:(C₀)*err R A.k ≤ 1/2) (a:(F₀).Index) (weight:((F₀).grades a).1=h):
    let s:R.family.label h:=Pi.single a 1
    let y:=entered R B (b₀) (p:=p) cb top s
    let q:=((F₀).grades a).2
    ∃ W:R.family.label h,(P₀) W=W ∧ (P₀) (A.R N p (a₀) (y-(K₀).terminal W))=0 ∧
      ∀ i:(F₀).Index, (1-err R B.k)*‖filed R A (a₀) N p (y-(K₀).terminal W) i-
        (signal R N p A.k B.k h q (M₀) (M₁):ℂ)*s i‖*(t₀)^((F₀).grades i).2  ≤ 
        rate R A.k B.k h *purse R N p A.k B.k h q (M₀) (M₁):=by
  intro s y q
  have room:A.k ≤ N:=by omega
  have heat:0 < t₀:=inv_pos.mpr (shrink_pos R.family R.makes room p)
  obtain ⟨W,low,cleared,receipt⟩:=WilsonPhysicalStationRestoredEntry.original R L fac A B h e da db (p:=p)
    hg ca cb dates top horizon gate a weight
  refine ⟨W,low,cleared,?_⟩
  intro i
  by_cases atTop:((F₀).grades i).1=h
  · let j:=((F₀).grades i).2
    have buy:=mul_le_mul_of_nonneg_right (receipt i atTop) (pow_nonneg heat.le j)
    rw [mul_assoc (rate R A.k B.k h),exchange R A B h (p:=p) room q j] at buy
    change (1-err R B.k)*‖_-(signal R N p A.k B.k h q (M₀) (M₁):ℂ)*s i‖*(t₀)^j  ≤  _
    by_cases same:i=a
    · subst i;exact buy
    · have empty:s i=0:=Pi.single_eq_of_ne same _
      have explicit:(Pi.single a (1:ℂ):(F₀).Coeff) i=0:=empty
      simpa only [empty,explicit,mul_zero,sub_zero] using buy
  · have dead:=WilsonPhysicalStationHorizontalWallet.fromLower (F₀) e _ cleared horizon i
      (lt_of_le_of_ne ((F₀).bound i) atTop)
    have filedZero:filed R A (a₀) N p (y-(K₀).terminal W) i=0:=by
      change (_:ℂ)^_*((_:ℂ)*A.R N p (a₀) (y-(K₀).terminal W) i)=0
      rw [dead,mul_zero,mul_zero]
    have empty:s i=0:=Pi.single_eq_of_ne (show i≠a by rintro rfl;exact atTop weight) _
    rw [filedZero,empty,mul_zero,sub_zero,norm_zero,mul_zero,zero_mul]
    apply mul_nonneg (positive R _ _ _)
    exact mul_nonneg (pow_nonneg (div_nonneg (mul_nonneg (R.family.S.a_pos _).le (Station.mag_pos ..).le)
      (mul_nonneg (R.family.S.a_pos _).le (Station.mag_pos ..).le)) _) (pow_nonneg (inv_pos.mpr (shrink_pos R.family R.makes top.le p)).le _)

end YM.Integration.WilsonPhysicalStationWeightedAxis
end
