import YM.Integration.WilsonPhysicalStationRestoredEntry
import YM.Integration.WilsonPhysicalStationMeasuredCash
import YM.Integration.WilsonPhysicalStationSameFiling

/-! Equal dates may retain different measured books. Their raw inputs share
one original factory and thermal regulator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationCoincidentEntry
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

local notation "M₀" => Station.mag (L₀) A.b A.k
local notation "M₁" => Station.mag (L₀) B.b B.k


open WilsonPhysicalStationMeasuredCash (aperture)
def rent (m:ℕ):ℝ:=(1+2*((L₀).params m).columns*(1+err R m))*(2*err R m)
theorem earned (m:ℕ):0 ≤ rent R m:=by
  have hn:=zero_le_one.trans ((L₀).params m).columns_ge
  have hp:0 ≤ err R m:=(Real.exp_pos _).le
  unfold rent
  positivity

theorem factor (dates:B.k=A.k) (top:B.k < N) (q:ℕ):
    row R h N p A.k h q (M₀)*aperture R A.k B.k h (M₀) (M₁)=row R h N p B.k h q (M₁):=by
  have a:0 < R.family.S.a A.k:=R.family.S.a_pos _
  have u:0 < shrink R.family A.k N p:=shrink_pos R.family R.makes (by omega) p
  have z:0 < (M₀):=Station.mag_pos ..
  rw [dates]
  unfold WilsonPhysicalStationMeasuredCash.aperture row
  simp only [div_pow,mul_pow]
  field_simp [a.ne',u.ne',z.ne']

theorem read (cb:B.checked f H D') (dates:B.k=A.k)
    (top:B.k<N) (s z:R.family.label h) (i:(F₀).Index) (weight:((F₀).grades i).1=h):
    let q:=((F₀).grades i).2
    let y:=entered R B (b₀) (p:=p) cb top s
    row R h N p A.k h q (M₀)*
        ‖filed R A (a₀) N p z i- (aperture R A.k B.k h (M₀) (M₁):ℂ)*s i‖ ≤
      μ (measured R A (a₀) N p z-measured R B (b₀) N p y) := by
  intro q y
  let v:=measured R A (a₀) N p z-measured R B (b₀) N p y
  have old:=WilsonPhysicalStationEndpointFactor.written R A (a₀) (p:=p) (show A.k≤N by omega) z i
  have fine:=WilsonPhysicalStationEndpointFactor.entrance R B (b₀) (p:=p) cb top s i
  change measured R A (a₀) N p z i=(row R h N p A.k ((F₀).grades i).1 q (M₀):ℂ)*_ at old
  change measured R B (b₀) N p y i=(row R h N p B.k ((F₀).grades i).1 q (M₁):ℂ)*_ at fine
  rw [weight] at old fine
  have scalar:(row R h N p A.k h q (M₀):ℂ)*(aperture R A.k B.k h (M₀) (M₁):ℂ)=
      (row R h N p B.k h q (M₁):ℂ):=by
    exact_mod_cast factor R A B h (p:=p) dates top q
  have id:v i = (row R h N p A.k h q (M₀):ℂ)*
      (filed R A (a₀) N p z i-(aperture R A.k B.k h (M₀) (M₁):ℂ)*s i):=by
    change measured R A (a₀) N p z i- measured R B (b₀) N p y i=_
    rw [old,fine,mul_sub,←mul_assoc,scalar]
  have one:‖v i‖≤μ v:=Finset.single_le_sum (f:=fun l:(F₀).Index=>‖v l‖)
    (fun _ _=>norm_nonneg _) (Finset.mem_univ i)
  rw [id,norm_mul,Complex.norm_real,Real.norm_of_nonneg (WilsonPhysicalStationEndpointFactor.row_pos R A (a₀)
      (p:=p) (by omega) h q).le] at one
  exact one

include fac in
theorem original (ca:A.checked f H D) (cb:B.checked f H D')
    (dates:B.k=A.k) (top:B.k<N) (horizon:h=e+1)
    (gate:(C₀)*err R A.k≤1/2) (a:(F₀).Index) (weight:((F₀).grades a).1=h):
    let s:R.family.label h:=Pi.single a 1
    let y:=entered R B (b₀) (p:=p) cb top s
    ∃ W:R.family.label h,(P₀) W=W ∧ (P₀) (A.R N p (a₀) (y-(K₀).terminal W))=0 ∧
      ∀ i:(F₀).Index, ((F₀).grades i).1=h →
      let qi:=((F₀).grades i).2
      let q:=((F₀).grades a).2
      (1-err R B.k)*‖filed R A (a₀) N p (y-(K₀).terminal W) i-
        (aperture R A.k B.k h (M₀) (M₁):ℂ)*s i‖ ≤
        rent R A.k*charge R h N p A.k B.k h q qi (M₀) (M₁) := by
  intro s y
  have low:(P₀) s=0:=by
    ext j
    by_cases hi:((F₀).grades j).1≤e
    · have ne:j≠a:=by rintro rfl;omega
      simp [Columns.low_apply,hi,s,Pi.single_eq_of_ne ne]
    · simp [Columns.low_apply,hi]
  have start:=WilsonPhysicalStationFineCorrection.entered R B (b₀) e (p:=p) cb top s low
  obtain ⟨W,lower,fitted,_,paid⟩:=WilsonPhysicalStationSameFiling.original R fac A B h e da db
    (p:=p) ca cb dates (by omega) (by omega) gate y start
  have pledge:μ (measured R A (a₀) N p (y-(K₀).terminal W)-measured R B (b₀) N p y)
      ≤ rent R A.k*μ (incoming R h N p y B.k).x:=by
    exact paid.trans_eq (congrArg (fun j=>rent R A.k*μ (incoming R h N p y j).x) dates.symm)
  refine ⟨W,lower,fitted,?_⟩
  intro i wi qi q
  let k:=row R h N p B.k h q (M₁)
  let m:=row R h N p A.k h qi (M₀)
  let ρ:=rent R A.k
  let x:=‖filed R A (a₀) N p (y-(K₀).terminal W) i-
        (aperture R A.k B.k h (M₀) (M₁):ℂ)*s i‖
  have head:=read R A B h da db (p:=p) cb dates top s (y-(K₀).terminal W) i wi
  have lowRow:m*x≤ρ*μ (incoming R h N p y B.k).x:=head.trans pledge
  have capital: (1-err R B.k)*μ (incoming R h N p y B.k).x≤k:=by
    have hn:=WilsonPhysicalStationEndpointFactor.start R B (b₀) (p:=p) cb top a
    change _≤row R h N p B.k ((F₀).grades a).1 q (M₁) at hn
    rw [weight] at hn
    exact hn
  have hm:0 < m:=WilsonPhysicalStationEndpointFactor.row_pos R A (a₀) (p:=p) (by omega) h qi
  have hρ:0 ≤ ρ:=earned R A.k
  change (1-err R B.k)*x≤ρ*(k/m)
  rw [←mul_div_assoc]
  apply (le_div_iff₀ hm).mpr
  calc
    _=(1-err R B.k)*(m*x):=by ring
    _≤(1-err R B.k)*(ρ*μ (incoming R h N p y B.k).x):=
      mul_le_mul_of_nonneg_left lowRow (WilsonPhysicalStationFiledGate.refund R B)
    _=ρ*((1-err R B.k)*μ (incoming R h N p y B.k).x):=by ring
    _≤_:=mul_le_mul_of_nonneg_left capital hρ

end YM.Integration.WilsonPhysicalStationCoincidentEntry
end
