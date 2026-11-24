import YM.Integration.WilsonPhysicalShiftedLicensedHead
import YM.Integration.WilsonMovingForkMeasuredWindow
import YM.Integration.WilsonReflectedMixedMasterSchool
import YM.Integration.WilsonViewerElectedHierarchy

/-! Restore the actual public source bills in the measured position coupling
linked to the originally elected hierarchy, for either weak prescription and every proper face. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalElectedSourceFare
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace
open GapsContact GapsContact.Seams GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonMeasuredPublicEntranceCellWords (physical)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}

local notation "C₀" => R.family
local notation "a_" => R.family.S.a
local notation "β" => (C₀).path.levels.clock.hatBeta

universe u
open RG17 PhysMS EveryPhase OPE.Orbits OPE.Log
open MS MS.Land FVA2 FVA2.Register Pert.Asymptotics
open WilsonThermometerUnitFilingFourPoolClock (outer)
variable (J:ℝ→tower S)(Z:WilsonPrescription G)
theorem original {I:Type}[Fintype I][Nonempty I]{simple:G.Simple}{course:Almanac F}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}{cohort:Ultrafilter (ℕ×ℕ)→Prop}
    (run:WilsonViewerElectedHierarchy.Selected.{u} F course Q J H z l simple cohort)
    (slow:WilsonWindowReportingPace.Slow R.kit)
    (clock:Coupling G (WilsonPositionHomogeneousFrame.reading F J Z))
    (D T h:ℕ)(d:I→Fin (D+1))(y:∀i,(Spin.comparator (C₀).book).Field (d i).val)
    (x:∀i,RG17.Free C₀ (d i).val){δ:ℝ}
    (books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (admit:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃M:I→ℝ,∃E:I→ℕ,(∀i,1≤M i) ∧ ∀p:ℕ,∀ᶠr in trail,
      ∀ρ:I→{s:ℝ //0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let f:=reporter F books ρ
      ∀{n:ℕ}(select:Fin n→I)(s:(Stock.census (Fin n)).Mode)(weak mode:Fin n→Bool) (q:ℕ),
      (∑i:↥s.val,E (select i.val))+2*(2*p)≤q →
      let field:=WilsonReflectedMixedMasterSchool.field F J Z D T d y x books
      let bill(i:Fin n):=Motion.orbitCost ((C₀).labels.level (d (select i)).val)*
        charge F ((books (ρ (select i))).rows (d (select i))) f (weak i)
          (field (select i) (ρ (select i)) (mode i) (weak i))
      (∏i:↥s.val,bill i.val)*((β f)^q)⁻¹ ≤
        (∏i:↥s.val,M (select i.val))*(WilsonPositionHomogeneousFrame.reading F J Z r)^p:=by
  classical
  obtain ⟨Mn,En,nb,named⟩:=WilsonAddressedMixedNamedIncome.original F J Z simple run.bliss slow run.leading run.obeys D T h d y x books
  obtain ⟨Mh,Eh,hb,homed⟩:=WilsonMovingForkHomeIncome.original F J Z simple run.bliss slow run.leading run.obeys D T h d x books admit
  let A(i:I):=max (Mn i) (Mh i)
  let E(i:I):=max (En i) (Eh i)
  let O(i:I):=Motion.orbitCost ((C₀).labels.level (d i).val)
  let M(i:I):=O i*A i
  have o₁(i:I):1≤O i:=Motion.orbitCost_one_le _
  have a₁(i:I):1≤A i:=(nb i).trans (le_max_left ..)
  have m₁(i:I):1≤M i:=one_le_mul_of_one_le_of_one_le (o₁ i) (a₁ i)
  refine ⟨M,E,m₁,?_⟩
  intro p
  let link:=wilson_link F simple run.bliss.budgets run.bliss.keen run.bliss.lies
  filter_upwards [named,homed,WilsonOriginalTwoFlatPublicOuter.original F simple run.bliss (2*p),
    WilsonMovingForkMeasuredWindow.room simple link clock,link.positive] with r nr hr gp compare pos
  intro ρ span near f n select s weak mode q enough field bill
  obtain ⟨i₀,eq⟩:=near
  have home: a_ f≤r:=by
    have past:=WilsonMovingForkOpticalBook.station_le F books ρ i₀ (d i₀) true
    change (books (ρ i₀)).W.k≤f at past
    exact ((C₀).S.strictAnti.antitone past).trans (((WilsonReflectedPublicBulbBerth.mesh R _ (books (ρ i₀)).checked).trans (books (ρ i₀)).active.le).trans eq.le)
  have bp:1≤β f:=((C₀).path.levels.fits.delayed f).le
  have bpos:0<β f:=zero_lt_one.trans_le bp
  have each(i:Fin n):bill i≤M (select i)*(β f)^(E (select i)):=by
    let j:=select i
    have instanceBill:charge F ((books (ρ j)).rows (d j)) f (weak i) (field j (ρ j) (mode i) (weak i))≤A j*(β f)^(E j):=by
      cases eqm:mode i
      · have old:=(nr ρ span ⟨i₀,eq⟩ (fun _=>weak i) j).2.2
        exact old.trans (mul_le_mul (le_max_left ..) (pow_le_pow_right₀ bp (le_max_left ..))
          (pow_nonneg bpos.le _) (zero_le_one.trans (a₁ j)))
      · have old:=(hr ρ span ⟨i₀,eq⟩ (fun _=>weak i) j).2.2
        exact old.trans (mul_le_mul (le_max_right ..) (pow_le_pow_right₀ bp (le_max_right ..))
          (pow_nonneg bpos.le _) (zero_le_one.trans (a₁ j)))
    simpa only [M,mul_assoc] using mul_le_mul_of_nonneg_left instanceBill (zero_le_one.trans (o₁ j))
  let reserve:=∑i:↥s.val,E (select i.val)
  let constant:=∏i:↥s.val,M (select i.val)
  have positive(i:Fin n):0≤bill i:=mul_nonneg (zero_le_one.trans (o₁ _)) (zero_le_one.trans (le_max_left ..))
  have cp:0≤constant:=Finset.prod_nonneg fun i _=>zero_le_one.trans (m₁ _)
  have product:(∏i:↥s.val,bill i.val)≤constant*(β f)^reserve:=by
    calc
      _ ≤ ∏i:↥s.val,M (select i.val)*(β f)^(E (select i.val)):=Finset.prod_le_prod (fun i _=>positive _) (fun i _=>each _)
      _ = _:=by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  have clockPrice:((wilson z r)⁻¹)^(2*p)≤(β f)^(2*(2*p)):=by
    apply (mul_le_mul_iff_of_pos_left gp.1).mp
    simpa only [outer,mul_comm ((β f)^(2*(2*p))) r] using gp.2.2 f home
  have rate:((β f)^(2*(2*p)))⁻¹≤(wilson z r)^(2*p):=by
    simpa only [←inv_pow,inv_inv] using inv_anti₀ (pow_pos (inv_pos.mpr pos) (2*p)) clockPrice
  calc
    _ ≤ (constant*(β f)^reserve)*((β f)^(reserve+2*(2*p)))⁻¹:=mul_le_mul product
      (inv_anti₀ (pow_pos bpos _) (pow_le_pow_right₀ bp enough)) (inv_nonneg.mpr (pow_nonneg bpos.le _)) (mul_nonneg cp (pow_nonneg bpos.le _))
    _ = constant*((β f)^(2*(2*p)))⁻¹:=by rw [pow_add,mul_inv_rev];field_simp [bpos.ne']
    _ ≤ constant*(wilson z r)^(2*p):=mul_le_mul_of_nonneg_left rate cp
    _ ≤ _:=by rw [pow_mul];exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (pow_nonneg pos.le 2) compare _) cp

end YM.Integration.WilsonPhysicalElectedSourceFare
end
