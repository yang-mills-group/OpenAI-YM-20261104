import YM.Integration.WilsonOriginalGeneralRosterHomePlacement
import YM.Integration.WilsonOriginalGeneralRosterHomeScalar

/-! Flash lodgings: moving upper sizes and absolute gap prices, on the
genuine roster. Variants of WilsonOriginalGeneralRoster* (point version,
including the licensed scalar phase). -/
set_option autoImplicit false
set_option quotPrecheck false

noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterHomePlacement
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Source Extraction Table Spec Trace.Pilot
open Trace.Physical.GermGraph PhysicalNext.Repeat.Legato RG16 RG16.Literal
open WilsonMovingForkOpticalBook (reporter)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonReceivedChronologicalFixedRoseVariation (cells charged)
open WilsonMeasuredPublicEntranceScreen (Ground)
open Climb Maxwell Maxwell.Free Trace.Terrace Trace.Physical Trace.Physical.Germ GapsContact
open scoped Classical BigOperators Topology

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
    {z:Trace.Terrace.Arch R.family}{I:Type}[Fintype I][Nonempty I]

/-- Sites with a separated lift on the genuine reporter mesh. Bounds in physical units. -/
def Grow (R:Run G) (n:ℕ)(box slit:ℝ)(f per:ℕ): Set (Fin n→Site (R.family.side f per)):=
  fun a=>∃ x:Fin n→ Cover, snap R.family f per x=a ∧
    (∀ i, ‖R.family.S.gridPoint f (x i)‖ ≤ box) ∧ Pairwise fun i k=>slit ≤ ‖R.family.S.gridPoint f (x i)-R.family.S.gridPoint f (x k)‖

theorem originalForFlash (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {D T:ℕ}{δ:ℝ}(d:I→Fin (D+1))(books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    {n:ℕ}[Nonempty (Fin n)]{L₀ η:ℝ}(lp:0<L₀)(ep:0<η)(h:ℕ):
    ∃apron:ℕ,∀floor:ℕ,∀ᶠr in trail,∀ρ:I→{s:ℝ//0<s ∧ s<δ},
      (∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let f:=reporter F books ρ
      ∃j:ℕ,floor≤j ∧ j+2≤f ∧ ∀N per,f≤N→∀a:Grow R n (L₀ * outer z h r) (η*r) f per,
        Ground R N per j f apron a.val ∧
        Pairwise fun i k=>(R.family.path.levels.budget f).B^2<separation (a.val i) (a.val k):=by
  classical
  obtain ⟨apron,grounds⟩:=WilsonSeparatedPrefixGridGround.original F simple bliss slow D T h d books lp ep
  refine ⟨apron,fun floor=>(grounds floor).mono ?_⟩
  intro r buy ρ span near f
  obtain ⟨j,late,height,ground⟩:=buy ρ span near
  refine ⟨j,late,height,?_⟩
  intro N per live a
  obtain ⟨x,snap_eq,box,apart⟩:= a.property
  have receipt: Ground R N per j f apron a.val:=snap_eq ▸ (ground (Fin n) N per live x box apart).1
  refine ⟨receipt,?_⟩
  intro i k ne
  have distance:=receipt.2.1 i k ne
  have eq:(R.family.path.rep N per f).p=R.family.path.levels.budget f:=(R.makes.wilson.represents N per f live).vac
  rw [eq] at distance
  exact distance


end YM.Integration.WilsonOriginalGeneralRosterHomePlacement
end

noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterHomeScalar
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open Climb Maxwell Maxwell.Free Trace.Terrace GapsContact PhysicalNext.Repeat.Legato
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonReceivedChronologicalFixedRoseVariation (cells charged)
open WilsonMeasuredPublicEntranceCellWords (physical)
open OPE PhysMS MS MS.Land FVA2 FVA2.Register Next.Extract GapsContact.Seams GapsContact.Ascent
open RG16 RG16.Literal RG05Readout RG05Readout.Address RG05Readout.Records Marker
open scoped Classical BigOperators Topology

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {I:Type}[Fintype I][Nonempty I]{D T h:ℕ}(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val){n:ℕ}(port:Fin n→I)
local notation "C" => R.family
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "g" => fun i:Fin n=>(d (port i)).val
local notation "modes" => Stock.census (Fin n)

open WilsonOriginalGeneralRosterScalar (gap directPrice)

open WilsonOriginalGeneralRosterHomePlacement (Grow)

theorem originalForFlash (fac:Facilities (C) order S)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {J u:ℕ}(stop:Stop (C) 0 J u){L₀ η:ℝ}(lp:0<L₀)(ep:0<η)(q:ℕ):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ//0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
    let f:=reporter F books ρ
    ∃uf:u≤f,∀N per (deep:f<N)(s:(modes).Mode)(weak:Fin n→Bool)(v:∀i,S.Field ((g) i))
      (a:Grow R n (L₀ * outer z h r) (η*r) f per)(turn:Fin n→Motion),
      let Y:=fun i=>(((books (ρ (port i))).rows (d (port i))).arm (weak i) (v i)).source (N,per)
      ‖gap (R:=R) d port uf deep s Y turn a.val‖≤directPrice F d books port ρ f q weak v s:=by
  classical
  obtain ⟨_,_,_,pkg⟩:=fac.costlier
  obtain ⟨w,house⟩:=WilsonSeparatedPrefixCellHousing.original F fac.simpleGate bliss slow D T h 0 d books L₀ lp
  obtain ⟨gate,invoice⟩:=WilsonPhysicalLicensedSelection.selected F pkg.toPackage fac.simpleGate slow stop d port books w q
  have res:=WilsonSeparatedPrefixMasterResolution.original (I:=I) F fac.simpleGate slow D T books ep
  filter_upwards [house (max (u+2) gate), res] with r home clear
  intro ρ span near f
  obtain ⟨c,late,cf,ratio,inside⟩:=home ρ span near
  have uc:u+2≤c:=(le_max_left ..).trans late
  have uf:u≤f:=by omega
  have license:=invoice ρ c ((le_max_right ..).trans late) uc cf ratio
  refine ⟨uf,?_⟩
  intro N per deep s weak v a turn Y
  by_cases use:s.val.Nonempty
  · obtain ⟨x,hx,box,apart⟩:= a.property
    have inc(i:Fin n)(_ : i∈s.val):8*‖(C).S.gridPoint f (x i)‖≤(C).S.a (c+1):=by
      simp only [Nat.cast_zero,mul_zero,zero_mul,add_zero] at inside
      exact (mul_le_mul_of_nonneg_left (box i) (by norm_num)).trans inside
    have sep:Pairwise fun i k:↥s.val=>2*(C).S.a f*(((C).path.levels.budget f).B:ℝ)^2≤
        ‖(C).S.gridPoint f (x i.val)-(C).S.gridPoint f (x k.val)‖:=
      fun _ _ ne=>(clear ρ near).le.trans (apart fun eq=>ne (Subtype.ext eq))
    have bill:=license s use N per deep x inc sep weak v turn uf
    dsimp only at bill
    rw [Finset.prod_coe_sort s.val (fun i:Fin n=>Motion.orbitCost ((C).labels.level ((g) i))*
      WilsonOriginalTwoFlatPublicFare.charge F ((books (ρ (port i))).rows (d (port i))) f (weak i) (v i))] at bill
    change ‖gap (R:=R) d port uf deep s Y turn (RG16.Literal.snap (C) f per x)‖≤_ at bill
    rwa [hx] at bill
  · have empty:=Finset.not_nonempty_iff_eq_empty.mp use
    have raw:physical R (g) (N:=N) Y turn a.val s=fun _=>1:=by
      funext U
      simp [physical,empty]
    rw [WilsonOriginalGeneralRosterScalar.gap,raw,actualTransport_const (C) R.makes le_rfl (1:ℂ) (uf.trans deep.le) 1]
    rw [show (C).omega N per (fun _=>1)=1 by simp [Family.omega,Wilson.moment]]
    simp only [sub_self,norm_zero,WilsonOriginalGeneralRosterScalar.directPrice,empty,Finset.prod_empty,one_mul]
    exact inv_nonneg.mpr (pow_nonneg ((zero_le_one.trans ((C).path.levels.fits.delayed f).le)) _)


end YM.Integration.WilsonOriginalGeneralRosterHomeScalar
end
