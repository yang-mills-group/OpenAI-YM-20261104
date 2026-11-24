import YM.Integration.WilsonOriginalGeneralRosterScalar

/-! The unrestricted original phase at an independently selected test radius inside the physical market. -/
set_option autoImplicit false
set_option quotPrecheck false
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

theorem original (fac:Facilities (C) order S)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {J u:ℕ}(stop:Stop (C) 0 J u)(φ:Test n)(q:ℕ):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ//0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
    let f:=reporter F books ρ
    ∀ scale : ℝ, r ≤ scale → scale ≤ outer z h r → ∃uf:u≤f,∀N per (deep:f<N)(s:(modes).Mode)(weak:Fin n→Bool)(v:∀i,S.Field ((g) i))
      (a:cells R φ scale (f,per))(turn:Fin n→Motion),
      let Y:=fun i=>(((books (ρ (port i))).rows (d (port i))).arm (weak i) (v i)).source (N,per)
      ‖gap (R:=R) d port uf deep s Y turn a.val‖≤directPrice F d books port ρ f q weak v s:=by
  classical
  obtain ⟨_,_,_,pkg⟩:=fac.costlier
  obtain ⟨L,η,lp,ep,shape⟩:=WilsonSeparatedPrefixCellProfile.shape φ
  have lp':0<L+1:=by linarith
  obtain ⟨w,house⟩:=WilsonSeparatedPrefixCellHousing.original F fac.simpleGate bliss slow D T h 0 d books (L+1) lp'
  obtain ⟨gate,invoice⟩:=WilsonPhysicalLicensedSelection.selected F pkg.toPackage fac.simpleGate slow stop d port books w q
  have res:=WilsonSeparatedPrefixMasterResolution.original (I:=I) F fac.simpleGate slow D T books (half_pos ep)
  have mesh:=WilsonMeasuredPublicEntranceProfileMesh.original (I:=I) F fac.simpleGate D T n books
    (t:=min 1 (η/4)) (lt_min zero_lt_one (by positivity))
  filter_upwards [house (max (u+2) gate),res,mesh,self_mem_nhdsWithin (a:=(0:ℝ))] with r home clear fine rp
  intro ρ span near f
  obtain ⟨c,late,cf,ratio,inside⟩:=home ρ span near
  have uc:u+2≤c:=(le_max_left ..).trans late
  have uf:u≤f:=by omega
  have license:=invoice ρ c ((le_max_right ..).trans late) uc cf ratio
  have rpos:0<r:=rp
  have size:=fine ρ near
  have bound:4*(n:ℝ)*R.family.S.a f≤r:=size.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_left 1 (η/4)) rpos.le)
  have away:4*(n:ℝ)*R.family.S.a f≤η/4*r:=size.trans (mul_le_mul_of_nonneg_right (min_le_right ..) rpos.le)
  intro scale lower upper
  refine ⟨uf,?_⟩
  intro N per deep s weak v a turn Y
  by_cases use:s.val.Nonempty
  · obtain ⟨site,snapped,issued⟩:=WilsonMeasuredPublicEntranceProfileSites.lifted R φ (per:=per) (rpos.trans_le lower) shape (bound.trans lower) (away.trans (mul_le_mul_of_nonneg_left lower (by positivity)))
    obtain ⟨box,apart⟩:=issued a.val (charged R φ scale (f,per) a)
    have inc(i:Fin n)(_ : i∈s.val):8*‖(C).S.gridPoint f (site a.val i)‖≤(C).S.a (c+1):=by
      simp only [Nat.cast_zero,mul_zero,zero_mul,add_zero] at inside
      exact (mul_le_mul_of_nonneg_left ((box i).trans (mul_le_mul_of_nonneg_left upper lp'.le)) (by norm_num)).trans inside
    have sep:Pairwise fun i k:↥s.val=>2*(C).S.a f*(((C).path.levels.budget f).B:ℝ)^2≤
        ‖(C).S.gridPoint f (site a.val i.val)-(C).S.gridPoint f (site a.val k.val)‖:=
      fun _ _ ne=>(clear ρ near).le.trans ((mul_le_mul_of_nonneg_left lower (half_pos ep).le).trans (apart fun eq=>ne (Subtype.ext eq)))
    have bill:=license s use N per deep (site a.val) inc sep weak v turn uf
    dsimp only at bill
    rw [Finset.prod_coe_sort s.val (fun i:Fin n=>Motion.orbitCost ((C).labels.level ((g) i))*
      WilsonOriginalTwoFlatPublicFare.charge F ((books (ρ (port i))).rows (d (port i))) f (weak i) (v i))] at bill
    change ‖gap (R:=R) d port uf deep s Y turn (RG16.Literal.snap (C) f per (site a.val))‖≤_ at bill
    rwa [snapped] at bill
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
