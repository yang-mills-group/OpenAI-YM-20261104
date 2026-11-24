import YM.Integration.WilsonOriginalTwoFlatPublicSameField
import YM.Integration.WilsonOriginalTwoFlatRoseSecant

/-! All seven attached physical Rose faces on one actual selected reporting grid. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRosePhase
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare

open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonReflectedPublicStationFare

open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {z:Trace.Terrace.Arch R.family}

local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS
open MS MS.Land FVA2 FVA2.Register


open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
variable (Jr:ℝ → tower S)(Z:WilsonPrescription G)

open WilsonPositionThermometerGradedSource
local notation "heads" => source (C) (Finset.univ:Finset (Fin 3))
local notation "SiteSet" => {s:Finset (Fin 3)//s.Nonempty}

def fields {T:ℕ}{δ:ℝ}(books:(r:{s:ℝ // 0<s ∧ s<δ}) → Book F (l:=l) H z 6 T r.val)
    (r:{s:ℝ // 0<s ∧ s<δ})(weak:Fin 3 → Bool)(N per:ℕ)(i:Fin 3):(C).label (grade i):=
  ((books r).rows (grade i)).arm (weak i) (homogeneous F Jr Z r.val (grade i) (heads i)) |>.source (N,per)

theorem selected (fac:Facilities C order S)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    {T:ℕ}{M η δ:ℝ}(one:1≤M)(ep:0<η)(dp:0<δ)
    (books:(r:{s:ℝ // 0<s ∧ s<δ}) → Book F (l:=l) H z 6 T r.val)
    (window:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃J u:ℕ,Stop C 0 J u ∧ ∀q:ℕ,∃A:ℝ,0≤A ∧ ∀ᶠr in trail,
      ∃inside:0<r ∧ r<δ,
      let h:=univ.sup (fun _i:Fin 3=>max (books ⟨r,inside⟩).stock.j (books ⟨r,inside⟩).W.k)
      let f:=berth R 5 h
      ∃uf:u≤f,∀N per:ℕ,∀live:f<N,∀o:Fin 3 → Cover,
      (∀i,‖(C).S.gridPoint f (o i)‖≤M*r) → 
      (Pairwise fun i j=>η*r≤‖(C).S.gridPoint f (o i)-(C).S.gridPoint f (o j)‖) → 
      ∀(weak:Fin 3 → Bool)(E:Finset (Fin 3)),E.Nonempty → 
        let Y:=fields F Jr Z books ⟨r,inside⟩ weak N per
        let pins:=fun i=>((C).S.toDepth live.le per).embed (snap C f per o i)
        let entire:=WilsonOriginalTwoFlatRoseSecant.field R Y pins E
        ‖gap R N per u (uf.trans live.le) entire‖ ≤ A*(wilson z r)^q ∧ Heard R fac.simpleGate N per u entire (A*(wilson z r)^q):=by
  classical
  obtain ⟨J,u,stop,program⟩:=WilsonOriginalTwoFlatPublicSameField.selected F Jr Z fac bliss slow lead paid
    6 T 0 grade heads one ep dp books window
  refine ⟨J,u,stop,?_⟩
  intro q
  let cash(s:SiteSet):ℝ:=(program q s.val s.property).choose
  have pos(s:SiteSet):0<cash s:=(program q s.val s.property).choose_spec.1
  have budgets:=Filter.eventually_all.mpr (fun s:SiteSet=>(program q s.val s.property).choose_spec.2)
  let all:SiteSet:=⟨univ,univ_nonempty⟩
  refine ⟨∑s,cash s,sum_nonneg (fun s _=>(pos s).le),?_⟩
  filter_upwards [budgets,(wilson_link F fac.simpleGate bliss.budgets bliss.keen bliss.lies).positive] with r table gpos
  have publicR:0<r ∧ r<δ:=by simpa only [outer,pow_zero,mul_one] using (And.intro (table all).1 (table all).2.1)
  let own : Fin 3 → {s:ℝ//0<s ∧ s<δ}:=fun _=>⟨r,publicR⟩
  have radius:∀i,r≤(own i).val ∧ (own i).val≤outer z 0 r:=by simp [own,outer]
  have oneAt:∃i,(own i).val=r:=⟨0,rfl⟩
  obtain ⟨uf,_⟩:=(table all).2.2 own radius oneAt
  refine ⟨publicR,uf,?_⟩
  intro N per live o shape sep weak E ne Y pins entire
  let mode:SiteSet:=⟨E,ne⟩
  obtain ⟨_,get⟩:=(table mode).2.2 own radius oneAt
  let f:=berth R 5 (univ.sup (fun _i:Fin 3=>max (books ⟨r,publicR⟩).stock.j (books ⟨r,publicR⟩).W.k))
  have housing(i:↥E):‖(C).S.gridPoint f (o i)‖≤M*outer z 0 r:=by simpa [outer] using shape i
  have housed:=get N per live (fun i=>o i) housing (fun i j ij=>sep (fun same=>ij (Subtype.ext same))) (fun i=>weak i)
  have equality:word R (fun i:↥E=>(grade i).val) f N per live.le (fun i=>o i) (fun i=>Y i)=entire:=by
    funext U
    change (∏i:↥E,(C).O N per (Y i) (pins i) U)=∏i∈E,(C).O N per (Y i) (pins i) U
    exact Finset.prod_coe_sort E (fun i=> (C).O N per (Y i) (pins i) U)
  have rate:cash mode*(wilson z r)^q ≤ (∑s,cash s)*(wilson z r)^q:=
    mul_le_mul_of_nonneg_right (single_le_sum (fun s _=>(pos s).le) (mem_univ mode)) (pow_nonneg gpos.le _)
  have small:‖gap R N per u (uf.trans live.le) entire‖ ≤ (∑s,cash s)*(wilson z r)^q :=by
    rw [←equality]
    exact housed.1.trans rate
  refine ⟨small,WilsonOriginalTwoFlatPublicHeard.earned R fac.simpleGate (uf.trans live.le) entire ?_ small⟩
  exact WilsonOriginalTwoFlatRoseSecant.regular R Y pins E

end YM.Integration.WilsonOriginalTwoFlatRosePhase
