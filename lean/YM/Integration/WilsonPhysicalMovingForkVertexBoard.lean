import YM.Integration.WilsonPhysicalDisplayedCapture
import YM.Integration.WilsonMovingForkShiftedSite
import YM.Integration.WilsonMovingForkCommonTranslation
import YM.Integration.WilsonMovingForkOpticalBook

import YM.Integration.WilsonPhysicalMovingForkPhase
import YM.Integration.WilsonMovingForkPaidHousing
import YM.Integration.WilsonSeparatedPrefixMasterResolution
import YM.Integration.WilsonMovingForkOpticalContrast
import YM.Integration.WilsonPhysicalMovingForkCapturedSites
/-! The unconditional moving-fork row may be shifted once, then heard at its licensed original flat. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalMovingForkVertexBoard
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace
open GapsContact GapsContact.Seams GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {lo wid teach}(L:Package R.family wid lo teach)
  {I:Type}[Fintype I]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta


open WilsonMovingForkShiftedSite (Reached)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)

open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonPositionProgramReporterBand (Band)
open Pert.Asymptotics

open WilsonMovingForkOpticalContrast (Node arity ports nearPorts pairPorts)
open WilsonSeparatedBranchStencil (Trial)
include L in
theorem original {z:Trace.Terrace.Arch R.family}{D T h b m n:ℕ}{δ:ℝ}
    (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (forecast:WilsonReportLampForecast.Ready (P))(hb:h≤b)(d:Fin m→Fin (D+1))
    (far:Fin m)(near:Fin n→Fin m)(head:I→Fin m)
    (books:(r:{r:ℝ //0<r ∧ r<δ})→Book F (l:=l) H z D T r.val)
    {width sep:ℝ}(inside:0<width)(sp:0<sep):
    ∃B opening:ℕ,∀u J depth stage goal q:ℕ,opening≤u → (C).ref 0≤u → Stop C 0 J u →
    ∀program:XSpace.Run,∀band:Band R program stage,
      ∃v:WilsonIndependentCapturedPages.Stop R program band u depth,∀floor:ℕ,∀ᶠr in trail,
      ∀ρ:Fin m→{r:ℝ //0<r ∧ r<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r) → (∃i,(ρ i).val=r) →
      let f:=reporter F books ρ
      ∃t:ℕ,let c:=band.reporter+t
      floor≤c ∧ c+2≤f ∧ a c/a f≤(β f)^B ∧
      ∃(uv:u≤v.date t)(vc:v.date t≤c),
      0<v.date t ∧ (∀per,Opened (C) 0 u per ∧ Opened (C) 0 (v.date t) per) ∧
      WilsonMovingForkMountedStage.Paid R program band v goal t ∧
      (∀N per:ℕ,c≤N→let g:=regulatorRun (C) N per c
        0<g ∧ g≤1 ∧ a c/a (v.date t)≤(g^depth)^2 ∧
        (C).S.scale c-(C).S.scale (v.date t)≤4*(2*depth+1)*Real.log g⁻¹) ∧
      ∀K:ℕ,∀(fk:f≤K)(ck:c≤K)(Y:Trial (n+1))(M:I→Trial 2),
      ∀(site:(e:Node Y M)→Fin (arity e)→ Lattice.Cover)(shift:Node Y M→Lattice.Cover),
      let offered:=fun e i=>site e i+shift e
      (∀e i,‖(C).S.gridPoint f (offered e i)‖≤width*outer z b r) →
      (∀e,Pairwise fun i k=>sep*r≤‖(C).S.gridPoint f (offered e i)-(C).S.gridPoint f (offered e k)‖) →
      ∀weak:Fin m→Bool,∀x:∀i,S.Field (d i).val,
      let rows:=fun i=>(books (ρ i)).rows (d i)
      let arms:=fun i=>(rows i).arm (weak i) (x i)
      ∀e: Node Y M,let port:=ports far near head e
        (∀per i,WilsonMovingForkPrintedFile.parent R ck per (WilsonMovingForkSeededPoint.seats (R:=R) fk per (offered e)) i=0) ∧
        Reached (fun i=>arms (port i)) fk uv vc ck (site e) (offered e)
          ((∏i,Motion.orbitCost ((C).labels.level (d (port i)).val)*charge F (rows (port i)) f (weak (port i)) (x (port i)))*((β f)^q)⁻¹):=by
  classical
  letI:Nonempty (Fin m):=⟨far⟩
  obtain ⟨B,house⟩:=WilsonMovingForkPaidHousing.original F simple bliss slow forecast D T h b 0 hb d books width inside
  obtain ⟨ear,allOpen⟩:=eventually_atTop.mp (open_late R.family simple 0)
  refine ⟨B,max 1 ear,?_⟩
  intro u J depth stage goal q clearU cu stopped program band
  obtain ⟨v,mounted⟩:=house u depth stage goal cu program band
  obtain ⟨allGate,full⟩:=WilsonPhysicalMovingForkPhase.original F L simple slow stopped d (nearPorts far near) books B q
  choose gates paired using fun k=>WilsonPhysicalMovingForkPhase.original F L simple slow stopped d (pairPorts far (head k)) books B q
  let gate:=max allGate (Finset.univ.sup gates)
  refine ⟨v,?_⟩
  intro floor
  filter_upwards [mounted (max (max gate floor) (u+2)),
    WilsonSeparatedPrefixMasterResolution.original (I:=Fin m) F simple slow D T books sp] with r geometry separate
  intro ρ homes anchor f
  obtain ⟨t,after,cf,range,wall,uv,vc,paid,fees⟩:=geometry ρ homes anchor
  have gf:= (le_max_left _ _).trans after
  have earliest:gate≤band.reporter+t:=(le_max_left ..).trans gf
  have gap:u+2≤band.reporter+t:=(le_max_right ..).trans after
  have lu:ear≤u:=(le_max_right ..).trans clearU
  have positive:0<v.date t:=lt_of_lt_of_le Nat.zero_lt_one ((le_max_left ..).trans (clearU.trans uv))
  refine ⟨t,(le_max_right ..).trans gf,cf,range,uv,vc,positive,
    fun per=>⟨allOpen u lu per,allOpen _ (lu.trans uv) per⟩,paid,fees,?_⟩
  intro K fk ck Y M site shift offered reach apart weak x rows arms e
  have fits(e:Node Y M)(i):8*‖(C).S.gridPoint f (offered e i)‖≤a (band.reporter+t+1):=by
    apply (mul_le_mul_of_nonneg_left (reach e i) (by norm_num : (0:ℝ)≤8)).trans
    simpa using wall
  have clear(e:Node Y M):Pairwise fun i k=>2*a f*(((P).budget f).B:ℝ)^2≤‖(C).S.gridPoint f (offered e i)-(C).S.gridPoint f (offered e k)‖:=
    fun _ _ ne=>(separate ρ anchor).le.trans (apart e ne)
  refine ⟨fun per=>WilsonPhysicalMovingForkCapturedSites.original R (by omega : band.reporter+t≤f) fk per
    (offered e) (fits e),?_⟩
  cases e with
  | inl node=>
    exact full ρ _ _ _ ((le_max_left ..).trans earliest) gap cf range fk uv vc ck
      (site (.inl node)) (shift (.inl node)) (fits (.inl node)) (clear (.inl node))
      (fun i=>weak (nearPorts far near i)) (fun i=>x (nearPorts far near i))
  | inr node=>
    have tall:gates node.1≤gate:= (Finset.le_sup (f:=gates) (Finset.mem_univ node.1)).trans (le_max_right ..)
    exact paired node.1 ρ _ _ _ (tall.trans earliest) gap cf range fk uv vc ck
      (site (.inr node)) (shift (.inr node)) (fits (.inr node)) (clear (.inr node))
      (fun i=>weak (pairPorts far (head node.1) i)) (fun i=>x (pairPorts far (head node.1) i))

end YM.Integration.WilsonPhysicalMovingForkVertexBoard
end
