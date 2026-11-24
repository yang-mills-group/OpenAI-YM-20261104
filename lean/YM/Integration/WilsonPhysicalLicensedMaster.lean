import YM.Integration.WilsonPhysicalLicensedFaces
import YM.Integration.WilsonSeparatedPrefixMasterResolution

/-! A common capture and both appointed ears for the original finite physical family.
The cutoff gate for all occupied rotations is imposed after selling one moving stop. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalLicensedMaster
open Filter Function Finset Set Lattice RG Wilson Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG16.Literal PhysMS Climb
open Trace.Terrace Trace.Pilot GapsContact OPE RG17
open WilsonReflectedPublicStationFare
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMovingForkOpticalBook (reporter)
open WilsonPositionProgramReporterBand (Band)
open Pert.Asymptotics
open Next.Rank Overlay Bid PhysicalNext.Repeat.Mallow Bandage RG16
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
  {lo wid teach}(L:Package R.family wid lo teach)
local notation "C" => R.family
local notation "a_" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta

include L in
theorem original {n:ℕ}[NeZero n](simple:G.Simple)(bliss:Bliss F l z H)
    (slow:WilsonWindowReportingPace.Slow R.kit)(forecast:WilsonReportLampForecast.Ready (C).path.levels)
    (D T h b:ℕ)(hb:h≤b)(d:Fin n→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    {M η:ℝ}(mp:0<M)(ep:0<η):
    ∃window:ℕ,∀u J depth stage goal q:ℕ,(C).ref 0≤u → Stop C 0 J u →∀P:XSpace.Run,∀B:Band R P stage,
      ∃v:WilsonIndependentCapturedPages.Stop R P B u depth,∀floor:ℕ,∀ᶠr in trail,
      ∀ρ:Fin n→{s:ℝ //0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let f:=reporter F books ρ
      ∃t:ℕ,let c:=B.reporter+t
      floor≤c ∧ c+2≤f ∧ a_ c/a_ f≤(β f)^window ∧ 8*(M*outer z b r+4*(n:ℝ)*a_ f)≤a_ (c+1) ∧
      2*a_ f*(((C).path.levels.budget f).B:ℝ)^2<η*r ∧ u≤v.date t ∧ v.date t≤c ∧
      WilsonMovingForkMountedStage.Paid R P B v goal t ∧
      (∀N per:ℕ,c≤N→let g:=regulatorRun (C) N per c
        0<g ∧ g≤1 ∧ a_ c/a_ (v.date t)≤(g^depth)^2 ∧
        (C).S.scale c-(C).S.scale (v.date t)≤4*(2*depth+1)*Real.log g⁻¹) ∧
      ∀s:(Stock.census (Fin n)).Mode,s.val.Nonempty →
        WilsonPhysicalLicensedFaces.measured F d books ρ q u f c s:=by
  obtain ⟨window,house⟩:=WilsonMovingForkPaidHousing.original F simple bliss slow forecast D T h b n hb d books M mp
  refine ⟨window,?_⟩
  intro u J depth stage goal q home ear P B
  obtain ⟨v,author⟩:=house u depth stage goal home P B
  obtain ⟨gate,paid⟩:=WilsonPhysicalLicensedFaces.original F L simple slow ear d books window q
  refine ⟨v,?_⟩
  intro floor
  filter_upwards [author (max (max floor (u+2)) gate),
    WilsonSeparatedPrefixMasterResolution.original (I:=Fin n) F simple slow D T books ep] with r ledger clear
  intro ρ span near f
  obtain ⟨t,leGate,cf,range,wall,uv,vc,sold,fees⟩:=ledger ρ span near
  have base:max floor (u+2)≤B.reporter+t:=(le_max_left ..).trans leGate
  exact ⟨t,(le_max_left ..).trans base,cf,range,wall,clear ρ near,uv,vc,sold,fees,
    paid ρ _ ((le_max_right ..).trans leGate) ((le_max_right ..).trans base) cf range⟩

end YM.Integration.WilsonPhysicalLicensedMaster
end
