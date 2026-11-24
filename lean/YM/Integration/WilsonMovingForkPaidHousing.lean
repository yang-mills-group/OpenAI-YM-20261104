import YM.Integration.WilsonMovingForkAbsoluteHousing
import YM.Integration.WilsonMovingForkMountedStage

/-! The wider absolute box and the actual paid two-stop vote occur at the
same capture and use the same stop and original public homes. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkPaidHousing
open Filter Function Finset Set Lattice RG Wilson Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG16.Literal PhysMS Climb
open Trace.Terrace Trace.Pilot GapsContact OPE RG17
open WilsonReflectedPublicStationFare
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMovingForkOpticalBook (reporter)
open WilsonPositionProgramReporterBand (Band)
open Pert.Asymptotics
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family f S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
  {I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family
local notation "a_" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta

omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (forecast:WilsonReportLampForecast.Ready (C).path.levels)(D T h b n:ℕ)(hb:h≤b)(d:I → Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (M:ℝ)(mp:0<M):
    ∃window:ℕ,∀u depth stage goal:ℕ,(C).ref 0≤u → ∀P:XSpace.Run,∀B:Band R P stage,
      ∃v:WilsonIndependentCapturedPages.Stop R P B u depth,∀gate:ℕ,∀ᶠr in trail,
      ∀ρ:I→{s:ℝ //0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let j:=reporter F books ρ
      ∃t:ℕ,let c:=B.reporter+t
      gate≤c ∧ c+2≤j ∧ a_ c/a_ j≤(β j)^window ∧
        8*(M*outer z b r+4*(n:ℝ)*a_ j)≤a_ (c+1) ∧ u≤v.date t ∧ v.date t≤c ∧
        WilsonMovingForkMountedStage.Paid R P B v goal t ∧
        ∀N per:ℕ,c≤N→let g:=regulatorRun (C) N per c
          0<g ∧ g ≤ 1 ∧ a_ c/a_ (v.date t)≤(g^depth)^2 ∧
          (C).S.scale c-(C).S.scale (v.date t)≤4*(2*depth+1)*Real.log g⁻¹:=by
  obtain ⟨window,house⟩:=WilsonMovingForkAbsoluteHousing.band F simple bliss slow D T h b n hb d books M mp
  refine ⟨window,?_⟩
  intro u depth stage goal cu P B
  obtain ⟨v,fits⟩:=house u depth stage P B
  obtain ⟨first,earned⟩:=eventually_atTop.mp (WilsonMovingForkMountedStage.original R simple slow forecast P B v cu goal)
  refine ⟨v,?_⟩
  intro gate
  filter_upwards [fits (max gate (B.reporter+first))] with r funded
  intro ρ homes near j
  obtain ⟨offset,large,fine,range,wall,uv,vc,fees⟩:=funded ρ homes near
  have late:first≤offset:=Nat.le_of_add_le_add_left ((le_max_right _ _).trans large)
  exact ⟨offset,(le_max_left _ _).trans large,fine,range,wall,uv,vc,earned offset late,fees⟩

end YM.Integration.WilsonMovingForkPaidHousing
