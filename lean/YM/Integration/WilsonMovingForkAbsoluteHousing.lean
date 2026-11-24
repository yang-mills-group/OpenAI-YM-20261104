import YM.Integration.WilsonMovingForkAbsolutePhase
import YM.Integration.WilsonSeparatedPrefixCellHousing
import YM.Integration.WilsonIndependentCapturedPages

/-! Move the original receiver far enough back from the housing that encloses
the enlarged cell. All dates precede the original cutoff, period, and shifts. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkAbsoluteHousing
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
theorem band (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h b n:ℕ)(hb:h≤b)(d:I → Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (M:ℝ)(mp:0<M):
    ∃window:ℕ,∀u depth stage:ℕ,∀P:XSpace.Run,∀B:Band R P stage,
      ∃v:WilsonIndependentCapturedPages.Stop R P B u depth,∀gate:ℕ,∀ᶠr in trail,
      ∀ρ:I→{s:ℝ //0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let j:=reporter F books ρ
      ∃t:ℕ,let c:=B.reporter+t
      gate≤c ∧ c+2≤j ∧ a_ c/a_ j≤(β j)^window ∧
        8*(M*outer z b r+4*(n:ℝ)*a_ j)≤a_ (c+1) ∧ u≤v.date t ∧ v.date t≤c ∧
        ∀N per:ℕ,c≤N→let g:=regulatorRun (C) N per c
          0<g ∧ g ≤ 1 ∧ a_ c/a_ (v.date t)≤(g^depth)^2 ∧
          (C).S.scale c-(C).S.scale (v.date t)≤4*(2*depth+1)*Real.log g⁻¹:=by
  obtain ⟨window,house⟩:=WilsonSeparatedPrefixCellHousing.original F simple bliss slow D T b n d books M mp
  refine ⟨window,?_⟩
  intro u dep stage P B
  obtain ⟨v⟩:=WilsonIndependentCapturedPages.original R P simple slow B u dep
  obtain ⟨start,valid⟩:=eventually_atTop.mp v.heard
  refine ⟨v,?_⟩
  intro gate
  let income:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  filter_upwards [house (max gate (B.reporter+start)),income.positive,
    (income.conforms simple).eventually (ge_mem_nhds zero_lt_one),length_rate.pos] with r fits gp small rp
  intro ρ homes near j
  have outer_le:outer z h r≤outer z b r:=mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ ((one_le_inv₀ gp).mpr small) hb) rp.le
  obtain ⟨c,large,fine,range,wall⟩:=fits ρ (fun i=>⟨(homes i).1,(homes i).2.trans outer_le⟩) near
  let t:=c-B.reporter
  have g0:gate≤c:=(le_max_left _ _).trans large
  have c0:B.reporter+start≤c:=(le_max_right _ _).trans large
  have ct:B.reporter+t=c:=by dsimp [t];omega
  have t0:start≤t:=by dsimp [t];omega
  have alive:=valid t t0
  exact ⟨t,ct.symm ▸ g0,ct.symm ▸ fine,ct.symm ▸ range,ct.symm ▸ wall,alive.1,v.upper t,alive.2⟩

end YM.Integration.WilsonMovingForkAbsoluteHousing
