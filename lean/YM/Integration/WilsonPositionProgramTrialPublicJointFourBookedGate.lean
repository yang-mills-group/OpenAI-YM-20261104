import YM.Integration.WilsonPositionProgramTrialPublicJointFourBookedSpan
import YM.Integration.WilsonPositionProgramTrialPublicJointFourBookedCurrency

/-! Physical optical inequalities at the original selected reporting date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourBookedGate
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
  {I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS


open WilsonOriginalPublicRelativeGramKineticMesh (thermal)

omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {base:ℕ}(Γ:WilsonViewerReportingGrid.Grid (ℓ:=l) F base (wilson z))
    (D T h τ:ℕ)(deep:2*(2*(2*Γ.stage+2)+3) ≤ τ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∃U:ℝ,1≤U ∧ ∀ᶠ r in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},
      (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) → (∃i,(ρ i).val=r) →
      let m:=Γ.date r
      let s:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 s
      let K:=berth R τ f
      let B:=2*T+11+2*h+(τ+1)
      ∀N per:ℕ,K≤N →
      let t:=Pert.Asymptotics.regulatorRun R.family N per m
      m≤K ∧ 0<t ∧ t≤1 ∧ 0<Pert.Asymptotics.regulatorRun R.family N per K ∧
        t≤4*(wilson z r) ∧ wilson z r≤U*t ∧
        a m/a K ≤ t^(-(2*(B:ℝ)+1)) ∧ a K/a m≤t:=by
  obtain ⟨A,ap,span⟩:=WilsonPositionProgramTrialPublicJointFourBookedSpan.original F simple bliss slow Γ D T h τ deep d books
  let B:=2*T+11+2*h+(τ+1)
  have cold: Tendsto (wilson z) trail (𝓝 0):=(wilson_link F simple bliss.budgets bliss.keen bliss.lies).conforms simple
  have small (P':ℝ):∀ᶠr in trail,P'*(wilson z r)≤1:=by
    have earned:=cold.const_mul P'
    rw [mul_zero] at earned
    exact earned.eventually_le_const zero_lt_one
  refine ⟨2*A+1,by linarith only [ap],?_⟩
  filter_upwards [span,small (2*A+1),small (4*(16*A)^B),small 4] with r booked low high hot
  intro ρ placed near m s f K B₀ N per top t
  obtain ⟨gp,_,mk,roof,mesh,thin,thick⟩:=booked ρ placed near
  have currency:=WilsonPositionProgramTrialPublicJointFourBookedCurrency.original R simple m K N per mk top
    (wilson z r) A gp ap roof mesh
  obtain ⟨pos,cap,floor,gpK⟩:=currency
  have upper:(a K/a m)⁻¹ ≤ (β K)^B:=by simpa only [inv_div] using thick
  have charge:=WilsonPositionProgramTrialPublicJointFourBookedCurrency.window (β K) (a K/a m) (wilson z r)
    t A B gp pos (zero_le_one.trans ((P).fits.delayed K).le) ap thin upper roof cap floor low high
  exact ⟨mk,pos,cap.trans hot,gpK,cap,floor,by simpa only [inv_div] using charge.2,charge.1⟩

end YM.Integration.WilsonPositionProgramTrialPublicJointFourBookedGate
end
