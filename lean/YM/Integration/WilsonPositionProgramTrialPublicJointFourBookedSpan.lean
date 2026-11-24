import YM.Integration.WilsonAddressedMixedOpticalMesh
import YM.Integration.WilsonIndependentMatchedReportedOpticalFuel
import YM.Integration.WilsonOriginalObservedRoseBornPairGrid
import YM.Integration.WilsonAddressedCollarWindow

/-! Locate both ends of the true union-campus window at the calibrated reporting date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourBookedSpan
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
    ∃A:ℝ,1 ≤ A ∧ ∀ᶠ r in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},
      (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) → (∃i,(ρ i).val=r) →
      let m:=Γ.date r
      let s:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 s
      let K:=berth R τ f
      let θ:=wilson z r
      0<θ ∧ θ≤1 ∧ m≤K ∧ β K*θ^2 ≤ A ∧ thermal R m ≤ 2*θ ∧
      a K/a m ≤ θ^2 ∧ a m/a K ≤ (β K)^(2*T+11+2*h+(τ+1)):=by
  classical
  let J:=2*(2*Γ.stage+2)
  let b:=2*T+11+2*h
  have heat:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  obtain ⟨A,ap,roof⟩:=WilsonAddressedMixedOpticalMesh.original F simple bliss slow D T h τ (by omega) d books
  obtain ⟨gate,window⟩:=eventually_atTop.mp (WilsonAddressedCollarWindow.original R simple slow τ zero_lt_one)
  have rebate:∀ᶠr in trail,Γ.allowance*(wilson z r) ≤ 1:=by
    have conv:=((heat.conforms simple).const_mul Γ.allowance)
    rw [mul_zero] at conv
    exact (conv.eventually_le_const zero_lt_one)
  refine ⟨A,ap,?_⟩
  filter_upwards [roof,WilsonOriginalTwoFlatPublicMixedSpan.original F simple bliss slow D T h d books,
    WilsonOriginalTwoFlatPublicOuter.original F simple bliss 1,Γ.inverse,Γ.upper,
    WilsonOriginalObservedRoseBornPairGrid.heat Γ simple heat,
    (heat.conforms simple).eventually_le_const zero_lt_one,rebate,
    (gt_mem_nhds ((C).S.a_pos gate)).filter_mono nhdsWithin_le_nhds] with r under sale outerRoom inverse upper billed small pay below
  intro ρ span anchor m s f K θ
  have entered:=sale ρ span anchor
  have bounded:=under ρ span anchor
  have gp:0<θ:=bounded.1
  have rp:0<r:=outerRoom.1
  have θone:θ≤1:=small
  have square:θ^2 ≤ 1:=by nlinarith only [mul_nonneg (sub_nonneg.mpr θone) (show 0≤1+θ by linarith only [gp])]
  have mf:a m ≤ r:=by simpa only [one_mul] using (div_le_iff₀ rp).mp (upper.trans square)
  have af:a f ≤ r:=entered.1
  have fj:gate≤f:=by
    by_contra! bad
    exact (not_lt_of_ge ((C).S.strictAnti.antitone bad.le)) (lt_of_le_of_lt af below)
  have ghat:θ⁻¹ ≤ (β f)^2:=by
    apply (mul_le_mul_iff_of_pos_left rp).mp
    simpa only [outer,pow_one,Nat.mul_one,mul_comm ((β f)^2) r] using outerRoom.2.2 f af
  have flux:a K/a f ≤ θ^(J+3):=WilsonIndependentMatchedReportedOpticalFuel.depth R f f K τ (J+3)
    le_rfl rfl deep θ gp ghat
  have gain:a K/a m ≤ θ^2:=calc
    _=(a K/a f)*(a f/r)*(r/a m):=by field_simp [((C).S.a_pos f).ne',rp.ne']
    _ ≤ θ^(J+3)*1*(r/a m):=by
      apply mul_le_mul_of_nonneg_right _ (div_nonneg rp.le ((C).S.a_pos _).le)
      exact mul_le_mul flux ((div_le_one rp).mpr af) (div_nonneg ((C).S.a_pos _).le rp.le) (pow_nonneg gp.le _)
    _=((r/a m)*θ^J)*θ^3:=by rw [pow_add];ring
    _≤Γ.allowance*θ^3:=mul_le_mul_of_nonneg_right inverse (pow_nonneg gp.le _)
    _≤θ^2:=calc
      _=(Γ.allowance*θ)*θ^2:=by ring
      _ ≤ 1*θ^2:=mul_le_mul_of_nonneg_right pay (sq_nonneg _)
      _=_:=one_mul _
  have mk:m≤K:=by
    by_contra! bad
    exact (not_lt_of_ge ((div_le_one ((C).S.a_pos _)).mp (gain.trans square))) ((C).S.strictAnti bad)
  obtain ⟨i,ri⟩:=anchor
  have mid:r/a f ≤ (β f)^b:=by
    rw [div_le_iff₀ ((C).S.a_pos _)]
    exact ri ▸ (entered.2 i).2
  have late:a f/a K ≤ (β f)^(τ+1):=by simpa only [Real.rpow_one,pow_succ] using (window f fj).2.2
  have mono:β f ≤ β K:=WilsonStartup.Timing.hat_mono P (Gauge.slopeConstant_pos simple).le
    (WilsonInvariantActionPosition.arrival R τ f).1.le
  refine ⟨gp,θone,mk,bounded.2.2,billed,gain,?_⟩
  calc
    _=(a m/r)*(r/a f)*(a f/a K):=by field_simp [rp.ne',((C).S.a_pos f).ne']
    _ ≤ (1*(β f)^b)*(β f)^(τ+1):=by
      apply mul_le_mul _ late (div_nonneg ((C).S.a_pos _).le ((C).S.a_pos _).le)
        (mul_nonneg zero_le_one (pow_nonneg (zero_le_one.trans ((P).fits.delayed f).le) _))
      exact mul_le_mul ((div_le_one rp).mpr mf) mid (div_nonneg rp.le ((C).S.a_pos _).le) zero_le_one
    _=(β f)^(b+(τ+1)):=by rw [one_mul,←pow_add]
    _ ≤ (β K)^(b+(τ+1)):=pow_le_pow_left₀ (zero_le_one.trans ((P).fits.delayed f).le) mono _

end YM.Integration.WilsonPositionProgramTrialPublicJointFourBookedSpan
end
