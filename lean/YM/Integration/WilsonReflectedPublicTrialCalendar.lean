import YM.Integration.WilsonReflectedPublicTrialCapital
/-! The two original preframe programmes receive their actual finite guarded
columns at the same pair of optical dates before the regulators are read. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicTrialCalendar
open Lattice Wilson RG Source Extraction Maxwell Maxwell.Free RG05Readout
open PhysicalNext.Repeat.Legato FVA2 FVA2.Register MS MS.Land
open Function Filter Set Table Spec Climb GapsContact GapsContact.Seams OPE Trace.Pilot
open Next.Rank Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open WilsonReflectedOpticalArm WilsonReflectedFullPanel WilsonReflectedFundedHearing
open WilsonOriginalMicroscopicGuardedPage WilsonReflectedRestoredStation
open Source Labels Extra.Histories Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open scoped Topology Classical
variable {G : Gauge} {R : Run G} {u : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family u S) {l : Ultrafilter (ℕ×ℕ)} {z : Trace.Terrace.Arch R.family}
    {H : (Bel R.family.book).Hierarchy}
local notation "C₀" => R.family
local notation "levels" => R.family.path.levels
local notation "mesh" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta

private theorem wrapped (d j f:ℕ){M:ℝ}
    (cash:WilsonReflectedAffordableArm.charge R d f*(1+wrapCost R d j) ≤ M):
    0 ≤ 1+wrapCost R d j ∧ 1+wrapCost R d j ≤ M :=by
  have w:0 ≤ WilsonCapturedPrimaryCoreBill.wrapFee ((C₀).labels.level d) (C₀).params:=
    mul_nonneg (Nat.cast_nonneg _) (germ_close ((C₀).labels.level d) (C₀).params).choose_spec.1.le
  have wrap:0 ≤ wrapCost R d j:=mul_nonneg (mul_nonneg w (Real.exp_nonneg _))
    (zero_le_one.trans ((levels).params _).columns_ge)
  have z:0 ≤ WilsonReflectedAffordableArm.projectionBill R d f:=mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have st:0 ≤ stock (C₀) f:=zero_le_one.trans ((levels).params f).columns_ge
  have heavy:1 ≤ WilsonReflectedAffordableArm.charge R d f:=by
    unfold WilsonReflectedAffordableArm.charge;linarith only [z,st]
  have non:0 ≤ 1+wrapCost R d j:=by linarith only [wrap]
  exact ⟨non,(le_mul_of_one_le_left non heavy).trans cash⟩

def span (D T q:ℕ):ℕ:=(2*T+9)+(WilsonReflectedOpticalRate.depth (q+1+2) (2*T+9) D+1)

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (width:∀i,((levels).budget i).supportExponent ≤ 100)(D d T q:ℕ)(cap:d ≤ D):
    ∃C:ℝ,0<C ∧ ∀ᶠ r in trail,∀{k:ℕ}
      {stock:Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
        (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T)}
      {W:Vane R.family k}{fits:D ≤ k}{U:Spin.change S d}
      (P:Pair F stock cap W fits U r),W.checked u H k→W.wheel.r=r→
    let m:=max stock.j W.k
    let f:=WilsonInvariantActionPosition.berth R 5 m
    let K:=WilsonInvariantActionPosition.berth R (WilsonReflectedOpticalRate.depth (q+1+2) (2*T+9) D) f
    ∀b:Bool,let j:=station F P b
      j ≤ f ∧ f<K ∧ 1 ≤ β f ∧ mesh j/mesh K ≤ (β f)^(span D T q) ∧
      0 ≤ 1+wrapCost R d j ∧ 1+wrapCost R d j ≤ C*(β f)^2 :=by
  let t:=WilsonReflectedOpticalRate.depth (q+1+2) (2*T+9) D
  obtain ⟨C,pos,paid⟩:=WilsonReflectedOpticalStock.original R simple slow d
  obtain ⟨first,finance⟩:=eventually_atTop.mp paid
  obtain ⟨floor,range⟩:=eventually_atTop.mp ((WilsonAddressedCollarWindow.original R simple slow 5
    (η:=1) zero_lt_one).and ((hat_rate levels simple).eventually_ge_atTop 1))
  obtain ⟨edge,high⟩:=eventually_atTop.mp (WilsonAddressedCollarWindow.original R simple slow t (η:=1) zero_lt_one)
  refine ⟨C,pos,?_⟩
  filter_upwards [WilsonReflectedPublicStationSpan.original F simple bliss T,
    WilsonReflectedPublicStationLate.original F simple bliss T (max floor (max first edge))]
    with r spend mature
  intro k stock W fits U P cleared exactR m f K b j
  have reached:=mature P cleared exactR
  have attained (i:Bool):station F P i ≤ m:=by cases i <;> simp [station,m]
  have rangeM:=range m ((le_max_left ..).trans ((reached b).trans (attained b)))
  have mf:m<f:=rangeM.1.1
  have start (i:Bool):station F P i ≤ f:=(attained i).trans mf.le
  have ratio (b : Bool) : mesh (station F P b)/mesh f ≤ (β f)^(2*T+9) := by
    have own := spend P cleared exactR b
    have edge : mesh m / mesh f ≤ (β m)^6 := by
      simpa [Real.rpow_one,show (6:ℕ)=5+1 by decide,pow_succ] using rangeM.1.2.2
    have positive := (R.family.S.a_pos m).ne'
    calc
      _ = (mesh (station F P b)/mesh m)*(mesh m/mesh f) := by field_simp
      _ ≤ (β m)^(2*T+3)*(β m)^6 := mul_le_mul own edge (div_nonneg (R.family.S.a_pos _).le
        (R.family.S.a_pos _).le) (pow_nonneg (zero_le_one.trans rangeM.2) _)
      _ = (β m)^(2*T+9) := by rw [←pow_add]
      _ ≤ _ := pow_le_pow_left₀ (zero_le_one.trans rangeM.2)
        (WilsonStartup.Timing.hat_mono _ (Gauge.slopeConstant_pos simple).le mf.le) _
  have room:=high f ((le_max_right ..).trans ((le_max_right ..).trans ((reached b).trans (start b))))
  have fK:mesh f/mesh K ≤ (β f)^(t+1):=by simpa [Real.rpow_one,pow_succ] using room.2.2
  have proper:=finance j ((le_max_left ..).trans ((le_max_right ..).trans (reached b))) f (start b)
    (width j) (width f)
  have fee:=wrapped (R:=R) d j f proper
  refine ⟨start b,room.1,((levels).fits.delayed f).le,?_,fee⟩
  calc
    _ = (mesh j/mesh f)*(mesh f/mesh K):=by field_simp [((C₀).S.a_pos f).ne',((C₀).S.a_pos K).ne']
    _ ≤ (β f)^(2*T+9)*(β f)^(t+1):=mul_le_mul (ratio b) fK
      (div_nonneg ((C₀).S.a_pos f).le ((C₀).S.a_pos K).le)
      (pow_nonneg (zero_le_one.trans ((levels).fits.delayed f).le) _)
    _ = _ :=(pow_add ..).symm

end YM.Integration.WilsonReflectedPublicTrialCalendar
end
