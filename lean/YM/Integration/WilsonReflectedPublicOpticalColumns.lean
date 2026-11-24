import YM.Integration.WilsonReflectedPublicStationLate
import YM.Integration.WilsonReflectedPublicStationReceipt
import YM.Integration.WilsonReflectedOpticalArm
import YM.Integration.WilsonReflectedRestoredStation

/-! The two original preframe programmes receive their actual finite guarded
columns at the same pair of optical dates before the regulators are read. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicOpticalColumns
open Lattice Wilson RG Source Extraction Maxwell Maxwell.Free RG05Readout
open PhysicalNext.Repeat.Legato FVA2 FVA2.Register MS MS.Land
open Function Filter Set Table Spec Climb GapsContact GapsContact.Seams OPE Trace.Pilot
open Next.Rank Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open WilsonReflectedOpticalArm WilsonReflectedFullPanel WilsonReflectedFundedHearing
open WilsonOriginalMicroscopicGuardedPage WilsonReflectedRestoredStation
open scoped Topology Classical
variable {G : Gauge} {R : Run G} {u : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family u S) {l : Ultrafilter (ℕ×ℕ)} {z : Trace.Terrace.Arch R.family}
    {H : (Bel R.family.book).Hierarchy}
local notation "C₀" => R.family
local notation "levels" => R.family.path.levels
local notation "mesh" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta

theorem original (simple : G.Simple) (bliss : Bliss F l z H)
    (slow : WilsonWindowReportingPace.Slow R.kit) (shop : RG05Preconstruction.ReadoutPurchase R.b)
    (width : ∀ i, 1 ≤ ((levels).budget i).supportExponent)
    (capWidth : ∀ i, ((levels).budget i).supportExponent ≤ 100)
    (law : OPE.Therm.Poetry levels) (D d T q jets : ℕ) (cap : d ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in trail, ∀ {k : ℕ}
      {stock : Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
        (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T)}
      {W : Vane R.family k} {fits : D ≤ k} {U : Spin.change S d}
      (P : Pair F stock cap W fits U r), W.checked u H k → W.wheel.r = r →
      let m := max stock.j W.k
      let f := WilsonInvariantActionPosition.berth R 5 m
      let K := WilsonInvariantActionPosition.berth R (WilsonReflectedOpticalRate.depth (q+2) (2*T+9) D) f
      ∃ h : f < K, ∃ start : ∀ b, station F P b ≤ f,
      ∀ N p (top : K ≤ N),
      ∃ M : Bool → (C₀).label d ≃ₗ[ℂ] (C₀).label d, ∀ b (v : S.Field d),
      let Y := (P.arm b v).source (N,p)
      let j := station F P b
      let w := (M b).symm (full R d N p j Y)
      receipt R d j K N p jets ((start b).trans h.le) top (1/32) (M b) Y (mesh j^d*fee F P b v) ∧
      ∀ side s o, ∃ A : Arm R d N p f K, A.Y = Y ∧ A.w = w ∧ A.b = side ∧ A.s = s ∧ A.o = o ∧
        Priced R A (C*((β f)^q)⁻¹*(mesh f)^d*fee F P b v) ∧
        ∃ B : Arm R d N p K K, Situated R h.le A B := by
  obtain ⟨C,cp,begin,issue⟩ := WilsonReflectedOpticalArm.funded R simple slow q (2*T+9) D d cap
    (η:=1) zero_lt_one
  obtain ⟨first,appointed⟩ := WilsonReflectedPublicStationReceipt.appointed R simple shop width law d jets
    (η:=1/32) (by norm_num)
  obtain ⟨floor,range⟩ := eventually_atTop.mp ((WilsonAddressedCollarWindow.original R simple slow 5
    (η:=1) zero_lt_one).and ((hat_rate levels simple).eventually_ge_atTop 1))
  refine ⟨C,cp,?_⟩
  filter_upwards [WilsonReflectedPublicStationSpan.original F simple bliss T,
    WilsonReflectedPublicStationLate.original F simple bliss T (max floor (max first begin))]
    with r spend mature
  intro k stock W fits U P cleared exactR m f K
  have reached := mature P cleared exactR
  have attained (b : Bool) : station F P b ≤ m := by cases b <;> simp [station,m]
  have rangeM := range m ((le_max_left ..).trans ((reached false).trans (attained false)))
  have mf : m < f := rangeM.1.1
  have start (b) := (attained b).trans mf.le
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
  have own (b : Bool) := issue (station F P b) ((le_max_right ..).trans ((le_max_right ..).trans (reached b)))
    f (start b) (ratio b) (capWidth _) (capWidth _)
  have h : f < K := (own false).choose
  refine ⟨h,start,?_⟩
  intro N p top
  have live (b : Bool) : station F P b < N := ((start b).trans_lt h).trans_le top
  have one (b : Bool) := appointed (station F P b) ((le_max_left ..).trans ((le_max_right ..).trans (reached b)))
    (WilsonReflectedPublicStationFare.original F P cleared b 0).1 K N p ((start b).trans h.le) top (live b)
  choose M hear using one
  refine ⟨M,?_⟩
  intro b v Y j w
  have fund := (WilsonReflectedPublicStationFare.original F P cleared b v).2 N p (live b)
  have paidAt := hear b Y _ fund
  have nn : 0 ≤ Next.UVStress.quota (C₀) d j N p Y := by
    unfold Next.UVStress.quota Labels.Frame.coeffSize
    positivity
  have pos := nonneg_of_mul_nonneg_right (nn.trans fund) (pow_pos (R.family.S.a_pos j) d)
  refine ⟨paidAt,?_⟩
  intro side s o
  obtain ⟨A,ay,aw,ab,as',ao,bill⟩ := (own b).choose_spec.2.2 N p jets top (M b) Y _ pos paidAt side s o
  refine ⟨A,ay,aw,ab,as',ao,bill,?_⟩
  obtain ⟨B,placed,_⟩ := WilsonReflectedRestoredStation.purchased R h.le ((start b).trans h.le) top
    A (ay.symm ▸ paidAt) (ay.symm ▸ aw)
  exact ⟨B,placed⟩

end YM.Integration.WilsonReflectedPublicOpticalColumns
end
