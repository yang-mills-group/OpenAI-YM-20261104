import YM.Integration.WilsonReflectedPublicSignedFare
/-! Both pre-appointed reflected programmes, their true inverse at K and the
signed native coefficients of the replacements at the common reporting mesh. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicOpticalSwaps
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
      let K := WilsonInvariantActionPosition.berth R (WilsonReflectedOpticalRate.depth (q+1+2) (2*T+9) D) f
      ∃ h : f < K, ∃ start : ∀ b, station F P b ≤ f,
      ∀ N p (top : K ≤ N),
      ∃ M : Bool → (C₀).label d ≃ₗ[ℂ] (C₀).label d, ∀ b (v : S.Field d),
      let Y := (P.arm b v).source (N,p)
      let j := station F P b
      let w := (M b).symm (full R d N p j Y)
      receipt R d j K N p jets ((start b).trans h.le) top (1/32) (M b) Y (mesh j^d*fee F P b v) ∧
      ∀ side s o, ∃ A : Arm R d N p f K, A.Y = Y ∧ A.w = w ∧ A.b = side ∧ A.s = s ∧ A.o = o ∧
        Priced R A (C*((β f)^(q+1))⁻¹*(mesh f)^d*fee F P b v) ∧
        (∃ B : Arm R d N p K K, Situated R h.le A B) ∧
        ∀ factor:ℂ, ‖factor‖≤1 → ∃E, WilsonReflectedPublicSignedFare.Restored R A h.le top factor
          ((2+Extra.Histories.Motion.orbitCost ((C₀).labels.level d))*C*((β f)^q)⁻¹*fee F P b v) E :=by
  obtain ⟨C,cp,market⟩:=WilsonReflectedPublicOpticalColumns.original F simple bliss slow shop width capWidth law D d T (q+1) jets cap
  obtain ⟨b₀,restore⟩:=eventually_atTop.mp (WilsonReflectedPublicSignedFare.original R simple shop d q)
  refine ⟨C,cp,?_⟩
  filter_upwards [market,WilsonReflectedPublicStationLate.original F simple bliss T b₀]
    with r quote far k stock W fits U P checked same
  let f:=WilsonInvariantActionPosition.berth R 5 (max stock.j W.k)
  let K:=WilsonInvariantActionPosition.berth R (WilsonReflectedOpticalRate.depth (q+1+2) (2*T+9) D) f
  obtain ⟨h,start,buy⟩:=quote P checked same
  refine ⟨h,start,?_⟩
  intro N p top
  obtain ⟨M,issued⟩:=buy N p top
  refine ⟨M,?_⟩
  intro b v
  obtain ⟨receipt,owned⟩:=issued b v
  refine ⟨receipt,?_⟩
  intro side s o
  obtain ⟨A,Y,w,real,sign,loc,budget,B⟩:=owned side s o
  refine ⟨A,Y,w,real,sign,loc,budget,B,?_⟩
  intro factor small
  obtain ⟨dates,income⟩:=WilsonReflectedPublicStationFare.original F P checked b v
  have salary:=income N p (((start b).trans_lt h).trans_le top)
  have nn:0≤Next.UVStress.quota (C₀) d (station F P b) N p ((P.arm b v).source (N,p)):=by
    unfold Next.UVStress.quota Labels.Frame.coeffSize;positivity
  have mp:=nonneg_of_mul_nonneg_right (nn.trans salary) (pow_pos ((C₀).S.a_pos _) d)
  exact restore f ((far P checked same b).trans (start b)) N p K A h.le top (dates.trans (start b))
    C (fee F P b v) cp.le mp budget factor small

end YM.Integration.WilsonReflectedPublicOpticalSwaps
end
