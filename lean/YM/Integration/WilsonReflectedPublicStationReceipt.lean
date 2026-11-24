import YM.Integration.WilsonReflectedAppointedIncome
import YM.Integration.WilsonReflectedPublicStationFare

/-! Fit the same physical matrix to both appointed fields, before inserting
any public measuring vector on either side. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicStationReceipt
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open GapsContact GapsContact.Seams GapsContact.Stamps Analysis Table Extraction Bid Spec Ascent Trace
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph Next.Rank.Price
open PhysicalNext PhysicalNext.Repeat.Legato OPE.Therm Push.AbsoluteSums.Animals
open WilsonReflectedOriginalTwoDeposit WilsonReflectedOriginalVanes WilsonThermometerUnitFilingFourPool
open WilsonOriginalMicroscopicGuardedReporters WilsonOriginalMicroscopicGuardedWallet
open scoped Classical BigOperators Topology
open WilsonOriginalNullCorridor WilsonPositionProgramOriginalBlockedTrial
open WilsonAddressedRestartedColumn WilsonPositionProgramBlockedPublicExperiment
open WilsonOriginalMicroscopicGuardedPage
open WilsonReflectedFullPanel WilsonReflectedPublicStationFare WilsonPositionProgramPublicStations
open MergeProof.East Climb WilsonMeasuredPublicBank
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G)
local notation "C₀" => R.family
local notation "A₀" => R.family.path.levels
local notation "F₀" d:max => R.family.labels.level d

theorem appointed (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1 ≤ ((A₀).budget j).supportExponent)(law:OPE.Therm.Poetry (A₀))
    (d q:ℕ){η:ℝ}(positive:0<η):
    ∃floor:ℕ,∀ j,floor ≤ j → (C₀).ref d ≤ j → ∀ K N p (before:j ≤ K) (high:K ≤ N), j<N →
      ∃M:(C₀).label d ≃ₗ[ℂ] (C₀).label d, ∀Y bank, Next.UVStress.quota (C₀) d j N p Y ≤ bank →
        receipt R d j K N p q before high η M Y bank:=by
  obtain ⟨first,offer⟩:=WilsonOriginalMicroscopicGuardedReporters.original R (fun _=>d) simple shop wide law q positive
  obtain ⟨second,hear⟩:=eventually_atTop.mp (WilsonReflectedAppointedIncome.original R simple d)
  refine ⟨max first (max second (R.t d)),?_⟩
  intro j late ref K N p before high live
  obtain ⟨A,fit,_⟩:=offer (fun _=>j) (fun _=>(le_max_left ..).trans late) K
    (fun _=>before) (fun _=>0) N p high (fun _=>live)
  refine ⟨A 0,?_⟩
  intro Y bank fund
  have matched:=fit 0 (full R d N p j Y)
  apply hear j ((le_max_left ..).trans ((le_max_right ..).trans late)) K N p q before high η (A 0) Y bank matched
  have value:=WilsonOriginalMicroscopicGuardedPage.wage (p:=p) R d
    ((le_max_right ..).trans ((le_max_right ..).trans late)) ref live.le (wide j) Y
  have safe:0≤1+wrapCost R d j:=by
    have w:0≤WilsonCapturedPrimaryCoreBill.wrapFee (F₀ d) (C₀).params:=
      mul_nonneg (Nat.cast_nonneg _) (germ_close (F₀ d) (C₀).params).choose_spec.1.le
    exact add_nonneg zero_le_one (mul_nonneg (mul_nonneg w (Real.exp_nonneg _)) (zero_le_one.trans ((A₀).params _).columns_ge))
  exact matched.1.trans (mul_le_mul_of_nonneg_left (value.2.trans (mul_le_mul_of_nonneg_left fund safe))
    (by unfold WilsonOriginalMicroscopicGuardedReporters.stretch;positivity))

variable {h:Extraction.Order} {S:Table R.family.book} (F:Final R.family h S)
    {l:Ultrafilter (ℕ×ℕ)} {H:(Bel R.family.book).Hierarchy} {D d k:ℕ} {s r B:ℝ}
    {stock:Bank F l D s B} {cap:d≤D} {W:Vane R.family k} {fits:D≤k} {T:Spin.change S d}

/-- In particular, both genuine sources of the published four-frame use their
own guarded physical inverse with its unit, on one common trial mesh K. -/
theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1 ≤ ((A₀).budget j).supportExponent)(law:OPE.Therm.Poetry (A₀))
    (q:ℕ){η:ℝ}(positive:0<η):
    ∃floor:ℕ,∀ (P:Pair F stock cap W fits T r), W.checked h H k →
    (∀b,floor ≤ station F P b) → ∀ K N p (before:∀b,station F P b ≤ K) (high:K ≤ N),
    (∀b,station F P b<N) → ∃M:Bool→(C₀).label d ≃ₗ[ℂ] (C₀).label d, ∀ b (v:S.Field d),
      receipt R d (station F P b) K N p q (before b) high η (M b) ((P.arm b v).source (N,p))
        ((C₀).S.a (station F P b)^d*fee F P b v):=by
  obtain ⟨n,issue⟩:=appointed R simple shop wide law d q positive
  refine ⟨n,?_⟩
  intro P sold late K N p before high live
  have one(b:Bool):=issue (station F P b) (late b) (WilsonReflectedPublicStationFare.original F P sold b 0).1 K N p (before b) high (live b)
  choose M ready using one
  exact ⟨M,fun b v=>ready b _ _ ((WilsonReflectedPublicStationFare.original F P sold b v).2 N p (live b))⟩

end YM.Integration.WilsonReflectedPublicStationReceipt
end
