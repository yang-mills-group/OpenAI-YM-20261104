import YM.Integration.WilsonOriginalObservedRoseMeshHeight
import YM.Integration.WilsonOlderFreshSoftSocketStationMass
import YM.Integration.WilsonReflectedOpticalStock

/-! Real regulator-uniform source expenses of the original three Rose columns including the zero basis choice. Their physical engineering scale is kept separately from the moving coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseVanePurse
open Function Filter Finset RG Lattice Wilson Source Labels Next.Rank Next.Rank.Price Next.Rank.Atlas
open Next.Rank.Station Further.CorrectedLift Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open Spec OPE OPE.Orbits RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize WilsonPositionCapTransport
open WilsonOlderFreshSoftSocketVane (quotaFare)
open scoped Classical BigOperators Topology

variable {G:Gauge}(R:Run G){f:Extraction.Order}{Y:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
    {S:Table R.family.book}
local notation "C" => R.family
local notation "road" => R.family.path.levels

open WilsonOriginalObservedRoseMeshHeight (variation)
open WilsonOriginalMicroscopicGuardedPage (wrapCost)
open Extra.Histories.Motion (orbitCost orbitCost_one_le)
open WilsonCapturedPrimaryCoreBill (wrapFee)
open Trace.Physical.Germ
open Source
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "a" => R.family.S.a

def ages:Fin 3→ℕ:=fun i=>(grade i).val

private theorem wrapped (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (wide:∀j,((road).budget j).supportExponent≤100)(d:ℕ):
    ∃cash:ℝ,0≤cash ∧ ∀ᶠj:ℕ in atTop,∀K,j≤K→0≤1+wrapCost R d j ∧ 1+wrapCost R d j≤cash*(β K):=by
  let bill:=wrapFee ((C).labels.level d) (C).params
  have bp:0≤bill:=mul_nonneg (Nat.cast_nonneg _) (germ_close ((C).labels.level d) (C).params).choose_spec.1.le
  refine ⟨1+bill*Real.exp 200,by positivity,?_⟩
  filter_upwards [WilsonReflectedOpticalStock.columns R simple slow] with j count
  intro K jk
  have stock:((road).params j).columns≤β K:=count.trans (WilsonReflectedOpticalStock.monotone R simple jk)
  have expo:Real.exp (2*((road).budget j).supportExponent)≤Real.exp 200:=
    Real.exp_le_exp.mpr (by linarith [wide j])
  have bound:wrapCost R d j≤bill*Real.exp 200*(β K):=
    mul_le_mul (mul_le_mul_of_nonneg_left expo bp) stock (zero_le_one.trans ((road).params j).columns_ge) (by positivity)
  have zero:0≤wrapCost R d j:=mul_nonneg (mul_nonneg bp (Real.exp_nonneg _)) (zero_le_one.trans ((road).params j).columns_ge)
  constructor
  · linarith
  · linarith only [bound,((road).fits.delayed K).le]

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (wide:∀j,((road).budget j).supportExponent≤100)(A:ℝ→Group C 6)(P:ℝ→tower S)
    (paid:Book (f:=f) (l:=Y) (H:=H) A P):
    ∃B:Fin 3→ℝ,(∀i,0≤B i) ∧ ∀ᶠr in trail,
      let k:=(A r).station.k
      ∀N per K:ℕ,k<N→k≤K→∀i:Fin 3,
        variation R ages k N per i (WilsonNeutralOffsetCutoff.named R (A r) N per i)*(a k)^ages i≤B i*(β K)^2:=by
  obtain ⟨W,W0,vane⟩:=WilsonOlderFreshSoftSocketStationMass.original R simple A P paid (η:=1) zero_lt_one
  choose overhead overhead0 cash using fun i:Fin 3=>wrapped R simple slow wide (ages i)
  let orb(i:Fin 3):=orbitCost (R.family.labels.level (ages i))
  have orb0(i:Fin 3):0≤orb i:=zero_le_one.trans (orbitCost_one_le _)
  refine ⟨fun i=>2*orb i*(overhead i*W i),fun i=>mul_nonneg (mul_nonneg (by norm_num) (orb0 i)) (mul_nonneg (overhead0 i) (W0 i)),?_⟩
  have dates:Tendsto (fun r=>(A r).station.k) trail atTop:=
    tendsto_atTop.mpr fun j=>(paid j).mono fun _ h=>h.1
  filter_upwards [vane,paid 0,dates.eventually (eventually_all.mpr cash),
    dates.eventually (WilsonOlderFreshSoftSocketVane.original (f:=f) (H:=H) R simple)] with r finance issued weights source
  intro k N per K deep before i
  let y:=WilsonNeutralOffsetCutoff.named R (A r) N per i
  have registered:Next.UVStress.quota R.family (ages i) k N per y≤quotaFare R (A r) i:=
    source (A r) rfl issued.2.1 N per deep i
  have quota:Next.UVStress.quota R.family (ages i) k N per y≤W i*β K:=
    registered.trans (by simpa only [Real.rpow_one] using finance K before i)
  have nonnegative:0≤Next.UVStress.quota R.family (ages i) k N per y:=by
    unfold Next.UVStress.quota Frame.coeffSize;exact Finset.sum_nonneg fun _ _=>norm_nonneg _
  obtain ⟨wn,wb⟩:=weights i K before
  have mesh:0≤a k^(ages i):=(pow_pos ((R.family).S.a_pos k) _).le
  calc variation R ages k N per i y*(a k)^ages i=
        |2*orb i*((1+wrapCost R (ages i) k)*
            (Next.Rank.Spindle.paid R.family (ages i) k N per y*(a k)^ages i))|:=by
           unfold WilsonOriginalObservedRoseMeshHeight.variation
           rw [←abs_of_nonneg mesh,←abs_mul]
           congr 1;simp only [orb,abs_of_nonneg mesh];ring
       _=2*orb i*((1+wrapCost R (ages i) k)*Next.UVStress.quota R.family (ages i) k N per y):=by
          rw [WilsonMatrixTicketLanesQuota.quota,abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) (orb0 i)) (mul_nonneg wn nonnegative))]
       _≤2*orb i*((overhead i*β K)*(W i*β K)):=mul_le_mul_of_nonneg_left
          (mul_le_mul wb quota nonnegative (mul_nonneg (overhead0 i) (zero_lt_one.trans ((road).fits.delayed K)).le)) (mul_nonneg (by norm_num) (orb0 i))
       _=(2*orb i*(overhead i*W i))*(β K)^2:=by ring

end YM.Integration.WilsonOriginalObservedRoseVanePurse
end
