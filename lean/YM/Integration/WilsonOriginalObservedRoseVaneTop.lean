import YM.Integration.WilsonOriginalObservedRoseVanePurse
import YM.Integration.WilsonOriginalObservedRoseScaledWallet

/-! Radius-restored pre-J_stop mass of every face of the actual elected original Rose. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseVaneTop
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

open Finset
open WilsonOriginalObservedRoseVanePurse (ages)
open WilsonOriginalObservedRoseMeshHeight (tilt height)
open WilsonOriginalObservedRoseScaledWallet (share)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonReceivedCanonicalVersePortfolio (weight Selection wallet)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonThermometerDeclaredSeeds
local notation "F" i:max => R.family.labels.level (ages i)
local notation "J" => Stock.census (Fin 3)

theorem wallet_scale (B:Fin 3→ℝ)(t:ℝ)(s:Finset (Fin 3)):
    wallet R ages (fun i=>B i*t) s=wallet R ages B s*t^(Fintype.card s):=by
  simp only [wallet,←mul_assoc,prod_mul_distrib,prod_const,card_univ]

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1≤((road).budget j).supportExponent)(narrow:∀j,((road).budget j).supportExponent≤100)
    (group:ℝ→Group C 6)(P:ℝ→tower S)(paid:Book (f:=f) (l:=Y) (H:=H) group P):
    ∃B:Fin 3→ℝ,(∀i,0≤B i) ∧ ∀m:ℕ,∀ᶠr in trail,
      let k:=(group r).station.k
      ∀(N per b K requested power tag:ℕ)(credit:ℝ)(bk:b≤K)(kn:K≤N),b<N→
        ∀(T:Panel R ages N per b K bk kn requested power tag credit)(file:Filed R ages K),
        T.slot=file.station→T.axis=file.A N per→(∀i,T.slot i=k)→
        (∀i,T.names i=WilsonNeutralOffsetCutoff.named R (group r) N per i)→
        ∀s:(J).Mode, ∀z:ℝ,1≤z → (a k)/(a K)≤z^m → r/(a K)≤z^m →
        let w:=votes R ages (N:=N) (per:=per) file T.names T.turn
        r^(height ages s.val)*(∑q:Selection R ages s.val,‖weight R ages N per K w s.val q‖)≤
          wallet R ages B s.val*(β K^2)^(Fintype.card s.val)*z^(m*height ages s.val+1):=by
  obtain ⟨B,B0,funded⟩:=WilsonOriginalObservedRoseVanePurse.original R simple slow narrow group P paid
  refine ⟨B,B0,?_⟩
  intro m
  have positive:0<tilt 3 m:=by unfold tilt;positivity
  obtain ⟨L,fitted⟩:=WilsonOriginalObservedRoseMeshPurse.original R ages simple shop wide positive
  filter_upwards [funded,paid L,self_mem_nhdsWithin] with r salaries booked rp
  intro k N per b K requested power tag credit bk kn deep T file station axes homes names s z large age top w
  have stocked:=fitted N per b K bk kn requested power tag credit T file station axes (fun i=>homes i ▸ booked.1) deep
  have past:k≤b:=homes 0 ▸ T.before 0
  have feepos(i:Fin 3):0≤B i*(β K)^2:=mul_nonneg (B0 i) (sq_nonneg _)
  have shares(i:Fin 3):r^(ages i)*(F i).coeffSize (w i)≤(B i*(β K)^2)*z^(m*ages i)*share 3 z:=by
    have wage:=stocked.1 i
    rw [homes i,names i] at wage
    apply WilsonOriginalObservedRoseScaledWallet.columns R ages m k K N per i _ _ rp large age top _ (salaries N per K (past.trans_lt deep) (past.trans bk) i)
    exact wage
  have result:=WilsonOriginalObservedRoseScaledWallet.original R ages N per K m kn w s.val (fun i=>B i*(β K)^2) rp large feepos (fun i _=>shares i)
  rwa [wallet_scale] at result

end YM.Integration.WilsonOriginalObservedRoseVaneTop
end
