import YM.Integration.WilsonOlderFreshSoftSocketVane
import YM.Integration.WilsonAddressedPublicOpticalClock
import YM.Integration.WilsonPositionThermometerStationNorm
import YM.Integration.WilsonPositionCapTransport

/-! On the original family of radii the whole station's income grows by an arbitrarily small power of the later planting budget. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationMass
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

theorem original (simple:G.Simple)(A:ℝ→Group C 6)(P:ℝ→tower S)
    (paid:Book (f:=f) (l:=Y) (H:=H) A P){η:ℝ}(ep:0<η):
    ∃B:Fin 3→ℝ,(∀i,0≤B i) ∧ ∀ᶠr in trail,∀K:ℕ,(A r).station.k≤K→∀i:Fin 3,
      quotaFare R (A r) i≤B i*((road).clock.hatBeta K)^η:=by
  obtain ⟨b,b1,price⟩:=WilsonAddressedPublicOpticalClock.monitor (R:=R) simple ep
  let u (i:Fin 3):=(source C univ i)
  let cost (i:Fin 3):=WilsonPositionThermometerStationNorm.cost C (grade i)
  let wage (i:Fin 3):=cost i*(‖u i‖+1)
  have c0 (i:Fin 3):0≤cost i:=mul_nonneg (Nat.cast_nonneg _) (ContinuousLinearMap.opNorm_nonneg _)
  have w0 (i:Fin 3):0≤wage i:=mul_nonneg (c0 i) (by positivity)
  refine ⟨fun i=>128*b*wage i,fun i=>mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans b1)) (w0 i),?_⟩
  have same:localCost trail P P:=fun d x=>by simp
  have front (i:Fin 3):∀ᶠr in trail,‖(A r).change (grade i) (u i)‖≤‖u i‖+1:=by
    have go:Tendsto (fun r=>(A r).change (grade i) (u i)) trail (𝓝 (u i)):=by
      simpa only [WilsonPositionCapTransport.through,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply] using WilsonPositionCapTransport.near P P A paid same (grade i) (u i)
    exact (go.norm.eventually_lt_const (lt_add_one _)).mono fun r hr=>hr.le
  have dates:Tendsto (fun r=>(A r).station.k) trail atTop:=
    tendsto_atTop.mpr fun k=>(paid k).mono fun _ h=>h.1
  have tiny:∀ᶠr in trail,r<1:=
    (show Tendsto id trail (𝓝 (0:ℝ)) from tendsto_id.mono_left nhdsWithin_le_nhds).eventually_lt_const zero_lt_one
  filter_upwards [paid 0,eventually_all.mpr front,tiny,dates.eventually (WilsonMaxwellThermometerStationHeads.clock R simple)] with r live move small heat
  intro K after i
  let k:=(A r).station.k
  let j:=index (A r) (grade i)
  let monitor:=(road).clock.monitor k
  have a1:1 ≤ monitor:=le_trans (by norm_num:(1:ℝ)≤2) heat.2.1
  have d6:j.val/2≤6:=by change (grade i).val/2≤6;have h:=(grade i).isLt;omega
  have r0:0≤Station.gap road (A r).station.b k:=(A r).station.wheel.rad.le
  have r1:Station.gap road (A r).station.b k≤1:=live.2.2.1.le.trans small.le
  have g1:(Station.gap road (A r).station.b k)^j.val≤1:=pow_le_one₀ r0 r1
  have measured:((C).labels.level j).coeffSize (ladder C j ((A r).change (grade i) (u i)))≤wage i:=
    (WilsonPositionThermometerStationNorm.ladder C j _).trans (mul_le_mul_of_nonneg_left (move i) (c0 i))
  have raw:(2*monitor)^(j.val/2)≤64*(b*((road).clock.hatBeta K)^η):=by
    calc
      (2*monitor)^(j.val/2)≤(2*monitor)^6:=pow_le_pow_right₀ (by linarith only [a1]) d6
      _=64*monitor^6:=by rw [mul_pow];norm_num
      _≤_:=mul_le_mul_of_nonneg_left (price after) (by norm_num)
  calc
    quotaFare R (A r) i=2*(Station.gap road (A r).station.b k)^j.val*(2*monitor)^(j.val/2)*
      ((C).labels.level j).coeffSize (ladder C j ((A r).change (grade i) (u i))):=rfl
    _≤2*1*(64*(b*((road).clock.hatBeta K)^η))*wage i:=by
      have h₀:0≤b:=zero_le_one.trans b1
      have hβ:0≤(road).clock.hatBeta K:=zero_le_one.trans ((road).fits.delayed K).le
      have hscore:0≤((C).labels.level j).coeffSize (ladder C j ((A r).change (grade i) (u i))):=
        sum_nonneg fun _ _=>norm_nonneg _
      gcongr
    _=_:=by ring

end YM.Integration.WilsonOlderFreshSoftSocketStationMass
end
