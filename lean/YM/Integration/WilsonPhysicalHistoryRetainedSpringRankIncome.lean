import YM.Integration.WilsonPhysicalHistoryRetainedSpringRankClock
import YM.Integration.WilsonPhysicalHistoryRetainedSpringRankSum
import YM.Integration.WilsonPhysicalHistoryRetainedSpringPitchSubpower

/-! The complete absolute coefficient mass of one rooted old action is of
order three in the actual physical coupling, uniformly before the cutoff and period. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open LocalComparison Marker Global FullQLocal IterationFour IterationFour.Vacuum
open Filter Finset Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree MeasureTheory
open ConnectedActivityE6 ConnectedActivityE6.Coat Push Precision Exterior Shell Channel Next.Fluctuations SectorMeasure
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Malachite
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Physical WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Bank.Bloom WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonStartup Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoherentMayerHearing WilsonPositionSeparatedProfileMayerWickInputs
open Lattice RG Pressure Pressure.Tube Tree Wilson Finset Precision Exterior Work.F03 Bid
open ConnectedActivityE6 Shell Coat Matter SliceRows Channel Push SectorMeasure Census Control Window RGLocalTaylor
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonStartup
open WilsonCoherentMayerHearing Dict06.Series PhysicalNext.Repeat.Malachite WilsonPositionSeparatedProfileMayerWickInputs
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Dict06.Series RGLocalTaylor.Insert Work.F03 Bid
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonStartup
open scoped Topology BigOperators Classical
variable {G : Gauge}

theorem cofinal_spring_rank (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (v : ℕ→Gear G→ℝ) (rows : FundedMarkedCoverRows.prices v R.kit) (credit : Credit) (d M r K : ℕ)
    {ε η : ℝ} (ep : 0<ε) (hp : 0<η) :
    let V:=R.family.path.levels
    ∀ᶠ m : ℕ in atTop,∀ N : ℕ,m+1<N → ∀ per : ℕ,
      let j:=m+1
      let C:=credit.buy (zz V j)+zz V j*V.clock.loopCap j
      let g:=Pert.Asymptotics.regulatorRun R.family N per j
      ∀ {σ : ℝ},0<σ → σ⁻¹≤zz V j → ∀ Z : SeriesA G,Draw Z σ C → Z.length≤M →
        (∀a∈Z,3≤a.grade) → (∀a∈Z,a.grade≤d) →
      ∀ {u : Side} {S : StepData u (R.family.side j per)} {T : Tube G S} {F : Forest S.ratio}
        (X : Coat T F) (x : Site (R.family.side j per)),
        Rise.coin (registeredSpring R N per j r Z X x K g)≤ε*g^((3:ℝ)-η) := by
  intro V
  let δ:=η/4
  have pos : 0<δ:=by dsimp only [δ];positivity
  let k:=r-2+1
  let total:=springRankTotal G k K d M
  have total0 : 0≤total:=rank_total_nonneg .. 
  obtain ⟨_,temper⟩:=cofinal_temperature R simple v rows r
  have fees (a : Fin (d+1)):=cofinal_rank_unit R simple (a.val+2) K 0 zero_lt_one pos
  filter_upwards [cofinal_rank_factor R simple 0 total total0 ep (half_pos hp),
    cofinal_rank_unit R simple 2 K 2 zero_lt_one pos,cofinal_rank_unit R simple 3 K 1 zero_lt_one pos,
    cofinal_rank_unit R simple 4 K 1 zero_lt_one pos,Filter.eventually_all.mpr fees,
    cofinal_path_scale R simple slow,WilsonVacuumPreResetRenderIncome.original R simple credit pos,
    (tendsto_add_atTop_nat 1).eventually (pitch_subpower R simple v rows r pos),
    (tendsto_add_atTop_nat 1).eventually temper] with m constant pair three four charged width bank pitched temp
  intro N later per j C g σ hs within Z filed limit low high u S T F X x
  let D:=V.params j
  let z:=zz V j
  let Gz:=Real.exp z
  let E:=g^(-δ)
  let γ:=g^2*pitchTail R N j r g
  let p:=finitePitch R N j r g
  let path:=(R.family.path.rep N per j).path
  have few : m<N:=Nat.lt_of_succ_lt later
  have cash:=bank N per few
  have hg : 0<g:=cash.1
  have g1 : g≤1:=cash.2.1
  have e0 : 0≤E:=Real.rpow_nonneg hg.le _
  have large : 1≤E:=Real.one_le_rpow_of_pos_of_le_one_of_nonpos hg g1 (neg_nonpos.mpr pos.le)
  have rep : R.family.path.Conv N per j:=R.makes.wilson.represents N per j later.le
  have actual : path.Bounds D.clip D.width D.paths (V.clock.loopCap j):=by
    dsimp only [path,D,V];rw [←rep.clip];exact rep.good.paths
  have direct : |D.clip.direct|≤1:=by
    rw [abs_of_pos D.clip.quadratic_pos]
    exact Push.PriceCompiler.Canonical.direct_le_one (R.alloy.B.support.cap j j le_rfl).metric
  have lo : 1/2≤p:=(temp N later per).2.2.1
  have hi : p≤3/2:=(temp N later per).2.2.2.1
  have pitch:=pitched N later per
  have gamma : |γ|≤g^2*(k:ℝ)*E:=by
    dsimp only [γ];rw [abs_mul,abs_of_nonneg (sq_nonneg _),mul_assoc]
    exact mul_le_mul_of_nonneg_left pitch.2.2 (sq_nonneg _)
  have wcap : |γ+R.alloy.B.kin.alpha N j|≤((k:ℝ)+1)*E:=by
    apply (abs_add_le ..).trans
    calc _ ≤ g^2*(k:ℝ)*E+E:=add_le_add gamma pitch.1
         _ ≤ 1*(k:ℝ)*E+E:=by gcongr;exact pow_le_one₀ hg.le g1
         _ = _:=by ring
  let H:=fun l : ℕ=>(max 1 D.width⁻¹)^siteRankPower l K*siteRankPaper G l K
  have hn (l : ℕ) : 0≤H l:=mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left ..)) _) (sum_nonneg fun _ _=>abs_nonneg _)
  have paid2 : Gz^2*H 2≤E:=by simpa only [one_mul] using pair N per few D.width width.2.1
  have gram:=site_root_factor X (gramEntries path) (by decide) actual.width (gram_finance path actual) x K hg.le g1
    (gram_rank_fee G D.paths_pos.le width.1 (hn 2) paid2)
  have paid3 : Gz*H 3≤E:=by simpa only [pow_one,one_mul] using three N per few D.width width.2.1
  have paid4 : Gz*H 4≤E:=by simpa only [pow_one,one_mul] using four N per few D.width width.2.1
  have tri:=site_root_factor X path.cubic (by decide) actual.width actual.three x K hg.le g1
    ((mul_le_mul_of_nonneg_right width.1 (hn 3)).trans paid3)
  have quart:=site_root_factor X path.quartic (by decide) actual.width actual.four x K hg.le g1
    ((mul_le_mul_of_nonneg_right width.1 (hn 4)).trans paid4)
  have atom (a : PrismA G) (ha : a∈Z) : Rise.coin (sitePortfolio X a.cells x K g)≤g^(a.rise+2)*(3*E^2):=by
    have ah:=a.rankA.trans (high _ ha)
    have price (i:Fin (d+1)):=charged i N per few σ (within.trans width.2.2)
    have amount : (max 1 σ⁻¹)^siteRankPower (a.rise+2) K*siteRankPaper G (a.rise+2) K≤E:=by
      simpa only [pow_zero,one_mul] using price ⟨a.rise,by omega⟩
    apply site_root_factor X a.cells (by omega) hs (filed.2 a ha).toll x K hg.le g1
    calc _≤(3*E)*E:=mul_le_mul ((le_abs_self C).trans cash.2.2.1) amount
              (mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left ..)) _) (sum_nonneg fun _ _=>abs_nonneg _)) (by positivity)
         _=_:=by ring
  have expense:=spring_rank_sum X D.clip path Z x k K d M hg g1 large limit direct gamma wcap lo hi low high gram tri quart atom
  have save : total≤ε*g^(-(η/2)):=by simpa only [pow_zero,mul_one] using constant N per few
  apply expense.trans
  calc total*g^3*E^2≤(ε*g^(-(η/2)))*g^3*E^2:=by gcongr
       _ = ε*(g^(-(η/2))*g^(3:ℝ)*g^(-δ)*g^(-δ)):=by
             dsimp only [E];rw [show g^(3:ℝ)=g^(3:ℕ) from Real.rpow_natCast g 3];ring
       _ = _:=by rw [←Real.rpow_add hg,←Real.rpow_add hg,←Real.rpow_add hg];dsimp only [δ];ring_nf

end YM.Integration.OriginalMarkedRunAction
