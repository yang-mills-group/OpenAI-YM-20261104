import YM.Integration.WilsonPositionProgramNominatedRoster
import YM.Integration.WilsonPositionProgramReportedCell

/-! The restored cutoff coordinates enter the original normalized scalar
report. Its covered limit and the resolved center integral use these same
coordinates even when they depend on the external finite regulators. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionProgramNominatedReporter
open Function Filter Finset Lattice Wilson Labels RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof.East Next.Rank.Price WilsonOriginalThermometerPalette WilsonPositionThermometerCapStation
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops WilsonPositionProgramThermometerCoordinates
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonPositionProgramNormalizedMaster (fee)
open WilsonPositionProgramNominatedRoster (selected selected_fee)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
  {a D k u e:ℕ}

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices v R.kit)
    (big:0<D)(rails:Rails 0 k u e)(child:Fin (a+1)→Fin 3)(d:Fin (a+1)→ℕ)
    (fit:∀i,levels (child i)<d i)(cap:capP (deck (G:=G) (levels ∘ child) d fit) ≤ k)
    (δ:ℝ)(pos:0<δ):
    let Q:=deck (G:=G) (levels ∘ child) d fit
    let L:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,1 ≤ zz L m →
    ∀A:Group R.family 6,A.station.k=m → A.station.checked f H A.horizon →
    ∀(phase:Fin 3→ℂ →L[ℝ] ℝ)(Z:ℝ)(B:Fin (a+1)→ℝ)(ε:ℝ),0<ε →
    ∃K:ℕ,m ≤ K ∧ ∀N p:ℕ,m<N → ∀n:ℕ,K ≤ n →
    ∀(φ:Wilt Q),Compar L.S (zz L) m m ≤ Z → Bough Q φ 1 Z B →
    ∀t:ℕ,t ≤ e → ∀i:Alma ((primes G).F 0),
      let X:=selected R child d fit A m N p phase
      let x:=normalized L R.metals.O Q X m
      let read:=fun n=>∫o:CellR,(locale o (LodeStar L R.metals.O φ (x n) m m n 1)).2 t 0 Fin.elim0 ∂dayMeasure
      let fixed:=PowerSeries.coeff t (lodgeIn L R.metals.O ((primes G).T 0) big φ x m m m k i)
      Tendsto read atTop (𝓝 fixed) ∧ ‖read n-fixed‖ < ε := by
  intro Q L
  obtain ⟨c,w,tariff⟩:=WilsonPositionProgramNormalizedMaster.original R simple v paid big rails
    (levels ∘ child) d fit cap
  filter_upwards [tariff,WilsonPositionProgramThermometerCoordinates.original (f:=f) (H:=H) R simple δ pos e
      (fun j=>levels j+1) (fun _=>Nat.lt_succ_self _)] with m settled charged
  intro clock A date checked phase Z B ε tol
  let money (i:Fin (a+1)):ℝ:=price R e (child i)*‖phase (child i)‖*((L.clock.hatBeta m)^δ*salary R A)
  let F:=max 1 (c.buy Z*∏i,B i*(w.buy (zz L m)*money i))
  have limit:Tendsto (fun n=>F*trailC L.S m n) atTop (𝓝 0):=by
    simpa using (fade L.S m).const_mul F
  obtain ⟨n₀,stop⟩:=eventually_atTop.mp (limit (Iio_mem_nhds tol))
  let K:=max m n₀
  refine ⟨K,le_max_left ..,?_⟩
  intro N p top n enough φ room shape t grade i X x read fixed
  have base:paceT L.S m m=1:=by exact div_self (L.S.a_pos m).ne'
  have shape':Bough Q φ (paceT L.S m m) Z B:=base ▸ shape
  have income:0≤w.buy (zz L m):=zero_le_one.trans (w.purchase clock)
  have gross:c.buy Z*∏i,B i*(w.buy (zz L m)*fee X e i)≤F:=by
    apply le_trans _ (le_max_right 1 _)
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (c.purchase shape.pos))
    apply Finset.prod_le_prod
    · intro i _
      exact mul_nonneg (shape.lanes i).1 (mul_nonneg income
        (Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _))
    · intro i _
      apply mul_le_mul_of_nonneg_left _ (shape.lanes i).1
      apply mul_le_mul_of_nonneg_left _ income
      rw [show fee X e i=_ from selected_fee R child d fit A m N p e phase i]
      exact charged A date checked N p top phase (child i)
  let row:=fun n=>PowerSeries.coeff t (Reports L R.metals.O ((primes G).T 0) big φ (x n) m m m n k i)
  have seen:=settled X m m le_rfl le_rfl φ B Z room shape' t grade i
  have eq:row=read:=funext fun n=>WilsonPositionProgramReportedCell.original L R.metals.O
    ((primes G).T 0) big φ (x n) m n k t i
  have paired:=seen.2 K n (le_max_left ..) enough
  rw [←eq]
  exact ⟨seen.1,paired.gap.trans_lt ((mul_le_mul_of_nonneg_right gross (trail_pos ..).le).trans_lt
    (stop K (le_max_right ..)))⟩

end YM.Integration.WilsonPositionProgramNominatedReporter
end
