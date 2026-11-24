import YM.Integration.ActualStartupAlbumBudget
import YM.Integration.FullQLocalNumericSchedule

/-! The fixed original-album budget is paid by the existing actual schedule.
Its geometry bill already contains the next monitor, which diverges on the
same Run. All rows and requested norm fields remain unchanged. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualStartupAdmittedAlbum
open Filter Lattice Wilson RG
open PhysicalNext.Repeat.Legato
open FullQLocal.RenderedStep
open scoped Topology

variable {G : Gauge} {V : Type}

/-- Every fixed finite cost is eventually below the original schedule bill.
No new rate, cost field, or increase of that bill is introduced. -/
theorem eventually_cost (R : Run G) (hG : G.Simple)
    (J : Request V) (A : NumericSchedule R.family J) (K : ℝ) :
    ∀ᶠ m : ℕ in atTop, K ≤ A.admittedCost m := by
  let D := R.family.path.levels
  have hdiv : Tendsto D.clock.hatBeta atTop atTop :=
    tendsto_atTop_add_const_left _ _
      (D.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hG))
  have ht : Tendsto
      (fun m : ℕ => Real.log (Real.log (D.clock.hatBeta (m + 1))))
      atTop atTop :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hdiv)).comp
      (tendsto_add_atTop_nat 1)
  filter_upwards [ht.eventually_ge_atTop K] with m hm
  have hmonitor : K ≤ D.clock.monitor (m + 1) := by
    change K ≤ Real.exp ((Real.log (Real.log (D.clock.hatBeta (m + 1)))) ^ 2)
    have he := Real.add_one_le_exp
      ((Real.log (Real.log (D.clock.hatBeta (m + 1)))) ^ 2)
    nlinarith [sq_nonneg
      (Real.log (Real.log (D.clock.hatBeta (m + 1))) - (1 / 2 : ℝ))]
  have hloop (k : ℕ) : 0 ≤ D.clock.loopCap k := by
    change 0 ≤ 2 * (D.clock.monitor k) ^ (D.clock.theta (D.clock.J k))
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Real.exp_nonneg _) _)
  have hcover0 : 0 ≤ (D.clock.coverSize m : ℝ) := Nat.cast_nonneg _
  have hcover1 : 0 ≤ (D.clock.coverSize (m + 1) : ℝ) := Nat.cast_nonneg _
  have hmonitor0 : 0 ≤ D.clock.monitor m := Real.exp_nonneg _
  have hpath0 := (D.params m).paths_pos
  have hpath1 := (D.params (m + 1)).paths_pos
  have hcolumn0 := (D.params m).columns_ge
  have hcolumn1 := (D.params (m + 1)).columns_ge
  have hrelax0 := (D.params m).clip.radius_pos
  have hrelax1 := (D.params (m + 1)).clip.radius_pos
  have hbill := A.cost_covers_geometry m
  change 1 + (D.clock.coverSize m : ℝ) + (D.clock.coverSize (m + 1) : ℝ) +
    D.clock.monitor m + D.clock.monitor (m + 1) +
    D.clock.loopCap m + D.clock.loopCap (m + 1) +
    (D.params m).paths + (D.params (m + 1)).paths +
    (D.params m).columns + (D.params (m + 1)).columns +
    (D.params m).clip.relaxation + (D.params (m + 1)).clip.relaxation ≤
      A.admittedCost m at hbill
  linarith [hloop m, hloop (m + 1)]

/-- At every sufficiently late startup level, the literal requested paid
album has the schedule's advertised budget. The chosen width bound and
finite rank-capacity check stay visible; no marked-test cost is inferred. -/
theorem eventually_paid_layers (R : Run G) (hG : G.Simple)
    (J : Request V) (A : NumericSchedule R.family J)
    (hrank : J.order + 2 ≤ J.vacuumRankCap) :
    ∀ᶠ m : ℕ in atTop, ∀ period : ℕ, A.inputWidth m ≤ 1 →
      Nonempty (FullQLocal.GradedVacuumLayers
        (ActualStartupInvoice.paidAlbum G (R.family.side (m + 1) period)
          (A.inputNorm m) (R.family.path.levels.params (m + 1))
          J.order (A.inputWidth m))
        (A.inputNorm m) J.order J.vacuumRankCap (A.inputWidth m)
        (A.admittedCost m)) := by
  filter_upwards [eventually_cost R hG J A
    (ActualStartupAlbumBudget.budget G J.inputSupport J.order)] with m hm period hw
  have hQ := ActualRepeatedNorm.norm_unique R.family
    J.inputFieldOrder J.inputDistanceOrder J.inputSupport
    (J.field_minimum.trans J.field_reserve)
    (J.distance_minimum.trans J.distance_reserve) J.input_support_pos
    (m + 1) (A.inputNorm m) (A.input_norm m)
  rw [hQ]
  obtain ⟨H⟩ := ActualStartupAlbumBudget.paid_layers R
    J.inputFieldOrder J.inputDistanceOrder J.inputSupport
    (J.field_minimum.trans J.field_reserve)
    (J.distance_minimum.trans J.distance_reserve) J.input_support_pos
    (m + 1) period J.order J.vacuumRankCap hrank (A.inputWidth m)
    (A.input_width_pos m).le hw
  refine ⟨{
    packets := {
      atom := H.packets.atom
      rank_bounded := H.packets.rank_bounded
      invariant := H.packets.invariant
      original_action := H.packets.original_action
      support := H.packets.support
      pieceCost := H.packets.pieceCost
      piece_cost_nonnegative := H.packets.piece_cost_nonnegative
      exponential := H.packets.exponential
      total := H.packets.total.trans hm
      coverOffset := H.packets.coverOffset
      coverSlope := H.packets.coverSlope
      cover := H.packets.cover
      width_reserved := H.packets.width_reserved
      cover_cost := H.packets.cover_cost.trans hm }
    orders := H.orders
    leading_rank := H.leading_rank }⟩

end YM.Integration.ActualStartupAdmittedAlbum
end
