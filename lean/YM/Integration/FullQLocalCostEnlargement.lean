import YM.Integration.FullQLocalNumericStepData

/-!
Enlarge only the auxiliary admitted-cost function. Every norm, width, radius,
rate and physical family stays fixed, and the original numerical prices are
transported without replacement. The new cost must have its own uniform
subpower bound; this is not inferred from a new choice of prices.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FullQLocalCostEnlargement
open Filter Lattice Wilson RG Marker Comparison.RG02
open IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep
open scoped Topology BigOperators

variable {G : Gauge} {V : Type} {C : Family G} {J : Request V}
    (A : NumericSchedule C J) (B : ℕ → ℝ)
    (hB : ∀ m, A.admittedCost m ≤ B m)
    (hsub : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ start : ℕ, ∀ m : ℕ, start ≤ m → ∀ N period : ℕ, m < N →
        B m ≤ Pert.Asymptotics.regulatorRun C N period (m + 1) ^ (-epsilon))

private theorem positive_of_bound {g b : ℝ} (hg : 0 ≤ g)
    (hb : 1 ≤ b) (h : b ≤ g ^ (-1 : ℝ)) : 0 < g := by
  rcases eq_or_lt_of_le hg with hz | hz
  · have hzero : b ≤ 0 := by simpa only [← hz, Real.zero_rpow (by norm_num : (-1 : ℝ) ≠ 0)] using h
    linarith
  · exact hz

private theorem bill_bound {g b e : ℝ} (hg : 0 < g) (hb : 0 ≤ b)
    (h : b ≤ g ^ (-1 : ℝ)) (he : 0 ≤ e) (c k : ℕ) :
    b ^ c * g ^ (-(k : ℝ)) * e ≤
      g ^ (-((k + c : ℕ) : ℝ)) * e := by
  have hc : b ^ c ≤ g ^ (-(c : ℝ)) := by
    calc
      b ^ c ≤ (g ^ (-1 : ℝ)) ^ c := pow_le_pow_left₀ hb h c
      _ = g ^ (-(c : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hg.le]
        congr 1
        ring
  calc
    b ^ c * g ^ (-(k : ℝ)) * e ≤
        g ^ (-(c : ℝ)) * g ^ (-(k : ℝ)) * e :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hg.le _)) he
    _ = g ^ (-((k + c : ℕ) : ℝ)) * e := by
      rw [← Real.rpow_add hg]
      congr 2
      push_cast
      ring

/-- This construction changes only admittedCost and its proof fields. -/
def schedule : NumericSchedule C J where
  inputNorm := A.inputNorm
  outputNorm := A.outputNorm
  input_norm := A.input_norm
  output_norm := A.output_norm
  inputWidth := A.inputWidth
  outputWidth := A.outputWidth
  input_width_pos := A.input_width_pos
  output_width_pos := A.output_width_pos
  admittedCost := B
  admitted_cost_nonnegative m := (A.admitted_cost_nonnegative m).trans (hB m)
  admitted_cost_ge_one m := (A.admitted_cost_ge_one m).trans (hB m)
  radiusLoss := A.radiusLoss
  radius_loss_positive := A.radius_loss_positive
  radius_loss_ge_one := A.radius_loss_ge_one
  calibrationCap := A.calibrationCap
  calibration_cap_nonnegative := A.calibration_cap_nonnegative
  calibration_cap_tendsto := A.calibration_cap_tendsto
  cost_covers_widths m := (A.cost_covers_widths m).trans (hB m)
  cost_covers_geometry m := (A.cost_covers_geometry m).trans (hB m)
  cost_covers_units m N period hm := (A.cost_covers_units m N period hm).trans (hB m)
  cost_subpower := hsub
  pathRate := A.pathRate
  path_rate_positive := A.path_rate_positive
  path_rate_width := A.path_rate_width
  path_rate_cost m := (A.path_rate_cost m).trans (hB m)
  regular_flat c k t := by
    obtain ⟨s, hs⟩ := hsub 1 (by norm_num)
    obtain ⟨u, hu⟩ := A.regular_flat 0 (k + c) t
    refine ⟨max s u, ?_⟩
    intro m hm N period hN
    have hb := hs m ((le_max_left s u).trans hm) N period hN
    have hg := positive_of_bound
      (show 0 ≤ Pert.Asymptotics.regulatorRun C N period (m + 1) by
        unfold Pert.Asymptotics.regulatorRun
        positivity)
      ((A.admitted_cost_ge_one m).trans (hB m)) hb
    exact (bill_bound hg ((A.admitted_cost_nonnegative m).trans (hB m))
      hb (Real.exp_nonneg _) c k).trans
      (by simpa only [pow_zero, one_mul] using
        hu m ((le_max_right s u).trans hm) N period hN)
  forced_flat delta hdelta c k d t := by
    obtain ⟨s, hs⟩ := hsub 1 (by norm_num)
    obtain ⟨u, hu⟩ := A.forced_flat delta hdelta 0 (k + c) d t
    refine ⟨max s u, ?_⟩
    intro m hm N period hN
    have hb := hs m ((le_max_left s u).trans hm) N period hN
    have hg := positive_of_bound
      (show 0 ≤ Pert.Asymptotics.regulatorRun C N period (m + 1) by
        unfold Pert.Asymptotics.regulatorRun
        positivity)
      ((A.admitted_cost_ge_one m).trans (hB m)) hb
    exact (bill_bound hg ((A.admitted_cost_nonnegative m).trans (hB m))
      hb (Real.exp_nonneg _) c k).trans
      (by simpa only [pow_zero, one_mul] using
        hu m ((le_max_right s u).trans hm) N period hN)

theorem schedule_data :
    (schedule A B hB hsub).inputNorm = A.inputNorm ∧
    (schedule A B hB hsub).outputNorm = A.outputNorm ∧
    (schedule A B hB hsub).inputWidth = A.inputWidth ∧
    (schedule A B hB hsub).outputWidth = A.outputWidth ∧
    (schedule A B hB hsub).radiusLoss = A.radiusLoss ∧
    (schedule A B hB hsub).calibrationCap = A.calibrationCap ∧
    (schedule A B hB hsub).pathRate = A.pathRate ∧
    (schedule A B hB hsub).admittedCost = B :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Preserve all original K data; only its polynomial upper-bound proof weakens. -/
def prices (K : NumericPrices A) : NumericPrices (schedule A B hB hsub) where
  vacuumConstant := K.vacuumConstant
  vacuum_constant_nonnegative := K.vacuum_constant_nonnegative
  markedConstant := K.markedConstant
  marked_constant_nonnegative := K.marked_constant_nonnegative
  vanishing := K.vanishing
  vanishing_nonnegative := K.vanishing_nonnegative
  vanishing_tendsto := K.vanishing_tendsto
  geometry := K.geometry
  geometry_nonnegative := K.geometry_nonnegative
  polynomialConstant := K.polynomialConstant
  polynomial_constant_nonnegative := K.polynomial_constant_nonnegative
  polynomialDegree := K.polynomialDegree
  polynomial_bound m := (K.polynomial_bound m).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith [A.admitted_cost_nonnegative m])
        (show 1 + A.admittedCost m ≤ 1 + B m by linarith [hB m])
        K.polynomialDegree)
      K.polynomial_constant_nonnegative)
  hullMultiplier := K.hullMultiplier
  hull_positive := K.hull_positive
  hull_bound m := (K.hull_bound m).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by linarith [A.admitted_cost_nonnegative m])
        (show 1 + A.admittedCost m ≤ 1 + B m by linarith [hB m])
        K.polynomialDegree)
      K.polynomial_constant_nonnegative)
  subpower := K.subpower

theorem prices_data (K : NumericPrices A) :
    (prices A B hB hsub K).vacuumConstant = K.vacuumConstant ∧
    (prices A B hB hsub K).markedConstant = K.markedConstant ∧
    (prices A B hB hsub K).vanishing = K.vanishing ∧
    (prices A B hB hsub K).geometry = K.geometry ∧
    (prices A B hB hsub K).polynomialConstant = K.polynomialConstant ∧
    (prices A B hB hsub K).polynomialDegree = K.polynomialDegree ∧
    (prices A B hB hsub K).hullMultiplier = K.hullMultiplier :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private def vacuum {n : Side} {layers : List (Piece G n)} {p : BudgetPoint}
    {rank order : ℕ} {width a b : ℝ}
    (H : GradedVacuumLayers layers p order rank width a) (hab : a ≤ b) :
    GradedVacuumLayers layers p order rank width b where
  orders := H.orders
  leading_rank := H.leading_rank
  packets := {
    atom := H.packets.atom
    rank_bounded := H.packets.rank_bounded
    invariant := H.packets.invariant
    original_action := H.packets.original_action
    support := H.packets.support
    pieceCost := H.packets.pieceCost
    piece_cost_nonnegative := H.packets.piece_cost_nonnegative
    exponential := H.packets.exponential
    total := H.packets.total.trans hab
    coverOffset := H.packets.coverOffset
    coverSlope := H.packets.coverSlope
    cover := H.packets.cover
    width_reserved := H.packets.width_reserved
    cover_cost := H.packets.cover_cost.trans hab }

variable [DecidableEq V] [Fintype V] {Gamma : Census V}
    {datum : LocalFormal.Datum C Gamma}

omit [Fintype V] in
private theorem paid {n : Side} {D : V → ComparisonDensity.Address.Orbit}
    {P : MarkedPackets D G n Gamma} {p : BudgetPoint}
    {address : V → Support n}
    {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
    {w : V → ℝ} {g width a b : ℝ} {offset slope : ℕ}
    (H : P.Paid p address region w g width a offset slope) (hab : a ≤ b) :
    P.Paid p address region w g width b offset slope where
  width_pos := H.width_pos
  positive := H.positive
  coefficient := H.coefficient
  paths := H.paths
  addresses := H.addresses
  symmetry := H.symmetry
  reads := H.reads
  multilinear := H.multilinear
  roots v := ⟨(H.roots v).1, (H.roots v).2.1, (H.roots v).2.2.trans hab⟩
  cover := H.cover
  width_reserved := H.width_reserved

/-- Admit the same complete analytic input under the enlarged auxiliary cost. -/
def input (F : Numeric.AnalyticInput J A datum) :
    Numeric.AnalyticInput J (schedule A B hB hsub) datum where
  whole_tests := F.whole_tests
  layers := F.layers
  layers_paid := F.layers_paid
  vacuum := vacuum F.vacuum (hB datum.level)
  fineRoots := F.fineRoots
  coarseRoots := F.coarseRoots
  roots := F.roots
  colors := F.colors
  packets := F.packets
  convention := F.convention
  rank_bounded := F.rank_bounded
  power_bounded := F.power_bounded
  whole_input := F.whole_input
  inputRadii := F.inputRadii
  outputRadii := F.outputRadii
  kernelCosts := F.kernelCosts
  input_radius_positive := F.input_radius_positive
  output_radius_positive := F.output_radius_positive
  kernel_positive := F.kernel_positive
  radius_admission := F.radius_admission
  inputAddresses := F.inputAddresses
  input_origins := F.input_origins
  inputRegion := F.inputRegion
  coverOffset := F.coverOffset
  coverSlope := F.coverSlope
  cover_cost := F.cover_cost.trans (hB datum.level)
  input_paid := paid F.input_paid (hB datum.level)
  physical_period := F.physical_period
  input_field_admitted := F.input_field_admitted
  input_distance_admitted := F.input_distance_admitted
  output_field_admitted := F.output_field_admitted
  output_distance_admitted := F.output_distance_admitted
  primary_admitted := F.primary_admitted

/-- Retain the exact model and Plan with the exact old K geometry bill. -/
def output {caps : Handoff.OutputCapacities} {Y : Bulk.Chain C.path}
    {K : NumericPrices A} {F : Numeric.AnalyticInput J A datum}
    (M : Numeric.AnalyticOutput caps Y K F) :
    Numeric.AnalyticOutput caps Y (prices A B hB hsub K) (input A B hB hsub F) where
  model := M.model
  prescribed := M.prescribed
  rank_bounded := M.rank_bounded
  power_bounded := M.power_bounded
  plan := M.plan
  fine_layers := M.fine_layers
  whole_action := M.whole_action
  output_layers_paid := M.output_layers_paid
  vacuum := M.vacuum
  region := M.region
  coverOffset := M.coverOffset
  coverSlope := M.coverSlope
  cover_cost := M.cover_cost
  paid := M.paid

theorem input_data (F : Numeric.AnalyticInput J A datum) :
    (input A B hB hsub F).layers = F.layers ∧
    (input A B hB hsub F).packets = F.packets ∧
    (input A B hB hsub F).inputRadii = F.inputRadii ∧
    (input A B hB hsub F).outputRadii = F.outputRadii ∧
    (input A B hB hsub F).kernelCosts = F.kernelCosts :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem output_data {caps : Handoff.OutputCapacities} {Y : Bulk.Chain C.path}
    {K : NumericPrices A} {F : Numeric.AnalyticInput J A datum}
    (M : Numeric.AnalyticOutput caps Y K F) :
    (output A B hB hsub M).model = M.model ∧
    (output A B hB hsub M).plan = M.plan :=
  ⟨rfl, rfl⟩

end YM.Integration.FullQLocalCostEnlargement
end
