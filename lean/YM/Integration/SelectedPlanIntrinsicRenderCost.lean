import YM.Integration.FiniteVacuumRenderBill
import YM.Integration.ZeroAwareCappedCreditPolynomial
import YM.Integration.FullQLocalNumericStepData
import YM.Extra.WILSON_STARTUP.Fast
import YM.MatchingLedger.Compass.Deck
import YM.Integration.ActualRunAdjacentHatBeta

/-! Intrinsic rendering bills at the fixed requested output norm. Every
original row, field function and activity is retained. Credit-only repricing
is an auxiliary proof device; no bound on the stored credits is assumed.
The native growing-order Room and the sharp kinetic defect remain separate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedPlanIntrinsicRenderCost
open Function Filter Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02
open ZeroAwareIntrinsicRenderInvoice MatchingLedger.Compass.Income
open scoped Topology ContDiff Classical BigOperators

private theorem dollars_repriced {G : Gauge} {n : Side}
    (c : Piece G n → ℝ) (S : List (Piece G n)) (k : ℤ → ℝ) :
    Render.dollars (fun a => ‖weight k a‖) (repriceLayers c S) =
      (S.map (fun a => ‖weight k a‖ * c a)).sum := by
  induction S with
  | nil => rfl
  | cons a S ih =>
      change ‖weight k a‖ * c a +
          Render.dollars (fun a => ‖weight k a‖) (repriceLayers c S) =
        ‖weight k a‖ * c a + (S.map (fun a => ‖weight k a‖ * c a)).sum
      rw [ih]

private theorem adorn_valid {G : Gauge} {n : Side} {p : BudgetPoint}
    {d z : ℝ} (S : List (Piece G n)) (f : Piece G n → ℝ)
    (E : Activities G n) (h : Render.permits S p) (hE : E.Valid p d z) :
    (Render.adorn f E S).Valid p
      (d + Render.dollars (fun a => ‖f a‖) S) z := by
  induction S with
  | nil => simpa only [Render.adorn, Render.dollars, add_zero] using hE
  | cons a S ih =>
      have hk := Payload.payment (f a) (Render.first h) (ih (Render.seated h))
      rw [Render.dollars, add_comm (‖f a‖ * a.credit)
        (Render.dollars (fun a => ‖f a‖) S), ← add_assoc]
      exact hk

/-- The complete original activities receive the intrinsic capped bill at
the supplied norm. The original list and its stored credits are unchanged. -/
theorem activities_valid {G : Gauge} {n : Side} {S : List (Piece G n)}
    {p : BudgetPoint} {rankCap : ℕ} {width budget d z : ℝ}
    (H : ZeroAwareVacuumPackets S p rankCap width budget)
    (h : Render.permits S p) (hw : 0 < width)
    (k : ℤ → ℝ) (E : Activities G n) (hE : E.Valid p d z) :
    (Render.adorn (weight k) E S).Valid p
      (d + ZeroAwareCappedRenderInvoice.bill H k) z := by
  have hp : Render.permits
      (repriceLayers (ZeroAwareCappedRenderInvoice.credit H) S) p := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact ZeroAwareCappedRenderInvoice.invoice H h hw a ha
  have hh := adorn_valid _ (weight k) E hp hE
  rw [adorn_unchanged, dollars_repriced] at hh
  exact hh

/-- Both exact native bills use the original occurrence costs. One factor
of budget pays the cover, and the other pays the full occurrence sum. -/
theorem intrinsic_bounds (G : Gauge) (r rankCap o q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ,
      ∀ {n : Side} {S : List (Piece G n)} {p : BudgetPoint} {width budget : ℝ}
        (H : ZeroAwareVacuumPackets S p rankCap width budget),
      p.order = o → p.power = q → 0 < width → Render.gradings S r →
      ∀ b W : ℝ, 1 ≤ b → 1 ≤ W → p.threshold / Currency.gain b ≤ W →
      let S' := repriceLayers (ZeroAwareCappedRenderInvoice.credit H) S
      Render.unitBill S' b ≤
          C * budget^2 * (1 + width⁻¹)^D * W^rankCap * Currency.gain b^3 ∧
        Render.shiftBill S' b ≤
          C * budget^2 * (1 + width⁻¹)^D * W^rankCap * Currency.gain b^5 := by
  obtain ⟨C, hC, D, hcredit⟩ :=
    ZeroAwareCappedCreditPolynomial.credit_bound G rankCap o q
  let K := |FiniteVacuumRenderBill.unitConstant r rankCap| +
    |FiniteVacuumRenderBill.shiftConstant r rankCap| + 1
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  refine ⟨K * C, mul_pos hK hC, D, ?_⟩
  intro n S p width budget H ho hq hw horders b W hb hW hratio
  dsimp only
  have hbudget : 0 ≤ budget := (Real.exp_pos _).le.trans H.cover_cost
  have hwidth : 0 ≤ 1 + width⁻¹ := by positivity
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hg : 0 ≤ Currency.gain b := by
    change 0 ≤ (Real.sqrt b)⁻¹
    positivity
  let B := C * (1 + width⁻¹)^D * budget
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hc : ∀ a ∈ S, ZeroAwareCappedRenderInvoice.credit H a ≤
      B * p.threshold^a.rank * H.pieceCost a := by
    intro a ha
    exact (hcredit H ho hq hw a ha).trans_eq (by dsimp only [B]; ring)
  have hu := FiniteVacuumRenderBill.unit_sum_bound r rankCap S
    (ZeroAwareCappedRenderInvoice.credit H) H.pieceCost
    b p.threshold B budget W hb p.threshold_pos.le hB hbudget hW hratio
    horders H.rank_bounded hc H.piece_cost_nonnegative H.total
  have hs := FiniteVacuumRenderBill.shift_sum_bound r rankCap S
    (ZeroAwareCappedRenderInvoice.credit H) H.pieceCost
    b p.threshold B budget W hb p.threshold_pos.le hB hbudget hW hratio
    horders H.rank_bounded hc H.piece_cost_nonnegative H.total
  have hunit : FiniteVacuumRenderBill.unitConstant r rankCap ≤ K := by
    dsimp only [K]
    linarith [le_abs_self (FiniteVacuumRenderBill.unitConstant r rankCap),
      abs_nonneg (FiniteVacuumRenderBill.shiftConstant r rankCap)]
  have hshift : FiniteVacuumRenderBill.shiftConstant r rankCap ≤ K := by
    dsimp only [K]
    linarith [le_abs_self (FiniteVacuumRenderBill.shiftConstant r rankCap),
      abs_nonneg (FiniteVacuumRenderBill.unitConstant r rankCap)]
  have hcompare (L : ℝ) (hL : L ≤ K) (j : ℕ) :
      L * B * budget * W^rankCap * Currency.gain b^j ≤
        (K * C) * budget^2 * (1 + width⁻¹)^D * W^rankCap * Currency.gain b^j := by
    have hnonneg : 0 ≤ C * budget^2 * (1 + width⁻¹)^D *
        W^rankCap * Currency.gain b^j := by positivity
    calc
      _ = L * (C * budget^2 * (1 + width⁻¹)^D *
          W^rankCap * Currency.gain b^j) := by dsimp only [B]; ring
      _ ≤ K * (C * budget^2 * (1 + width⁻¹)^D *
          W^rankCap * Currency.gain b^j) :=
        mul_le_mul_of_nonneg_right hL hnonneg
      _ = _ := by ring
  constructor
  · change Render.unitBill
      (S.map fun a => {a with credit := ZeroAwareCappedRenderInvoice.credit H a}) b ≤ _
    rw [FiniteVacuumRenderBill.unitBill_reprice]
    exact hu.trans (hcompare _ hunit 3)
  · change Render.shiftBill
      (S.map fun a => {a with credit := ZeroAwareCappedRenderInvoice.credit H a}) b ≤ _
    rw [FiniteVacuumRenderBill.shiftBill_reprice]
    exact hs.trans (hcompare _ hshift 5)

private theorem hatted_units {G : Gauge} (T : Run G) (hG : G.Simple)
    {V : Type} {J : Request V} (A : NumericSchedule T.family J) :
    ∀ᶠ m : ℕ in atTop,
      1 ≤ Currency.B T.family.path.levels m ∧
      (A.outputNorm m).threshold / Currency.gain (Currency.B T.family.path.levels m) ≤
        2 * A.admittedCost m := by
  filter_upwards [ActualRunAdjacentHatBeta.three_halves T hG] with m hm
  let a := Currency.B T.family.path.levels m
  let beta := T.family.path.β (m+1) 0 (m+1)
  let g := Pert.Asymptotics.regulatorRun T.family (m+1) 0 (m+1)
  have ha : 1 < a := T.family.path.levels.fits.delayed m
  have hg : 0 < g := Weather.runs_pos T.family T.makes le_rfl 0
  have hband := (T.makes.wilson.represents (m+1) 0 (m+1) le_rfl).band
  have hmono := WilsonStartup.Timing.hat_mono T.family.path.levels (G.slopeConstant_pos hG).le
    (Nat.le_succ m)
  have hnext : T.family.path.levels.clock.hatBeta (m+1) ≤ (3/2 : ℝ) * a := hm
  have hbeta : beta ∈ Currency.stripe a := by
    change a / 4 ≤ beta ∧ beta ≤ 4 * a
    have hlo : T.family.path.levels.clock.hatBeta (m+1) / 2 ≤ beta := hband.1
    have hhi : beta ≤ 2 * T.family.path.levels.clock.hatBeta (m+1) := hband.2
    change a ≤ T.family.path.levels.clock.hatBeta (m+1) at hmono
    constructor <;> linarith only [ha, hlo, hhi, hmono, hnext]
  have hgain : g ≤ 2 * Currency.gain a := (Currency.sizes_band (zero_lt_one.trans ha) hbeta).2
  have hga : 0 < Currency.gain a := by
    change 0 < (Real.sqrt a)⁻¹
    exact inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans ha))
  have hratio : g / Currency.gain a ≤ 2 := (div_le_iff₀ hga).2 hgain
  have hunit : T.family.path.levels.clock.threshold m / g ≤ A.admittedCost m := by
    have h := A.cost_covers_units m (m+1) 0 (Nat.lt_succ_self m)
    change T.family.path.levels.clock.threshold m / g +
      T.family.path.levels.clock.threshold (m+1) / g ≤ A.admittedCost m at h
    have ht : 0 ≤ T.family.path.levels.clock.threshold (m+1) / g := by
      have hp : 0 < T.family.path.levels.clock.threshold (m+1) :=
        (T.family.path.levels.budget (m+1)).threshold_pos
      exact div_nonneg hp.le hg.le
    linarith
  refine ⟨ha.le, ?_⟩
  rw [(A.output_norm m).threshold]
  change T.family.path.levels.clock.threshold m / Currency.gain a ≤ 2 * A.admittedCost m
  calc
    _ = (T.family.path.levels.clock.threshold m / g) * (g / Currency.gain a) := by
      field_simp [hg.ne', hga.ne']
    _ ≤ A.admittedCost m * 2 :=
      mul_le_mul hunit hratio (div_nonneg hg.le hga.le) (A.admitted_cost_nonnegative m)
    _ = _ := by ring

/-- The same selected model has intrinsic unit/shift bills of gain orders
three/five at its exact requested output norm, uniformly before all data. -/
theorem selected_bounds {G : Gauge} (T : Run G) (hG : G.Simple)
    {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {J : Request V} (caps : Handoff.OutputCapacities)
    (A : NumericSchedule T.family J) (K : NumericPrices A) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ᶠ m : ℕ in atTop,
      ∀ (datum : LocalFormal.Datum T.family R), datum.level = m →
      ∀ (Y : Bulk.Chain T.family.path) (I : AnalyticInput J A datum)
        (M : AnalyticOutput caps Y K I),
      let S' := repriceLayers (ZeroAwareCappedRenderInvoice.credit M.vacuum.packets)
        (M.plan.layers datum.level)
      let b := Currency.B T.family.path.levels datum.level
      Render.unitBill S' b ≤ C * A.admittedCost datum.level^d * Currency.gain b^3 ∧
        Render.shiftBill S' b ≤ C * A.admittedCost datum.level^d * Currency.gain b^5 := by
  obtain ⟨C, hC, D, hbound⟩ := intrinsic_bounds G J.order caps.vacuumRank
    J.outputFieldOrder J.outputDistanceOrder
  let P := 1 + K.polynomialConstant * 2^K.polynomialDegree
  have hP : 0 < P := by
    have hp := K.polynomial_constant_nonnegative
    dsimp only [P]
    positivity
  let C' := C * P^2 * 2^D * 2^caps.vacuumRank
  have hC' : 0 < C' := by dsimp only [C']; positivity
  refine ⟨C', hC', K.polynomialDegree * 2 + D + caps.vacuumRank, ?_⟩
  filter_upwards [hatted_units T hG A] with m hm
  intro datum hlevel Y I M
  subst m
  dsimp only
  let W := A.admittedCost datum.level
  let b := Currency.B T.family.path.levels datum.level
  have hW : 1 ≤ W := A.admitted_cost_ge_one datum.level
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hw := A.output_width_pos datum.level
  have hg : 0 ≤ Currency.gain b := by change 0 ≤ (Real.sqrt b)⁻¹; positivity
  have hwidth : 1 + (A.outputWidth datum.level)⁻¹ ≤ 2 * W := by
    have hbill := A.cost_covers_widths datum.level
    have hi := (inv_pos.mpr (A.input_width_pos datum.level)).le
    have hr := (A.radius_loss_positive datum.level).le
    dsimp only [W] at *
    linarith
  have hgeometry : K.geometry datum.level ≤ P * W^K.polynomialDegree := by
    calc
      _ ≤ K.polynomialConstant * (1 + W)^K.polynomialDegree := K.polynomial_bound _
      _ ≤ K.polynomialConstant * (2 * W)^K.polynomialDegree :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by linarith) _) K.polynomial_constant_nonnegative
      _ ≤ P * W^K.polynomialDegree := by
        rw [mul_pow]
        have hp : K.polynomialConstant * 2^K.polynomialDegree ≤ P := by
          dsimp only [P]
          linarith
        exact (show K.polynomialConstant * (2^K.polynomialDegree * W^K.polynomialDegree) =
            (K.polynomialConstant * 2^K.polynomialDegree) * W^K.polynomialDegree by ring).le.trans
          (mul_le_mul_of_nonneg_right hp (pow_nonneg hW0 _))
  have hgeom0 := K.geometry_nonnegative datum.level
  have hwidth0 : 0 ≤ 1 + (A.outputWidth datum.level)⁻¹ := by positivity
  have hscalar : C * (K.geometry datum.level)^2 *
      (1 + (A.outputWidth datum.level)⁻¹)^D * (2*W)^caps.vacuumRank ≤
      C' * W^(K.polynomialDegree * 2 + D + caps.vacuumRank) := by
    calc
      _ ≤ C * (P * W^K.polynomialDegree)^2 *
          (2*W)^D * (2*W)^caps.vacuumRank := by
        have hp := mul_le_mul
          (pow_le_pow_left₀ hgeom0 hgeometry 2)
          (pow_le_pow_left₀ hwidth0 hwidth D)
          (pow_nonneg hwidth0 D) (sq_nonneg (P * W^K.polynomialDegree))
        have ht := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp hC.le)
          (pow_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hW0) caps.vacuumRank)
        simpa only [mul_assoc] using ht
      _ = _ := by
        dsimp only [C']
        simp only [mul_pow, pow_add, pow_mul]
        ring
  have hp := hbound M.vacuum.packets (A.output_norm datum.level).order
    (A.output_norm datum.level).distance hw M.vacuum.orders b (2*W)
    hm.1 (by linarith) hm.2
  exact ⟨hp.1.trans (mul_le_mul_of_nonneg_right hscalar (pow_nonneg hg 3)),
    hp.2.trans (mul_le_mul_of_nonneg_right hscalar (pow_nonneg hg 5))⟩

end YM.Integration.SelectedPlanIntrinsicRenderCost
end
