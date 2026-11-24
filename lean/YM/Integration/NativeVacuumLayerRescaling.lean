import YM.Integration.QLocalGradedVacuumLayers

/-!
# Fixed-ratio rescaling of the literal vacuum layer list

Only coefficients are scaled. Every power, curvature rank, original row,
address and support is retained. Integer step orders retain the possible
negative powers -1 and -2. The same fixed ratio is used for every field.
Stored credits are multiplied by the exact absolute coefficient factor;
no comparison between those credits and intrinsic atom costs is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativeVacuumLayerRescaling

open Function Finset Lattice Wilson RG
open YM.IterationFour.Vacuum
open LocalComparison.Global FullQLocal
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side}

/-- A scalar on the full native payload, without changing any address. -/
def payload (k : ℝ) (P : Payload G n) : Payload G n where
  labels := P.labels
  action i U := k * P.action i U

/-- Integer exponent: a rank exceeding the power is not truncated. -/
def factor (ratio : ℝ) (a : Piece G n) : ℝ :=
  ratio ^ Render.stepOrder a

def piece (ratio : ℝ) (a : Piece G n) : Piece G n where
  power := a.power
  rank := a.rank
  packet := payload (factor ratio a) a.packet
  credit := ‖factor ratio a‖ * a.credit

def layers (ratio : ℝ) (S : List (Piece G n)) : List (Piece G n) :=
  S.map (piece ratio)

@[simp] theorem factor_piece (r t : ℝ) (a : Piece G n) :
    factor r (piece t a) = factor r a := rfl

@[simp] theorem factor_inv (r : ℝ) (a : Piece G n) :
    factor r⁻¹ a = (factor r a)⁻¹ := by
  exact inv_zpow r (Render.stepOrder a)

theorem factor_pos {r : ℝ} (hr : 0 < r) (a : Piece G n) :
    0 < factor r a := zpow_pos hr _

/-- Exact inverse, including old numerical credits. It also prevents loss of
old atom witnesses when different list entries have identical payloads. -/
theorem inverse {r : ℝ} (hr : r ≠ 0) (a : Piece G n) :
    piece r⁻¹ (piece r a) = a := by
  have hn : factor r a ≠ 0 := zpow_ne_zero _ hr
  have hm : (factor r a)⁻¹ * factor r a = 1 := inv_mul_cancel₀ hn
  have hc : ‖(factor r a)⁻¹‖ * ‖factor r a‖ = 1 := by
    rw [← norm_mul, hm, norm_one]
  rcases a with ⟨power, rank, ⟨labels, action⟩, credit⟩
  simp only [piece, payload, factor_inv]
  congr 1
  · congr 1
    funext i U
    change (factor r ⟨power, rank, ⟨labels, action⟩, credit⟩)⁻¹ *
      (factor r ⟨power, rank, ⟨labels, action⟩, credit⟩ * action i U) = action i U
    rw [← mul_assoc, hm, one_mul]
  · change ‖(factor r ⟨power, rank, ⟨labels, action⟩, credit⟩)⁻¹‖ *
      (‖factor r ⟨power, rank, ⟨labels, action⟩, credit⟩‖ * credit) = credit
    rw [← mul_assoc, hc, one_mul]

/-- Native Invoice transport on the entire payload. In particular affine
nullity, movement and every original regular row are preserved. -/
theorem payload_invoice {P : Payload G n} {p : BudgetPoint} {c : ℝ}
    (h : P.Invoice p c) (k : ℝ) :
    (payload k P).Invoice p (‖k‖ * c) := by
  refine ⟨fun i => WilsonStartup.Start.times_reg k (h.smooth i),
    ?_, ?_, ?_, ?_⟩
  · intro i
    change k * P.action i 1 = 0
    rw [h.flat i, mul_zero]
  · intro i hi x y hx hy
    let f := AnalyticBridge.VerifiedReset.germ (P.action i)
    change (iteratedFDeriv ℝ 2 (k • f) 0) _ = 0
    rw [iteratedFDeriv_const_smul_apply
      (AnalyticBridge.VerifiedReset.germ_diff (h.smooth i))]
    exact (congr_arg (k • ·) (h.null i hi x y hx hy)).trans (smul_zero ..)
  · intro s b
    obtain ⟨e, he⟩ := h.moves s b
    refine ⟨e, fun i => ⟨(he i).1, (he i).2.1, fun U => ?_⟩⟩
    exact congrArg (k * ·) ((he i).2.2 U)
  · obtain ⟨v, hv, hb⟩ := h.credit
    refine ⟨fun i => ‖k‖ * v i,
      fun i => WilsonStartup.Start.times_bound k (hv i), fun o => ?_⟩
    have hh := YM.Push.AbsoluteSums.budget_scale (norm_nonneg k) (hb o)
    simpa only [payload, BudgetPoint.mass, mul_left_comm, mul_ite, mul_zero]
      using hh

theorem permits {S : List (Piece G n)} {p : BudgetPoint}
    (h : Render.permits S p) (ratio : ℝ) :
    Render.permits (layers ratio S) p := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact payload_invoice (h b hb) (factor ratio b)

/-- Scalar multiplication commutes with every original mask and the full
countable payload sum, including fields where flags are present. -/
theorem payload_amount (k : ℝ) (P : Payload G n) (p : BudgetPoint)
    (U : Config G n) :
    (payload k P).amount p U = k * P.amount p U := by
  unfold Payload.amount
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  change masked p.threshold (P.labels i).support (fun U => k * P.action i U) U =
    k * masked p.threshold (P.labels i).support (P.action i) U
  by_cases hi : Healthy p.threshold (P.labels i).support U
  · rw [masked_eq _ _ _ _ hi, masked_eq _ _ _ _ hi]
  · rw [masked_ne _ _ _ _ hi, masked_ne _ _ _ _ hi, mul_zero]

theorem payload_unmasked (k : ℝ) (P : Payload G n) (U : Config G n) :
    unmaskedPayload (payload k P) U = k * unmaskedPayload P U := by
  exact (tsum_mul_left : (∑' i, k * P.action i U) = k * ∑' i, P.action i U)

/-- Full masked rendered function at the changed coupling, without dropping
flags, changing the field or replacing the original list by a jet. -/
theorem renders (ratio g : ℝ) (S : List (Piece G n)) (p : BudgetPoint)
    (U : Config G n) :
    Render.renders (Render.prefactor g) p U (layers ratio S) =
      Render.renders (Render.prefactor (ratio * g)) p U S := by
  induction S with
  | nil => rfl
  | cons a S ih =>
      change Render.prefactor g (piece ratio a) *
          (payload (factor ratio a) a.packet).amount p U +
          Render.renders (Render.prefactor g) p U (layers ratio S) =
        Render.prefactor (ratio * g) a * a.packet.amount p U +
          Render.renders (Render.prefactor (ratio * g)) p U S
      rw [payload_amount, ih]
      simp only [Render.prefactor, Render.stepOrder, piece, factor, mul_zpow]
      ring

theorem unmasked (ratio g : ℝ) (S : List (Piece G n)) (U : Config G n) :
    unmaskedLayers (layers ratio S) g U =
      unmaskedLayers S (ratio * g) U := by
  induction S with
  | nil => rfl
  | cons a S ih =>
      change Render.prefactor g (piece ratio a) *
          unmaskedPayload (payload (factor ratio a) a.packet) U +
          unmaskedLayers (layers ratio S) g U =
        Render.prefactor (ratio * g) a * unmaskedPayload a.packet U +
          unmaskedLayers S (ratio * g) U
      rw [payload_unmasked, ih]
      simp only [Render.prefactor, Render.stepOrder, piece, factor, mul_zpow]
      ring

/-- Explicit finite factor range. The inverse square is essential. -/
def factorBound (ratio : ℝ) (order : ℕ) : ℝ :=
  max (ratio ^ (-2 : ℤ)) (ratio ^ (order : ℤ))

theorem factor_bound {ratio : ℝ} (hr : 0 < ratio) {S : List (Piece G n)}
    {p : BudgetPoint} {order rankCap : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers S p order rankCap width budget) :
    1 ≤ factorBound ratio order ∧
      ∀ a ∈ S, ‖factor ratio a‖ ≤ factorBound ratio order := by
  have hb : 1 ≤ factorBound ratio order := by
    by_cases h : 1 ≤ ratio
    · exact (one_le_zpow₀ h (by positivity : (0 : ℤ) ≤ order)).trans
        (le_max_right _ _)
    · exact (one_le_zpow_of_nonpos₀ hr (le_of_not_ge h) (by norm_num : (-2 : ℤ) ≤ 0)).trans
        (le_max_left _ _)
  refine ⟨hb, fun a ha => ?_⟩
  have hlo : (-2 : ℤ) ≤ Render.stepOrder a := by
    have hh := H.leading_rank a ha
    unfold Render.stepOrder
    omega
  have hhi : Render.stepOrder a ≤ (order : ℤ) := by
    have hh := (H.orders a ha).2
    unfold Render.stepOrder
    omega
  rw [Real.norm_eq_abs, abs_of_pos (factor_pos hr a)]
  by_cases h : 1 ≤ ratio
  · exact (zpow_le_zpow_right₀ h hhi).trans (le_max_right _ _)
  · exact (zpow_le_zpow_right_of_le_one₀ hr (le_of_not_ge h) hlo).trans
      (le_max_left _ _)

end YM.Integration.NativeVacuumLayerRescaling
end
