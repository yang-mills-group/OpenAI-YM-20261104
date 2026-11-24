import YM.Integration.ActualQlocalRequestTransport

/-! A countable family of complete finite requests for one fixed real recipe.
The independent slot tests remain whole orbits with their original D and W.
Only the three nonnegative scalar costs are enlarged to a common natural cap.
This is not grant cofinality: an actual application must supply this real
recipe, its input transport, and the stronger period lower bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualQlocalRequestFamily
open Lattice Wilson RG FullQLocal.RenderedStep ActualQlocalNaturalRequests
open scoped Classical

variable {V : Type}

/-- Real parameters are fixed before the countable numerical enumeration. -/
structure Recipe where
  eta : ℝ
  eta_pos : 0 < eta
  eta_lt_half : eta < 1 / 2
  spareSupport : ℝ
  spare_pos : 0 < spareSupport
  reserveFugacity : ℝ
  fugacity_nonnegative : 0 ≤ reserveFugacity
  fugacity_lt_one : reserveFugacity < 1
  inputSupport : ℝ
  input_pos : 0 < inputSupport
  outputSupport : ℝ
  output_pos : 0 < outputSupport

structure Matches (P : Recipe) (J : Request V) : Prop where
  eta : P.eta = J.eta
  spare : P.spareSupport = J.spareSupport
  fugacity : P.reserveFugacity = J.reserveFugacity
  input : P.inputSupport = J.inputSupport
  output : P.outputSupport = J.outputSupport

/-- Every discrete admissibility inequality is checked on the code itself. -/
def Valid (c : Code) : Prop :=
  2 ≤ c.2.1 0 ∧ 6 ≤ c.2.1 4 ∧ 2 ≤ c.2.1 6 ∧
  c.2.1 4 ≤ c.2.1 3 ∧ c.2.1 6 ≤ c.2.1 5 ∧
  c.2.1 1 ≤ c.2.1 3 ∧ c.2.1 2 ≤ c.2.1 4 ∧
  (∀ i, (c.2.2 i).1 ≤ c.2.1 1) ∧
  (∀ i, (c.2.2 i).2.1 ≤ c.2.1 2) ∧
  ∀ i, max (c.2.2 i).1 (c.2.2 i).2.1 + 2 ≤ (c.2.2 i).2.2.1

instance (c : Code) : Decidable (Valid c) := by
  unfold Valid
  infer_instance

abbrev GoodCode := {c : Code // Valid c}

def defaultCode : GoodCode :=
  ⟨⟨0, ![2, 0, 0, 6, 6, 2, 2, 0, 0, 0, 0, 0, 0], Fin.elim0⟩,
    by simp [Valid]⟩

theorem valid_code {n : ℕ} (e : Fin n ≃ V) (J : Request V) :
    Valid (requestCode e J) := by
  dsimp [Valid, requestCode, scalarCode, slotCode]
  exact ⟨J.order_ge_two, J.field_minimum, J.distance_minimum,
    J.field_reserve, J.distance_reserve, J.input_engineering,
    J.output_engineering, fun i => J.input_weight_le (e i),
    fun i => J.output_weight_le (e i), fun i => J.test_order (e i)⟩

def build (P : Recipe) (c : GoodCode) : Request (Fin c.val.1) where
  order := c.val.2.1 0
  order_ge_two := c.property.1
  eta := P.eta
  eta_pos := P.eta_pos
  eta_lt_half := P.eta_lt_half
  inputHorizon := c.val.2.1 1
  outputHorizon := c.val.2.1 2
  inputWeight i := (c.val.2.2 i).1
  outputWeight i := (c.val.2.2 i).2.1
  input_weight_le := c.property.2.2.2.2.2.2.2.1
  output_weight_le := c.property.2.2.2.2.2.2.2.2.1
  inputFieldOrder := c.val.2.1 3
  outputFieldOrder := c.val.2.1 4
  field_minimum := c.property.2.1
  inputDistanceOrder := c.val.2.1 5
  outputDistanceOrder := c.val.2.1 6
  distance_minimum := c.property.2.2.1
  field_reserve := c.property.2.2.2.1
  distance_reserve := c.property.2.2.2.2.1
  input_engineering := c.property.2.2.2.2.2.1
  output_engineering := c.property.2.2.2.2.2.2.1
  spareSupport := P.spareSupport
  spare_support_positive := P.spare_pos
  reserveFugacity := P.reserveFugacity
  reserve_fugacity_nonnegative := P.fugacity_nonnegative
  reserve_fugacity_lt_one := P.fugacity_lt_one
  inputSupport := P.inputSupport
  outputSupport := P.outputSupport
  output_support_pos := P.output_pos
  input_support_pos := P.input_pos
  tests i := ⟨.whole, (c.val.2.2 i).2.2.1, (c.val.2.2 i).2.2.2⟩
  test_order := c.property.2.2.2.2.2.2.2.2.2
  inheritedConstant := c.val.2.1 12
  inherited_constant_nonnegative := Nat.cast_nonneg _
  physicalPeriodLower := c.val.2.1 12
  physical_period_nonnegative := Nat.cast_nonneg _
  vacuumRankCap := c.val.2.1 7
  inputPacketRankCap := c.val.2.1 8
  outputPacketRankCap := c.val.2.1 9
  inputPacketPowerCap := c.val.2.1 10
  outputPacketPowerCap := c.val.2.1 11
  forcedConstant := c.val.2.1 12
  forced_constant_nonnegative := Nat.cast_nonneg _

def capped (J : Request V) : Request V :=
  { J with
    inheritedConstant := costCap J
    inherited_constant_nonnegative := Nat.cast_nonneg _
    physicalPeriodLower := costCap J
    physical_period_nonnegative := Nat.cast_nonneg _
    forcedConstant := costCap J
    forced_constant_nonnegative := Nat.cast_nonneg _ }

/-- The reconstructed request is the original relabeled request, with exactly
the three stated scalar enlargements and no change of tests or real recipe. -/
theorem build_code (P : Recipe) {n : ℕ} (e : Fin n ≃ V) (J : Request V)
    (hP : Matches P J)
    (hwhole : ∀ v, ∃ d w : ℕ, J.tests v = ⟨.whole, d, w⟩) :
    build P ⟨requestCode e J, valid_code e J⟩ =
      capped (ActualQlocalRequestTransport.reindex e J) := by
  have ht :
      (fun i : Fin n => (⟨.whole, (J.tests (e i)).D, (J.tests (e i)).W⟩ :
        ComparisonDensity.Address.Orbit)) = (fun i => J.tests (e i)) := by
    funext i
    exact (whole_test_recover J (e i) (hwhole (e i))).symm
  rcases hP with ⟨hη, hs, hf, hi, ho⟩
  cases J
  cases P
  simp_all [build, requestCode, scalarCode, slotCode, capped,
    ActualQlocalRequestTransport.reindex, costCap]

def dictionary (j : ℕ) : GoodCode :=
  (Encodable.decode j).getD defaultCode

def family (P : Recipe) (j : ℕ) : Σ n : ℕ, Request (Fin n) :=
  let c := dictionary j
  ⟨c.val.1, build P c⟩

theorem family_index (P : Recipe) (c : GoodCode) :
    family P (Encodable.encode c) = ⟨c.val.1, build P c⟩ := by
  have hc : dictionary (Encodable.encode c) = c := by
    simp [dictionary]
  exact congrArg
    (fun d : GoodCode => (⟨d.val.1, build P d⟩ : Σ n : ℕ, Request (Fin n))) hc

theorem complete (P : Recipe) {n : ℕ} (e : Fin n ≃ V) (J : Request V)
    (hP : Matches P J)
    (hwhole : ∀ v, ∃ d w : ℕ, J.tests v = ⟨.whole, d, w⟩) :
    ∃ j : ℕ, family P j = ⟨n, capped (ActualQlocalRequestTransport.reindex e J)⟩ := by
  let c : GoodCode := ⟨requestCode e J, valid_code e J⟩
  refine ⟨Encodable.encode c, ?_⟩
  calc
    family P (Encodable.encode c) = ⟨n, build P c⟩ := family_index P c
    _ = ⟨n, capped (ActualQlocalRequestTransport.reindex e J)⟩ :=
      congrArg (fun K : Request (Fin n) => (⟨n, K⟩ : Σ k : ℕ, Request (Fin k)))
        (build_code P e J hP hwhole)

theorem complete_finite [Fintype V] (P : Recipe) (J : Request V)
    (hP : Matches P J)
    (hwhole : ∀ v, ∃ d w : ℕ, J.tests v = ⟨.whole, d, w⟩) :
    ∃ e : Fin (Fintype.card V) ≃ V, ∃ j : ℕ,
      family P j = ⟨Fintype.card V,
        capped (ActualQlocalRequestTransport.reindex e J)⟩ := by
  let e := (Fintype.equivFin V).symm
  obtain ⟨j, hj⟩ := complete P e J hP hwhole
  exact ⟨e, j, hj⟩

theorem sameNorm_capped (J : Request V) (hJ : SameNorm J) :
    SameNorm (capped J) where
  field_order := hJ.field_order
  distance_order := hJ.distance_order
  support := hJ.support

/-- A scalar cap does not change any numerical norm, width, or tail field. -/
def schedule_capped {G : Gauge} {C : Family G} {J : Request V}
    (A : YM.Integration.FullQLocal.RenderedStep.Schedule C J) : YM.Integration.FullQLocal.RenderedStep.Schedule C (capped J) where
  inputNorm := A.inputNorm
  outputNorm := A.outputNorm
  input_norm := A.input_norm
  output_norm := A.output_norm
  inputWidth := A.inputWidth
  outputWidth := A.outputWidth
  input_width_pos := A.input_width_pos
  output_width_pos := A.output_width_pos
  width_reserve := A.width_reserve
  admittedCost := A.admittedCost
  admitted_cost_nonnegative := A.admitted_cost_nonnegative
  admitted_cost_ge_one := A.admitted_cost_ge_one
  radiusLoss := A.radiusLoss
  radius_loss_positive := A.radius_loss_positive
  radius_loss_ge_one := A.radius_loss_ge_one
  calibrationCap := A.calibrationCap
  calibration_cap_nonnegative := A.calibration_cap_nonnegative
  calibration_cap_tendsto := A.calibration_cap_tendsto
  cost_covers_widths := A.cost_covers_widths
  cost_covers_geometry := A.cost_covers_geometry
  cost_covers_units := A.cost_covers_units
  cost_subpower := A.cost_subpower
  pathRate := A.pathRate
  path_rate_positive := A.path_rate_positive
  path_rate_width := A.path_rate_width
  path_rate_cost := A.path_rate_cost
  regular_flat := A.regular_flat
  forced_flat := A.forced_flat

theorem inherited_capped (J : Request V) (x t : ℝ) (ht : 0 ≤ t)
    (hx : x ≤ J.inheritedConstant * t) :
    x ≤ (capped J).inheritedConstant * t := inherited_bound J x t ht hx

theorem forced_capped (J : Request V) (x : ℝ) (hx : x ≤ J.forcedConstant) :
    x ≤ (capped J).forcedConstant := forced_bound J x hx

/-- The larger cutoff is a sufficient condition for the original cutoff. -/
theorem period_capped (J : Request V) (x : ℝ)
    (hx : (capped J).physicalPeriodLower ≤ x) :
    J.physicalPeriodLower ≤ x := period_bound J x hx

end YM.Integration.ActualQlocalRequestFamily
end
