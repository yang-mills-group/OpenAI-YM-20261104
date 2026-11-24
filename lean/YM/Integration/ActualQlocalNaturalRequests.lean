import YM.Integration.FullQLocalRequestData
import Mathlib.Logic.Encodable.Pi
import Mathlib.Data.Fin.VecNotation

/-! A countable numerical skeleton of an actual finite qlocal Request.
All natural fields and each slot's original test orders are retained.
The three nonnegative cost parameters are dominated by one natural ceiling.
This does not encode or change eta, support, fugacity, or analytic widths,
and is not a cofinality theorem for complete analytic Request or grant data. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualQlocalNaturalRequests
open FullQLocal.RenderedStep
open scoped Classical

variable {V : Type}

def costCap (J : Request V) : ℕ :=
  Nat.ceil (max J.inheritedConstant (max J.physicalPeriodLower J.forcedConstant))

theorem inherited_le_cap (J : Request V) :
    J.inheritedConstant ≤ (costCap J : ℝ) := by
  exact (le_max_left _ _).trans (Nat.le_ceil _)

theorem period_le_cap (J : Request V) :
    J.physicalPeriodLower ≤ (costCap J : ℝ) := by
  exact (le_max_left _ _).trans ((le_max_right _ _).trans (Nat.le_ceil _))

theorem forced_le_cap (J : Request V) :
    J.forcedConstant ≤ (costCap J : ℝ) := by
  exact (le_max_right _ _).trans ((le_max_right _ _).trans (Nat.le_ceil _))

/-- Order, two horizons, four norm orders, five packet capacities, and cost cap. -/
def scalarCode (J : Request V) : Fin 13 → ℕ :=
  ![J.order, J.inputHorizon, J.outputHorizon,
    J.inputFieldOrder, J.outputFieldOrder,
    J.inputDistanceOrder, J.outputDistanceOrder,
    J.vacuumRankCap, J.inputPacketRankCap, J.outputPacketRankCap,
    J.inputPacketPowerCap, J.outputPacketPowerCap, costCap J]

def slotCode (J : Request V) (v : V) : ℕ × ℕ × ℕ × ℕ :=
  (J.inputWeight v, J.outputWeight v, (J.tests v).D, (J.tests v).W)

/-- This is the original Request receipt, not an upgrade of Datum.depth_le. -/
theorem test_order_code (J : Request V) (v : V) :
    max (slotCode J v).1 (slotCode J v).2.1 + 2 ≤
      (slotCode J v).2.2.1 := J.test_order v

theorem whole_test_recover (J : Request V) (v : V)
    (h : ∃ d w : ℕ, J.tests v = ⟨.whole, d, w⟩) :
    J.tests v = ⟨.whole, (slotCode J v).2.2.1, (slotCode J v).2.2.2⟩ := by
  change J.tests v = ⟨.whole, (J.tests v).D, (J.tests v).W⟩
  rcases h with ⟨d, w, hw⟩
  rw [hw]

abbrev Code := Σ n : ℕ, (Fin 13 → ℕ) × (Fin n → ℕ × ℕ × ℕ × ℕ)

def requestCode {n : ℕ} (e : Fin n ≃ V) (J : Request V) : Code :=
  ⟨n, scalarCode J, fun i => slotCode J (e i)⟩

def dictionary (j : ℕ) : Code :=
  (Encodable.decode j).getD ⟨0, (fun _ => 0), Fin.elim0⟩

theorem dictionary_code {n : ℕ} (e : Fin n ≃ V) (J : Request V) :
    ∃ j : ℕ, dictionary j = requestCode e J := by
  refine ⟨Encodable.encode (requestCode e J), ?_⟩
  simp [dictionary]

theorem actual_request_code [Fintype V] (J : Request V) :
    ∃ e : Fin (Fintype.card V) ≃ V, ∃ j : ℕ,
      dictionary j = requestCode e J := by
  let e := (Fintype.equivFin V).symm
  obtain ⟨j, hj⟩ := dictionary_code e J
  exact ⟨e, j, hj⟩

theorem inherited_bound (J : Request V) (x t : ℝ) (ht : 0 ≤ t)
    (hx : x ≤ J.inheritedConstant * t) :
    x ≤ (costCap J : ℝ) * t :=
  hx.trans (mul_le_mul_of_nonneg_right (inherited_le_cap J) ht)

theorem forced_bound (J : Request V) (x : ℝ) (hx : x ≤ J.forcedConstant) :
    x ≤ (costCap J : ℝ) := hx.trans (forced_le_cap J)

theorem period_bound (J : Request V) (x : ℝ) (hx : (costCap J : ℝ) ≤ x) :
    J.physicalPeriodLower ≤ x := (period_le_cap J).trans hx

end YM.Integration.ActualQlocalNaturalRequests
end
