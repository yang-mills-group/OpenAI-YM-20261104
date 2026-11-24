import YM.Integration.QLocalVacuumDerivativePrice

/-!
# Intrinsic invoices for an arbitrary returned zero-aware layer list

Original permits supply the structural fields only. The numerical credit
comes from the original atom's actual rank and true exponential row price.
A temporary credit-only repricing has exactly the same full activities and
rendered function. Thus the native Valid conclusion applies to the original
list even when its stored credits were unnecessarily large.

The weight may be any function of the integer step order, including a raw
negative power or the exact difference of two coupling prefactors. No
smallness, ratio bound or comparison with the next admission is inferred.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.ZeroAwareIntrinsicRenderInvoice

open Function Finset Lattice Wilson RG
open YM.IterationFour.Vacuum
open LocalComparison.Global
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side}

def weight (k : ℤ → ℝ) (a : Piece G n) : ℝ := k (Render.stepOrder a)

def reprice (credit : Piece G n → ℝ) (a : Piece G n) : Piece G n :=
  { a with credit := credit a }

def repriceLayers (credit : Piece G n → ℝ) (S : List (Piece G n)) :=
  S.map (reprice credit)

theorem renders_unchanged (credit : Piece G n → ℝ) (S : List (Piece G n))
    (k : ℤ → ℝ) (p : BudgetPoint) (U : Config G n) :
    Render.renders (weight k) p U (repriceLayers credit S) =
      Render.renders (weight k) p U S := by
  induction S with
  | nil => rfl
  | cons a S ih =>
      change weight k a * a.packet.amount p U +
          Render.renders (weight k) p U (repriceLayers credit S) =
        weight k a * a.packet.amount p U + Render.renders (weight k) p U S
      rw [ih]

theorem adorn_unchanged (credit : Piece G n → ℝ) (S : List (Piece G n))
    (k : ℤ → ℝ) (A : Activities G n) :
    Render.adorn (weight k) A (repriceLayers credit S) =
      Render.adorn (weight k) A S := by
  induction S with
  | nil => rfl
  | cons a S ih =>
      change a.packet.attach (weight k a)
          (Render.adorn (weight k) A (repriceLayers credit S)) =
        a.packet.attach (weight k a) (Render.adorn (weight k) A S)
      rw [ih]

private theorem dollars_repriced (credit : Piece G n → ℝ)
    (S : List (Piece G n)) (k : ℤ → ℝ) :
    Render.dollars (fun a => ‖weight k a‖) (repriceLayers credit S) =
      (S.map (fun a => ‖weight k a‖ * credit a)).sum := by
  induction S with
  | nil => rfl
  | cons a S ih =>
      change ‖weight k a‖ * credit a +
          Render.dollars (fun a => ‖weight k a‖) (repriceLayers credit S) =
        ‖weight k a‖ * credit a + (S.map (fun a => ‖weight k a‖ * credit a)).sum
      rw [ih]

variable {S : List (Piece G n)} {p : BudgetPoint} {rankCap : ℕ}
    {width budget : ℝ}
    (H : ZeroAwareVacuumPackets S p rankCap width budget)

/-- Actual rank, threshold power, reserved-width moment and true piece cost. -/
def intrinsicCredit (a : Piece G n) : ℝ :=
  H.derivativeFactor a.rank * H.pieceCost a

/-- No bound on a.credit is used. Its Invoice contributes only the four
structural requirements that do not mention numerical credit. -/
theorem invoice (h : Render.permits S p) (hw : 0 < width)
    (a : Piece G n) (ha : a ∈ S) :
    a.packet.Invoice p (intrinsicCredit H a) := by
  have old := h a ha
  refine ⟨old.smooth, old.flat, old.null, old.moves, ?_⟩
  refine ⟨fun i => Next.Scheduling.Wages.price p (H.atom a i),
    fun i => H.canonical_price a ha i, fun o => ?_⟩
  exact H.derivative_budget hw a ha o

theorem repriced_permits (h : Render.permits S p) (hw : 0 < width) :
    Render.permits (repriceLayers (intrinsicCredit H) S) p := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  exact invoice H h hw b hb

def bill (k : ℤ → ℝ) : ℝ :=
  (S.map (fun a => ‖weight k a‖ * intrinsicCredit H a)).sum

theorem bill_nonnegative (h : Render.permits S p) (hw : 0 < width)
    (k : ℤ → ℝ) : 0 ≤ bill H k := by
  rw [bill, ← dollars_repriced]
  exact Render.loose (repriced_permits H h hw)
    (fun a => ‖weight k a‖) (fun a => norm_nonneg _)

/-- The literal original appended activities obtain the intrinsic numerical
bill. Forced rows and their original allowance remain exactly unchanged. -/
theorem valid (R : Rep G n) {S : List (Piece G n)}
    {rankCap : ℕ} {width budget d z : ℝ}
    (H : ZeroAwareVacuumPackets S R.p rankCap width budget)
    (h : Render.permits S R.p) (hw : 0 < width) (k : ℤ → ℝ)
    (hR : R.activities.Valid R.p d z) :
    (Render.append S R (weight k)).activities.Valid R.p (d + bill H k) z := by
  have hh := Render.addition (weight k) (repriced_permits H h hw) hR
  change (Render.adorn (weight k) R.activities
      (repriceLayers (intrinsicCredit H) S)).Valid R.p
      (d + Render.dollars (fun a => ‖weight k a‖)
        (repriceLayers (intrinsicCredit H) S)) z at hh
  rw [adorn_unchanged, dollars_repriced] at hh
  exact hh

end YM.Integration.ZeroAwareIntrinsicRenderInvoice
end
