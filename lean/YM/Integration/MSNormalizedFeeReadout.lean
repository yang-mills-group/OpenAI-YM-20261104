import YM.FVA2.Pond
import YM.Integration.MSFeeReadout

/-! Exact graded fee transition on the same original regulator before its
Taylor removal. The two engineering totals are those of the concrete words. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSNormalizedFeeReadout

open Finset FVA2 Lattice MS MS.Local.Physical MS.Land MS.Menus MS.Rake
open MS.Book.Program MSFeeCoordinates MSFeeReadout
open scoped BigOperators Classical

variable {G : Gauge} {B : Deck G} {I : Type} [LinearOrder I] [Fintype I]
variable (V : Warehouse G) (P : Prescription B) (q : Side) (d : I → ℕ)
variable (o : Cover) (c : I → Cover) (μ θ : ℝ)

abbrev into : PowerSeries ℝ →+* PowerSeries ℂ := PowerSeries.map Complex.ofRealHom

def price (Z : (i : I) → Acts B (d i)) : PowerSeries ℂ :=
  PowerSeries.C (Port.τ (Vane.charge d Finset.univ) θ) *
    into (Track.ticketRead V q d P.team (μ-θ) Z o c Finset.univ)

def word (a : Slots B d Finset.univ) : I → Label B :=
  fun i => ColorCode.labelAt B (a ⟨i, Finset.mem_univ i⟩)

theorem original (a : Slots B d Finset.univ) (k : ℕ) :
    PowerSeries.coeff k (price V P q (dimensions d a) o c μ θ (originalFees d P a)) =
      Pond.markedPrice μ (word d a) V P q θ o c Finset.univ k := by
  rw [price, PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  rfl

theorem split (u v : ℕ) :
    Port.τ (u : ℤ) θ = Port.τ ((u : ℤ)-v) θ * Port.τ (v : ℤ) θ := by
  unfold Port.τ
  rw [← Complex.ofReal_mul, ← zpow_add₀ (Real.exp_ne_zero θ)]
  congr 2
  omega

def transition (Z : (i : I) → Acts B (d i)) (a : Slots B d Finset.univ) : PowerSeries ℂ :=
  PowerSeries.C (Port.τ ((Vane.charge d Finset.univ : ℤ) -
       (Vane.charge (dimensions d a) Finset.univ : ℤ)) θ) *
    into (evaluate (μ-θ) (∏ i : (Finset.univ : Finset I), receiver P (Z i.val) (a i)))

theorem written (Z : (i : I) → Acts B (d i)) :
    price V P q d o c μ θ Z =
      ∑ a : Slots B d Finset.univ, transition P d μ θ Z a *
        price V P q (dimensions d a) o c μ θ (originalFees d P a) := by
  classical
  rw [price, MSFeeReadout.whole, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, transition, price]
  simp only [map_prod]
  rw [split θ (Vane.charge d Finset.univ) (Vane.charge (dimensions d a) Finset.univ)]
  rw [map_mul]
  ring

theorem coefficient (Z : (i : I) → Acts B (d i)) (k : ℕ) :
    PowerSeries.coeff k (price V P q d o c μ θ Z) =
      ∑ a : Slots B d Finset.univ, ∑ l ∈ Finset.HasAntidiagonal.antidiagonal k,
        PowerSeries.coeff l.1 (transition P d μ θ Z a) *
          Pond.markedPrice μ (word d a) V P q θ o c Finset.univ l.2 := by
  rw [written, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro l _
  rw [original]

omit [LinearOrder I] in
theorem value (Z : (i : I) → Acts B (d i)) (a : Slots B d Finset.univ) (k : ℕ) :
    PowerSeries.coeff k (transition P d μ θ Z a) =
      Port.τ ((Vane.charge d Finset.univ : ℤ) -
        (Vane.charge (dimensions d a) Finset.univ : ℤ)) θ *
        ((PowerSeries.coeff k
          (∏ i : (Finset.univ : Finset I), receiver P (Z i.val) (a i))).eval (μ-θ) : ℝ) := by
  rw [transition, PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
  change _ * (((PowerSeries.coeff k (evaluate (μ-θ) _)) : ℝ) : ℂ) = _
  rw [evaluate, PowerSeries.coeff_map]
  rfl

end YM.Integration.MSNormalizedFeeReadout
