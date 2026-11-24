import YM.Integration.FVA1Physical.Round2.SharedWilsonPrice

/-! Recover the first Wilson vacuum bank from the independently prescribed field
values. A finite jet of this bank determines the same jet after the actual reset. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open RG Lattice YM.Wilson Exterior Tree Marker PhysicalNext.Repeat.Legato Comparison.RG02
open MSbar MSbar.Rolling MSbar.Wave MSbar.Midpoint Push Push.Uniform Precision
open MSbar.Lis FormalOPE.RG10.InversionTop
open scoped Classical Matrix.Norms.Frobenius

/-- Recover a real polynomial from its full field evaluation when one exists. -/
def polynomialFor {σ : Type} (f : (σ → ℝ) → ℝ) : MvPolynomial σ ℝ :=
  if h : ∃ P : MvPolynomial σ ℝ, ∀ x, MvPolynomial.eval x P = f x then h.choose else 0

theorem polynomialFor_eq {σ : Type} (f : (σ → ℝ) → ℝ) (P : MvPolynomial σ ℝ)
    (h : ∀ x, MvPolynomial.eval x P = f x) : polynomialFor f = P := by
  have ex : ∃ V : MvPolynomial σ ℝ, ∀ x, MvPolynomial.eval x V = f x := ⟨P,h⟩
  rw [polynomialFor, dif_pos ex]
  apply MvPolynomial.funext
  intro x
  exact (ex.choose_spec x).trans (h x).symm

theorem bley_coeff_congr {σ : Type} [Fintype σ] (b : PowerSeries ℝ) (P : MvPolynomial σ ℝ)
    {T V : PowerSeries (MvPolynomial σ ℝ)} {r : ℕ}
    (eq : ∀ i ≤ r, PowerSeries.coeff i T = PowerSeries.coeff i V) (i : ℕ) (hi : i ≤ r) :
    PowerSeries.coeff i (bley b T P) = PowerSeries.coeff i (bley b V P) := by
  unfold bley
  rw [map_sub,map_sub]
  congr 1
  unfold ticket
  simp only [PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro j hj
  unfold Wave.fare
  rw [eq j ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hi)]

theorem film_coeff_congr {G : Gauge} {n : Side} (Q : Rep G n) (g : ℝ) {T V : Nesting G n} (p : ℕ)
    (eq : ∀ i ≤ p, PowerSeries.coeff i T = PowerSeries.coeff i V) :
    Aqua.film Q T g p = Aqua.film Q V g p := by
  funext x
  change Aqua.vine Q g x - Aqua.ore Q T g p x = Aqua.vine Q g x - Aqua.ore Q V g p x
  congr 1
  unfold Aqua.ore
  apply Finset.sum_congr rfl
  intro i hi
  unfold Lis.atlas Wave.joy Wave.tariff
  simp only [map_sub,eq i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

variable {G : Gauge} {C : Family G} (L : Bulk.Chain C.path) {I : Type} [DecidableEq I] [Fintype I]
    (R : Census I) (j n : ℕ) {d : ℕ} (U : I → Stamp.Reservation C (C.side (j+1) n) d)
    (F : Forest (C.path.levels.clock.op j n).ratio) (v : (C.path.levels.clock.op j n).Choices) (r : ℕ)

def centeredWilsonSeries : Nesting G (C.side j n) := PowerSeries.mk fun i =>
  polynomialFor fun x =>
    let D := MSMatch.SourceTop.datum R j n U F v (tint G _ x)
    (D.vacuumAction L r i (tint G _ x)).re - (D.vacuumAction L r i 0).re

/-- Restore the fixed kinetic reference to the independent centered action. -/
def bareWilsonBank : Nesting G (C.side j n) := centeredWilsonSeries L R j n U F v r +
  PowerSeries.C (ink (C.side j n) (C.path.levels.params j).clip (L.kin.path (j+1) j))

/-- All retained coefficients of the independently constructed Wilson bank,
transported through the measured scene's reset, equal the actual scene bank. -/
theorem first_reset_coeff {S : Scene C.path.levels n r} (h : firstWilsonBank C L j n r S)
    (i : ℕ) (hi : i ≤ r) :
    PowerSeries.coeff i (bley (S.action j) (bareWilsonBank L R j n U F v r)
      (ink (C.side j n) (C.path.levels.params j).clip (L.kin.path (j+1) j))) =
      PowerSeries.coeff i (S.Poly j) := by
  obtain ⟨B,u,hreset,hbank⟩ := h
  rw [hreset]
  apply bley_coeff_congr _ _ _ i hi
  intro k hk
  let Z := colorCut B u (L.kin.path (j+1) (j+1)) (C.path.levels.params (j+1)).clip L.O
    (S.Poly (j+1)) (L.kin.stationary (j+1) j n B)
  let a := ink (C.side j n) (C.path.levels.params j).clip (L.kin.path (j+1) j)
  change PowerSeries.coeff k (centeredWilsonSeries L R j n U F v r + PowerSeries.C a) = PowerSeries.coeff k Z
  rw [map_add]
  unfold centeredWilsonSeries
  rw [PowerSeries.coeff_mk,polynomialFor_eq _ (PowerSeries.coeff k (Z-PowerSeries.C a))
    (fun x => hbank I R d U F v x k hk),map_sub]
  abel
end YM.Integration.FVA1Physical.Round2
