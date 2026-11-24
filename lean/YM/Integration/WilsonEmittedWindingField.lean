import YM.Integration.WilsonEmittedHealthyField
import YM.Integration.WilsonEmittedWindingSlice

/-! Keep the complete compact difference on the group. Its finite-period low
coefficients are allowed a signed error on the original thermal and link chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedWindingField
open Function Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn
open Comparison.RG02 Comparison.Density Comparison.Density.Mirrors
open Transport AnalyticBridge.SectorAffine.Offset
open scoped BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} (B : BudgetPoint) (L : LinkTube G)
variable {o u : Site n} {a k D j m l : ℕ} {g w P S T ε : ℝ}

theorem original (f h : ℝ × Directions G n → ℂ) (short far : ℝ → Config G n → ℂ)
    (hε : 0 ≤ ε) (seam : ∀ i < j, ‖iteratedFDeriv ℝ i (f-h) 0‖ ≤ ε)
    (split : ∀ A : Directions G n, (f-h) (g,A)=short g (increment 1 A)+far g (increment 1 A))
    (whole : ∀ z : ℝ × Directions G n, ‖z‖ ≤ 1 → Through m (f-h) z P)
    (kept : ∀ z : ℝ × Directions G n, ‖z‖ ≤ 1 →
      Through m (fun v : ℝ × Directions G n => short v.1 (increment 1 v.2)) z S)
    (removed : Through m (fun v : ℝ × Directions G n => far v.1 (increment 1 v.2)) (g,0) T)
    (hg : 0 < g) (hg' : g ≤ 1) (hl : l ≤ j) (hj : j ≤ m)
    (fit : LocalOn (neighborhood k o) (short g))
    (ward : GaugeInvariant (short g)) (borel : Measurable (short g))
    (ha : separation o u ≤ a) (hk : k < D) (room : Room B n L D w) (order : B.order ≤ m) :
    B.Regular (neighborhood D o) (short g) ∧
    B.supBounds u (neighborhood D o) (short g)
      (Anchor.focus k a B^B.order *
        (groupPrice L B.order * (l*(((j:ℝ)*ε+P*g^(j-l))+T)+S*w^l))) := by
  have unit : ‖((g,0):ℝ × Directions G n)‖ ≤ 1 := by simp [Prod.norm_def,abs_of_pos hg,hg']
  have base := whole (g,0) unit
  have hP := base.nonneg
  have top (A : Directions G n) (hA : ‖A‖ ≤ w) : Through m (short g ∘ increment 1) A S := by
    exact WilsonEmittedCouplingSlice.fixed (kept (g,A)
      (by change max ‖g‖ ‖A‖ ≤ 1; exact max_le (by simpa [abs_of_pos hg] using hg') (hA.trans room.small)))
  have nonnegative := (top 0 (by simpa using B.threshold_pos.le.trans room.budget)).nonneg
  have low := WilsonEmittedWindingSlice.original (f-h) hj hl hg.le hg' hP hε
    (fun z z' => whole z (z'.trans hg')) seam
  have close := WilsonEmittedCouplingSlice.fixed base
  have distant : Through m (far g ∘ increment 1) (0:Directions G n) T := WilsonEmittedCouplingSlice.fixed removed
  have decomposition : short g ∘ increment 1 =
      (fun A : Directions G n => (f-h) (g,A)) - (far g ∘ increment 1) := by
    funext A
    change short g (increment 1 A)=(f-h) (g,A)-far g (increment 1 A)
    rw [split]; abel
  have atzero (i : ℕ) (hi : i < l) : ‖iteratedFDeriv ℝ i (short g ∘ increment 1) 0‖ ≤ ((j:ℝ)*ε+P*g^(j-l))+T := by
    rw [decomposition,iteratedFDeriv_sub_apply
      (Transport.through_le close (hi.le.trans (hl.trans hj))).smooth
      (Transport.through_le distant (hi.le.trans (hl.trans hj))).smooth]
    exact (norm_sub_le ..).trans (add_le_add (low i hi) (distant.pay i (hi.le.trans (hl.trans hj))))
  have localSet := Finset.Subset.refl (neighborhood k o)
  exact ⟨Anchor.aligned B L (short g) localSet hk room order borel fit ward top,
    Anchor.pay B L (short g) u ha localSet hk room order (hl.trans hj) nonnegative
      (add_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hε) (mul_nonneg hP (pow_nonneg hg.le _))) removed.nonneg) fit ward top atzero⟩

end YM.Integration.WilsonEmittedWindingField
