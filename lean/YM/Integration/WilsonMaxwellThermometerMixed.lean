import YM.Integration.WilsonMaxwellThermometerDifferentiated

/-! The potentially nonzero two-color upper jet. An invariant bilinear
reading on native Maxwell slots annihilates every mixed chiral word
through the upper cap of the thermometer. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerMixed
open Maxwell.Free XSpace.Chiral WilsonMaxwellThermometerRotations WilsonMaxwellThermometerChiralSlots
open WilsonMaxwellThermometerDifferentiated
open scoped BigOperators

private theorem exchange {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W →ₗ[ℝ] ℂ)
    (A : Ticket → V → V) (B : Ticket → W → W)
    (holds : ∀ n v w, L (A n v) (B n w) = L v w)
    (reverse : ∀ n w, B n (B n.rev w) = w)
    (v : V) (w : W) {p q : ℝ} (hpq : p ≠ q)
    (hp : (∑ n : Ticket, A n v) = p • v) (hq : (∑ n : Ticket, B n w) = q • w) :
    L v w = 0 := by
  have ht (n : Ticket) : L (A n v) w = L v (B n.rev w) := by
    simpa only [reverse] using holds n v (B n.rev w)
  have H : L (p • v) w = L v (q • w) := by
    rw [← hp, ← hq, map_sum, LinearMap.sum_apply, map_sum]
    simp only [ht]
    exact Equiv.sum_comp (Fin.revPerm (n:=8)) (fun n => L v (B n w))
  simp only [map_smul, LinearMap.smul_apply, Complex.real_smul] at H
  exact (mul_left_cancel₀ (show (p : ℂ) - q ≠ 0 from sub_ne_zero.mpr (by exact_mod_cast hpq))
    (show ((p : ℂ)-q) * L v w = ((p:ℂ)-q) * 0 by rw [sub_mul, H, sub_self, mul_zero]))

abbrev Invariant {j l : ℕ} (L : Flavor j →ₗ[ℝ] Flavor l →ₗ[ℝ] ℂ) :=
  ∀ (s : Bool) (n : Ticket) u v,
    L (actFlavor (rotation s n) j u) (actFlavor (rotation s n) l v) = L u v

private theorem back {j : ℕ} (s : Bool) (n : Ticket) (p : Flavor j) :
    actFlavor (rotation s n) j (actFlavor (rotation s n.rev) j p) = p := by
  rw [reversed, act_inv_f]

private theorem averaging {j l : ℕ} (L : Flavor j →ₗ[ℝ] Flavor l →ₗ[ℝ] ℂ) (h : Invariant L)
    (s : Bool) (u : Flavor j) (v : Flavor l) {x y : ℝ} (hxy : x ≠ y)
    (hu : ∑ n : Ticket, actFlavor (rotation s n) j u = x • u)
    (hv : ∑ n : Ticket, actFlavor (rotation s n) l v = y • v) : L u v = 0 :=
  exchange L (fun n => actFlavor (rotation s n) j) (fun n => actFlavor (rotation s n) l)
    (h s) (back s) u v hxy hu hv

private theorem rest (s t : Bool) (h : t ≠ s) (b : P) :
    ∑ n : Ticket, actFlavor (rotation s n) 0 (slot t b) = (8:ℝ) • slot t b := by
  simp only [WilsonMaxwellThermometerChiralSlots.fixed t s h, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  norm_num [← Nat.cast_smul_eq_nsmul ℝ]

theorem zero_zero (L : Flavor 0 →ₗ[ℝ] Flavor 0 →ₗ[ℝ] ℂ) (h : Invariant L)
    (s t : Bool) (h' : t ≠ s) (a b : P) : L (slot s a) (slot t b) = 0 :=
  averaging L h s _ _ (by norm_num : (0:ℝ) ≠ 8) (by rw [zero_smul, average]) (rest s t h' b)

theorem one_zero (L : Flavor 1 →ₗ[ℝ] Flavor 0 →ₗ[ℝ] ℂ) (h : Invariant L)
    (s t : Bool) (h' : t ≠ s) (k : Axis) (a b : P) : L (firstSlot s k a) (slot t b) = 0 :=
  averaging L h s _ _ (by norm_num : (-2:ℝ) ≠ 8) (moving s k a) (rest s t h' b)

theorem one_one (L : Flavor 1 →ₗ[ℝ] Flavor 1 →ₗ[ℝ] ℂ) (h : Invariant L)
    (s t : Bool) (h' : t ≠ s) (k l : Axis) (a b : P) : L (firstSlot s k a) (firstSlot t l b) = 0 :=
  averaging L h s _ _ (by norm_num : (-2:ℝ) ≠ 4) (moving s k a)
    (WilsonMaxwellThermometerDifferentiated.fixed t s h' l b)

theorem two_zero (L : Flavor 2 →ₗ[ℝ] Flavor 0 →ₗ[ℝ] ℂ) (h : Invariant L)
    (s t : Bool) (h' : t ≠ s) (v : E4) (k : Axis) (a b : P) :
    L (feed v 1 (firstSlot s k a)) (slot t b) = 0 := by
  let B : Flavor 1 →ₗ[ℝ] E4 →ₗ[ℝ] ℂ :=
    LinearMap.mk₂ ℝ (fun u w => L (feed w 1 u) (slot t b))
      (by intro u u' w; simp) (by intro c u w; simp)
      (by intro u x y; change L (insert u (x+y)) _ = _; rw [map_add, map_add, LinearMap.add_apply]; rfl)
      (by intro c u w; change L (insert u (c • w)) _ = _; rw [map_smul, map_smul, LinearMap.smul_apply]; rfl)
  apply exchange B (fun n => actFlavor (rotation s n) 1) (fun n => Ortho.move (rotation s n))
      _ _ (firstSlot s k a) v (show (-2:ℝ) ≠ 4 by norm_num) (moving s k a)
      (by rw [direction]; norm_num [← Nat.cast_smul_eq_nsmul ℝ])
  · intro n u w
    change L (feed (Ortho.move (rotation s n) w) 1 (actFlavor (rotation s n) 1 u)) (slot t b) =
      L (feed w 1 u) (slot t b)
    rw [← natural]
    simpa only [WilsonMaxwellThermometerChiralSlots.fixed t s h'] using
      h s n (feed w 1 u) (slot t b)
  · intro n w; rw [reversed, Ortho.move_inv]

end YM.Integration.WilsonMaxwellThermometerMixed
