import YM.Integration.WilsonMaxwellThermometerChiralSlots
import YM.Integration.WilsonMaxwellThermometerFirstRows

/-! The two distinct angular averages on actual once differentiated Maxwell
curvatures. The arithmetic uses the original physical equations. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonMaxwellThermometerDifferentiated
open Set Function Maxwell Maxwell.Free XSpace.Chiral WilsonMaxwellThermometerRotations
open WilsonMaxwellThermometerChiralSlots
open scoped BigOperators

def insert {j : ℕ} (p : Flavor j) : E4 →ₗ[ℝ] Flavor (j+1) where
  toFun x := feed x j p
  map_add' x y := by
    apply LinearMap.ext; intro f
    change p (lower ℝ j (x+y) f) = p (lower ℝ j x f) + p (lower ℝ j y f)
    rw [← map_add]
    apply congrArg p
    apply Subtype.ext
    funext a b
    apply ContinuousMultilinearMap.ext; intro v
    change (↑(j+1 : ℕ) : ℝ) • (f.val a b).curryLeft (x+y) v =
      (↑(j+1 : ℕ) : ℝ) • (f.val a b).curryLeft x v + (↑(j+1 : ℕ) : ℝ) • (f.val a b).curryLeft y v
    rw [map_add, add_apply, smul_add]
  map_smul' c x := by
    apply LinearMap.ext; intro f
    change p (lower ℝ j (c • x) f) = c • p (lower ℝ j x f)
    rw [← map_smul]
    apply congrArg p
    apply Subtype.ext
    funext a b
    apply ContinuousMultilinearMap.ext; intro v
    change (↑(j+1 : ℕ) : ℝ) • (f.val a b).curryLeft (c • x) v =
      c • ((↑(j+1 : ℕ) : ℝ) • (f.val a b).curryLeft x v)
    rw [map_smul, smul_apply, smul_comm]

theorem natural {j : ℕ} (o : Ortho) (p : Flavor j) (x : E4) :
    actFlavor o (j+1) (feed x j p) = feed (Ortho.move o x) j (actFlavor o j p) := by
  ext f
  apply congrArg p
  simpa using turn_comp_shift o⁻¹ f (Ortho.move o x)

def firstSlot (s : Bool) (k : Axis) (a : P) := feed (basis k) 0 (slot s a)

theorem read (s : Bool) (k : Axis) (a : P) (f : Sheet 1) :
    firstSlot s k a f =
      WilsonMaxwellThermometerJets.chiral s a (WilsonMaxwellThermometerJets.first (asWave f) 0 k) := by
  simp only [firstSlot, slot, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    WilsonMaxwellThermometerJets.chiral, WilsonMaxwellThermometerJets.first, shift_mark,
    shift, smul_eq_mul]

private theorem expand (s : Bool) (n : Ticket) (k : Axis) {j : ℕ} (p : Flavor j) :
    feed (Ortho.move (rotation s n) (basis k)) j p =
      ∑ l : Axis, ((entry s n l k : ℝ)/2) • feed (basis l) j p := by
  change insert p (Ortho.move (rotation s n) (basis k)) = _
  rw [ortho_expansion, map_sum]
  simp only [map_smul, coordinates]; rfl

private theorem dated (s t : Bool) (n : Ticket) (k : Axis) (a : P) :
    (8:ℝ) • actFlavor (rotation t n) 1 (firstSlot s k a) =
      ∑ l : Axis, ∑ b : P,
        ((entry t n l k : ℝ) * (spin s t n a b : ℝ)) • firstSlot s l b := by
  let o := rotation t n
  let v := Ortho.move o (basis k)
  calc
    _ = (2:ℝ) • feed v 0 ((4:ℝ) • actFlavor o 0 (slot s a)) := by
      simp only [firstSlot, v, o, natural, map_smul, smul_smul]
      norm_num
    _ = _ := by
      rw [rotate, map_sum, Finset.smul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_smul, expand, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [firstSlot, smul_smul]; congr 1; ring

theorem fixed (s t : Bool) (h : s ≠ t) (k : Axis) (a : P) :
    ∑ n : Ticket, actFlavor (rotation t n) 1 (firstSlot s k a) =
      (4:ℝ) • firstSlot s k a := by
  simp only [firstSlot, natural, WilsonMaxwellThermometerChiralSlots.fixed s t h]
  change ∑ n : Ticket, insert (slot s a) (Ortho.move (rotation t n) (basis k)) = _
  rw [← map_sum, direction, map_nsmul]
  norm_num [← Nat.cast_smul_eq_nsmul ℝ, insert]

theorem moving (s : Bool) (k : Axis) (a : P) :
    ∑ n : Ticket, actFlavor (rotation s n) 1 (firstSlot s k a) =
      (-2:ℝ) • firstSlot s k a := by
  apply LinearMap.ext; intro f
  let F (n : Ticket) := (actFlavor (rotation s n) 1 (firstSlot s k a)) f
  let X : WilsonMaxwellThermometerFirstRows.Array1 ℝ := fun l b => firstSlot s l b f
  have hh : WilsonMaxwellThermometerJets.Equations s X := by
    simpa only [X, read] using WilsonMaxwellThermometerJets.field s (asWave f) (wavePoly f) 0
  have H (n : Ticket) : 8 * F n = ∑ l : Axis, ∑ b : P,
      ((entry s n l k : ℝ) * (spin s s n a b : ℝ)) * X l b := by
    simpa only [F, X, LinearMap.smul_apply, smul_eq_mul, LinearMap.sum_apply]
      using LinearMap.congr_fun (dated s s n k a) f
  have paid : 8 * (∑ n : Ticket, F n) = -16 * X k a := by
    rw [Finset.mul_sum]; simp_rw [H]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s:=Finset.univ (α:=Ticket)) (t:=Finset.univ (α:=P)), ← Finset.sum_mul]
    exact WilsonMaxwellThermometerFirstRows.measured s a k X hh
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  change (∑ n : Ticket, F n) = -2 * X k a
  linarith only [paid]

end YM.Integration.WilsonMaxwellThermometerDifferentiated
