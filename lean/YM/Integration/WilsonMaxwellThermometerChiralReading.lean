import YM.Integration.WilsonMaxwellThermometerProfile
import YM.Integration.WilsonMaxwellThermometerMixed

/-! Mixed curvature jets heard against the two genuine chiral, color-summed
quadratic sources on the original separated profile. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerChiralReading
open Maxwell Maxwell.Free XSpace XSpace.Chiral XSpace.Rose WilsonMaxwellThermometerRotations
open WilsonMaxwellThermometerChiralSlots WilsonMaxwellThermometerDifferentiated
open WilsonMaxwellThermometerProfile WilsonMaxwellThermometerMixed
open scoped BigOperators
variable {G : Gauge}

def polar (G : Gauge) (s : Bool) : WickPol G := ∑ a : P, team G (slot s a) (slot s a)

private theorem orthogonal : ∀ (s t : Bool) (n : Ticket) (b c : P),
    (∑ a : P, spin s t n a b * spin s t n a c) = if b=c then 16 else 0 := by decide

private theorem bilinear_sum {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (D : E →ₗ[ℝ] E →ₗ[ℝ] F) (c : P → ℝ) (p : P → E) :
    D (∑ b, c b • p b) (∑ b, c b • p b) =
      ∑ b : P, ∑ d : P, (c b * c d) • D (p b) (p d) := by
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl
    fun d _ => by rw [mul_comm (c d)]

private theorem expand (s t : Bool) (n : Ticket) (a : P) :
    (16:ℝ) • team G (actFlavor (rotation t n) 0 (slot s a)) (actFlavor (rotation t n) 0 (slot s a)) =
      ∑ b : P, ∑ c : P, ((spin s t n a b : ℝ) * (spin s t n a c : ℝ)) • team G (slot s b) (slot s c) := by
  let D := duetL G 0 0
  let u := actFlavor (rotation t n) 0 (slot s a)
  change (16:ℝ) • D u u = ∑ b : P, ∑ c : P, _ • D (slot s b) (slot s c)
  calc
    _ = D ((4:ℝ) • u) ((4:ℝ) • u) := by
      simp only [map_smul, LinearMap.smul_apply, smul_smul]; norm_num
    _ = _ := by rw [show (4:ℝ) • u = _ from rotate s t n a]; exact bilinear_sum D _ _

private theorem collect (s t : Bool) (n : Ticket) (p : P → P → WickPol G) (b : P) :
    (∑ a : P, ∑ c : P, ((spin s t n a b : ℝ) * (spin s t n a c : ℝ)) • p b c) = (16:ℝ) • p b b := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, ← Int.cast_mul, ← Int.cast_sum, orthogonal, Int.cast_ite,
    Int.cast_ofNat, Int.cast_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem conserved (s t : Bool) (n : Ticket) :
    reflectPol (rotation t n) (polar G s) = polar G s := by
  apply (smul_right_injective _ (by norm_num : (16:ℝ) ≠ 0))
  change (16:ℝ) • reflectPol (rotation t n) (polar G s) = (16:ℝ) • polar G s
  rw [polar, map_sum, Finset.smul_sum, Finset.smul_sum]
  simp_rw [orient_team, expand]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => collect s t n (fun i j => team G (slot s i) (slot s j)) b

private theorem tested {V : Normalize.Store G} (K : Pick V) (c d : Bool) (j l : ℕ) :
    Invariant (paired K (polar G c) (polar G d) j l) :=
  fun s n => paired_rotates K _ _ _ (conserved c s n) (conserved d s n)

theorem undifferentiated {V : Normalize.Store G} (K : Pick V)
    (c d s t : Bool) (h : t ≠ s) (a b : P) :
    read K (polar G c) (polar G d) (team G (slot s a) (slot t b)) = 0 :=
  zero_zero _ (tested K c d 0 0) s t h a b

theorem first {V : Normalize.Store G} (K : Pick V)
    (c d s t : Bool) (h : t ≠ s) (k : Axis) (a b : P) :
    read K (polar G c) (polar G d) (team G (firstSlot s k a) (slot t b)) = 0 :=
  one_zero _ (tested K c d 1 0) s t h k a b

theorem split {V : Normalize.Store G} (K : Pick V)
    (c d s t : Bool) (h : t ≠ s) (k l : Axis) (a b : P) :
    read K (polar G c) (polar G d) (team G (firstSlot s k a) (firstSlot t l b)) = 0 :=
  one_one _ (tested K c d 1 1) s t h k l a b

theorem second {V : Normalize.Store G} (K : Pick V)
    (c d s t : Bool) (h : t ≠ s) (u : E4) (k : Axis) (a b : P) :
    read K (polar G c) (polar G d) (team G (feed u 1 (firstSlot s k a)) (slot t b)) = 0 :=
  two_zero _ (tested K c d 2 0) s t h u k a b

end YM.Integration.WilsonMaxwellThermometerChiralReading
