import YM.Next.RANK.GaussTags
import YM.Integration.WilsonMaxwellThermometerFirstCells

/-! In the seven ordinary faces of a triple of quadratic Gaussian insertions
    all three local normal-order conventions cancel, before the period limit. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonMaxwellThermometerGroundDiagonal
open MvPolynomial Next.Rank.Normal Finset
open scoped BigOperators
variable {V : Type*}

def faces (Q : Symmetric (Fin 3 × V)) (p : Fin 3 → poly V) (s : Finset (Fin 3)) : ℂ :=
  blend Q 0 (pot s p)

private def three {B : Type*} [CommSemiring B] [Algebra ℂ B] (E : B →ₗ[ℂ] ℂ) (a b c : B) :=
  E (a*b*c) - (E (a*b)*E c+E (a*c)*E b+E (b*c)*E a) + 2*(E a*E b*E c)

private theorem printed (Q : Symmetric (Fin 3 × V)) (p : Fin 3 → poly V) :
    WilsonPositionThermometerConnected.value (faces Q p) =
      three (blend Q 0) (post 0 (p 0)) (post 1 (p 1)) (post 2 (p 2)) := by
  classical
  simp [WilsonPositionThermometerConnected.value,faces,three,pot,Fin.prod_univ_succ,mul_assoc]

private theorem shifted {B : Type*} [CommSemiring B] [Algebra ℂ B]
    (E : B →ₗ[ℂ] ℂ) (unmarked : E 1=1) (a b c : B) (x y z : ℂ) :
    three E (a+x•1) (b+y•1) (c+z•1) = three E a b c := by
  simp only [three, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_one, one_mul,
    map_add, map_smul, smul_eq_mul, unmarked, mul_one]
  ring

theorem constants (Q : Symmetric (Fin 3 × V)) (p : Fin 3 → poly V) (c : Fin 3→ℂ) :
    WilsonPositionThermometerConnected.value (faces Q (fun i=>p i+C (c i))) =
      WilsonPositionThermometerConnected.value (faces Q p) := by
  simp only [printed, map_add, post_C, show ∀ x : ℂ, C (σ:=Fin 3×V) x=x • 1 from
    fun x => by rw [MvPolynomial.smul_eq_C_mul, mul_one]]
  exact shifted _ (fresh Q 0) .. 

private theorem single (Q : Symmetric V) (a : V) : milk Q (X a) = X a := by
  have h := feeds Q a (1:poly V)
  simpa only [mul_one,pure,Derivation.map_one_eq_zero,add_zero] using h

private theorem quadratic (Q : Symmetric V) (a b : V) :
    milk Q (X a * X b) = X a * X b + C (Q.cov a b) := by rw [feeds,single,slit_X]

/-- An arbitrary diagonal covariance change can be discarded simultaneously
    at all seven ordinary faces once their connected scalar is taken. -/
theorem original {T : Type*} [Fintype T] (Q : Symmetric (Fin 3 × V))
    (M : Fin 3 → Symmetric V) (a b : Fin 3 → T → V)
    (price : Fin 3 → T → ℂ) (unit : Fin 3 → ℂ) :
    let p (i : Fin 3) := C (unit i)+∑ t, price i t • (X (a i t)*X (b i t) : poly V)
    WilsonPositionThermometerConnected.value (faces (Q + -(self M)) p) =
      WilsonPositionThermometerConnected.value (faces Q p) := by
  classical
  intro p
  let c (i : Fin 3) := ∑t, price i t * (-(M i)).cov (a i t) (b i t)
  have moved (i : Fin 3) : milk (-(M i)) (p i) = p i + C (c i) := by
    dsimp only [p]
    simp only [_root_.map_add, fine, _root_.map_sum, _root_.map_smul, quadratic, smul_add,
      sum_add_distrib, add_assoc]
    congr 2
    simp [c, MvPolynomial.smul_eq_C_mul]
  have all : faces (Q + -(self M)) p = faces Q (fun i=>p i+C (c i)) := by
    ext s : 1
    unfold faces
    rw [← barn M Q 0 p s]
    simp_rw [moved]
  rw [all, constants]

end YM.Integration.WilsonMaxwellThermometerGroundDiagonal
