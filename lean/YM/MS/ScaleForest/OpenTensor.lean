import YM.MS.ScaleForest.Gaussian
/-!
# Open tensor before Taylor cutoff

For a two-edge Gaussian, integrate exactly. The shifts can be any vector
(change of variables in four dims) so this accounts for both the constant
and the two angular projected moments on general evaluation rays.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.SquareShift
open Function Filter Set Finset MeasureTheory Metric
open MS Plane Koszul Heat Flux Landau Tone Momentum Real Frame Wire Color Detect Native
open _root_.YM.PertExtension
open RG FormalOPE FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open Complex (I)
open WilsonMS.BetaValue WilsonMS.BetaValue.HeatPapers Papers
open scoped Topology ContDiff BigOperators ENNReal

-- expectation by Γ / directional IBP
local notation "V" => HeatPapers.Poly

variable (q p : QP) (i j : Axis) (a b x t : ℝ)

def sqPane (a : ℝ) (q : QP) : V := rsqP + (spring (2*a))* alongP q + spring (a^2 * q.sq)

def sqD (a : ℝ) (q : QP) (i : Axis) : V := (2:ℝ) • petal i + spring (2*a*q i)

theorem moved_sq : (p+a • q).sq = p.sq + 2*a * xdot p q + a^2*q.sq := by
  unfold Momentum.sq xdot; rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; simp; ring

theorem at_pane : meterR p (sqPane a q)=(p+a • q).sq := by simp only [sqPane,map_add,map_mul,atR,at_dot,at_sq,moved_sq]

theorem deriv_pane : AxisDeriv i (sqPane a q) (sqD a q i) := by
  unfold sqPane sqD
  convert ( (deriv_sqP.add ((deriv_const _).product (deriv_along _))).add (deriv_const _) ) using 1
  simp only [zero_mul,zero_add,add_zero,spring,map_mul]

theorem deriv_D : AxisDeriv j (sqD a q i) (spring (2*kk j i)) := by
  unfold sqD
  convert ((deriv_petal j i).scale (2:ℝ)).add (deriv_const _) using 1
  rw [spring,spring,map_mul,add_zero, Algebra.smul_def]

def squarePoly (q : QP) (a b : ℝ) : V := sqPane a q * sqPane b q

def squareD (q : QP) (a b : ℝ) (i : Axis) : V := sqD a q i * sqPane b q + sqD b q i * sqPane a q

def squareDD (q : QP) (a b : ℝ) (i j : Axis) : V :=
  spring (2 * kk j i) * sqPane b q + sqD a q i * sqD b q j + (spring (2 * kk j i)*sqPane a q + sqD b q i * sqD a q j)

theorem Dpoly : AxisDeriv i (squarePoly q a b) (squareD q a b i) := by
  rw [squareD,mul_comm (sqD b ..)]; exact (deriv_pane _ _ _).product (deriv_pane _ _ _)

theorem DDpoly : AxisDeriv j (squareD q a b i) (squareDD q a b i j) :=
  ((deriv_D _ _ _ _).product (deriv_pane _ _ _)).add ((deriv_D _ _ _ _).product (deriv_pane _ _ _))

def bothPoly (q : QP) (a b : ℝ) (i j : Axis) : V :=
  squarePoly q a b * (petal i + spring (b*q i)) * (petal j + spring (a * q j))

def tensorPol (q : QP) (i j : Axis) (p : QP) := p.sq * (p+q).sq * (p+q) i * p j

theorem at_both (ht : b=a+x) : tensorPol (x•q) i j (p+a•q) = meterR p (bothPoly q a b i j) := by
  unfold tensorPol bothPoly squarePoly
  simp only [add_assoc p,← add_smul,← ht,map_mul,map_add,atP,atR,at_pane,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [ht]; ring
-- Expectations in IBP price
section expect
variable {α : ℝ} (h : 0 < α)
set_option quotPrecheck false
local notation "Φ" => Papers.opening mplane (Beam α h)
local notation "s" => gaussS α

def squareValue (s' a b Q : ℝ) := 24*s'^2 +4*(a^2+b^2)*s'*Q+4*a*b*s'*Q+(a*b)^2*Q^2

def firstValue (s' a b Q : ℝ) := 12*(a+b)*s'^2 + 2*a*b*(a+b)*s'*Q

def pairValue (Q p r d s' a b : ℝ) := s'*d*(squareValue s' a b Q)+s'^2*( (24*s'+2*(a^2+b^2)*Q)*d + 8*a*b*p*r ) +
    p*r*((a+b)*firstValue s' a b Q + a*b*squareValue s' a b Q)

include h

theorem from_const (t : ℝ) (X : V) : Φ (spring t*X)= t * Φ X := by rw [spring, ← Algebra.smul_def]; exact map_smul Φ t X

theorem to_const (t : ℝ) (X : V) : Φ (X*spring t)= t * Φ X := by rw [mul_comm X, from_const]

theorem payment_square : Φ (squarePoly q a b)=squareValue s a b q.sq := by
  let A := alongP q; let R := rsqP
  let x := spring (2*a); let y:= spring (2*b); let r := spring (a^2*q.sq); let u := spring (b^2*q.sq)
  have he : squarePoly q a b = R*R+x*(R*A)+y*(R*A)+r*R+u*R+x*(y*(A*A))+u*(x*A)+r*(y*A)+r*u := by
    change (R+x*A+r)*(R+y*A+u)=_; ring
  rw [he]; unfold A R x y r u squareValue; simp only [map_add,from_const,
    phi_const,phi_sq_mul_sq,phi_sq_mul_pa,phi_along_sq,phi_sqP,phi_along]; ring

theorem payment_first : Φ (squarePoly q a b * petal i)=q i*firstValue s a b q.sq := by
  rw [stein h (Dpoly q i a b)]
  have ht (a b : ℝ) : Φ (sqD a q i * sqPane b q) =
    4*b*(s*q i)+(2*a*q i)*(4*s+b^2*q.sq) := by
    rw [mul_comm (sqD ..)]; simp only [sqPane,sqD,mul_add,mul_smul_comm,add_mul,map_add,map_smul,
      to_const,from_const, mul_assoc (spring _),phi_sqP,phi_const,phi_petal,phi_along,phi_sq_mul_p,phi_along_p]
    simp only [smul_eq_mul]; ring
  unfold squareD firstValue; rw [map_add,ht,ht]; ring

theorem payment_second : Φ (squarePoly q a b * petal i * petal j)= s* kk i j * squareValue s a b q.sq +
    s^2*((24*s+2*(a^2+b^2)*q.sq)*kk i j+8*a*b*q i*q j) := by
  rw [stein h ((Dpoly q j a b).product (deriv_petal j i)),map_add,to_const,payment_square,stein h (DDpoly q j i a b)]
  have ht (a b : ℝ) (i j : Axis) : Φ (sqD a q i * sqD b q j)=
    4*s*kk i j+4*a*b*q i*q j:= by
    simp only [sqD,mul_add,add_mul,to_const,from_const,map_add,mul_smul_comm,smul_mul_assoc,
      map_smul,phi_const,phi_pair,phi_petal,smul_eq_mul]; ring
  unfold squareDD sqPane; simp only [map_add,from_const,phi_const,phi_along,phi_sqP,ht,kk_comm j i]; ring

theorem payment_both : Φ (bothPoly q a b i j)=pairValue q.sq (q i) (q j) (kk i j) s a b := by
  unfold bothPoly pairValue; rw [mul_add _ (petal j),map_add,to_const, mul_add _ (petal i),
    map_add,to_const,add_mul,map_add,mul_right_comm _ (spring _) (petal j),to_const, payment_second,
    payment_first, payment_first,payment_square]; ring
end expect

-- shift in completed square

def slope (t : ℝ) := -(t^2/ν t)

def volume4 (t : ℝ) := (Real.pi ^ 2 / ν t ^ 2 / (2 * Real.pi)^4)

theorem moveDensity : Pill t (x•q) (p+(slope t*x)•q)=t^3 * exp (slope t*x^2*q.sq) * exp (-(ν t * p.sq)) := by
  unfold Pill City.brush; rw [one_pow,one_pow,one_mul,one_mul,mul_left_comm,mul_assoc,← exp_add,← exp_add]
  rw [add_assoc p,← add_smul,moved_sq,moved_sq]; congr 2
  unfold slope ν; field_simp; ring

def heatValue (Q p r d x t : ℝ) := t^3 * exp (slope t*x^2*Q)*volume4 t*
  pairValue Q p r d (gaussS (ν t)) (slope t * x) ((slope t+1)*x)

theorem two_rank : tune (x•q) (tensorPol (x•q) i j) t = heatValue q.sq (q i) (q j) (kk i j) x t := by
  unfold tune heatValue volume4
  let a := slope t*x; let b:=(slope t+1)*x
  let X := bothPoly q a b i j
  have he (p : QP) : tensorPol (x•q) i j (p+(slope t*x)•q) = X.val p := at_both _ _ _ _ a b x (by unfold a b; ring)
  rw [← integral_add_right_eq_self _ ((slope t*x)•q), ← payment_both q i j a b (ν_pos t), mul_assoc (t^3*_)]
  rw [← net_order (ν_pos t)]
  simp_rw [moveDensity,he,mul_assoc,MeasureTheory.integral_const_mul,← neg_mul];
  exact congr_arg₂ _ rfl (congr_arg₂ _ rfl (integral_congr_ae (Eventually.of_forall fun z : QP => mul_comm ..)))
end YM.MS.ScaleForest.SquareShift
