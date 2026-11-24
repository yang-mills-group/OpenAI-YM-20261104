import YM.WilsonMS.Beta.GaussianScale
/-!
# Two-edge Gaussian payment, **open** directions

In the projected four-space use the rigorous normalizations & integrability
proofs of the angular scheme. This part of the calculation works as well with
the Ghost as with the two Rose-momenta. Arbitrary external momentum and we
retain the δ and q_i q_j moments separately. This and OpenTensor below reduce
the exact integrated tensor (before external Taylor) to one integral on
[0,1]. No need to assume any rotational symmetry of the **continued
interacting** theory.
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

abbrev xdot (p q : QP) := ∑ i : Axis,p i * q i

def kk (a b : Axis) : ℝ := if a=b then 1 else 0
@[simp] theorem kk_self (a : Axis) : kk a a = 1 := if_pos rfl
theorem kk_comm (a b : Axis) : kk a b=kk b a := by simp [kk, eq_comm]

def rsqP : V := ∑ j : Axis, petal j * petal j

def alongP (q : QP) : V := ∑ j : Axis, q j • petal j

theorem at_sq (q : QP) : meterR q rsqP = q.sq := by
  simp [Momentum.sq, rsqP, atP,pow_two]

theorem at_dot (p q : QP) : meterR p (alongP q) = xdot p q := by
  simp [alongP,xdot, atP,mul_comm]

abbrev AxisDeriv (i : Axis) (W W' : V) : Prop := ∀ (p : QP) (x : ℝ),
    HasDerivAt (fun u=> meterR (p+u • Detect.spike i) W) (meterR (p+x • Detect.spike i) W') x

namespace AxisDeriv
variable {U V₁ U' V' : V} {i : Axis}

theorem add (h : AxisDeriv i U U') (hg : AxisDeriv i V₁ V') : AxisDeriv i (U+V₁) (U'+V') := by
  intro p x; simp only [map_add]; exact (h p x).add (hg p x)

theorem product (h : AxisDeriv i U U') (hg : AxisDeriv i V₁ V') : AxisDeriv i (U*V₁) (U'*V₁+U*V') := by
  intro p x; simp only [map_add,map_mul]; exact (h p x).mul (hg p x)

theorem scale (h : AxisDeriv i U U') (k : ℝ) : AxisDeriv i (k • U) (k • U') := by
  intro p x; simp only [map_smul]; exact (h p x).const_smul k

theorem sum {I : Type} (f f' : I → V) (s : Finset I) (ht : ∀ j∈s, AxisDeriv i (f j) (f' j)) :
    AxisDeriv i (∑ j∈s,f j) (∑ j∈s, f' j) := by
  intro p x; simp only [map_sum]; exact HasDerivAt.fun_sum fun j hj => ht j hj p x
end AxisDeriv

variable {i : Axis}

theorem deriv_const (x : ℝ) : AxisDeriv i (spring x) 0 := fun _ _=> hasDerivAt_const ..

theorem deriv_petal (i j : Axis) : AxisDeriv i (petal j) (spring (kk i j)) := by
  intro p u; simp_rw [atP,atR,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [show Detect.spike i j=kk i j from ?_]; convert! ((hasDerivAt_id' u).mul_const (kk i j)).const_add (p j) using 1; simp
  by_cases h:i=j <;> simp [kk,h,mt Eq.symm]

theorem deriv_along (p : QP) : AxisDeriv i (alongP p) (spring (p i)) := by
  obtain ht := AxisDeriv.sum (i:=i) _ _ univ (fun j (_ : j∈(univ : Finset Axis)) => (deriv_petal i j).scale (p j))
  simp [kk,smul_ite] at ht
  rw [← Algebra.algebraMap_eq_smul_one] at ht; exact ht

theorem deriv_sqP : AxisDeriv i rsqP ((2:ℝ) • petal i) := by
  obtain ht := AxisDeriv.sum (i:=i) _ _ univ (fun j (_ : j∈(univ : Finset Axis)) => (deriv_petal i j).product (deriv_petal i j))
  simp [kk,ite_mul,mul_ite,sum_add_distrib] at ht
  rw [two_smul]; exact ht

variable {α : ℝ} (h : 0 < α)
set_option quotPrecheck false
local notation "Φ" => Papers.opening mplane (Beam α h)

abbrev gaussS (α : ℝ) : ℝ := (2 * α)⁻¹
local notation "s" => gaussS α

include h

theorem stein {U U' : V} (he : AxisDeriv i U U') : Φ (U*petal i)=s * Φ U' := by
  rw [omitting h U U' i he, gaussS]; field_simp

theorem phi_const (x : ℝ) : Φ (spring x) = x := by
  change Φ (algebraMap ℝ _ x)=x; rw [Algebra.algebraMap_eq_smul_one,map_smul,Papers.starts]
  exact mul_one _

theorem phi_petal (i : Axis) : Φ (petal i)=0 := by simpa using (stein h (i:=i) (deriv_const 1))

theorem phi_pair (i j : Axis) : Φ (petal i*petal j) = s * kk i j := by rw [stein h (deriv_petal j i), phi_const,kk_comm]

theorem phi_sqP : Φ rsqP=4*s := by
  simp [rsqP, phi_pair, show Fintype.card Axis=4 from rfl]

theorem phi_along (p : QP) : Φ (alongP p)=0 := by simp [alongP,phi_petal]

theorem phi_sq_mul_p (i : Axis) : Φ (rsqP*petal i)=0 := by rw [stein h deriv_sqP,map_smul,phi_petal]; simp

theorem phi_along_p (p : QP) (i : Axis) : Φ (alongP p * petal i)=s*p i:= by rw [stein h (deriv_along _),phi_const]

theorem phi_sq_mul_pa (p : QP) : Φ (rsqP*alongP p)=0 := by
  simp [alongP,mul_sum,phi_sq_mul_p]

theorem phi_sq_mul_sq : Φ (rsqP*rsqP)=24*s^2 := by
  have he (i:Axis) : Φ (rsqP* (petal i * petal i))=6*s^2 := by
    rw [ ← mul_assoc,stein h (deriv_sqP.product (deriv_petal i i)),kk_self,show spring 1=1 from map_one (algebraMap ℝ _),
      mul_one,smul_mul_assoc,map_add,map_smul,phi_pair,kk_self,mul_one,phi_sqP]; simp only [smul_eq_mul]; ring
  rw [show rsqP*rsqP = ∑ i:Axis, rsqP* (petal i * petal i) from Finset.mul_sum ..]
  simp [he, show Fintype.card Axis = 4 from rfl]; ring

theorem phi_along_sq (p : QP) : Φ (alongP p * alongP p)=s*p.sq := by
  rw [show alongP p * alongP p = ∑ i:Axis, alongP p * (p i • petal i) from Finset.mul_sum ..]
  simp [phi_along_p,Momentum.sq,pow_two,Finset.mul_sum,mul_left_comm (p _)]
end YM.MS.ScaleForest.SquareShift
