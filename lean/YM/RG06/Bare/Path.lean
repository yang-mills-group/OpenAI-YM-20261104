import YM.RG06.Bare.Calculus
import YM.UVExt.PathJet
import YM.Pert.Lattice.Plate
/-!
# Explicit all-order fluctuation Feynman rule for paths and plates

Ordered matrix products, ℝ Taylor parameter (t link coupling), skew projection
on a plaquette based at the STOP, transported by path x to stop before output.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Rules
open Function Filter CubicMatch Lattice
open scoped Matrix.Norms.Frobenius ContDiff Topology BigOperators InnerProductSpace
variable {G : Gauge}{X : Type*}[AddCommGroup X][One X]

def expRay {X : Type*} (v : Links X G.Color) (t : ℝ) : Links X G.El := fun e=> G.lieExp (t • v e)

def signed (d : Step) (x : Four X) (v : Links X G.Color) := if d.neg then -v (d.used x) else v (d.used x)

theorem read_ray (d : Step) (x : Four X) (v : Links X G.Color) (t : ℝ) :
    d.read (expRay v t) x = G.lieExp (t • signed d x v) := by
  unfold Step.read signed; split
  · rw [smul_neg,Work.F03.exp_neg_color]; rfl
  rfl

def exponential (v : G.Color) (k : ℕ) : G.Mat := (k.factorial:ℝ)⁻¹ • (G.colorMat v)^k

theorem exponential_exact (v : G.Color) : HasCoefficients (fun t:ℝ=>G.mat (G.lieExp (t • v))) (exponential v) := by
  refine ⟨(G.exp_jet.comp (contDiff_id.smul contDiff_const)).contDiffAt,fun k=>?_⟩
  unfold CubicMatch.term
  change (k.factorial:ℝ)⁻¹ • iteratedDeriv k (fun t:ℝ=>G.mat (G.lieExp (t • v))) 0 = _
  rw [UVExt.Paths.ray_deriv v]
  simp [exponential]

/-- Finite recursion needs only input through order k. Path length is list length,
not endpoint displacement. -/
def travelCoeff (v : Links X G.Color) (x : Four X) : Walk → ℕ → G.Mat
  | [] => C 1
  | d::w => times (exponential (signed d x v)) (travelCoeff v (x+d.vec) w)

variable (v : Links X G.Color) (x : Four X) (w : Walk)

theorem travel_exact : HasCoefficients
    (fun t=> G.mat (travel (expRay v t) x w)) (travelCoeff v x w) := by
  induction w generalizing x with
  | nil => simpa only [G.mat_one,travel,travelCoeff] using HasCoefficients.constant (1:G.Mat)
  | cons d s ih =>
    simp_rw [travel,travelCoeff,G.mat_mul,read_ray]
    apply (exponential_exact _).mul (ih _)

private lemma flat_path {K : Type*}[Group K] (u : Walk) (y : Four X) : travel (1 : Links X K) y u=1 := by
  induction u generalizing y with
  | nil=>rfl
  | cons d s ih=>simp [travel,ih,Step.read]

private lemma flat_exp {X : Type*}(A : Links X G.Color) : expRay A 0 = 1 := by
  funext e; change G.lieExp _ = 1; apply G.mat_injective; simp

@[simp] theorem travel_zero : travelCoeff v x w 0 = 1 := by
  rw [← (travel_exact v x w).head, flat_exp,flat_path,G.mat_one]

/-- Compatibly with `Rep` definition, recover the skew part's color, and use exact
conjugation for transport. -/
def skewColor (M : G.Mat) := G.projectColor ((1/2 : ℝ) • (M - star M))

def holColor (v : Links X G.Color) (x : Four X) (w : Walk) (k : ℕ) : G.Color :=
  skewColor (travelCoeff v x w k)

def plate (v : Links X G.Color) (x : Four X) (w : Walk) (a b : Axis) (k : ℕ) : G.Color :=
  G.projectColor (times
    (times (travelCoeff v x w)
      (fun i=> G.colorMat (holColor v (stop x w) (square a b) i)))
    (fun i=> star (travelCoeff v x w i)) k)

lemma curvature_skew (g : G.El) : G.curvature g = skewColor (G.mat g) := by unfold Gauge.curvature skewColor; rw [G.mat_inv]

lemma starMat {p:ℝ→G.Mat}{c:ℕ→G.Mat} (h:HasCoefficients p c) : HasCoefficients (fun x=> star (p x)) (fun i=> star (c i)) :=
  HasCoefficients.linear ((starL ℝ : G.Mat ≃L[ℝ] G.Mat).toContinuousLinearMap) h

theorem curvature_exact : HasCoefficients
    (fun t=> G.curvature (travel (expRay v t) x w)) (holColor v x w) := by
  simp_rw [curvature_skew]; unfold holColor skewColor
  let p (t:ℝ) := G.mat (travel (expRay v t) x w)
  have ht : HasCoefficients p (travelCoeff v x w) := travel_exact v x w
  exact HasCoefficients.linear G.projectColor.toContinuousLinearMap ((ht.sub (starMat ht)).smul _)

lemma transport (g : G.El) (c : G.Color) : G.adjoint g c = G.projectColor (G.mat g*G.colorMat c*star (G.mat g)) := rfl

theorem plate_exact (a b : Axis) : HasCoefficients
    (fun t=> Pert.Bare.plateU (expRay v t) x w a b) (plate v x w a b) := by
  unfold Pert.Bare.plateU; simp_rw [transport]; unfold plate
  let p (t:ℝ) := G.mat (travel (expRay v t) x w)
  have ht : HasCoefficients p (travelCoeff v x w) := travel_exact v x w
  have hf := HasCoefficients.linear G.colorMat.toContinuousLinearMap (curvature_exact v (stop x w) (square a b))
  exact HasCoefficients.linear G.projectColor.toContinuousLinearMap ((ht.mul hf).mul (starMat ht))

@[simp] theorem plate_zero (a b : Axis) : plate v x w a b 0 = 0 := by
  rw [← (plate_exact v x w a b).head]
  simp [Pert.Bare.plateU,flat_exp,flat_path]

/-! Leading open slot check on the same RAW INTERIOR paths (arbitrary input
array, not assuming translation invariance or transverse). -/
lemma exponential_one (z : G.Color) : exponential z 1 = G.colorMat z := by simp [exponential]
@[simp] lemma exponential_zero (z : G.Color) : exponential z 0=1 := by simp [exponential]

lemma times_one {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] (p q : ℕ→E) : times p q 1 = p 0*q 1 + p 1*q 0 := by simp [times,Finset.sum_range_succ]
lemma times_zero {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] (p q : ℕ→E) : times p q 0 = p 0*q 0 := by simp [times]

def linPath (v : Links X G.Color) (x : Four X) : Walk → G.Color
  | [] => 0
  | d::w => signed d x v + linPath v (x+d.vec) w

@[simp] theorem travel_one : travelCoeff v x w 1 = G.colorMat (linPath v x w) := by
  induction w generalizing x with
  | nil=>simp [travelCoeff,C,linPath]
  | cons d s ih => simp [travelCoeff,linPath,times_one,ih,exponential_one,add_comm]

@[simp] lemma holColor_zero : holColor v x w 0 = 0 := by simp [holColor,skewColor]
@[simp] lemma holColor_one : holColor v x w 1 = linPath v x w := by
  unfold holColor skewColor; rw [travel_one,G.colorMat_skew,sub_neg_eq_add,← two_smul ℝ,smul_smul]
  norm_num

theorem plate_one (a b : Axis) : plate v x w a b 1 = linPath v (stop x w) (square a b) := by
  simp [plate,times_one,times_zero]

-- orientation check
lemma square_lead (a b:Axis) : linPath v x (square a b) =
    v (x,a)+v (x+step a,b) - v (x,b)-v (x+step b,a) := by
  have ha : x+step a+step b-step a=x+step b:=by abel
  unfold square; simp [linPath,signed,Step.used,ha,posDir,negDir,Step.vec,← sub_eq_add_neg]; abel
end YM.RG06.Rules
