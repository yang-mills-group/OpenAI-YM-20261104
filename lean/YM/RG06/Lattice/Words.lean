import YM.RG06.Taylor
import YM.Pert.First.ActionVertex -- Work.F03, plaque conventions
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Log-link Feynman rule for finite Wilson stencils

Independent algebraic coefficient recipe (ordered Cauchy products of matrix exponential
coefficients), and its exact identification for real charts on the actual group links. Use on
the cover, the torus, or before restriction to the inversion regulator. Does *not* put complex
fields in G. `t : ℝ` is the log expansion variable: one power for each potential/fluctuation
leg when substituting `rise v t`. h/a spacings and the actual threshold normalization of C's
operators haven't entered yet. Work over ordered walks and positive bonds of YM.Lattice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.WilsonRules
open Lattice Wilson MvPolynomial NormedSpace
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace

variable {G : Gauge} {X : Type*}

abbrev LogBond (X : Type*) := Edge (Four X)
abbrev LogField (G : Gauge) (X : Type*) := Links X G.Color
abbrev Key (G : Gauge) (X : Type*) := LogBond X × G.ColorIndex
abbrev Feynman (G : Gauge) (X : Type*) := MvPolynomial (Key G X) ℂ
abbrev PMat (G : Gauge) (X : Type*) := Matrix (Fin G.repDim) (Fin G.repDim) (Feynman G X)

/-- Expand a determinant/primal stencil only, not a clamped density. The common parameter for
all links and all insertions. -/
def rise (v : LogField G X) (t : ℝ) : Links X G.El := fun e=> G.lieExp (t • v e)

def baseColor (G : Gauge) (i : G.ColorIndex) : G.Color := EuclideanSpace.basisFun _ ℝ i
@[simp] theorem base_inner (v : G.Color) (i : G.ColorIndex) : inner ℝ (baseColor G i) v = v i := by
  rw [baseColor, EuclideanSpace.basisFun_inner]

lemma base_expansion (v : G.Color) : ∑ i, v i • baseColor G i = v := by
  let L:= EuclideanSpace.basisFun G.ColorIndex ℝ
  change ∑ i, v i • L i = v
  simpa only [L,L.repr_apply_apply,EuclideanSpace.basisFun_inner] using L.sum_repr v

def read (v : LogField G X) : Feynman G X →+* ℂ :=
  MvPolynomial.eval fun k=> (↑(v k.1 k.2):ℂ)

def readMat (v : LogField G X) : PMat G X →+* G.Mat := (read v).mapMatrix

@[simp] theorem read_C (v : LogField G X) (z : ℂ) : read v (MvPolynomial.C z) = z := by
  simp [read]
@[simp] theorem read_X (v : LogField G X) (e : LogBond X) (i : G.ColorIndex) :
    read v (MvPolynomial.X (e,i)) = (↑(v e i):ℂ) := MvPolynomial.eval_X _
@[simp] theorem readMat_apply (v : LogField G X) (M : PMat G X) (i j : Fin G.repDim) :
    readMat v M i j = read v (M i j) := rfl

def generator (G : Gauge) {X : Type*} (e : LogBond X) : PMat G X := Matrix.of fun i j=>
  ∑ a : G.ColorIndex, MvPolynomial.X (e,a) * MvPolynomial.C (G.colorMat (baseColor G a) i j)

lemma generator_read (v : LogField G X) (e : LogBond X) :
    readMat v (generator G e) = G.colorMat (v e) := by
  ext1 i j
  rw [readMat_apply]; unfold generator; simp only [Matrix.of_apply, _root_.map_sum,_root_.map_mul,read_C,read_X]
  conv_rhs => rw [← base_expansion (v e)]
  simp only [_root_.map_sum,map_smul,Matrix.sum_apply,Matrix.smul_apply,Complex.real_smul]

/-- Exponential series in the specified (positive-bond) color matrix or its negative, 1/k!
unshifted. One univariate `PowerSeries` indeterminate (g at the step in question); spatial
and color labels belong to the coefficient ring. -/
def kick (G : Gauge) {X : Type*} (e : LogBond X) (back : Bool) : PowerSeries (PMat G X) :=
  PowerSeries.mk fun k=> MvPolynomial.C (σ:=Key G X) ((k.factorial:ℂ)⁻¹) • ((if back then - generator G e else generator G e)^k)

variable [AddCommGroup X] [One X]
/-- Preserve even immediate returns and repeats. Do not abelianize. -/
def ordered (G : Gauge) (x : Four X) : Walk → PowerSeries (PMat G X)
  | [] => 1
  | d::w => kick G (d.used x) d.neg * ordered G (x+d.vec) w

/-- Generic analytic receipt for matrix exponential on a real line. -/
lemma exp_deriv (M : G.Mat) (k : ℕ) : iteratedDeriv k (fun t : ℝ=> NormedSpace.exp (t • M)) =
    (fun t=> NormedSpace.exp (t • M) * M^k) := by
  induction k with
  | zero => ext1 t; simp
  | succ k ih =>
    rw [iteratedDeriv_succ,ih]; ext1 t; rw [pow_succ', ← Matrix.mul_assoc]; exact ((hasDerivAt_exp_smul_const M t).mul_const (M^k)).deriv

lemma exp_smooth (M : G.Mat) : ContDiff ℝ ω (fun t : ℝ=> NormedSpace.exp (t • M)) := by
  have hx : ContDiff ℝ ω (fun x:G.Mat=>NormedSpace.exp x) := (contDiff_iff_contDiffAt.mpr fun x=> (NormedSpace.exp_analytic (𝕂:=ℝ) x).contDiffAt)
  exact hx.comp (f:=fun t:ℝ=> t • M) (contDiff_id.smul contDiff_const)

lemma exp_jet (M : G.Mat) (k : ℕ) : Germ.jet (fun t : ℝ=> NormedSpace.exp (t • M)) k =
    ((k.factorial:ℝ)⁻¹) • M^k := by simp [Germ.jet,exp_deriv]

 omit [AddCommGroup X] [One X] in
private lemma readMat_smul (v : LogField G X) (z : ℂ) (M : PMat G X) :
    readMat v (MvPolynomial.C (σ:=Key G X) z • M) = z • readMat v M := by
  ext1 i j
  simp [Matrix.smul_apply,smul_eq_mul]

private lemma group_path (v : LogField G X) (t : ℝ) (x : Four X) (d : Step) :
    G.mat (d.read (rise v t) x) =
      NormedSpace.exp (t • (if d.neg then - G.colorMat (v (d.used x)) else G.colorMat (v (d.used x)))) := by
  cases hb : d.neg <;> simp [Step.read,rise,hb,G.mat_lieExp,map_smul,← Work.F03.exp_neg_color]

 omit [AddCommGroup X] [One X] in
lemma kick_eval (v : LogField G X) (e : LogBond X) (back : Bool) :
    PowerSeries.map (readMat v) (kick G e back) = Germ.series (fun t : ℝ=>
      NormedSpace.exp (t • (if back then - G.colorMat (v e) else G.colorMat (v e)))) := by
  ext1 k
  rw [PowerSeries.coeff_map,Germ.series_coeff,kick,PowerSeries.coeff_mk, readMat_smul,_root_.map_pow,
    exp_jet]
  ext1 i j
  cases back <;> simp [generator_read, Matrix.smul_apply, Complex.real_smul] -- readMat_apply simp expands!

lemma step_smooth (v : LogField G X) (x : Four X) (d : Step) :
    ContDiff ℝ ω (fun t=> G.mat (d.read (rise v t) x)) := by simp_rw [group_path]; exact exp_smooth _

lemma word_smooth (v : LogField G X) (x : Four X) (s : Walk) :
    ContDiff ℝ ω (fun t=> G.mat (travel (rise v t) x s)) := by
  induction s generalizing x with
  | nil => exact contDiff_const
  | cons d s H =>
    simp only [travel,G.mat_mul]
    exact (step_smooth v x d).mul (H _)

lemma word_eval (v : LogField G X) (x : Four X) (s : Walk) :
    PowerSeries.map (readMat v) (ordered G x s) = Germ.series (fun t=> G.mat (travel (rise v t) x s)) := by
  induction s generalizing x with
  | nil =>
      change PowerSeries.map (readMat v) 1 = Germ.series (fun _=> G.mat 1)
      rw [_root_.map_one, Germ.series_const,G.mat_one,_root_.map_one]
  | cons d s H =>
      rw [ordered, _root_.map_mul,kick_eval,H]
      simp_rw [travel, G.mat_mul, group_path]
      exact (Germ.series_mul ((exp_smooth (G:=G) _).contDiffAt.of_le le_top) ((word_smooth v _ s).contDiffAt.of_le le_top)).symm

end YM.RG06.WilsonRules
