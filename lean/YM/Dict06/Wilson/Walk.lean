import YM.Dict06.Series.Germ
import YM.Gauge.Curvature
import YM.Exterior.Complex

/-! Coupling-rescaled Wilson link germ, positive orientation source links,
with actual word order in the chosen representation. Works on the cover and
periods. No regulator choice involving a gauge slice or fermions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Dict06.Wil
open Lattice PowerSeries Function Series
open scoped Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {X : Type*} [AddCommGroup X] [One X]

-- Amplitude A independent of g, link *integrated* convention. No factor
-- of representation dimension in the exponential: colorMat includes it.
def positive (A : Links X G.Color) (g : ℝ) : Links X G.El := fun e => G.lieExp (g • A e)
private lemma flat_link {G : Gauge} : G.lieExp 0=1 := G.mat_lieExp_zero
omit [AddCommGroup X] [One X] in
@[simp] lemma positive_zero (A : Links X G.Color) : positive A 0 = 1 := funext fun e=> by
    change G.lieExp _=1; rw [zero_smul,flat_link]

/-- Signed component, FROM the current site even on negative steps. -/
def oriented (A : Links X G.Color) (x : Four X) (d : Step) :=
  if d.neg then -A (d.used x) else A (d.used x)

lemma oriented_exp (A : Links X G.Color) (t x d) :
    G.mat (Step.read d (positive A t) x) = NormedSpace.exp (t • G.colorMat (oriented A x d)) := by
  unfold Step.read oriented positive; cases d.neg
  · simp
  simp only [↓reduceIte,G.mat_inv,G.mat_lieExp, map_neg, map_smul, smul_neg]
  -- star_exp? 
  haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
  rw [NormedSpace.star_exp]; simp [star_smul,G.colorMat_skew]

/-- Taylor series before factor/slot powers have been removed. -/
def linkSeries (A : Links X G.Color) (x : Four X) (d : Step) : PowerSeries G.Mat :=
  PowerSeries.mk fun n => (n.factorial:ℝ)⁻¹ • (G.colorMat (oriented A x d))^n
@[simp] lemma link_at (A : Links X G.Color) (x : Four X) (d : Step) (n : ℕ) :
    coeff n (linkSeries A x d) = (n.factorial:ℝ)⁻¹ • (G.colorMat (oriented A x d))^n := coeff_mk ..
lemma honest_link (A : Links X G.Color) (x : Four X) (d : Step) :
    ContDiff ℝ ∞ (fun t=>G.mat (d.read (positive A t) x)) ∧
      ps (fun t=>G.mat (d.read (positive A t) x))=linkSeries A x d := by
  simp_rw [oriented_exp]
  exact ⟨(G.contDiff_exp.of_le le_top).comp (f:=fun t:ℝ=>t • _) (contDiff_id.smul contDiff_const), exponential _⟩

def path (A : Links X G.Color) (x : Four X) : Walk → PowerSeries G.Mat
  | [] => 1
  | d::w => linkSeries A x d * path A (x+d.vec) w

lemma honest_walk (A : Links X G.Color) (x : Four X) (w : Walk) :
    ContDiff ℝ ∞ (fun t => G.mat (travel (positive A t) x w)) ∧
      ps (fun t => G.mat (travel (positive A t) x w)) = path A x w := by
  induction w generalizing x with
  | nil =>
    simp only [travel,path,G.mat_one]; exact ⟨contDiff_const,ps_one⟩ -- defeq const fn =1
  | cons d w ih=>
    obtain ⟨hf,h⟩:=honest_link A x d
    obtain ⟨hg,e⟩:=ih (x+d.vec)
    simp_rw [travel,G.mat_mul,path]
    exact ⟨hf.mul hg,(ps_mul _ _ hf.contDiffAt hg.contDiffAt).trans (congrArg₂ (· * ·) h e)⟩

/-- Multiplication coefficients at one for matrices, no commutation. -/
private lemma prod_one (f g : PowerSeries G.Mat) :
    coeff 1 (f*g) = coeff 1 f * coeff 0 g + coeff 0 f * coeff 1 g := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i f*coeff j g)]
  simp [Finset.sum_range_succ,add_comm]

lemma path_first (A : Links X G.Color) (x : Four X) (w : Walk) :
    coeff 0 (path A x w)=1 ∧ coeff 1 (path A x w) = G.colorMat (Exterior.linkSum A x w) := by
  induction w generalizing x with
  | nil => simp [Exterior.linkSum,path]
  | cons d w ih=>
    obtain ⟨ha,hb⟩:=ih (x+d.vec)
    have e0 : coeff 0 (linkSeries A x d) = 1 := by rw [link_at]; simp
    have e1 : coeff 1 (linkSeries A x d) = G.colorMat (oriented A x d) := by rw [link_at]; simp
    constructor
    · simp only [path,coeff_mul]; rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i _ * coeff j _)]
      simp [ha]
    · rw [path,prod_one,e0,e1,ha,hb,mul_one,one_mul,Exterior.linkSum,map_add]; rfl

end YM.Dict06.Wil
