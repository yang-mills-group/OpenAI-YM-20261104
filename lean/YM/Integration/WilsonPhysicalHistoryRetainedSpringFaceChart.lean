import YM.Integration.WilsonPhysicalHistoryRetainedSpringFaceRay
import YM.Integration.WilsonPhysicalHistoryRetainedSpringGaussian
import YM.Integration.WilsonCoherentMayerRootKernel

/-! The normalized four-link Wilson trace has a single finite coordinate chart,
independent of the site and the period. Its bond map preserves repeated visits. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Lattice RG Pressure Pressure.Tube Tree Wilson Finset Work.F03 Bid
open WilsonMeasuredPathTaylor WilsonWalkMatrixSecant
open WilsonCoeffUV WilsonCoeffUV.Blue PhysicalNext.Repeat
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {f : Side}

abbrev FaceSlot (G : Gauge) := Fin 4 × G.ColorIndex

def faceBond (x : Site f) (a : PlaqAxes) : Fin 4→Edge (Site f):=
  let i:=a.val.1
  let j:=a.val.2
  ![(x,i),(x+step i,j),(x+step i+step j-step i,i),(x+step i+step j+(-step i)-step j,j)]

def faceFrame (v : Directions G f) (x : Site f) (a : PlaqAxes) : Lawn (FaceSlot G):=
  fun t=>v (faceBond x a t.1) t.2

def faceColor (G : Gauge) (v : Lawn (FaceSlot G)) (i : Fin 4) : G.Color:=
  colorReader G fun b=>v (i,b)

private theorem face_color_smooth (G : Gauge) (i : Fin 4) :
    ContDiff ℝ ω (fun v : Lawn (FaceSlot G)=>faceColor G v i) :=
  (colorReader G).contDiff.comp (contDiff_pi.mpr fun b=>contDiff_apply ℝ ℝ (i,b))

def faceMatrix (G : Gauge) (v : Lawn (FaceSlot G)) : G.Mat:=
  G.mat (G.lieExp (faceColor G v 0)) * (G.mat (G.lieExp (faceColor G v 1)) *
    (G.mat (G.lieExp (-(faceColor G v 2))) * G.mat (G.lieExp (-(faceColor G v 3)))))

def faceTrace (G : Gauge) (v : Lawn (FaceSlot G)) : ℝ:=normalizedTrace G (faceMatrix G v)

theorem face_trace_smooth (G : Gauge) : ContDiff ℝ ω (faceTrace G):=by
  apply (normalizedTrace G).contDiff.comp
  exact (G.exp_jet.comp (face_color_smooth G 0)).mul ((G.exp_jet.comp (face_color_smooth G 1)).mul
    ((G.exp_jet.comp (face_color_smooth G 2).neg).mul (G.exp_jet.comp (face_color_smooth G 3).neg)))

theorem face_matrix_curve (v : Directions G f) (x : Site f) (a : PlaqAxes) (t : ℝ) :
    curve v x (square a.val.1 a.val.2) t=faceMatrix G (t • faceFrame v x a) := by
  have slot (i : Fin 4) : faceColor G (t • faceFrame v x a) i=t • v (faceBond x a i):=rfl
  simp only [curve,square,travel,Step.pos_read,Step.neg_read,Step.vec_pos,Step.vec_neg,mul_one,
    G.mat_mul,faceMatrix,slot,Work.F03.exp_neg_color,field]
  rfl

def faceRankPrice (G : Gauge) (j : ℕ) : ℝ:=
  ∑ t : Fin j→FaceSlot G, |rye (faceTrace G) j t|

theorem face_rank_nonneg (G : Gauge) (j : ℕ) : 0≤faceRankPrice G j:=
  sum_nonneg fun _ _=>abs_nonneg _

open private linear from YM.Integration.WilsonMeasuredPathTaylor

theorem face_trace_coefficient (v : Directions G f) (x : Site f) (a : PlaqAxes) (j : ℕ) :
    MvPolynomial.eval (faceFrame v x a) (PowerSeries.coeff j (Blue.jet (faceTrace G)))=
      (j.factorial:ℝ)⁻¹*normalizedTrace G (iteratedDeriv j (curve v x (square a.val.1 a.val.2)) 0) := by
  rw [Blue.rayon]
  have h:=PertExtension.Series.Radial.homogeneous_derivative (faceTrace G) (faceFrame v x a) j
    ((face_trace_smooth G).contDiffAt.of_le le_top)
  change _= _ at h
  apply h.trans
  congr 1
  have same : (fun t : ℝ=>faceTrace G (t • faceFrame v x a))=
      (normalizedTrace G) ∘ curve v x (square a.val.1 a.val.2):=by
    funext t
    exact congrArg (normalizedTrace G) (face_matrix_curve v x a t).symm
  rw [same]
  exact linear (normalizedTrace G) (smooth v x (square a.val.1 a.val.2)) j 0

end YM.Integration.OriginalMarkedRunAction
