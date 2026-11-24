import YM.RG11Proof.Neighborhood.Lens
/-!
# Exact correlated front, supplementary back row, formal transport

Replacement output uses all through h. Electronics in the horizon max.
Also any such replacement operators linear in kernels (contact residual
if any not included). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Neighborhood
open scoped Classical ContDiff BigOperators Topology
open Set Filter MeasureTheory Labels Maxwell
open PowerSeries YM.RG11.Fields YM.RG11.Grove YM.RG11.Stress YM.RG11.Jets YM.RG11.Nodes
variable {G:Gauge} {F:Frames G}{n m i H:ℕ}

-- in fixed subtraction length, u=log(1/r). No scale-law of actual coupling implied.
def frontRow (A:ShapeReport G F)(k d:ℕ)(x:Design n)(y:Tail m)(s:ℝ):=
   link A k d (x.taps (Real.exp (-s)) y)

/-- Replacement on a single output (through H), at center c. -/
def rear (A:ShapeReport G F)(H d:ℕ)(p:leverage (1+m)): Rect (lab F H) (sheaf F m d) (PowerSeries ℂ):=
   (link A H d p).submatrix (fun i (_:Fin 1)=> i) id

def close (y:Tail m):Points (1+m):=coupled (points (fun _:Fin 1=>y.c)) y.y

def backRow (A:ShapeReport G F)(H d:ℕ)(y:Tail m):= rear A H d (here (close y))

variable {A B:ShapeReport G F}{T:Window.AxisData A}{M:Window.AxisData B}{Z:∀ d,Window.SquareAt F d}{p:PowerSeries ℝ}
variable (h:Window.Direction A T B M p Z)
include h
 theorem rear_linked {m : ℕ}(H j:ℕ)(q:leverage (1+m))(N:ℕ): MatThrough N (rear B H j q) (rug (Jets.deposit p) (plank (Z H)) (rear A H j q) (Matrix.transpose (castNet (Z j) m))):=by
   intro i e; apply Through.trans (Matrices.linked A B h H j q N (fun _:Fin 1=>i) e)
   unfold rug; simp_rw [Matrix.mul_apply]
   have he (v:sheaf F m j) : (∑ a:sheaf F 1 H, castNet (Z H) _ (fun _:Fin 1=>i) a * subs (Jets.deposit p) (link A H j q) a v)= ∑ a:lab F H,plank (Z H) i a * subs (Jets.deposit p) (rear A H j q) a v:= by
     let g:sheaf F 1 H≃lab F H:=Equiv.funUnique (Fin 1) (lab F H)
     refine Fintype.sum_equiv g _ _ (fun x=>?_)
     have hv:x=(fun _=>x 0):=funext fun i=>by rw [@Subsingleton.elim (Fin 1) _ i 0]
     conv_lhs=> rw [hv]
     change _ = plank _ i (x 0) * _
     simp only [castNet,cluster,Matrix.of_apply,cross,Fin.prod_univ_one]
     congr 1
   simp_rw [he]; exact Through.refl _

-- Output coefficients C_M = C_X(T) precomposed D on inputs and apply D^-1 to output. Keep neg orientation.
def fieldInv {H:ℕ}(Z:Square (lab F H) (PowerSeries ℝ)):=squareInv (plank Z)

end YM.RG11.Neighborhood
