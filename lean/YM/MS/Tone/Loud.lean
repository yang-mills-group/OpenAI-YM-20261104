import YM.MS.Tone.Attaches
import YM.Work.F03.Transport
import YM.Work.F03.Calculus
import YM.Work.F03.Metric
/-!
# S-two actually from plaquette

Compute curvature norm and analytic at port. Complex adjoint etc.

-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tone.Frame
open Function Filter Set Finset Koszul Cylinder Lab Taylor Lattice Native Bare Focus Landau Momentum Orient Draft Sew Native.Chart
open scoped Topology ContDiff InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}
abbrev Thread := Lot G Axis
def curve : Thread (G:=G) →L[ℝ] G.Color:= let T: Axis→ Thread (G:=G) →L[ℝ] G.Color:= fun i=> ContinuousLinearMap.proj i; T 0 +T 1-T 2-T 3
lemma curves (a:Lot G Axis): curve a=a 0+a 1-a 2-a 3:= rfl

def lime (a: Thread (G:=G))(t:ℝ):=atCart (G.lieExp ∘(t • a))
@[simp] lemma lime0 (a: Thread (G:=G)): lime a 0=1:= by simp [lime,atCart]
lemma limeD (a:Thread (G:=G)): HasDerivAt (G.mat ∘ lime a) (G.colorMat (curve a)) 0:= by
   let V i t := G.lieExp ((t:ℝ) • a i); let f i:=G.mat ∘ V i; let g i:=G.mat ∘ fun t=> (V i t)⁻¹
   have he i : HasDerivAt (f i) (G.colorMat (a i)) 0:= Maurer.colorDerivative _
   have hv i : HasDerivAt (g i) (-G.colorMat (a i)) 0:= by
      have hp:= (he i).star; rw [G.colorMat_skew] at hp; exact hp
   convert! (((he 0).mul (he 1)).mul (hv 2)|>.mul (hv 3)) using 1
   simp [curves,f,g,V]; abel

lemma bended (p q: Thread (G:=G)): iteratedFDeriv ℝ 2 gone 0 ![p,q]= -⟪curve p,curve q⟫_ℝ:= by
   have ht s := Work.F03.price_limit (lime0 (G:=G) s) (limeD s)
   have he := Work.F03.hessian_of_limit (f:=gone) (E:=Lot G Axis) (bill_gone.of_le le_top) (Q:=fun p q=> - inner ℝ (curve p) (curve q)) ?lim ?add ?sym
   case lim=> intro s; simpa [lime,gone,real_inner_self_eq_norm_sq,neg_div] using (ht s).neg
   case add=> intro a b c; simp [inner_add_left]; rw [add_comm]
   case sym=> intro a b; rw [real_inner_comm]
   exact he.2.2 ..
lemma rank2_port (i j:Axis×Conn G): ink priv gone [i,j]= -( (∑ k, curve (priv i) k * curve (priv j) k: ℝ):ℂ ) := by
    let f:= gone (G:=G); have he : germ f:= bill_gone
    let a:= priv i; let b:=priv j
    change ((layer b (layer a f) 0:ℝ):ℂ)=_
    have hL : layer b (layer a f) 0= iteratedFDeriv ℝ 2 f 0 ![b,a]:= by
       unfold layer; rw [((he.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)|>.hasFDerivAt.clm_apply (hasFDerivAt_const a _) |>.fderiv)]; simp [iteratedFDeriv_two_apply]
    rw [hL, show iteratedFDeriv ℝ 2 f 0 _= _ from bended b a, real_inner_comm,Work.F03.inner_color]; push_cast; rfl
end YM.MS.Tone.Frame
