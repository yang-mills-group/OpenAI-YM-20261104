import YM.OPE.Compatible.Melon.Bends
import YM.OPE.Compatible.Tides.Vivid
import YM.Pert.Lattice.Action
/-!
# Wilson face cubic. Vertex legs antisym at zero. Pure tree pole
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Stubble
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Wilson Exterior Maxwell Cascade PertExtension Series Score Next.Foundations
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
attribute [local instance] Gauge.frobInner
variable {n:Side}{G:Gauge}
abbrev Tile (G:Gauge):= Fin 4→G.Color
def mace (p:Tile G):G.El:= G.lieExp (p 0)*G.lieExp (p 1)*(G.lieExp (p 2))⁻¹*(G.lieExp (p 3))⁻¹
def maceX (p:Tile G):G.Mat:=G.mat (mace p)-1
def Wj (p:Tile G):G.Color:=p 0+p 1-p 2-p 3
lemma sheet : ContDiff ℝ ω (maceX (G:=G)):=by
   have he(i:Fin 4):ContDiff ℝ ω (fun p:Tile G=> G.mat (G.lieExp (p i))):= G.exp_jet.comp (show ContDiff ℝ ω (fun p:Tile G=>p i) from contDiff_pi.mp contDiff_id i)
   have hh(i:Fin 4):ContDiff ℝ ω (fun p:Tile G=> G.mat (G.lieExp (p i))⁻¹):=(show G.Mat≃L[ℝ]G.Mat from starL ℝ).contDiff.comp (he i)
   unfold maceX mace; simp only [G.mat_mul]; exact ((((he 0).mul (he 1)).mul (hh 2)).mul (hh 3)).sub contDiff_const
lemma seamW :maceX (0:Tile G)=0:=by simp [maceX,mace]
lemma wick0 (p:Tile G):deriv (fun x:ℝ=> maceX (x • p)) 0=G.colorMat (Wj p):=by
    have ht(i:Fin 4):HasDerivAt (fun x:ℝ=> G.mat (G.lieExp (x • p i))⁻¹) (-G.colorMat (p i)) 0:= G.colorMat_skew _ ▸ (Pert.Orb.line_diff _).star
    have he:=((((Pert.Orb.line_diff (p 0)).mul (Pert.Orb.line_diff (p 1))).mul (ht 2)).mul (ht 3)).sub_const (1:G.Mat); have hx:=he.deriv; simp only [maceX,mace,Pi.smul_apply,G.mat_mul]; erw [hx]
    unfold Wj; simp only [zero_smul,G.mat_lieExp_zero, inv_one,G.mat_one, Pi.mul_apply,mul_one,one_mul,map_sub,map_add]; abel
section py
variable {E F X: Type*} [NormedAddCommGroup E][NormedAddCommGroup F][NormedAddCommGroup X] [NormedSpace ℝ E] [NormedSpace ℝ F][NormedSpace ℝ X]{f:ℝ→E}{g:ℝ→F}{L:E→L[ℝ] F→L[ℝ] X}
abbrev cat (L:E→L[ℝ] F→L[ℝ] X)(f:ℝ→E)(g:ℝ→F)(x:ℝ):=L (f x) (g x)
lemma sat (L:E→L[ℝ] F→L[ℝ] X)(hf:ContDiff ℝ ω f)(hg:ContDiff ℝ ω g):ContDiff ℝ ω (cat L f g) :=(L.contDiff.comp hf).clm_apply hg
lemma cosmic (L:E→L[ℝ] F→L[ℝ] X)(hf:ContDiff ℝ ω f)(hg:ContDiff ℝ ω g): deriv (cat L f g)=cat L f (deriv g)+cat L (deriv f) g:=by
    funext x; have ht:= L.hasFDerivAt.comp_hasDerivAt x (hf.differentiable (by simp) x|>.hasDerivAt); change _= cat L f (deriv g) x + cat L (deriv f) g x; rw [add_comm]; exact (ht.clm_apply (hg.differentiable (by simp) x|>.hasDerivAt)).deriv
lemma moon (hf:ContDiff ℝ ω f):ContDiff ℝ ω (deriv f):=ContDiff.deriv' (by simp; exact hf)
lemma ast (L:E→L[ℝ] F→L[ℝ] X)(hf:ContDiff ℝ ω f)(hg:ContDiff ℝ ω g): deriv (deriv (cat L f g))= (cat L f (deriv (deriv g))+cat L (deriv f) (deriv g))+(cat L (deriv f) (deriv g)+cat L (deriv (deriv f)) g):=by
   rw [cosmic _ hf hg]; rw [show deriv (_+_) = deriv (cat L f (deriv g))+deriv (cat L (deriv f) g) from funext fun y=> deriv_add (sat _ hf (moon hg)|>.differentiable (by simp) y) (sat _ (moon hf) hg|>.differentiable (by simp) y)]; rw [cosmic _ hf (moon hg),cosmic _ (moon hf) hg]
lemma blitz (L:E→L[ℝ] F→L[ℝ] X)(hf:ContDiff ℝ ω f)(hg:ContDiff ℝ ω g)(ht:f 0=0)(hu:g 0=0): iteratedDeriv 3 (cat L f g) 0=3 • (L (iteratedDeriv 2 f 0) (deriv g 0)+L (deriv f 0) (iteratedDeriv 2 g 0)):=by
   have hl:= hf
   simp_rw [show (3:ℕ)=2+1 from rfl,iteratedDeriv_succ (n:=2), show iteratedDeriv 2 f= _ from iteratedDeriv_succ (n:=1), show iteratedDeriv 2 g=_ from iteratedDeriv_succ (n:=1), show iteratedDeriv 2 (cat L f g)=_ from iteratedDeriv_succ (n:=1),iteratedDeriv_one]
   rw [ast _ hf hg]; let H:=cat L f (deriv (deriv g)); let I:=cat L (deriv f) (deriv g); let J:=cat L (deriv (deriv f)) g; have hh:=sat L hf (moon (moon hg)); have he:=sat L (moon hf) (moon hg); have hz:=sat L (moon (moon hf)) hg; change deriv ((H+I)+(I+J)) 0=_; have hA:DifferentiableAt ℝ H 0:=hh.differentiable (by simp) 0; have hB:DifferentiableAt ℝ I 0:=he.differentiable (by simp) 0; have hC:DifferentiableAt ℝ J 0:=hz.differentiable (by simp) 0; rw [deriv_add (hA.add hB) (hB.add hC),deriv_add hA hB,deriv_add hB hC]; unfold H I J; simp_rw [cosmic _ hf (moon (moon hg)), cosmic _ (moon hf) (moon hg),cosmic _ (moon (moon hf)) hg]; simp only [cat,Pi.add_apply,ht,hu,map_zero,zero_apply]; abel
end py
end YM.OPE.Stubble
