import YM.OPE.Compatible.Weave.Plaid
/-!
# Sign change on Ward legs
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix Tree
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir Stationary
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Pilot Woody Virgin Work.F08 Flume.Page Prairies
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {n c f:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{d k j r w e m:ℕ} {I J:Type} (a:Axis)
def wallV : List Axis→ Cover | []=>0| i::l=> dust a i+wallV l
def roadV (p:Nestle.Pose):Nestle.Pose:=⟨p.m,p.a,p.b,wallV a p.m +dust a p.a+dust a p.b+(Wm a).act p.x⟩
def himp (l:List Axis):ℝ:=∏ k:Fin l.length, φ a (l.get k)
def Rate (p:Nestle.Pose):ℝ:= φ a p.a *φ a p.b * himp a p.m
lemma redoP (x:Ice G n)(p:Reed G)(y: Site n): fence p y (flo a x)= Rate a p.1 * fence ((roadV a p.1,p.2):Reed G) (dart a y) x:=by
    rw [fee, fee]; simp_rw [F_leg]; let i:=p.1.a; let j:= p.1.b; let f(i:Axis)(v:Site n):=x (v,i,p.2); let g(i:Axis)(v):=φ a i*f i ((Wm a).act v+dust a i); let c:=φ a i*φ a j; let G':=fwd i (f j)-fwd j (f i); let O(a' b:Axis):= dust a a'+dust (R:=Per n) a b
    have he (i' j':Axis)(p:Site n): fwd i' (g j') p= (φ a i'* φ a j')*fwd i' (f j') ((Wm a).act p+ O i' j'):=by
         unfold fwd g; rw [norm_step]; unfold O dust φ; by_cases h:i'=a<;> by_cases H:j'=a<;>simp only [h,H,ite_true,ite_false,zero_add, add_zero,neg_one_mul,one_mul,mul_neg,neg_neg] <;>abel_nf
    have hG(v: Site n): (fwd i (g j)-fwd j (g i)) v=c*G' ((Wm a).act v+O i j):=by rw [Pi.sub_apply,he,he]; unfold c G'; rw [show O j i= O i j from add_comm .., mul_comm (φ a j),Pi.sub_apply,mul_sub] -- occ
    have ht(l:List Axis)(v:Site n): Knot l (fwd i (g j) -fwd j (g i)) v=c*himp a l * Knot l G' ((Wm a).act v +O i j+wrap _ (wallV a l)):=by
        induction l generalizing v with
        | nil=> simp only[Knot,List.foldr_nil,himp, List.length_nil, Fin.prod_univ_zero,mul_one,wallV,map_zero,add_zero,hG] -- need sum
        | cons b l ih=> change Knot l _ _-Knot l _ _= c*himp _ _*(Knot l _ _-Knot l _ _); rw [ih,ih,norm_step, show himp a (b::l)= φ a b*himp a l from Fin.prod_univ_succ ..]; rw [show wallV a (b::l)=dust a b+wallV a l from rfl,map_add]; unfold φ dust; by_cases h:b=a<;> simp only [h,ite_true,ite_false,zero_add,map_zero,map_neg,wrap_step] <;> abel_nf <;> ring_nf -- abel inside? 
    change tip p.1 g y=c*himp a p.1.m*tip (roadV a p.1) f (dart a y); unfold tip; rw [ht]; congr 2; unfold i j O roadV; rw [Signed.act_add]; simp only [wrap_signed,map_add]; simp_rw [fog_m (n:=n)];abel
lemma manners (p:Nestle.Pose): Rate a p*Rate a p=1:=by
    have h : himp a p.m * himp a p.m=1:=by unfold himp; rw [← Finset.prod_mul_distrib]; apply Finset.prod_eq_one; intro i _; unfold φ; split<;>ring
    change _*_= _; unfold Rate φ at *; split_ifs <;>simp_all
lemma kin_flip (p q:Reed G)(y: Site n)(M:KernelChoices)(h:4≤r): evenCov r M n y p q= Rate a p.1 * Rate a q.1 * evenCov r M n (dart a y) ((roadV a p.1,p.2):Reed G) (roadV a q.1,q.2):=by
     unfold evenCov; conv_lhs=> rw [← score_flo a _ _ M h]
     let P:= Rate a p.1; let V:= (roadV a p.1,p.2); have hp(p:Reed G): fence p y ∘ₗ (flo a).toLinearMap= Rate a p.1 • fence ((roadV a p.1,p.2):Reed G) (dart a y):=LinearMap.ext (fun x=>redoP ..); rw [hp,hp]; unfold ProbeCov; simp only [LinearMap.smul_apply,smul_eq_mul,Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> by ring
include L in
lemma firmQ (p q:Reed G): firm p q= Rate a p.1 * Rate a q.1 * firm ((roadV a p.1,p.2):Reed G) (roadV a q.1,q.2):=by
      let X:= twin (2:Side); let hN(i:ℕ):Even (X.M i).val:= (show Even (2:Side).val from ⟨1,rfl⟩).mul_right _; have hp(p q:Reed G)(u:(i:ℕ)→Site (X.M i)):=barometer (L:=L) p q X.M u X.sides (Eventually.of_forall hN) (show 4≤4 from le_rfl)
      apply tendsto_nhds_unique (hp p q (fun _=>0)); simp_rw [kin_flip a p q (M:=L) (h:= (le_refl 4))]; apply Tendsto.const_mul; exact hp ..
end YM.OPE.Quit
