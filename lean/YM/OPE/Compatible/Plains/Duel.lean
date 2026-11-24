import YM.OPE.Compatible.Plains.Moan
import YM.Pert.Align.Nesting
/-!
# Leading finite Wick polynomial. transport H⊆...
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prairies
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Flume Flume.Script Flock StageLight Balsam Nestle Pert.Full
open Silt Silt.Float Shell Char FreeResolvent Paver Rill Saga Shrew
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {N:Side}{G:Gauge}{L:RG.KernelChoices}{P:ChartRatio G}{U:Gloam}{d k j r w e m:ℕ}{I:Type}[Fintype I] {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
-- lattice sharp
local notation "AX"=> Axis
def slideW (l:List AX):Cover:= (l.map step).sum
lemma Knot_fit (x y:Site N)(P a:List AX): Knot a (fun y=> mildX P (x-y)) y=(-1:ℝ)^a.length * mildX (a++P) (x-y-wrap _ (slideW a)):=by
      induction a generalizing y with
      | nil=>simp [Knot,slideW]
      | cons i l ih=>
        change Knot l _ _- Knot l _ _ = _; rw [ih,ih]; rw [show x-(y+step i)-wrap _ (slideW l)=x-y-wrap _ (slideW (i::l)) from ?_,List.length_cons,pow_succ,List.cons_append,mild_more]; swap; · simp only [slideW,List.map_cons,List.sum_cons,map_add,wrap_step]; abel
        rw [show x-y-wrap _ (slideW (i::l))+step i=x-y-wrap _ (slideW l) from ?_]; ring; simp only [slideW,List.map_cons,List.sum_cons,map_add,wrap_step]; abel
lemma Knot_energy (p:Nestle.Pose)(a:AX)(z x:Site N)(l:List AX): Knot l (paper p a z) x= (-1:ℝ)^l.length*p.Lck (fun i=> mildX (l++(i::p.m)) (z+wrap _ p.x-x-wrap _ (slideW l))) a:=by
      unfold paper Pose.Lck; rw [show (fun y:Site N=>_)= (if a=p.b then (fun y:Site N=>mildX (p.a::p.m) ((z+wrap _ p.x)-y)) else 0)-(if a=p.a then fun y:Site N=> mildX (p.b::p.m) ((z+wrap _ p.x)-y) else 0) from ?_, cork_sub];swap; · funext y; rw [sub_add_eq_add_sub]; split_ifs <;>rfl
      split_ifs <;> simp only [Knot_fit,zeroKn,Pi.zero_apply,sub_zero,zero_sub, mul_zero,mul_neg,mul_sub]
abbrev mission (p q:Nestle.Pose)(F: List AX→Cover→ℝ)(l:List AX)(a:AX) := (-1:ℝ)^l.length*p.Lck (fun i=>F (l++(i::p.m)) (p.x-q.x-slideW l)) a
def Wind (p q:Nestle.Pose)(F:List Axis→Cover→ℝ):= mission p q F (q.a::q.m) q.b-mission p q F (q.b::q.m) q.a
lemma forecast (p q:Nestle.Pose)(x y:Site N): tip q (fun i=>paper p i x) y= Wind p q fun D a=> mildX D (x-y+wrap _ a):=by
     unfold tip; rw [cork_sub,Knot_f,Knot_f,Knot_energy,Knot_energy]; unfold Wind mission Pose.Lck; simp_rw [map_sub]; rw [show ∀ (a:Site N),x+wrap N p.x-(y+wrap N q.x)-a=x-y+(wrap N p.x-wrap N q.x-a) from ?_] -- rw one
     · rw [show ∀ (a:Site N),x+wrap N p.x-(y+wrap N q.x)-a=x-y+(wrap N p.x-wrap N q.x-a) from fun i=>by abel]
     intro i; abel
open Maxwell Maxwell.Free Pert.Nesting Next.Rank.Radian -- overload
lemma Kw_leg (x y:E4)(p q:Reed G)(h:x≠y): Maxwell.Free.K (rayLeg p) (rayLeg q) x y= if p.2=q.2 then Wind p.1 q.1 (fun l _=>dV l Maxwell.Green (x-y)) else 0:=by
    have hv:= reads_mixed (basis ∘ p.1.m.get) (basis ∘ q.1.m.get) p.1.a p.1.b q.1.a q.1.b p.2 q.2 h
    let hx:= sub_ne_zero.mpr h; rw [K_pairing _ _ h]; unfold rayLeg; rw [map_smul,map_smul,LinearMap.smul_apply, show pairing (show x-y∈Maxwell.away from hx) (Maxwell.Free.leg (fun i=>basis (p.1.m.get i)) _ _ _) (Maxwell.Free.leg (fun i=>basis (q.1.m.get i)) _ _ _) =_ from hv]; simp only [smul_eq_mul]; split_ifs
    swap; · rw [mul_zero,mul_zero]
    let M:= p.1.m; let T:=q.1.m; let P:= bareCurl p.1.a p.1.b q.1.a q.1.b
    let l:=M.get; let u:=T.get; let V(w:E4):=Tensor.coeff P M.length w (basis ∘ M.get); have hV: (fun y=>Tensor.coeff (fun x=>P (x-y)) p.1.m.length x (basis∘p.1.m.get))=fun y=> V (x-y):=by funext y; unfold Tensor.coeff V Tensor.coeff; rw [iteratedFDeriv_comp_sub] -- name
    have hp:ContDiffAt ℝ ∞ P (x-y):=clean_chart _ _ _ _ _ hx
    have he: Tensor.coeff (fun y=> V (x-y)) T.length y= (-1:ℝ)^T.length • Tensor.coeff V T.length (x-y):=by
        apply Tensor.oppositeCoeff; exact ((((ContinuousMultilinearMap.apply ℝ (fun _ : Fin M.length=> E4) ℝ (basis ∘ l)).contDiff.contDiffAt.comp (x-y)
                  (Tensor.coeff_smooth hp M.length))).of_le (WithTop.coe_le_coe.mpr le_top))
    have ht(a b:Axis): Pert.Nesting.tagged (M++[a]) (T++[b]) (x-y)= dV ((b::T)++(a::M)) Green (x-y) :=by
        apply clean_perm clean_green _ hx; apply List.Perm.trans List.perm_append_comm; apply (List.Perm.append · ·); all_goals exact List.perm_append_comm
    let w:=P; change _*(_*Tensor.coeff (fun z=>Tensor.coeff (fun x=>P (x-z)) _ x (basis∘ M.get)) T.length y _)=_
    rw [hV, he,_root_.smul_apply,show V=(fun y=>Tensor.coeff P M.length y (basis∘l)) from rfl, stack_coeff (f:=P) l u (show Clean P from clean_chart p.1.a p.1.b q.1.a q.1.b) hx]; unfold u l; simp only [List.ofFn_get]; unfold P; rw [bare M T p.1.a p.1.b q.1.a q.1.b (x-y) hx]; simp_rw [ht]; unfold Wind mission Pose.Lck; simp only [List.length_cons, smul_eq_mul]; rw [pow_succ]; change ((T.length.factorial:ℕ):ℝ) * (((M.length.factorial:ℕ):ℝ) * _) = _; field_simp; unfold T M; split_ifs <;> ring
end YM.OPE.Prairies
