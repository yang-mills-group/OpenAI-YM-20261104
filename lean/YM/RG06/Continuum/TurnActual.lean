import YM.RG06.Continuum.Rotation

/-! Continuum chart covariance under O(4) for the external prescription -/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.Continuum
open Analysis Tensor Maxwell Extra.FD Pert.Bare Labels
open scoped Topology ContDiff Matrix.Norms.Frobenius ComplexConjugate BigOperators Classical
namespace O
variable {G:Gauge}(s:Ortho)(g:ℝ) (A:Connection G)

def align (f:Section G):Section G:=Function.comp f (mov s⁻¹)
def position : Connection G:= fun i=>∑ b:Axis, s.val i b • align s (A b)
lemma health (q:Section G)(h:Good q):Good (align s q):=ContDiff.comp h (mov s⁻¹).contDiff
lemma whole (h:Smooth A) :Smooth (position s A):= by
 intro i; unfold position; rw [show (∑ b:Axis,s.val i b • align s (A b))=fun x=>∑ b:Axis,s.val i b • align s (A b) x from funext (fun _=> Finset.sum_apply ..)]
 exact ContDiff.sum fun b _=> ContDiff.const_smul (s.val i b) (health s (A b) (h b))
lemma gra (i:Axis)(q:Section G)(h:Good q):par i (align s q)=∑ b:Axis,s.val i b • align s (par b q):=by
 funext x
 rw [Finset.sum_apply]; exact Extra.FD.mov_gradient s i (f:=q) (x:=x) (ContDiff.contDiffAt h)

lemma tangent (i:Axis)(q: Section G)(h:Good q):
  covariant g (position s A) i (align s q)=∑ b:Axis,s.val i b • align s (covariant g A b q):=by
  rw [covariant,gra s _ q h]; unfold position covariant; funext x
  simp only [align,Function.comp_apply,Pi.add_apply,bracket,Pi.smul_apply, Finset.sum_apply,map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply, smul_add,Finset.sum_add_distrib,Finset.smul_sum]; congr 1
  exact Finset.sum_congr rfl fun _ _=> smul_comm ..

lemma plate (i j:Axis)(h:Smooth A) : curvature g (position s A) i j=
    ∑ a:Axis,∑ b:Axis,s.val i a • s.val j b • align s (curvature g A a b):=by
  rw [curvature]; unfold position; rw [par_lincombo (h:=fun a _=>health s _ (h a)),par_lincombo (h:=fun a _=>health s _ (h a))]
  funext x
  have hd (a b:Axis) := gra s b (A a) (h a)
  simp_rw [hd]
  simp only [curvature]
  simp only [Pi.add_apply,Pi.smul_apply, Pi.neg_apply,align,Function.comp_apply, Finset.sum_apply, Finset.smul_sum, bracket,_root_.map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_add,Finset.sum_add_distrib, smul_neg];
  -- rw [Finset.sum_comm];simp_rw [← Finset.sum_neg_distrib]
  apply congrArg₂ (·+·)
  · apply congrArg₂ (·+·)
    · rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a _=>Finset.sum_congr rfl fun b _=>?_ ; rw [smul_comm (s.val j b)]
    simp only [Finset.sum_neg_distrib]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a _=>Finset.sum_congr rfl fun b _=>?_ ; simp only [smul_smul]; congr 1; ring
  -- associativity and adj bracket index sums

lemma oriented(h:Smooth A){j:ℕ}(w:Fin j→Axis)(q:Section G)(hf:Good q):
 nablas g (position s A) w (align s q)=
  ∑ t:Fin j→Axis,(∏ a,s.val (w a) (t a)) • align s (nablas g A t q):=by
  induction j with
  | zero=>rw [nablas,Fintype.sum_subsingleton _ (Fin.elim0 (α:=Axis))]; simp [nablas]
  | succ j H=>
      let e:(Fin (j+1)→Axis)≃ Axis×(Fin j→Axis):=
       {toFun w:=(w 0,Fin.tail w)
        invFun w:=Fin.cons w.1 w.2
        left_inv w:= by simp
        right_inv w:=by simp}
      rw [← Equiv.sum_comp e.symm (fun t=> (∏ a,s.val (w a) (t a)) • align s (nablas g A t q)), Fintype.sum_prod_type,
       nablas,H,cov_lincombo g (position s A) Finset.univ _ (fun t:Fin j→Axis=>align s (nablas g A t q)) (w 0) (fun t _=>health s _ (Smooth.higherCov g A h t _ hf))]
      simp_rw [tangent s g A _ (nablas g A _ q) (Smooth.higherCov g A h _ q hf),Finset.smul_sum]
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; refine Finset.sum_congr rfl fun b _=>?_; change (∏ i:Fin j,s.val (w i.succ) (b i)) • s.val (w 0) a • align s (covariant g A a (nablas g A b q))=
        (∏ i,s.val (w i) (Fin.cons (α:=fun _=>Axis) a b i)) • align s (nablas g A (Fin.cons (α:=fun _=>Axis) a b) q)
      rw [smul_smul,Fin.prod_univ_succ,Fin.cons_zero,nablas,Fin.cons_zero,Fin.tail_cons,mul_comm];rfl
lemma lincombo {I:Type*}(h:Smooth A){j:ℕ}(w:Fin j→Axis)(z:Finset I)(c:I→ℝ)(f:I→Section G)(he:∀ i∈z,Good (f i)):
  nablas g A w (∑ i∈z,c i • f i)=∑ i∈z,c i • nablas g A w (f i):=by
  induction j with
  | zero=>rfl
  | succ j H=>simp_rw [nablas,H,cov_lincombo g A z _ _ _ (fun i hi=>Smooth.higherCov g A h (Fin.tail w) _ (he i hi))]

lemma applies (h:Smooth A)(x:E4):
  Form.evaluate g (position s A) x=Form.turning s (Form.evaluate g A (mov s⁻¹ x)):=by
  funext j i b w
  let q (a c:Axis):=align s (curvature g A a c)
  have hq(a c:Axis):Good (q a c):=health s _ (Smooth.F g A h a c)
  let m i j a c:=s.val (i:Axis) (a:Axis)*s.val (j:Axis) (c:Axis)
  have he (i j:Axis):curvature g (position s A) i j=∑ z:Axis×Axis,m i j z.1 z.2 • q z.1 z.2:=by rw [Fintype.sum_prod_type]; simp only [m,mul_smul,q]; exact plate _ _ A _ _ h
  change (j.factorial:ℝ)⁻¹ • nablas _ _ w (curvature _ _ _ _) x=_
  rw [he,lincombo g (position s A) (whole s A h) w Finset.univ _ (fun z:Axis×Axis=>q z.1 z.2) (fun z _=> hq ..)]
  unfold q; have ho(a c:Axis):= oriented s g A h w (curvature g A a c) (Smooth.F g A h a c)
  simp_rw [ho]; unfold Form.turning
  rw [Form.turned_basis,Fintype.sum_prod_type]; simp only [Finset.smul_sum,Finset.sum_apply,Pi.smul_apply,align, Function.comp_apply]; unfold Form.spread Form.evaluate
  simp_rw [bi_eval]
  have ht (t a:Axis):mov s⁻¹ (basis t) a=s.val t a:=M4.move_basis _ _ _ -- orientation inverse
  change (∑ a, ∑ c, ∑ t,(j.factorial:ℝ)⁻¹ • m i b a c • (∏ k,s.val (w k) (t k)) • nablas g A t (curvature g A a c) ((mov s⁻¹) x))=_
  refine Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun c _=>?_
  change _=s.val i a • s.val b c • (∑ t : Fin j→Axis, spaceMon t (covJet g A t a c ((mov s⁻¹) x))) (fun l=> mov s⁻¹ (basis (w l)))
  rw [sum_apply]; simp_rw [mon_eq,ht,Finset.smul_sum, covJet]; refine Finset.sum_congr rfl fun t _=>?_; simp only [smul_smul,m]; congr 1;ring

lemma radial_shift (d:ℕ)(J:Labels.Jet G): position s (radField d J)=radField d (Labels.changedJet (fun _=> Taylor.turn s) J):=by
   funext i x; unfold position radField Source.potential
   simp_rw [Finset.sum_apply]; simp only [Pi.smul_apply,align,Function.comp_apply,Labels.changedJet,Taylor.turn_value]; rw [Finset.sum_comm]; simp only [Finset.smul_sum,mov_apply]
end O
namespace Form
variable {G:Gauge}
lemma actual_rotation (s:Ortho)(g:ℝ)(A:Connection G)(h:Smooth A)(p:Pol G)(x:E4):
  actual g (O.position s A) (Ortho.move s x) (depart s p)=actual g A x p:=by
   unfold actual; rw [O.applies s g A h, turned_labels, turning_composes,inv_mul_cancel, turning_id,mov_apply,Ortho.inv_move]
lemma bridge_turn (s:Ortho)(g:ℝ){d:ℕ}(p:Field G d): bridge g (turnField s p)=Labels.tensor s (bridge g p):=by
  refine Subtype.ext (Labels.eval_ext _ _ (fun v=>?_)); change Labels.read v (toCommon _ (turnField s p).val)=Labels.read v (Labels.rotated s (toCommon _ p.val))
  rw [radial_checks, Labels.rotated,Labels.eval_changed,radial_checks,← O.radial_shift s⁻¹ d v]
  change actual g (radField d v) 0 (depart s p.val)=_
  have hm:mov (s⁻¹)⁻¹ 0=(0:E4):=map_zero _
  unfold actual; rw [O.applies s⁻¹ g _ (rad_smooth d v),turned_labels,hm]
end Form
end YM.RG06.Continuum
