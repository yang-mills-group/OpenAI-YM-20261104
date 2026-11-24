import YM.X.Reed.Graded
/-!
Gauge decomposition into unit-width centered homogeneous polynomials. K=0 (rather than Lap and divergence-free) enough. Color action commutes; needed for cancellation exact CT's. Signed action can enter later by averaging.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Reed
open Lattice Wilson Stems Next.Rank.CellsInt Tensor TensorProduct Filter MeasureTheory Metric Finset Function Maxwell
open scoped Topology ContDiff BigOperators
variable {G:Gauge} {n:ℕ}
def windP (p:Axis → T E4 G.Color n) : T E4 G.Color (n+1):=
      ((↑(n+1:ℕ)):ℝ)⁻¹ • ∑ i:Axis,Tensor.added (p i) (Maxwell.compAxis i)
lemma windP_sym (p:Specs G n): Tensor.Sym (windP p.val):= by intro v s; simp only [windP,smul_apply,_root_.sum_apply,Tensor.added_sym _ _ v s]
lemma windP_diag (p:Specs G n): diagonal (windP p.val)=fun x:E4=> ((↑(n+1:ℕ)):ℝ)⁻¹ • ∑ i:Axis,x i • diagonal (p.val i) x:= by
      funext x; simp only [windP,diagonal,smul_apply,_root_.sum_apply]; apply congr_arg; exact sum_congr rfl fun i _=> Tensor.added_diag ..

lemma windP_burst (p:Specs G n)(h:∀ i j:Axis,Maxwell.grad i (diagonal (p.val j))= Maxwell.grad j (diagonal (p.val i)))(j:Axis): burst j (windP p.val)= p.val j:= by
      apply Tensor.ext_diag _ _ (burst_sym (windP_sym p) _) (p.sym j); funext x; rw [burst_diag (windP_sym p),windP_diag]; let c:=((↑(n+1:ℕ)):ℝ)
      let f:=fun x:E4 => ∑ i:Axis,x i • diagonal (p.val i) x
      have ht:DifferentiableAt ℝ f x:= DifferentiableAt.fun_sum fun b _=> (Maxwell.compAxis b).differentiableAt.smul ((Tensor.diag_smooth _ ∞).differentiable (by simp) x)
      rw [show Maxwell.grad j (fun z=>c⁻¹ • f z) x=c⁻¹ • Maxwell.grad j f x by simp only [Maxwell.grad,Analysis.D,fderiv_fun_const_smul ht]; rfl, Maxwell.grad_self]; conv_lhs => enter [2,2,2,k]; rw [h j k] -- simplify if k=j for grad
      rw [Maxwell.grad_euler (p.val j) (p.sym j)]; nth_rw 1 [← one_smul ℝ (diagonal (p.val j) x)]; rw [← add_smul,show (1:ℝ)+n= c by simp [c,add_comm],smul_smul,inv_mul_cancel₀ (by unfold c; positivity),one_smul]
lemma equival (p:Specs G n) (h:∀ i j:Axis,Maxwell.grad i (diagonal (p.val j))= Maxwell.grad j (diagonal (p.val i))): skew n p.val=raised (reach 0 (windP p.val)):= by
      funext x; change reach (tip x.2) (p.val x.2) x.1=stepValue (reach _ _) x.2 x.1; rw [step_grabs (windP_sym p),zero_add,windP_burst p h]
lemma horizontal0 (u: Specs G 0): skew _ u.val=raised (reach 0 (windP u.val)):= by
    apply equival; intro i j; simp_rw [show ∀i:Axis, diagonal (u.val i)=fun x:E4=> u.val i Fin.elim0 from fun i=> funext fun _=> congr_arg (u.val i) (Subsingleton.elim ..)];funext x; simp [grad,Analysis.D]
lemma fasten (p:Specs G (n+1))(h:trot p.val=0)(i j:Axis) :Maxwell.grad i (diagonal (p.val j))= Maxwell.grad j (diagonal (p.val i)):= by
    have he:= congr_fun (congr_fun h i) j; change burst i (p.val j)-burst j (p.val i)=(0:T E4 G.Color n) at he
    funext x; rw [← burst_diag (p.sym j),← burst_diag (p.sym i),sub_eq_zero.mp he]
lemma horizontal (p:Okay G (n+1))(h:shelve n p=0): skew _ p.val.val= raised (reach 0 (windP p.val.val)):= equival p.val (fasten _ (congr_arg Subtype.val h))

def rightCur : (n:ℕ)→ Okay G n→ₗ[ℝ] Okay G n
 | 0 =>0
 | n+1=> slip ∘ₗ (shelve n)
def gaugeShift (n:ℕ) : (Specs G n)→ₗ[ℝ] Cover→G.Color where
    toFun p:= reach 0 (windP p.val)
    map_add' p s:= by
       have he : windP (p.val+s.val)=windP p.val+windP s.val:=by
          apply Tensor.ext_diag _ _ (windP_sym (p+s)) (fun _ _=> congr_arg₂ HAdd.hAdd (windP_sym p ..) (windP_sym s ..)) -- .. check implicit
          funext x; rw [windP_diag (p+s)]; change _ = diagonal (windP p.val) x+diagonal (windP s.val) x; rw [windP_diag p,windP_diag s]; change ((↑(n+1:ℕ)):ℝ)⁻¹ • ∑ i:Axis,x i • ( diagonal (p.val i) x+diagonal (s.val i) x)= _; simp [smul_add,sum_add_distrib]
       change reach 0 (windP (p.val+s.val))=_; rw [he,map_add]
    map_smul' r p:= by
       have he : windP (r • p.val) = r • windP p.val:=by
          apply Tensor.ext_diag _ _ (windP_sym (r•p)) (fun _ _=> congr_arg (r • ·) (windP_sym p ..)); funext x; rw [windP_diag (r•p)]; change _ = r • diagonal (windP p.val) x; rw [windP_diag p]; change ((↑(n+1:ℕ)):ℝ)⁻¹ • ∑ i:Axis,x i • (r • diagonal (p.val i) x)= _; rw [smul_comm r]; apply congr_arg; rw [Finset.smul_sum]; exact sum_congr rfl fun i _=> smul_comm ..
       change reach 0 (windP (r • p.val))=r • _; rw [he,map_smul]
def phase (p:Okay G n):Cover→G.Color:= gaugeShift n (p-rightCur n p).val
def valP (n:ℕ): Okay G n→ₗ[ℝ] Brush G:= skew n ∘ₗ (evenShape n).subtype ∘ₗ (LinearMap.ker (downKG n)).subtype
lemma poles (p:Okay G n) : valP n p-valP n (rightCur n p)=raised (phase p):= by
    rw [←map_sub]; cases n with
    | zero=> exact horizontal0 _
    | succ n => exact horizontal (p-rightCur _ p) (by rw [show shelve n (p-(rightCur (n+1)) p) = _ from map_sub (shelve n) p _,rightCur,LinearMap.comp_apply,shelve_slip,sub_self])
end YM.PositionX.Reed
