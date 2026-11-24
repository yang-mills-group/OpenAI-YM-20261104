import YM.FormalBulk08.Plait.Curl

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Plait
open Function Wick Orb Series Jets PowerSeries Filter
open Matrix (of)
open scoped BigOperators Topology Classical Matrix ContDiff
variable {V I:Type*}[Fintype V][Fintype I][DecidableEq V]
def litR (f:Matrix V V (Jets.Rays I→ℝ)): Matrix V V (Pap I):= of fun i j=> paste (f i j)
def dimR (f:Matrix V V (Jets.Rays I→ℝ))(x:Jets.Rays I):Matrix V V ℝ:=of fun i j=> f i j x
lemma paint_R (f:Matrix V V (Jets.Rays I→ℝ))(h:∀ i j, ContDiffAt ℝ ∞ (f i j) 0): paste (fun x=>(dimR f x).det)= (litR f).det := by
    let Y (s:Equiv.Perm V): Jets.Rays I→ℝ:= ∏ i:_, f (s i) i
    let D (s:Equiv.Perm V): Jets.Rays I→ℝ:= (fun _:Jets.Rays I=> ((s.sign:ℤ):ℝ))*Y s
    have he s: ContDiffAt ℝ ∞ (Y s) 0:=drawing _ _ (fun i _=> h (s i) i)
    have ht s: ContDiffAt ℝ ∞ (D s) 0:= contDiffAt_const.mul (he s)
    rw [show (fun x=>(dimR f x).det)=∑ s,D s by ext; simp [Y,D,Finset.sum_apply,Finset.prod_apply,dimR,Matrix.det_apply'], garter _ _ (fun i _=> ht i), Matrix.det_apply']; apply Finset.sum_congr rfl; intro s _; unfold D; rw [paste_mul _ _ contDiffAt_const (he s), paste_flat]; unfold Y; rw [shaving _ _ (fun i _=> h (s i) i)];simp [litR]
lemma paint_a (f:Matrix V V (Jets.Rays I→ℝ))(h:∀ i j, ContDiffAt ℝ ∞ (f i j) 0): ContDiffAt ℝ ∞ (fun x=>(dimR f x).det) 0:= by
    simp only [Matrix.det_apply',dimR,Matrix.of_apply]; refine ContDiffAt.sum (fun i _=>contDiffAt_const.mul ?_); rw [show (fun x=>∏ j:V,f (i j) j x)=∏ j:V,f (i j) j by ext; simp [Finset.prod_apply]]; exact drawing _ _ (fun j _=> h _ _)
-- scalar commutations at Hessian curve
omit [DecidableEq V] [Fintype I] in lemma constant_fort (B:Matrix V V (TypeR I))(P:Matrix V V (Pap I))(m): fort ((of fun i j=>C (B i j))*P) m= B*fort P m:=by
    ext; simp only [fort,Matrix.of_apply,Matrix.mul_apply, map_sum, coeff_C_mul]
lemma deter_lux (T:Hull V I)(f:Matrix V V (Jets.Rays I →ℝ))(hw: ∀ i j,ContDiffAt ℝ ∞ (f i j) 0) (h:dimR f 0=T.saddle.P)(hp:0<(dimR f 0).det) :
    coeff 2 (paste (fun x=> Real.log (dimR f x).det)) = (rhoq T.saddle.q * fort (litR f) 2).trace- halve (((rhoq T.saddle.q*fort (litR f) 1)*(rhoq T.saddle.q *fort (litR f) 1)).trace):= by
    have hb: T.saddle.P.det≠0:= h ▸ hp.ne'
    let q:= T.saddle.q;let p:= litR f;let a:ℝ:= q.det; let Q:= rhoq (I:=I) q; let A:=C.mapMatrix Q
    let g x:=a*(dimR f x).det
    have hQ (i j): A i j=C (Q i j):=by unfold A; simp
    have ha: a=q.det:=rfl
    have he:a*T.saddle.P.det=1:= by rw [ha,←Matrix.det_mul,mul_eq_one_comm.mp T.saddle.inv,Matrix.det_one]
    have ha':0 < a:= pos_of_mul_pos_left (he.symm ▸ zero_lt_one) (h ▸ hp.le)
    have hh : (fun x=> Real.log (g x))=ᶠ[𝓝 0] ((fun _=>Real.log a)+(fun x=>Real.log (dimR f x).det)) := by
       filter_upwards [(paint_a f hw).continuousAt.eventually (lt_mem_nhds hp)] with x hx; exact Real.log_mul ha'.ne' hx.ne'
    have hg: ContDiffAt ℝ ∞ g 0 := contDiffAt_const.mul (paint_a f hw)
    have h1:g 0=1:=by unfold g; rw [h,he]
    have hP: paste g=(A*p).det:= by
       rw [show g=(fun _=>a)*(fun x=>(dimR f x).det) from rfl,paste_mul _ _ (contDiffAt_const (c:=a)) (paint_a f hw),paste_flat,paint_R f hw]; rw [Matrix.det_mul]; unfold A Q rhoq a;rw [←RingHom.map_det,←RingHom.map_det]
    have h0 : fort (A*p) 0=1:= by
       rw [show A= of (fun i j=> C (Q i j)) from by ext1 i j; exact hQ i j, constant_fort, show fort p 0=rhoq T.saddle.P from ?_]
       · unfold Q rhoq; rw [←map_mul, mul_eq_one_comm.mp T.saddle.inv,map_one]
       ext i j; simp only [fort,p,litR,Matrix.of_apply,paste_first,rhoq,RingHom.mapMatrix_apply,Matrix.map_apply]; rw [show f i j 0=_ from congr_fun (congr_fun h i) j]
    have ht:=log_height _ h0; rw [← hP,← pin_rung _ h1 hg,paste_replace (f:=Real.log ∘ g) hh,paste_sum _ _ (contDiffAt_const (c:=Real.log a)) ((paint_a f hw).log hp.ne'),paste_flat,map_add, coeff_C, if_neg (by omega), zero_add, show A= of (fun i j=> C (Q i j)) from by ext1 i j;exact hQ i j,constant_fort,constant_fort] at ht; exact ht
end YM.FormalBulk08.Plait
