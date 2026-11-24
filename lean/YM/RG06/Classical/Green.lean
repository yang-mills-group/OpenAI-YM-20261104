import YM.RG06.Classical.Level

/-!
# Solving polynomial Poisson in a homogeneous stencil sector

Canonical G-color independent spatial recursion. Preserves homogeneous and smooth. All calculations
classical. `sprout k a f` solves Δq = (|x|²)^a f where f homogeneous of degree k.
This gives an explicit right inverse for the linear obstruction in each order once applied on antisymmetric
tensors. No analytic or quantum continuation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG06.ClassicalOn
open Function Labels Analysis Continuum Tensor
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace Topology
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {f g:E4→E}{u:E4→F}{k m n:ℕ}

lemma par_sum{I:Type*}(s:Finset I)(f:I→E4→E)(e:∀ i∈s,Good (f i))(i:Axis):par i (∑ k∈s,f k)=∑ k∈s,par i (f k):=by
 classical
 induction s using Finset.induction_on with
 | empty=> simp only [Finset.sum_empty]; funext x; simp [par,D]
 | insert a t h H=>
    have hv(k)(ht:k∈t):=e k (Finset.mem_insert_of_mem ht)
    have hg:Good (∑ k∈t,f k):=by rw [show (∑ k∈t,f k)= fun z=>∑k∈t,f k z from funext fun _=>Finset.sum_apply ..]; exact ContDiff.sum hv
    rw [Finset.sum_insert h,Finset.sum_insert h,par_add (e a (Finset.mem_insert_self ..)) hg, H hv]

lemma par_eval {a:E4→ℝ}{f:E4→E} (h:Good a)(hf:Good f)(i:Axis)(x:E4):
    par i (fun x=> a x • f x) x= par i a x • f x + a x • par i f x:=by
  have he:= ((h.germ x).hasFDerivAt.smul (hf.germ x).hasFDerivAt).fderiv
  unfold par D; erw [he]; exact add_comm ..

def lap (f:E4→E): E4→E := ∑ i:Axis,par i (par i f)
lemma GoodLap (h:Good f):Good (lap f) :=by unfold lap; rw [show (∑ i:Axis,par i (par i f))=fun x => ∑ i:Axis,par i (par i f) x from funext fun _=>Finset.sum_apply ..]; exact ContDiff.sum (fun i _=>(h.par i).par i)
lemma lap_level (h:Level (k+2) f):Level k (lap f):=Level.sum _ _ fun i _=> (h.advance i).advance i
lemma lap_add (h:Good f)(e:Good g):lap (f+g)=lap f+lap g:=by unfold lap; simp_rw [par_add h e,par_add (h.par _) (e.par _),Finset.sum_add_distrib]
lemma lap_scale(c:ℝ)(h:Good f):lap (c • f)=c • lap f:=by unfold lap; simp_rw [par_scale c h,par_scale c (h.par _),Finset.smul_sum]
lemma lap_eval {a:E4→ℝ}(h:Good a)(hf:Good f)(x:E4):
    lap (fun x=>a x • f x) x= lap a x • f x + a x • lap f x + (2:ℝ) • (∑ i:Axis,par i a x • par i f x):=by
  have he(i:Axis):par i (fun x=>a x • f x)= (fun x=>par i a x • f x)+(fun x=>a x • par i f x):=funext (par_eval h hf i)
  have hv(i:Axis): Good (fun x=>par i a x • f x):= ContDiff.smul (h.par i) hf
  have hw(i:Axis): Good (fun x=>a x • par i f x):=ContDiff.smul h (hf.par i)
  unfold lap; simp only [he, par_add (hv _) (hw _),Pi.add_apply,Finset.sum_apply, par_eval (h.par _) hf, par_eval h (hf.par _), Finset.sum_add_distrib,two_smul]
  rw [Finset.smul_sum,Finset.sum_smul]; abel

def mass (x:E4):ℝ:=∑ i:Axis, x i^2
lemma mass_level : Level 2 mass:= by
  have he(i:Axis) := (Level.component i).eval (Level.component i)
  rw [show mass=∑ i:Axis,fun x:E4=>x i*x i by ext; simp [mass,pow_two]]
  exact Level.sum (E:=ℝ) Finset.univ (fun i=>fun x:E4=> (x i) * (x i)) (fun i _=>he i)
lemma mass_p (i:Axis)(x:E4): par i mass x= 2*x i :=by
  unfold mass; rw [show (fun x:E4=>∑ j:Axis,x j^2)=∑ j:Axis,fun x:E4=>x j^2 by ext x; simp]; rw [par_sum (E:=ℝ) (f:=fun j x=> (x j)^2) (s:=Finset.univ) (fun j _=>ContDiff.pow (Level.component j).smooth _), Finset.sum_apply]
  have he(j:Axis): par i (fun x:E4=>x j^2) x=2*x j * (basis i j):=by
      unfold par D; let L:= (EuclideanSpace.proj j:E4→L[ℝ]ℝ)
      have hz:= (L.hasFDerivAt.pow 2 (x:=x)).fderiv
      change fderiv ℝ (fun x=>L x^2) x _=_
      rw [hz]; simp [L]
  simp_rw [he,basis_eq]; simp [mul_ite]
lemma mass_lap (x:E4): lap mass x=8:=by
  have hF (i): par i mass= fun x=> (2:ℝ) • (x i):=funext (mass_p i)
  unfold lap; simp_rw [Finset.sum_apply,hF,show ∀ i:Axis, par i (fun x:E4=>(2:ℝ) • (x i))=fun x:E4=>(2:ℝ) • par i (fun x:E4=>x i) x from fun _=> par_scale 2 (Level.component _).smooth _]
  have he(i:Axis):par i (fun x:E4=>x i) x=1:=by unfold par D; let L:= (EuclideanSpace.proj i:E4→L[ℝ]ℝ); change fderiv ℝ L x _= _; rw [L.fderiv]; simp [L]
  simp [he]; norm_num
lemma mass_meter (h:Level n f)(x:E4): lap (fun x=>mass x • f x) x = mass x • lap f x + (8+4*(n:ℝ)) • f x:=by
 rw [lap_eval mass_level.smooth h.smooth,mass_lap]; simp_rw [mass_p, mul_smul, ←Finset.smul_sum,h.euler]
 module

def mask (m:ℕ)(f:E4→E):E4→E:=fun x=>mass x^m • f x
lemma untold {f:E4→E}:mask 0 f=f:=by ext;simp [mask]
lemma mask_next(m:ℕ):mask (m+1) f=mask 1 (mask m f):=by funext x; simp only [mask,pow_succ,pow_zero,one_mul,smul_smul,mul_comm]
lemma mask_level (m:ℕ)(h:Level k f):Level (k+2*m) (mask m f):=by
 induction m with
 | zero=>simpa [untold] using! h
 | succ m H=>rw [mask_next, show k+2*(m+1)=2+(k+2*m) by omega]; simpa only [show mask 1 (mask m f)=(fun x=>mass x • mask m f x) by funext x; rw [mask,pow_one]] using! mass_level.eval H
lemma lap_mask (a:ℕ)(h:Level k f)(x:E4):
    lap (mask (a+1) f) x= mask (a+1) (lap f) x+ (4*(a+1:ℕ)*((k+a+2:ℕ):ℝ):ℝ) • mask a f x:=by
 induction a with
 | zero => simp only [zero_add,mask,pow_one,pow_zero,one_smul,Nat.add_zero,Nat.cast_one,mul_one]; rw [show mask 1 f = (fun x=>mass x • f x) by funext x; rw [mask,pow_one],mass_meter h]; congr 2; push_cast;ring
 | succ a H=>
    have he(i)(F:E4→E):mask 1 (mask i F) x=mass x • mask i F x:=by simp [mask]
    have hv:Level (k+2*(a+1)) (mask (a+1) f):=mask_level _ h
    rw [mask_next (a+1),mask_next (f:=lap f) (a+1),show mask 1 (mask (a+1) f)=(fun x=>mass x • mask (a+1) f x) from (by funext x; simp only [mask,pow_one]), mass_meter hv,H]
    simp only [mask,pow_succ,smul_add,smul_smul,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
    module

-- canonically linear homotopy solving Delta = original homogeneous data, no group choices.
def inverse (k:ℕ)(a:ℕ)(f:E4→E) : E4→E:=
 let c:ℝ:= ((4:ℝ)*↑(a+1:ℕ)*↑(k+a+2:ℕ))⁻¹
 if k<2 then c • mask (a+1) f else c • (mask (a+1) f - inverse (k-2) (a+1) (lap f))
 termination_by k
 decreasing_by omega
lemma inverse_hom (k:ℕ)(a:ℕ){f:E4→E}(h:Level k f): Level (k+2*a+2) (inverse k a f) :=by
 induction k using Nat.strong_induction_on generalizing a f with | h k H=>
 have he:=mask_level (a+1) h
 have hu := show k+2*a+2=k+2*(a+1) by omega
 rw [inverse, hu]; split;exact he.scale _
 next ht=> refine (he.sub ?_).scale _
           rw [show k+2*(a+1)=(k-2)+2*(a+1)+2 by omega]
           apply H (k-2) (by omega); apply lap_level (f:=f); rwa [Nat.sub_add_cancel (by omega)]
lemma lap_bottom(h:Level k f)(e:k<2):lap f=0:=by
 unfold lap; apply Finset.sum_eq_zero; intro i _
 apply Level.bottom
 have hc: Level (k-1) (par i f):=Level.advances h i
 rwa [show 0 = k-1 by omega]

lemma solved (k:ℕ)(a:ℕ){f:E4→E}(h:Level k f): lap (inverse k a f) = mask a f:=by
 induction k using Nat.strong_induction_on generalizing a f with | h k H=>
 let c:ℝ:=4*(a+1:ℕ)*(k+a+2:ℕ)
 have he : c≠0:= by unfold c; positivity
 have ht :=mask_level (a+1) h
 have hx :=funext (lap_mask a h)
 change lap (mask (a+1) f)=mask (a+1) (lap f) + c • mask a f at hx
 rw [inverse]; split
 · next hk=> rw [lap_scale _ ht.smooth,hx,lap_bottom h hk,show mask (a+1) (0:E4→E)=0 by ext; simp [mask],zero_add,inv_smul_smul₀ he]
 next hk=>
   have hv : Level (k-2) (lap f):=by apply lap_level; rwa [Nat.sub_add_cancel (by omega)]
   let q:= inverse (k-2) (a+1) (lap f)
   have hh:Good q:=(inverse_hom (k-2) (a+1) hv).smooth
   change lap (c⁻¹ • (mask (a+1) f-q))= _
   rw [lap_scale (f:=mask (a+1) f-q) _ (ContDiff.sub ht.smooth hh), sub_eq_add_neg, lap_add (g:=-q) ht.smooth (ContDiff.neg hh), show lap (-q) = -lap q by unfold lap; simp_rw [par_neg, Finset.sum_neg_distrib], hx]
   rw [show lap q= _ from H (k-2) (by omega) (a+1) hv]; rw [add_right_comm,add_neg_cancel,zero_add,inv_smul_smul₀ he]

end YM.RG06.ClassicalOn
