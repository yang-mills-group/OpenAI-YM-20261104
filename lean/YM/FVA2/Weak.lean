import YM.FVA2.CovForms

/-!
# Position-space precision inversion on quotient

Coordinatewise weak identities later consumed on ANY chosen basis. Includes harmonic term
of constant ghost. Keep halves explicit (a factor often shared with loop signs).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Green
open Lattice MS MS.Orbit Finset
variable {n : Side}

def move (y : Site n) : (Site n → ℝ) →ₗ[ℝ] (Site n → ℝ) := LinearMap.pi fun x => LinearMap.proj (x-y)
lemma move_v (y x : Site n) (f : Site n → ℝ) : move y f x = f (x-y) := rfl
lemma moved_fwd (f : Site n → ℝ) (y : Site n) (j : Axis) : fwd j (move y f)= move y (fwd j f) := by ext x; simp_rw [move_v,fwd_of,move_v]; rw [add_sub_right_comm]
lemma moved_back (f : Site n → ℝ) (y : Site n) (j : Axis) : back j (move y f)=move y (back j f) := by ext x; simp_rw [move_v,back_of,move_v]; rw [sub_right_comm x]
lemma moved_lap (f : Site n→ℝ) (y : Site n) : lap (move y f)=move y (lap f):= by unfold lap; simp_rw [LinearMap.sum_apply,LinearMap.comp_apply,moved_fwd,moved_back,map_sum]
lemma reflected_neg (j : Axis) (x : Site n) : -(-x-step j)-step j=x := by abel

/-- quotient scalar mean-zero inverse column. -/
def siteG (y : Site n) := move y (kernel 1) + move (-y) (kernel 1)
lemma move_mean (y : Site n) : ∑ x : Site n, move y (kernel 1) x=0:= by
  rw [show (∑ x : Site n,move y (kernel 1) x)=∑ x : Site n,kernel 1 x from Eq.trans (sum_congr rfl ?_) (Equiv.sum_comp (Equiv.addRight (-y)) (kernel 1)), mean_zero 0]
  intro x _; rw [move_v,sub_eq_add_neg]; rfl
lemma reflect_site (y x : Site n) : move y (kernel 1) (-x)=move (-y) (kernel 1) x:= by rw [move_v,move_v,← kernel_even 1 (-x-y), show -(-x-y)=x- -y from (by abel)]
lemma siteG_even (x y : Site n) : siteG y (-x) = siteG y x:= by unfold siteG; rw [Pi.add_apply,Pi.add_apply,reflect_site,reflect_site,neg_neg,add_comm]
lemma siteG_mean (y : Site n) : ∑ x : Site n, siteG y x=0:= by simp_rw [siteG,Pi.add_apply,Finset.sum_add_distrib,move_mean,add_zero]
lemma siteG_sym (x y : Site n) : siteG y x=siteG x y := by simp_rw [siteG,Pi.add_apply,move_v]; rw [← kernel_even 1 (y-x),neg_sub]; rw [sub_neg_eq_add,sub_neg_eq_add, add_comm x y]
lemma lap_siteG (x y:Site n): lap (siteG y) x=(if x=y then 1 else 0)+(if x= -y then 1 else 0)-2*νt n:= by
    simp only [siteG,map_add,Pi.add_apply, moved_lap,move_v, lapR 0 ,if_true, zero_kernel, sub_eq_zero]; ring

theorem pay_siteG (f:Site n→ℝ) (h:∀ x,f (-x)=f x)(he:∑ x : Site n,f x=0)(y:Site n):
     ∑ x : Site n, f x * lap (siteG y) x = 2*f y := by
    simp_rw [lap_siteG,mul_sub,mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite,mul_one,mul_zero]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq', ← Finset.sum_mul, he, h]; simp only [Finset.mem_univ,if_true,zero_mul,sub_zero]; ring

lemma siteLine (x y : Site n) (j : Axis) : siteVector j (x-y)-siteVector j (x-(-y-step j)) = - fwd j (siteG x) y := by
   rw [fwd_of, ← siteG_sym x (y+step j), ← siteG_sym x y]; simp_rw [siteG,Pi.add_apply,move_v,siteVector,back_of]
   rw [ show x-(y+step j)= x-y-step j from (by abel), show x-(-(y+step j))= x-(-y-step j) from (by abel), show x-(-y-step j)-step j=x-(-y) from (by abel)]
   ring

/-- Real scalar link arrays. -/
abbrev ArrayA (n : Side) := Axis → Site n → ℝ

def div : ArrayA n →ₗ[ℝ] (Site n → ℝ) := ∑ i : Axis,(back i).comp (LinearMap.proj i)
lemma divergence (A : ArrayA n) : Green.div A=∑ i : Axis, back i (A i) := by simp_rw [Green.div, LinearMap.sum_apply]; rfl
lemma divergence_v (A : ArrayA n) (x : Site n) : Green.div A x=∑ i : Axis, back i (A i) x := by rw [divergence,Finset.sum_apply]

def grad : (Site n → ℝ) →ₗ[ℝ] ArrayA n := LinearMap.pi fwd
lemma grad_v (f : Site n → ℝ) (i : Axis) : grad f i= fwd i f:=rfl
lemma div_grad (f : Site n → ℝ) : Green.div (grad f)=lap f := by ext x; rw [lap_of,divergence_v]; rfl

lemma vectorFn (i j : Axis) (n : Side) : @vectorLine n i j = (if i=j then kernel 1 else 0)-fwd i (back j (kernel 2)) := by split <;> ext <;> simp_all only [vectorLine,↓reduceIte,Pi.zero_apply,Pi.sub_apply]
lemma lap_two : lap (@kernel n 2)=kernel 1 := by ext x; rw [lapR 1]; simp
lemma back_vline (j : Axis) : ∑ i : Axis, back i (@vectorLine n i j)=0 := by
   simp_rw [vectorFn,map_sub,Finset.sum_sub_distrib,apply_ite,map_zero]
   rw [Finset.sum_ite_eq',if_pos (Finset.mem_univ j)]
   rw [show ∑ i : Axis, back i (fwd i (back j (@kernel n 2))) = lap (back j (@kernel n 2)) from (by unfold lap; rw [LinearMap.sum_apply]; rfl), lap_back,lap_two, sub_self]
lemma lap_one (x:Site n) : lap (kernel 1) x=(if x=0 then 1 else 0)-νt n:= by rw [lapR 0,if_pos rfl,zero_kernel]

lemma lap_vLine (i j : Axis) (n : Side) : lap (@vectorLine n i j)=
       (if i=j then lap (kernel 1) else 0)-fwd i (back j (kernel 1)):= by
   rw [vectorFn,map_sub,lap_fwd,lap_back,lap_two]; split; rfl; rw [map_zero]

/-- At position (x,i) return Chill( A(x,i), A(y,j)). -/
def imageVLine (y : Site n)(j : Axis) : ArrayA n:= fun i => move y (vectorLine i j)-move (-y-step j) (vectorLine i j)

lemma flipV (x y : Site n) (i j : Axis) :
    move y (vectorLine i j) x= move (-y-step j) (vectorLine i j) (-x-step i):= by
   rw [move_v,move_v]; unfold vectorLine
   apply congr_arg₂ (·-·)
   · split
     next h => subst i; rw [show -x-step j-(-y-step j)=-(x-y) from (by abel), kernel_even]
     rfl
   let z:=x-y; change fwd i _ z= _; rw [show -x-step i-(-y-step j)= -z+step j-step i by unfold z; abel]
   simp_rw [fwd_of,back_of]
   rw [sub_add_cancel, add_sub_cancel_right (-z) (step j), kernel_even,
       show -z+step j-step i-step j= -(z+step i) from (by abel), kernel_even,
       show -z+step j-step i= -(z+step i-step j) from (by abel), kernel_even,
       show -z+step j= -(z-step j) from (by abel), kernel_even]; ring
lemma imageVLine_odd (x y : Site n) (i j : Axis) :
    imageVLine y j i (-x-step i) = -imageVLine y j i x := by
   simp_rw [imageVLine,Pi.sub_apply]
   rw [flipV (-x-step i) y i j,reflected_neg, ← flipV x y i j]; abel
lemma imageVLine_transverse (x : Site n) (j : Axis) : Green.div (imageVLine x j)=0:=by
   rw [divergence]; simp_rw [imageVLine,map_sub, moved_back,Finset.sum_sub_distrib,← map_sum (move _), back_vline,map_zero, sub_zero]

lemma lap_imageV (x y : Site n)(j i : Axis) : lap (imageVLine y j i) x=
       (if i=j then ((if x=y then 1 else 0)-(if x= -y-step j then 1 else 0)) else 0)- fwd i (move y (back j (kernel 1))-move (-y-step j) (back j (kernel 1))) x := by
   simp_rw [imageVLine,map_sub,Pi.sub_apply,moved_lap,lap_vLine]
   rw [map_sub,Pi.sub_apply,map_sub,Pi.sub_apply,moved_fwd,moved_fwd]
   by_cases h:i=j
   · simp only [h,if_true,move_v,lap_one,sub_eq_zero]; ring
   rw [if_neg h, if_neg h]; simp
   ring

def dot (a b : Site n→ℝ) := ∑ x : Site n,a x * b x
lemma dot_addl (a b c : Site n→ℝ): Green.dot (a+b) c=Green.dot a c + Green.dot b c:= by unfold Green.dot; simp_rw [Pi.add_apply,add_mul,Finset.sum_add_distrib]
lemma dot_neg (a b : Site n→ℝ) : Green.dot (-a) b = -(Green.dot a b):= by unfold Green.dot;simp_rw [Pi.neg_apply,neg_mul,Finset.sum_neg_distrib]
lemma dot_zero (a : Site n→ℝ) : Green.dot (0:Site n→ℝ) a=0:=by unfold Green.dot;simp
lemma dot_subl (a b c : Site n→ℝ): Green.dot (a-b) c=Green.dot a c-Green.dot b c:= by simp_rw [sub_eq_add_neg,dot_addl,dot_neg]
lemma dot_turn (a b : Site n→ℝ):Green.dot a b=Green.dot b a:= Finset.sum_congr rfl fun i _=> mul_comm (a i) (b i)
lemma dot_subr (a b c : Site n→ℝ): Green.dot c (a-b)=Green.dot c a-Green.dot c b := by rw [dot_turn c (a-b),dot_subl,dot_turn a c,dot_turn c b]
lemma dot_sum {I : Type*} (s : Finset I) (a : I→Site n→ℝ) (b : Site n→ℝ) : Green.dot b (∑ i∈s,a i)= ∑ i∈s, Green.dot b (a i):= by unfold Green.dot; simp_rw [Finset.sum_apply, Finset.mul_sum]; exact Finset.sum_comm
lemma dot_dr (i:Axis) (a b:Site n→ℝ): Green.dot a (back i b)=Green.dot (fwd i a) b:= adjoint' ..
lemma dot_db (i:Axis) (a b:Site n→ℝ): Green.dot a (fwd i b)=Green.dot (back i a) b:= adjoint ..
lemma dot_grads (f g : Site n→ℝ) : Green.dot f (lap g)= ∑ i : Axis, Green.dot (fwd i f) (fwd i g):= by rw [← div_grad, divergence, dot_sum]; simp_rw [dot_dr,grad_v]

def closedD (f : Site n→ℝ) := ∀ i : Axis, fwd i f=0 -- gradient zeros

def linkdot (a b : ArrayA n) := ∑ i : Axis, Green.dot (a i) (b i)

def curl (a : ArrayA n) (i j : Axis) := fwd i (a j)-fwd j (a i)
lemma curl_op (a : ArrayA n) (i j : Axis): curl a j i= -(curl a i j):=by unfold curl; abel
lemma curl_grad (p : Site n→ℝ) (i j : Axis) : curl (grad p) i j=0:= by simp_rw [curl,grad_v,fwd_swap i j,sub_self]

def curldot (a b : ArrayA n) := ∑ k:PlaqAxes, Green.dot (curl a k.val.1 k.val.2) (curl b k.val.1 k.val.2)

lemma dot_expand (f g : ArrayA n) : 2*curldot f g = ∑ i:Axis, ∑ j:Axis, Green.dot (curl f i j) (curl g i j):= by
   apply MS.Tone.Frame.two_faces (fun ij => Green.dot (curl f ij.1 ij.2) (curl g ij.1 ij.2)) _ _
   · intro i; simp only [curl,sub_self,dot_zero]
   intro i j; rw [curl_op f j i, curl_op g j i, dot_neg,dot_turn (curl f j i), dot_neg,neg_neg,dot_turn ] -- verify orientation
lemma divergence_adj (a : ArrayA n) (p : Site n→ℝ) : linkdot a (grad p)=Green.dot (Green.div a) p := by unfold linkdot; rw [dot_turn (Green.div a),divergence,dot_sum]; simp_rw [grad_v,dot_db,dot_turn p]
lemma curl_cost (a b : ArrayA n) : curldot a b= linkdot a (fun i=>lap (b i))-Green.dot (Green.div a) (Green.div b) := by
   have he : Green.dot (Green.div a) (Green.div b)=∑ j:Axis, Green.dot (a j) (fwd j (Green.div b)):= (divergence_adj a _).symm
   have hv i j: Green.dot (fwd j (a i)) (curl b i j)= -Green.dot (fwd j (a i)) (curl b j i):= by
         rw [curl_op b j i, dot_turn, dot_neg, dot_turn]
   have hI : (∑ i:Axis,∑ j:Axis,Green.dot (fwd i (a j)) (curl b i j))=
          linkdot a (fun i=>lap (b i))-Green.dot (Green.div a) (Green.div b):= by
       rw [Finset.sum_comm,he,linkdot, ← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun j _=> ?_
       rw [divergence, map_sum, dot_sum,dot_grads]; simp_rw [curl,dot_subr, Finset.sum_sub_distrib]
       simp_rw [← dot_dr, mixed_swap j]
   rw [← hI]; apply mul_left_cancel₀ (show (2:ℝ)≠0 by norm_num)
   have he i j: Green.dot (curl a i j) (curl b i j)=Green.dot (fwd i (a j)) (curl b i j) + Green.dot (fwd j (a i)) (curl b j i):= by change Green.dot (_-_) _=_; rw [dot_subl,hv]; abel
   rw [dot_expand,two_mul]; simp_rw [he, Finset.sum_add_distrib]; congr 1; exact Finset.sum_comm

lemma sum_one (i : Axis) (j : Axis) (y : Site n)(A : ArrayA n) :
   ∑ x : Site n, A i x * (if i=j then ((if x=y then 1 else 0)-(if x= -y-step j then 1 else 0)) else 0)=
      if i=j then A i y - A i (-y-step j) else 0 := by split; simp only [ mul_sub, mul_ite,mul_one,mul_zero,Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,↓reduceIte]; simp
lemma lap_price (A : ArrayA n)(ht: Green.div A=0)(he:∀ i x,A i (-x-step i)= -A i x)(y:Site n)(j:Axis):
    linkdot A (fun i=> lap (imageVLine y j i))=2*A j y:= by
   let v : Site n→ℝ:= move y (back j (kernel 1))-move (-y-step j) (back j (kernel 1))
   have hz : linkdot A (grad v)=0:=by rw [divergence_adj,ht,dot_zero]
   have hv i: Green.dot (A i) (lap (imageVLine y j i)) = (if i=j then A i y - A i (-y-step j) else 0)-Green.dot (A i) (grad v i):= by
        unfold Green.dot; simp_rw [lap_imageV,mul_sub,Finset.sum_sub_distrib]; -- mul_sub beneath ite?
        rw [sum_one]; rfl
   unfold linkdot; simp_rw [hv,Finset.sum_sub_distrib]; rw [show ∑ i, Green.dot (A i) (grad v i)=0 from hz,Finset.sum_ite_eq',if_pos (Finset.mem_univ j), he]; ring
lemma curldot_inverse (A : ArrayA n)(ht:Green.div A=0)(he:∀ i x,A i (-x-step i)= -A i x)(y:Site n)(j:Axis):
     curldot A (imageVLine y j)=2*A j y:= by rw [curl_cost,lap_price A ht he y j,ht,dot_zero,sub_zero]

end YM.FVA2.Green
