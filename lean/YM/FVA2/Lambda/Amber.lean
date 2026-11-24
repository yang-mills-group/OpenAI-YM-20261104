import YM.FVA2.Lambda.Pages
/-!
# Concrete d=4 compact polynomials at chosen axes. external pack

 Expand δ and combine identities for the contraction. Then Gaussian jets in Pars. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.Lathe
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open Canvas (quad high line4 triple upperquad trigger)
open MS.City MS.Plane.Flux
open Area Shells Pages
open Complex (I)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
variable {G:Gauge}{s t:ℝ}
local notation "g"=>triple G
local notation "Z"=>Momentum.sq (A:=Axis)
variable (q:QP)(x a:ℝ)(i:G.ColorIndex)
abbrev north (x:ℝ):= rayC 0 x
def marble (h y z x:ℝ):ℝ:= 10*y^2*z^2 + 20*h*y^2*z*x + (4*h^2*y^2-8*h^2*z+6*y^2*z+8*z^2)*x^2 + 8*h*(z-h^2)*x^3+4*(z-h^2)*x^4
def partQ (q:QP)(x:ℝ):= marble (q 0) (q 1) (Z q) x
lemma zipper : Z (q+north x)=Z q+2*x*(q 0)+x^2:= by simp [ Momentum.sq,Fin.sum_univ_four,north,spray,rayC, Axis, Pi.single_apply ]; ring
lemma vaneP : van q (north x) 0= ( Z q-(q 0)^2 )*(2* Z q+2*x*q 0+x^2):= by unfold van surf; rw [zipper]; simp only [precision,Landau.delta, ↓reduceIte ]; ring
local notation "d"=>Slice.delta
abbrev Mat:= Axis→Axis→ℝ
-- d project first.B.Project. maybe linear map use simp add.Force split.
def coral (q y:QP)(A B:Mat): ℝ:= ∑ a:Axis,∑ b:Axis,∑ i:Axis,∑ l:Axis, A i a*precision i l y*precision a b q*B l b
variable (u v:QP)(A B C:Mat)
lemma coral_comm : coral u v A B=coral u v B A:= by
    unfold coral; rw [ Finset.sum_comm ]; apply Finset.sum_congr rfl; intro a _; refine Finset.sum_congr rfl (fun b _=>?_); rw [ Finset.sum_comm ]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; rw [ realK b a u, realK j i v ]; ring -- q? fix
lemma coral_sum : coral u v (A+B) C=coral u v A C+coral u v B C:= by simp [coral, add_mul, Finset.sum_add_distrib]
lemma coral_scale : coral u v (x • A) C=x*coral u v A C:= by simp [coral,Finset.mul_sum,mul_assoc]
-- separable rank1.S
abbrev leaf (u v:QP): Mat:= fun i a=> u i * v a
lemma despoke : coral u v ( leaf v q ) B=0:= by
    unfold coral; apply Finset.sum_eq_zero; intro a _; apply Finset.sum_eq_zero; intro b _; rw [ Finset.sum_comm ]; apply Finset.sum_eq_zero; intro j _; have he (i:Axis): leaf v q i a * precision i j v*precision a b u * B j b= v i*precision i j v *(q a*precision a b u * B j b):= by unfold leaf; ring
    simp_rw [ he ]; rw [ ← Finset.sum_mul, transit, zero_mul ]
lemma dospoke : coral u v ( leaf q u ) B=0:= by
    unfold coral; have he (f:Axis→ Axis→ Axis→ℝ): (∑ a:Axis,∑ b:Axis,∑ c:Axis,f a b c)=∑ b:Axis,∑ c:Axis,∑ a:Axis,f a b c:= by rw [ Finset.sum_comm ]; exact Finset.sum_congr rfl fun i _=> Finset.sum_comm
    rw [ Finset.sum_comm ]; apply Finset.sum_eq_zero; intro b _; rw [he]; apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro l _; have hp (a:Axis): leaf q u i a * precision i l v*precision a b u*B l b=u a * precision a b u * (q i*precision i l v* B l b ):= by unfold leaf; ring
    simp_rw [hp]; rw [← Finset.sum_mul,transit,zero_mul]
def echo (q:QP)(x:ℝ): Mat:= fun i a=> Slice.rib i a 1 (-(q+north x)) q (north x)
-- projection only d cross. Name frame.
def Dmat :Mat:= d
def rim (i j:Axis):Mat:= fun v x=> leaf (spray i) (spray j) v x
def shock (q:QP)(x:ℝ):Mat:= (-2*q 1) • Dmat + (-2*x) • ( rim 0 1 ) + (2*x) • ( rim 1 0 )
lemma spray_χ (a b:Axis): spray a b=d a b:= by unfold spray Slice.delta; rw [Pi.single_apply]; split <;> split <;> simp_all
lemma delta_sym (a b:Axis): d a b=d b a:= by unfold Slice.delta; split <;> split <;> simp_all
-- simplify ψ.E. axis.
lemma echo_shock : echo q x= shock q x+ leaf (q+north x) (spray 1) + leaf (spray 1) q:= by
    ext i a; unfold echo shock leaf rim Dmat Slice.rib; simp only [Pi.add_apply,Pi.smul_apply,Pi.neg_apply,Pi.sub_apply,smul_eq_mul]; simp only [spray_χ, leaf, show d 0 1=0 from ( by norm_num [Slice.delta, Axis] ) ]; rw [delta_sym a 1 ]; ring
    -- want d 0 1 simplified; d 1 a = da1. etc.
lemma compact : gum q (north x) 1= coral q (q+north x) ( shock q x ) ( shock q x ):= by
    have he : gum q (north x) 1=coral q (q+north x) ( echo q x ) (echo q x):= by unfold gum gum1 coral; simp_rw [ Finset.mul_sum ]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun b _=>?_ ; unfold echo; ring
    rw [ he ]; have ht (A:Mat): coral q (q+north x) ( echo q x ) A=coral q (q+north x) (shock q x) A:= by rw [ echo_shock, coral_sum, coral_sum, despoke,dospoke ]; ring
    rw [ ht,coral_comm, ht ] -- orientation.L.
lemma catD : coral u v Dmat B=∑ a:Axis,∑ b:Axis,∑ i:Axis,precision a i v*precision a b u* B i b:= by
    unfold coral Dmat Slice.delta; refine Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun b _=> ?_; simp [ite_mul, Finset.sum_ite_irrel]
lemma catK (i j:Axis): coral u v (rim i j) B=∑ b:Axis,∑ l:Axis, precision i l v*precision j b u* B l b:= by
    unfold coral rim leaf; simp only [spray_χ]; unfold Slice.delta; simp [ite_mul,mul_ite,Finset.sum_ite_irrel]
lemma hereDD : coral u v Dmat Dmat=∑ a:Axis,∑ b:Axis,precision a b v*precision a b u:= by rw [catD]; unfold Dmat Slice.delta; simp [mul_ite]
lemma hereKD (i j:Axis): coral u v (rim i j) Dmat=∑ b:Axis,precision i b v*precision j b u:= by rw [catK ]; unfold Dmat Slice.delta; simp [mul_ite];
lemma hereKK (i j a b:Axis): coral u v (rim i j) ( rim a b)= precision i a v* precision j b u:= by rw [catK]; unfold rim leaf; simp only [spray_χ]; unfold Slice.delta; simp [mul_ite]
lemma buds : coral u v (shock q x) B= (-2*q 1) * coral u v Dmat B+(-2*x)*coral u v ( rim 0 1 ) B+(2*x)*coral u v ( rim 1 0 ) B:= by rw [shock,coral_sum,coral_sum]; simp only [coral_scale _ _ _ _] -- arguments?
set_option maxHeartbeats 750000 in
lemma statQ : gum q (north x) 1 -2*syrup q (north x) 1=partQ q x:= by
    rw [compact,buds]; simp_rw [coral_comm _ _ _ (shock q x),buds, hereDD, hereKD,coral_comm _ _ Dmat ( rim _ _ ), hereKD, hereKK ]; unfold syrup partQ marble; simp only [precision,zipper ]; norm_num [ Fin.sum_univ_four, Axis, Slice.delta,Landau.delta, north, spray, rayC, Pi.single_apply, Momentum.sq, show (0:Fin 4)≠1 from (by decide), show (0:Fin 4)≠2 from (by decide), show (0:Fin 4)≠3 from (by decide), show (1:Fin 4)≠0 from (by decide), show (1:Fin 4)≠2 from (by decide), show (1:Fin 4)≠3 from (by decide), show (2:Fin 4)≠0 from (by decide), show (2:Fin 4)≠1 from (by decide), show (2:Fin 4)≠3 from (by decide), show (3:Fin 4)≠0 from (by decide), show (3:Fin 4)≠1 from (by decide), show (3:Fin 4)≠2 from (by decide) ]; ring
end YM.FVA2.Lambda.Lathe
