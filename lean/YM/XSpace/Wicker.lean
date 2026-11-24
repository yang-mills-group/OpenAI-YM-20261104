import YM.XSpace.Satin
import YM.XSpace.Tipping

/-!
# α=1 Feynman gauge Meet:

Prove exact Hodge identity on step-one fields also with projection. This is sufficient
gauge comparison even though this Green is not the tree Green on potentials.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Feynman
open Function Set Topology Filter Module Chart2 Lattice
open scoped Topology BigOperators InnerProductSpace
variable {G:Gauge} {R:Period} {n:Side} {E: Type*} [AddCommGroup E] [Module ℝ E]
abbrev Table (n:Side) (E:Type*):= Site n → E
abbrev Fields (n:Side) (G:Gauge):= LogLinks (Per n) G

def slide (t:Site n): End ℝ (Table n E):= LinearMap.pi fun x=> LinearMap.proj (x+t)
lemma slide_at (t:Site n) (f:Table n E) (x:Site n): slide t f x=f (x+t):=rfl
lemma slide_slide (h g:Site n) (p:Table n E): slide h (slide g p)=slide g (slide h p):=funext fun i=> by simp [slide_at, add_right_comm]

def job (t:Site n): End ℝ (Table n E):= slide t-LinearMap.id
lemma job_at (t:Site n) (f:Table n E) (x:Site n): job t f x= f (x+t)-f x:=rfl
lemma job_job (h g:Site n) (p:Table n E): job h (job g p)=job g (job h p):=by simp only [job,LinearMap.sub_apply, LinearMap.id_coe,id_eq,map_sub,slide_slide h]; abel

def green (n:Side): End ℝ (Table n E):= LinearMap.pi fun x=> ∑ y:Site n, Potential.G n (x-y) • LinearMap.proj y
lemma green_at (p:Table n E) (x:Site n): green n p x=∑ y:Site n, Potential.G n (x-y) • p y:=by unfold green; rw [LinearMap.pi_apply,LinearMap.sum_apply]; rfl
lemma green_pair (x y:Site n): Potential.G n (x-y)= Potential.G n (y-x):=by unfold Potential.G; rw [← Potential.even, neg_sub]
lemma green_shift (p:Table n E) (t:Site n): green n (slide t p)= slide t (green n p):=by
  funext x; rw [slide_at,green_at,green_at,← Equiv.sum_comp (Equiv.addRight t) (fun y=> Potential.G n (x+t-y) • p y)]; simp only [Equiv.coe_addRight,add_sub_add_right_eq_sub,slide_at]
lemma green_ref (p:Table n E): green n (fun i=>p (-i))=fun i=> green n p (-i):=by funext x; rw [green_at,green_at,← Equiv.sum_comp (Equiv.neg (Site n)) (fun y=> Potential.G n (-x-y) • p y)]; simp only [Equiv.neg_apply, sub_neg_eq_add, ← sub_eq_neg_add]; simp_rw [green_pair x]
lemma green_step (t:Site n) (p:Table n E): green n (job t p) = job t (green n p):= by simp [job,green_shift]

abbrev forw (i:Axis): End ℝ (Table n E):= job (step i)
abbrev backw (i:Axis): End ℝ (Table n E):= job (-step i)
def heat (n:Side): End ℝ (Table n E):= ∑ i:Axis,(forw i).comp (backw i)
lemma green_heat (p:Table n E): green n (heat n p)= heat n (green n p):= by unfold heat; simp only [LinearMap.sum_apply,LinearMap.comp_apply,map_sum,forw,backw,green_step]
lemma heat_at (p:Table n E) (x:Site n): heat n p x=∑ i:Axis,(p x-p (x+step i)+(p x-p (x-step i))):=by unfold heat; rw [LinearMap.sum_apply,Finset.sum_apply]; apply Finset.sum_congr rfl; intro i _; simp only [LinearMap.comp_apply,forw,backw,job_at,add_neg_cancel_right]; rw [← sub_eq_add_neg]; abel
def mean (p:Table n E): E:= (((n.val:ℝ)^4)⁻¹) • ∑ i:Site n,p i
lemma green_pays (p:Table n E) (x:Site n) :green n (heat n p) x=p x-mean p:=by
  rw [green_heat,heat_at]; simp_rw [green_at, ← Finset.sum_sub_distrib,← Finset.sum_add_distrib, ← sub_smul, ← add_smul]; rw [Finset.sum_comm]; simp_rw [← Finset.sum_smul]
  have he y : Potential.scalar (Potential.G n) (x-y)=(∑ i:Axis,(Potential.G n (x-y)-Potential.G n (x+step i-y)+(Potential.G n (x-y)-Potential.G n (x-step i-y)))):=by rw [Potential.scalar_at]; apply Finset.sum_congr rfl; intro i _; rw [sub_add_eq_add_sub x y,sub_right_comm x y]
  simp_rw [← he,Potential.poisson,sub_smul,mean,Finset.sum_sub_distrib,Finset.smul_sum, sub_eq_zero]; simp [ite_smul]

-- fields and prices
abbrev slate (p:Fields n G) (i:Axis) :Table n G.Color := fun x=> p (x,i)
def flux (p:Fields n G) (i j:Axis): Table n G.Color:= forw i (slate p j)-forw j (slate p i)
lemma flux_at (p:Fields n G) (i j:Axis) (x): flux p i j x=(p (x+step i,j)-p (x,j))-(p (x+step j,i)-p (x,i)):=rfl
lemma flux_inv (p:Fields n G) (i j:Axis): flux p i j= -flux p j i:= neg_sub .. |>.symm
lemma flux_linear (p:Fields n G)(a:Face (Per n)): flux p a.2.val.1 a.2.val.2 a.1= linearFace a p:=by rw [angular,flux_at]; abel

def plume (v:Table n E):= ∑ x, v x
-- IBP
abbrev innerT (p q: Table n G.Color):= ∑ i, inner ℝ (p i) (q i)
abbrev innerF (p q: Fields n G):= ∑ i:Axis, innerT (slate p i) (slate q i)
lemma innerT_comm (p q:Table n G.Color): innerT p q=innerT q p:=Finset.sum_congr rfl fun _ _=> real_inner_comm ..
lemma innerT_sum {ι:Type*} (s:Finset ι) (P:ι→Table n G.Color) (p:Table n G.Color): innerT (∑ i∈s,P i) p= ∑ i∈s, innerT (P i) p:=by simp_rw [innerT,Finset.sum_apply,sum_inner]; rw [Finset.sum_comm]
lemma innerT_sub (p q x:Table n G.Color):innerT (p-q) x=innerT p x-innerT q x:=by simp only [innerT,Pi.sub_apply, inner_sub_left,Finset.sum_sub_distrib]
lemma innerT_minus (p q:Table n G.Color):innerT (-p) q= -innerT p q:=by simp only [innerT,Pi.neg_apply,inner_neg_left,Finset.sum_neg_distrib]
lemma innerF_comm (p q:Fields n G): innerF p q=innerF q p:=Finset.sum_congr rfl fun _ _=> innerT_comm ..
lemma parts (p q:Table n G.Color) (i:Axis) : innerT (backw i p) q=innerT p (forw i q):=by
  unfold backw forw job; simp_rw [LinearMap.sub_apply,LinearMap.id_coe,id_eq]; rw [innerT_comm p,innerT_sub,innerT_sub,innerT_comm q]; congr 1; unfold innerT; rw [← Equiv.sum_comp (Equiv.addRight (step i)) (fun x=> inner ℝ ((slide (-(step i:Site n))) p x) (q x))]; simp only [Equiv.coe_addRight,slide_at,add_neg_cancel_right]; exact Finset.sum_congr rfl fun _ _=> real_inner_comm ..

def cost (A:Fields n G): Fields n G:= fun p=> (∑ i:Axis, backw i (flux A i p.2)) p.1
lemma cost_at (A:Fields n G) (i): slate (cost A) i=∑ j:Axis, backw j (flux A j i):=rfl

-- split sum for antisym table by ordered face axes
lemma order_cost (p:Axis→Axis→ℝ) (h:∀ i,p i i=0) : (∑ j:Axis,∑ i:Axis,p i j)= ∑ o:PlaqAxes, (p o.val.1 o.val.2+p o.val.2 o.val.1):=by
  classical
  let L: Finset (Axis×Axis):= Finset.univ.filter (fun i=>i.1 < i.2)
  let X:Finset (Axis × Axis) := Finset.univ.filter (fun i=> i.2 < i.1)
  let Y:Finset (Axis × Axis) := Finset.univ.filter (fun i=> i.1≠i.2)
  have ht: Y=L ∪ X:= Finset.ext fun i=> by simp [Y,L,X]
  have hp (f: Axis × Axis →ℝ):∑ i∈L,f i=∑ i:PlaqAxes, f i.val := by unfold L PlaqAxes; generalize_proofs hz; exact (Finset.sum_subtype_eq_sum_filter ..).symm
  have hh : Disjoint L X:= Finset.disjoint_left.mpr (by intro i h q; simp [L] at h; simp [X] at q; exact (not_lt_of_gt h) q)
  let F i:= p (i:Axis×Axis).1 i.2; have hv : ∑ i∈X,F i=∑ i∈L,F (Prod.swap i):= by
    have hx : X=L.image Prod.swap:= Finset.ext fun ⟨i,j⟩=> by simp [X,L]
    rw [hx, Finset.sum_image]; intro i _ j _ h; exact (Equiv.prodComm Axis Axis).injective h
  calc _ = ∑ i:Axis×Axis, F i:= (Fintype.sum_prod_type_right ..).symm
       _ = ∑ i∈Y,F i:= Eq.symm (Finset.sum_subset (Finset.subset_univ _) (fun i _ hb=> by simp [Y] at hb; simp [F,hb,h]))
       _ = _ := by rw [ht,Finset.sum_union hh,hv,hp,hp, ← Finset.sum_add_distrib]; rfl

lemma whole_cost (A B:Fields n G): innerF (cost A) B= ∑ p:Face (Per n), inner ℝ (linearFace p A) (linearFace p B):=by
  unfold innerF; simp_rw [cost_at,innerT_sum,parts]
  rw [order_cost (fun i j=> innerT (flux A i j) (forw i (slate B j))) (fun i=> by simp [flux,innerT])]
  rw [Fintype.sum_prod_type_right]; apply Finset.sum_congr rfl; intro i _; simp_rw [← flux_linear]; rw [flux_inv A i.val.2, innerT_minus,← sub_eq_add_neg]
  have he (p q r:Table n G.Color): innerT p (q-r)= innerT p q-innerT p r:=by rw [innerT_comm p (q-r),innerT_sub,innerT_comm q,innerT_comm r]
  exact (he (flux A i.val.1 i.val.2) (forw i.val.1 (slate B i.val.2)) (forw i.val.2 (slate B i.val.1))).symm


def inward (p:Fields n G):Table n G.Color:=∑ i:Axis, backw i (slate p i)
theorem wave (A:Fields n G)(i:Axis): slate (cost A) i= heat n (slate A i)-forw i (inward A):=by
  rw [cost_at]; simp_rw [flux,map_sub,forw,backw,job_job (-_ : Site n)]; unfold inward heat; rw [LinearMap.sum_apply, map_sum, Finset.sum_sub_distrib]; rfl


def beamField (n:Side) : End ℝ (Fields n G):= LinearMap.pi fun e=> (LinearMap.proj e.1 ∘ₗ green n) ∘ₗ LinearMap.pi fun x=> LinearMap.proj (x,e.2)
lemma beam_val (A:Fields n G) (e:Edge (Site n)): beamField n A e=∑ y:Site n, Potential.G n (e.1-y) • A (y,e.2) := green_at ..
lemma beam_slate (A:Fields n G) (i:Axis): slate (beamField n A) i=green n (slate A i):=rfl
lemma beam_cost (A:Fields n G): beamField n (cost A)= A-(grad (green n (inward A))+fun e=> mean (slate A e.2)):=by
  funext e; obtain ⟨x,i⟩:=e; change slate (beamField n (cost A)) i x= A _ - (grad _ _ + mean _)
  rw [beam_slate,wave,map_sub,Pi.sub_apply,green_pays,forw,green_step,job_at,grad_at]; unfold slate; abel
lemma beam_inverse (A:R.Bonds→ G.Color): R.curl (beamField R.side (cost A))= R.curl A:=by rw [beam_cost,map_sub,map_add,Chart2.grad_eq_deriv R,R.curl_derivative, zero_add, show R.curl (fun e=>mean (slate A e.2))=0 from funext fun _=> by rw [R.curl_at]; simp [Period.curlIJ],sub_zero]
lemma green_sym (p q:Table n G.Color): innerT (green n p) q=innerT p (green n q):=by
  simp_rw [innerT, green_at,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro y _; rw [green_pair y]
lemma beam_sym (p q:Fields n G): innerF (beamField n p) q=innerF p (beamField n q):=by unfold innerF; simp_rw [beam_slate,green_sym]
lemma mirror_sym (p q:Fields R.side G): innerF (R.mirrorLink p) q= innerF p (R.mirrorLink q) := by
  apply Finset.sum_congr rfl; intro i _
  let L (x:R.Sites):= (R.reflect (x,i)).1
  have he : Function.Involutive L:= fun x=> congr_arg Prod.fst (R.reflect_invol (x,i))
  unfold innerT; rw [← Equiv.sum_comp (he.toPerm L) (fun x=>inner ℝ (slate p i x) (slate (R.mirrorLink q) i x))]; apply Finset.sum_congr rfl; intro x _; change inner ℝ (-(p _)) (q _) =inner ℝ (p (R.reflect (x,i))) (-q (R.reflect (R.reflect (x,i)))); rw [R.reflect_invol,inner_neg_left,inner_neg_right]
lemma reflected (A:Fields R.side G): R.mirrorLink (beamField R.side A)=beamField R.side (R.mirrorLink A):=by
  have he (i:Axis)(p:Fields R.side G): slate (R.mirrorLink p) i= -(slide (step i) (fun x=> slate p i (-x))):=by
    funext x; change -(p (R.reflect _)) = -(slate p i _); congr 2; refine Prod.ext (R.reflect_base _) rfl
  funext i; obtain ⟨x,i⟩:=i
  change slate (R.mirrorLink _) i x= slate (beamField _ _) i x
  rw [he i, beam_slate (R.mirrorLink A),he i,map_neg,green_shift,green_ref]; rfl
lemma hues (p:Fields R.side G) (c:G.ColorIndex): R.mirrorLink (light c p)= light c (R.mirrorLink p):=funext fun i=>by rw [R.mirror_apply, light_at,light_at,R.mirror_apply,map_neg]
lemma beam_color (p:Fields n G) (c:G.ColorIndex): beamField n (light c p)=light c (beamField n p):=by
  funext i; rw [beam_val,light_at,beam_val,map_sum]; simp_rw [map_smul,light_at]

-- unweighted Hilbert basis

def cellVec (b:Edge (Site n)) (i:G.ColorIndex):Fields n G:= Pi.single b (basisC G i)
lemma vec_at (b:Edge (Site n)) (i:G.ColorIndex): cellVec b i b=basisC G i:= Pi.single_eq_same ..
lemma knot (b:Edge (Site n)) (i:G.ColorIndex) (p:Fields n G):innerF p (cellVec b i)=p b i:=by
  obtain ⟨x,j⟩:=b; unfold innerF; rw [Finset.sum_eq_single j]
  · unfold innerT; rw [Finset.sum_eq_single x]; rw [show slate (cellVec (x,j) i) j x=_ from vec_at (x,j) i, real_inner_comm (basisC G i) _,EuclideanSpace.basisFun_inner]
    · intro y _ H; simp [slate,cellVec, Pi.single_eq_of_ne (show (y,j)≠(x,j) by simp [H])]
    simp
  · intro k _ H; unfold innerT; apply Finset.sum_eq_zero; intro y _; simp [slate,cellVec,Pi.single_eq_of_ne (show (y,k)≠(x,j) by simp [H])]
  simp
lemma innerF_b (p q:Fields n G):innerF p q= ∑ i:Edge (Site n),∑ j:G.ColorIndex, p i j*q i j:=by simp only [innerT,innerF, Fintype.sum_prod_type_right, PiLp.inner_apply, RCLike.inner_apply,starRingEnd_apply]; simp [mul_comm,slate]
lemma unique {p q:Fields n G} (he : ∀ A, innerF p A=innerF q A):p=q:=by ext i j; rw [← knot i j p, ← knot i j q]; apply he

def observe (v:Fields R.side G): RealDual (R:=R) (G:=G) where
  toFun p:= innerF v p
  map_add' p q:= by simp [innerF_b,mul_add,Finset.sum_add_distrib]
  map_smul' r p:= by simp only [innerF_b,RingHom.id_apply,Pi.smul_apply,PiLp.smul_apply,smul_eq_mul,mul_left_comm _ r, Finset.mul_sum]

def refer (R:Period) : RealDual (R:=R) (G:=G)→ₗ[ℝ] Fields R.side G where
  toFun p x:= WithLp.toLp 2 fun i=> p (cellVec x i)
  map_add' _ _:= rfl
  map_smul' _ _:= rfl
lemma refer_entry (p:RealDual (R:=R) (G:=G)) (b:R.Bonds)(i:G.ColorIndex): refer R p b i=p (cellVec b i):=rfl
lemma refer_ok (p:RealDual (R:=R) (G:=G)) (A:Fields R.side G): p A=innerF (refer R p) A:=by
  suffices H:p=observe (refer R p) from DFunLike.congr_fun H _
  classical
  refine (Pi.basis (fun _ : R.Bonds=> (basisC G).toBasis)).ext ?_; rintro ⟨i,j⟩; rw [Pi.basis_apply]; exact (knot i j (refer R p)).symm
end YM.XSpace.Feynman
